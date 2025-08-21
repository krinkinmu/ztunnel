// Copyright Istio Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::identity::{Identity, SecretManager};
use crate::proxy::{Error, HboneAddress, OnDemandDnsLabels};
use crate::rbac::Authorization;
use crate::state::policy::PolicyStore;
use crate::state::service::{
    Endpoint, IpFamily, LoadBalancerMode, LoadBalancerScopes, ServiceStore,
};
use crate::state::service::{Service, ServiceDescription};
use crate::state::workload::{
    GatewayAddress, InboundProtocol, NamespacedHostname, NetworkAddress, Workload, WorkloadStore, address::Address,
    gatewayaddress::Destination, network_addr,
};
use crate::strng::Strng;
use crate::tls;
use crate::xds::istio::security::Authorization as XdsAuthorization;
use crate::xds::istio::workload::Address as XdsAddress;
use crate::xds::{AdsClient, Demander, LocalClient, ProxyStateUpdater};
use crate::{cert_fetcher, config, rbac, xds};
use crate::{proxy, strng};
use educe::Educe;
use futures_util::FutureExt;
use hickory_resolver::TokioResolver;
use hickory_resolver::config::*;
use hickory_resolver::name_server::TokioConnectionProvider;
use itertools::Itertools;
use rand::prelude::IteratorRandom;
use rand::seq::IndexedRandom;
use serde::Serializer;
use std::collections::{HashMap, HashSet};
use std::convert::Into;
use std::default::Default;
use std::fmt;
use std::net::{IpAddr, SocketAddr};
use std::str::FromStr;
use std::sync::{Arc, RwLock, RwLockReadGuard};
use std::time::Duration;
use tracing::{info, debug, trace, warn};

use self::workload::ApplicationTunnel;

pub mod policy;
pub mod service;
pub mod workload;

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Upstream {
    /// Workload is the workload we are connecting to
    pub workload: Arc<Workload>,
    /// selected_workload_ip defines the IP address we should actually use to connect to this workload
    /// This handles multiple IPs (dual stack) or Hostname destinations (DNS resolution)
    /// The workload IP might be empty if we have to go through a network gateway.
    pub selected_workload_ip: Option<IpAddr>,
    /// Port is the port we should connect to
    pub port: u16,
    /// Service SANs defines SANs defined at the service level *only*. A complete view of things requires
    /// looking at workload.identity() as well.
    pub service_sans: Vec<Strng>,
    /// If this was from a service, the service info.
    pub destination_service: Option<ServiceDescription>,
    /// Original target VIP we tried to resolve. When we resolve waypoints, this should be VIP of
    /// the original target service or workload and not waypoint address
    pub original_target: SocketAddr,
    /// When connection is routed through a waypoint this will be true, false otherwise.
    pub through_waypoint: bool,
    /// Port we connect to when we talk to a ztunnel on the other side (e.g., no waypoint and using
    /// HBONE protocol).
    pub hbone_port: u16,
}

impl Upstream {
    pub fn workload_socket_addr(&self) -> Option<SocketAddr> {
        // When we talk to another ztunnel directly (e.g., no waypoint) instead of connecting to
        // the target port we need to connect to the HBONE port where ztunnel listens.
        let port = if self.workload.protocol == InboundProtocol::HBONE && !self.through_waypoint {
            self.hbone_port
        } else {
            self.port
        };
        self.selected_workload_ip.map(|ip| SocketAddr::new(ip, port))
    }

    pub fn workload_and_services_san(&self) -> Vec<Identity> {
        self.service_sans
            .iter()
            .flat_map(|san| match Identity::from_str(san) {
                Ok(id) => Some(id),
                Err(err) => {
                    warn!("ignoring invalid SAN {}: {}", san, err);
                    None
                }
            })
            .chain(std::iter::once(self.workload.identity()))
            .collect()
    }

    pub fn service_sans(&self) -> Vec<Identity> {
        self.service_sans
            .iter()
            .flat_map(|san| match Identity::from_str(san) {
                Ok(id) => Some(id),
                Err(err) => {
                    warn!("ignoring invalid SAN {}: {}", san, err);
                    None
                }
            })
            .collect()
    }

    pub fn hbone_target_destination(&self) -> Result<Option<HboneAddress>, Error> {
        if self.through_waypoint {
            // When request is routed through a waypoint using HBONE, we preserve the original
            // target as HBONE :authority.
            //
            // NOTE: there is one exception for this and that's when we send request to another
            // network through an E/W gateway - in this case we always use target service hostname
            // instead of an original VIP.
            Ok(Some(HboneAddress::SocketAddr(self.original_target)))
        } else {
            // If request does not go through the waypoint and we use HBONE protocol it basically
            // means that we are talking directly to another waypoint. When it is the case we can
            // use the workload address directly as the HBONE target.
            //
            // And when protocol is TCP, then we don't use HBONE at all, so there is no HBONE
            // :authority to begin with.
            //
            // NOTE: There is one exception to this - when we talk to E/W gateway. When that's the
            // case we will see protocol TCP, but we still would need to use HBONE (actually double
            // HBONE) protocol, but it's a special case that the caller need to handle.
            match self.workload.protocol {
                InboundProtocol::HBONE => self.selected_workload_ip.map(
                    |ip| Some(HboneAddress::SocketAddr(SocketAddr::new(ip, self.port))))
                    .ok_or(Error::NoValidDestination(Box::new((*self.workload).clone()))),
                InboundProtocol::TCP => Ok(None),
            }
        }
    }
}

// Workload information that a specific proxy instance represents. This is used to cross check
// with the workload fetched using destination address when making RBAC decisions.
#[derive(
    Debug, Clone, Eq, Hash, Ord, PartialEq, PartialOrd, serde::Serialize, serde::Deserialize,
)]
#[serde(rename_all = "camelCase")]
pub struct WorkloadInfo {
    pub name: String,
    pub namespace: String,
    pub service_account: String,
}

impl fmt::Display for WorkloadInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}.{} ({})",
            self.service_account, self.namespace, self.name
        )
    }
}

impl WorkloadInfo {
    pub fn new(name: String, namespace: String, service_account: String) -> Self {
        Self {
            name,
            namespace,
            service_account,
        }
    }

    pub fn matches(&self, w: &Workload) -> bool {
        self.name == w.name
            && self.namespace == w.namespace
            && self.service_account == w.service_account
    }
}

#[derive(Educe, Debug, Clone, Eq, serde::Serialize)]
#[educe(PartialEq, Hash)]
pub struct ProxyRbacContext {
    pub conn: rbac::Connection,
    #[educe(Hash(ignore), PartialEq(ignore))]
    pub dest_workload: Arc<Workload>,
}

impl ProxyRbacContext {
    pub fn into_conn(self) -> rbac::Connection {
        self.conn
    }
}

impl fmt::Display for ProxyRbacContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ({})", self.conn, self.dest_workload.uid)?;
        Ok(())
    }
}

#[derive(Clone)]
struct Candidate {
    workload: Arc<Workload>,
    waypoint: Option<Arc<Service>>,
    endpoint: Endpoint,
    port: u16,
}

struct EndpointPicker<'a> {
    source_workload: &'a Workload,
    target_service: &'a Service,
    candidates: HashMap<Strng, Candidate>,
    clusters: HashMap<Strng, Vec<Candidate>>,
    best_rank: usize,
    has_waypoints: bool,
    has_directs: bool,
}

impl<'a> EndpointPicker<'a> {
    fn new(source_workload: &'a Workload, target_service: &'a Service) -> Self {
        EndpointPicker {
            source_workload,
            target_service,
            candidates: Default::default(),
            clusters: Default::default(),
            best_rank: 0,
            has_waypoints: false,
            has_directs: false,
        }
    }

    /// Rank tells us how closly does the target workload match the routing preferences of the
    /// service. The higher the rank the better the target workload fit the load balancing
    /// preferences.
    ///
    /// If target workload does not match load balancing policy at all, None is returned.
    fn workload_rank(&self, target: &Workload) -> Option<usize> {
        // Say load balancing policy sets routing prefernces so we need to consider network,
        // region and zone (e.g., routing preferences list is [Network, Region, Zone].
        //
        // We will go over the routing preferences list and compare network, region and zone
        // of the source and target workloads in that order. When they match we will add +1
        // to the rank, and when they don't match we stop.
        //
        // So in the example above, when all the criteria match we will get rank 3. If zone is
        // different, but network and region are the same, we will get rank 2. If network matches
        // but the region does not, then regardless of whether the zone matches, the rank will be
        // 1.
        match &self.target_service.load_balancer {
            Some(lb) if lb.mode != LoadBalancerMode::Standard => {
                let source = &self.source_workload;
                let mut rank = 0;
                for scope in &lb.routing_preferences {
                    let matches = match scope {
                        LoadBalancerScopes::Region => source.locality.region == target.locality.region,
                        LoadBalancerScopes::Zone => source.locality.zone == target.locality.zone,
                        LoadBalancerScopes::Subzone => source.locality.subzone == target.locality.subzone,
                        LoadBalancerScopes::Node => source.node == target.node,
                        LoadBalancerScopes::Cluster => source.cluster_id == target.cluster_id,
                        LoadBalancerScopes::Network => source.network == target.network,
                    };
                    if matches {
                        rank += 1;
                    } else {
                        break;
                    }
                }
                if lb.mode == LoadBalancerMode::Strict && rank != lb.routing_preferences.len() {
                    return None;
                }
                Some(rank)
            },
            _ => Some(0),
        }
    }

    fn add_waypoint_endpoint(&mut self, workload: Arc<Workload>, waypoint: Arc<Service>, endpoint: Endpoint, port: u16) {
        let candidate = Candidate {
            workload,
            waypoint: Some(waypoint),
            endpoint,
            port,
        };
        self.add_candidate(candidate);
    }

    fn add_direct_endpoint(&mut self, workload: Arc<Workload>, endpoint: Endpoint, port: u16) {
        let candidate = Candidate {
            workload,
            waypoint: None,
            endpoint,
            port,
        };
        self.add_candidate(candidate);
    }

    fn add_candidate(&mut self, candidate: Candidate) {
        let rank = match self.workload_rank(&candidate.workload) {
            Some(rank) => rank,
            _ => return,
        };

        if rank < self.best_rank {
            // If it's not as good as some other options we've seen already, then we can ignore it
            return;
        }

        if rank > self.best_rank {
            // If it's strictly better than anything we've seen so far, then we can drop all the
            // endpoints we've considered up to this point and start from scratch.
            self.candidates = Default::default();
            self.clusters = Default::default();
            self.best_rank = rank;
            self.has_waypoints = false;
            self.has_directs = false;
        }

        let uid = candidate.workload.uid.clone();
        let cluster_id = candidate.workload.cluster_id.clone();

        if self.candidates.insert(uid, candidate.clone()).is_none() {
            if candidate.waypoint.is_some() {
                self.has_waypoints = true;
            } else {
                self.has_directs = true;
            }
            self.clusters.entry(cluster_id).or_insert(Vec::new()).push(candidate);
        }
    }

    fn pick_candidate(&self) -> Option<&Candidate> {
        // We have multiple options how we can pick an endpoint out of many availble in
        // multi-cluster scenario and none of those options is ideal:
        //
        // 1. We can pick random cluster from the list assuming equal weight and then pick an
        //    endpoint in that cluster
        // 2. We can pick among all endpoints proportionally to workload capacity.
        //
        // Why both of those options are not ideal?
        //
        // If we keep cluster randomly first, that assumes that all clusters have roughly the
        // same capacity to handle requests, which may not necessarily be true.
        //
        // To address the problem above, we may pick a backend ignoring clusters according to
        // the capacity of the endpoint. That would work in uniform setup, however, in non-unifrom
        // setup we will be picking between actual service endpoints and waypoint endpoints which
        // is like compraing apples and oranges.
        //
        // In the alpha version what we did is as follows:
        //
        // 1. We assumed that setup is uniform, e.g. the same service will either have or not have
        //    a waypoint in all the clusters
        // 2. For services with waypoint, we inherit PreferLocal load balancing policy, so traffic
        //    will stay local unless there are no healthy waypoint endpoints in the local cluster,
        //    in which case it will failover to a remote cluster
        // 3. For services with no waypoint, if there is no traffic policy set on the service, we
        //    will distribute the load between endpoints according to endpoint capacity.
        //
        // As far as multi-cluster setups are concerned, while alpha behavior makes sense it's
        // somewhat inconsistent (i.e., services with waypoint keep traffic local, while
        // services without waypoint do not).
        //
        // In this version, we opted into bringing some consistency when we have a choice between
        // clusters:
        //
        // 1. We respect the load balancing policy (if load balancing policy prefers local, we will
        //    try to stay local)
        // 2. When load balancing policy does not set preference, we just distribute the load
        //    between clusters and pick a backend within the cluster according to capacity.
        //
        // With this, both services with and without waypoint will distribute the load between
        // clusters by default. If users want to change that, they could set PreferClose on the
        // service to prefer local clusters and only failover when there are no healthy local
        // endpoints. It's also somewhat closer to multi-cluster behavior in sidecar mode.
        //
        // Forward looking, a north star if you will, should be implementing latency based load
        // balancing and outlier detection. e2e latency is a good unifying metric that would allow
        // us to compare routes through waypoint, e/w gateways and directly service backends
        // uniformly, while outlier detection would allow us to eject routes that result in failed
        // requests.
        //
        // Additionally, when setup is completely uniform (e.g., either all endpoints are waypoints
        // or none of them are) we use to capacity based load-balancing.

        if self.candidates.is_empty() {
            assert!(self.clusters.is_empty());
            return None;
        }
        assert!(!self.clusters.is_empty());

        // For the purposes of selecting our load balancing algorithm, we consider the setup
        // uniform if it all the endpoints are waypoints or if none of them are waypoints. When
        // it's the case, we can compare costs of the backends directly and avoid comparing apples
        // to organges (where regular service backends are apples and waypoint backends are
        // oranges). When setup is uniform we pick endpoint proportionally to the capacity (and it
        // would either be a capacity of the target service backend or capacity of waypoint).
        let setup_is_uniform = self.has_waypoints != self.has_directs;
        if setup_is_uniform {
            let options = self.candidates.iter().map(|(_, c)| { c }).collect::<Vec<_>>();

            if options.is_empty() {
                None
            } else {
                options.choose_weighted(&mut rand::rng(), |c| c.workload.capacity as u64).ok().map(|r| *r)
            }
        } else {
            // When setup is not uniform, directly comparing capacity of workloads is a bit strange
            // because we would comparing capacity of the actual service backends to capacity of a
            // proxy in front of the actual service backends.
            //
            // Instead we use another dubious approximation - we assume all clusters are equal and
            // randomly pick a cluster and then pick a backend in that cluster proportionally to
            // capacity.
            let clusters = self.clusters.iter().map(|(c, _)| { c }).collect::<Vec<_>>();
            // We checked above that the list of candidates is not empty and each candidate belongs
            // to a cluster, so the list of clusters must not be empty either.
            let cluster = clusters.choose(&mut rand::rng()).unwrap();

            self.clusters[*cluster].choose_weighted(
                &mut rand::rng(), |c| { c.workload.capacity as u64 }).ok()
        }
    }
}

/// The current state information for this proxy.
#[derive(Debug)]
pub struct ProxyState {
    pub workloads: WorkloadStore,

    pub services: ServiceStore,

    pub policies: PolicyStore,
}

#[derive(serde::Serialize, Debug)]
#[serde(rename_all = "camelCase")]
struct ProxyStateSerialization<'a> {
    workloads: Vec<Arc<Workload>>,
    services: Vec<Arc<Service>>,
    policies: Vec<Authorization>,
    staged_services: &'a HashMap<NamespacedHostname, HashMap<Strng, Endpoint>>,
}

impl serde::Serialize for ProxyState {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        // Services all have hostname, so use that as the key
        let services: Vec<_> = self
            .services
            .by_host
            .iter()
            .sorted_by_key(|k| k.0)
            .flat_map(|k| k.1)
            .cloned()
            .collect();
        // Workloads all have a UID, so use that as the key
        let workloads: Vec<_> = self
            .workloads
            .by_uid
            .iter()
            .sorted_by_key(|k| k.0)
            .map(|k| k.1)
            .cloned()
            .collect();
        let policies: Vec<_> = self
            .policies
            .by_key
            .iter()
            .sorted_by_key(|k| k.0)
            .map(|k| k.1)
            .cloned()
            .collect();
        let serializable = ProxyStateSerialization {
            workloads,
            services,
            policies,
            staged_services: &self.services.staged_services,
        };
        serializable.serialize(serializer)
    }
}

impl ProxyState {
    pub fn new(local_node: Option<Strng>) -> ProxyState {
        ProxyState {
            workloads: WorkloadStore::new(local_node),
            services: Default::default(),
            policies: Default::default(),
        }
    }

    /// Find either a workload or service by the destination.
    pub fn find_destination(&self, dest: &Destination) -> Option<Address> {
        match dest {
            Destination::Address(addr) => self.find_address(addr),
            Destination::Hostname(hostname) => self.find_hostname(hostname),
        }
    }

    /// Find either a workload or a service by address.
    pub fn find_address(&self, network_addr: &NetworkAddress) -> Option<Address> {
        // 1. handle workload ip, if workload not found fallback to service.
        match self.workloads.find_address(network_addr) {
            None => {
                // 2. handle service
                if let Some(svc) = self.services.get_by_vip(network_addr) {
                    return Some(Address::Service(svc));
                }
                None
            }
            Some(wl) => Some(Address::Workload(wl)),
        }
    }

    /// Find either a workload or a service by hostname.
    pub fn find_hostname(&self, name: &NamespacedHostname) -> Option<Address> {
        // Hostnames for services are more common, so lookup service first and fallback to workload.
        self.services
            .get_by_namespaced_host(name)
            .map(Address::Service)
            .or_else(|| {
                // Slow path: lookup workload by O(n) lookup. This is an uncommon path, so probably not worth
                // the memory cost to index currently
                self.workloads
                    .by_uid
                    .values()
                    .find(|w| w.hostname == name.hostname && w.namespace == name.namespace)
                    .cloned()
                    .map(Address::Workload)
            })
    }

    /// Find services by hostname.
    pub fn find_service_by_hostname(&self, hostname: &Strng) -> Result<Vec<Arc<Service>>, Error> {
        // Hostnames for services are more common, so lookup service first and fallback to workload.
        self.services
            .get_by_host(hostname)
            .ok_or_else(|| Error::NoHostname(hostname.to_string()))
    }

    fn find_upstream(
        &self,
        network: Strng,
        source_workload: &Workload,
        addr: SocketAddr,
        resolution_mode: ServiceResolutionMode,
    ) -> Option<(Arc<Workload>, u16, Option<Arc<Service>>)> {
        if let Some(svc) = self
            .services
            .get_by_vip(&network_addr(network.clone(), addr.ip()))
        {
            return self.find_upstream_from_service(
                source_workload,
                addr.port(),
                resolution_mode,
                svc,
            );
        }
        if let Some(wl) = self
            .workloads
            .find_address(&network_addr(network, addr.ip()))
        {
            return Some((wl, addr.port(), None));
        }
        None
    }

    fn find_upstream_from_service(
        &self,
        source_workload: &Workload,
        svc_port: u16,
        resolution_mode: ServiceResolutionMode,
        svc: Arc<Service>,
    ) -> Option<(Arc<Workload>, u16, Option<Arc<Service>>)> {
        // Randomly pick an upstream
        // TODO: do this more efficiently, and not just randomly
        let Some((ep, wl)) = self.load_balance(source_workload, &svc, svc_port, resolution_mode)
        else {
            debug!("Service {} has no healthy endpoints", svc.hostname);
            return None;
        };

        let svc_target_port = svc.ports.get(&svc_port).copied().unwrap_or_default();
        let target_port = if let Some(&ep_target_port) = ep.port.get(&svc_port) {
            // prefer endpoint port mapping
            ep_target_port
        } else if svc_target_port > 0 {
            // otherwise, see if the service has this port
            svc_target_port
        } else if let Some(ApplicationTunnel { port: Some(_), .. }) = &wl.application_tunnel {
            // when using app tunnel, we don't require the port to be found on the service
            svc_port
        } else {
            // no app tunnel or port mapping, error
            debug!(
                "found service {}, but port {} was unknown",
                svc.hostname, svc_port
            );
            return None;
        };

        Some((wl, target_port, Some(svc)))
    }

    fn load_balance(
        &self,
        src: &Workload,
        svc: &Service,
        svc_port: u16,
        resolution_mode: ServiceResolutionMode,
    ) -> Option<(Endpoint, Arc<Workload>)> {
        let target_port = svc.ports.get(&svc_port).copied();

        if resolution_mode == ServiceResolutionMode::Standard && target_port.is_none() {
            // Port doesn't exist on the service at all, this is invalid
            debug!("service {} does not have port {}", svc.hostname, svc_port);
            return None;
        };

        debug!("picking an end point for service: {:?}", svc);

        let mut picker = EndpointPicker::new(src, svc);
        for ep in svc.endpoints.iter() {
            debug!("considering {}", ep.workload_uid);
            let Some(wl) = self.workloads.find_uid(&ep.workload_uid) else {
                debug!("failed to fetch workload for {}", ep.workload_uid);
                continue;
            };

            let in_network = wl.network == src.network;
            let has_network_gateway = wl.network_gateway.is_some();
            let has_address = !wl.workload_ips.is_empty() || !wl.hostname.is_empty();
            if !has_address {
                // Workload has no IP. We can only reach it via a network gateway
                // WDS is client-agnostic, so we will get a network gateway for a workload
                // even if it's in the same network; we should never use it.
                if in_network || !has_network_gateway {
                    continue;
                }
            }

            match resolution_mode {
                ServiceResolutionMode::Standard => {
                    if target_port.unwrap_or_default() == 0 && !ep.port.contains_key(&svc_port) {
                        // Filter workload out, it doesn't have a matching port
                        debug!(
                            "filter endpoint {}, it does not have service port {}",
                            ep.workload_uid, svc_port
                        );
                        continue;
                    }
                }
                ServiceResolutionMode::Waypoint => {
                    if target_port.is_none() && wl.application_tunnel.is_none() {
                        // We ignore this for app_tunnel; in this case, the port does not need to be on the service.
                        // This is only valid for waypoints, which are not explicitly addressed by users.
                        // We do happen to do a lookup by `waypoint-svc:15008`, this is not a literal call on that service;
                        // the port is not required at all if they have application tunnel, as it will be handled by ztunnel on the other end.
                        debug!(
                            "filter waypoint endpoint {}, target port is not defined",
                            ep.workload_uid
                        );
                        continue;
                    }
                }
            }

            picker.add_direct_endpoint(wl, ep.clone(), /*calling code figures out the right port*/0);
        }

        if let Some(candidate) = picker.pick_candidate() {
            debug!("identified a candiate");
            Some((candidate.endpoint.clone(), candidate.workload.clone()))
        } else {
            debug!("failed to find a viable candidate");
            None
        }
    }
}

/// Wrapper around [ProxyState] that provides additional methods for requesting information
/// on-demand.
#[derive(serde::Serialize, Clone)]
pub struct DemandProxyState {
    #[serde(flatten)]
    state: Arc<RwLock<ProxyState>>,

    /// If present, used to request on-demand updates for workloads.
    #[serde(skip_serializing)]
    demand: Option<Demander>,

    #[serde(skip_serializing)]
    metrics: Arc<proxy::Metrics>,

    #[serde(skip_serializing)]
    dns_resolver: TokioResolver,

    #[serde(skip_serializing)]
    hbone_port: u16,
}

impl DemandProxyState {
    pub(crate) fn get_services_by_workload(&self, wl: &Workload) -> Vec<Arc<Service>> {
        self.state
            .read()
            .expect("mutex")
            .services
            .get_by_workload(wl)
    }
}

impl DemandProxyState {
    pub fn new(
        state: Arc<RwLock<ProxyState>>,
        demand: Option<Demander>,
        dns_resolver_cfg: ResolverConfig,
        dns_resolver_opts: ResolverOpts,
        metrics: Arc<proxy::Metrics>,
        hbone_port: u16,
    ) -> Self {
        let mut rb = hickory_resolver::Resolver::builder_with_config(
            dns_resolver_cfg,
            TokioConnectionProvider::default(),
        );
        *rb.options_mut() = dns_resolver_opts;
        let dns_resolver = rb.build();
        Self {
            state,
            demand,
            dns_resolver,
            metrics,
            hbone_port,
        }
    }

    #[cfg(any(test, feature = "testing"))]
    pub fn set_hbone_port(&mut self, hbone_port: u16) {
        self.hbone_port = hbone_port;
    }

    pub fn read(&self) -> RwLockReadGuard<'_, ProxyState> {
        self.state.read().unwrap()
    }

    pub async fn assert_rbac(
        &self,
        ctx: &ProxyRbacContext,
    ) -> Result<(), proxy::AuthorizationRejectionError> {
        let wl = &ctx.dest_workload;
        let conn = &ctx.conn;
        let state = self.read();

        // We can get policies from namespace, global, and workload...
        let ns = state.policies.get_by_namespace(&wl.namespace);
        let global = state.policies.get_by_namespace(&crate::strng::EMPTY);
        let workload = wl.authorization_policies.iter();

        // Aggregate all of them based on type
        let (allow, deny): (Vec<_>, Vec<_>) = ns
            .iter()
            .chain(global.iter())
            .chain(workload)
            .filter_map(|k| {
                let pol = state.policies.get(k);
                // Policy not found. This is probably transition state where the policy hasn't been sent
                // by the control plane, or it was just removed.
                if pol.is_none() {
                    warn!("skipping unknown policy {k}");
                }
                pol
            })
            .partition(|p| p.action == rbac::RbacAction::Allow);

        trace!(
            allow = allow.len(),
            deny = deny.len(),
            "checking connection"
        );

        // Allow and deny logic follows https://istio.io/latest/docs/reference/config/security/authorization-policy/

        // "If there are any DENY policies that match the request, deny the request."
        for pol in deny.iter() {
            if pol.matches(conn) {
                debug!(policy = pol.to_key().as_str(), "deny policy match");
                return Err(proxy::AuthorizationRejectionError::ExplicitlyDenied(
                    pol.namespace.to_owned(),
                    pol.name.to_owned(),
                ));
            } else {
                trace!(policy = pol.to_key().as_str(), "deny policy does not match");
            }
        }
        // "If there are no ALLOW policies for the workload, allow the request."
        if allow.is_empty() {
            debug!("no allow policies, allow");
            return Ok(());
        }
        // "If any of the ALLOW policies match the request, allow the request."
        for pol in allow.iter() {
            if pol.matches(conn) {
                debug!(policy = pol.to_key().as_str(), "allow policy match");
                return Ok(());
            } else {
                trace!(
                    policy = pol.to_key().as_str(),
                    "allow policy does not match"
                );
            }
        }
        // "Deny the request."
        debug!("no allow policies matched");
        Err(proxy::AuthorizationRejectionError::NotAllowed)
    }

    // Select a workload IP, with DNS resolution if needed
    async fn pick_workload_destination_or_resolve(
        &self,
        dst_workload: &Workload,
        src_workload: &Workload,
        original_target_address: SocketAddr,
        ip_family_restriction: Option<IpFamily>,
    ) -> Result<Option<IpAddr>, Error> {
        // If the user requested the pod by a specific IP, use that directly.
        if dst_workload
            .workload_ips
            .contains(&original_target_address.ip())
        {
            return Ok(Some(original_target_address.ip()));
        }
        // They may have 1 or 2 IPs (single/dual stack)
        // Ensure we are meeting the Service family restriction (if any is defined).
        // Otherwise, prefer the same IP family as the original request.
        if let Some(ip) = dst_workload
            .workload_ips
            .iter()
            .filter(|ip| {
                ip_family_restriction
                    .map(|f| f.accepts_ip(**ip))
                    .unwrap_or(true)
            })
            .find_or_first(|ip| ip.is_ipv6() == original_target_address.is_ipv6())
        {
            return Ok(Some(*ip));
        }
        if dst_workload.hostname.is_empty() {
            if dst_workload.network_gateway.is_none() {
                debug!(
                    "workload {} has no suitable workload IPs for routing",
                    dst_workload.name
                );
                return Err(Error::NoValidDestination(Box::new(dst_workload.clone())));
            } else {
                // We can route through network gateway
                return Ok(None);
            }
        }
        let ip = Box::pin(self.resolve_workload_address(
            dst_workload,
            src_workload,
            original_target_address,
        ))
        .await?;
        Ok(Some(ip))
    }

    async fn resolve_workload_address(
        &self,
        workload: &Workload,
        src_workload: &Workload,
        original_target_address: SocketAddr,
    ) -> Result<IpAddr, Error> {
        let labels = OnDemandDnsLabels::new()
            .with_destination(workload)
            .with_source(src_workload);
        self.metrics
            .as_ref()
            .on_demand_dns
            .get_or_create(&labels)
            .inc();
        self.resolve_on_demand_dns(workload, original_target_address)
            .await
    }

    async fn resolve_on_demand_dns(
        &self,
        workload: &Workload,
        original_target_address: SocketAddr,
    ) -> Result<IpAddr, Error> {
        let workload_uid = workload.uid.clone();
        let hostname = workload.hostname.clone();
        trace!(%hostname, "starting DNS lookup");

        let resp = match self.dns_resolver.lookup_ip(hostname.as_str()).await {
            Err(err) => {
                warn!(?err,%hostname,"dns lookup failed");
                return Err(Error::NoResolvedAddresses(workload_uid.to_string()));
            }
            Ok(resp) => resp,
        };
        trace!(%hostname, "dns lookup complete {resp:?}");

        let (matching, unmatching): (Vec<_>, Vec<_>) = resp
            .as_lookup()
            .record_iter()
            .filter_map(|record| record.data().ip_addr())
            .partition(|record| record.is_ipv6() == original_target_address.is_ipv6());
        // Randomly pick an IP, prefer to match the IP family of the downstream request.
        // Without this, we run into trouble in pure v4 or pure v6 environments.
        matching
            .into_iter()
            .choose(&mut rand::rng())
            .or_else(|| unmatching.into_iter().choose(&mut rand::rng()))
            .ok_or_else(|| Error::EmptyResolvedAddresses(workload_uid.to_string()))
    }

    // same as fetch_workload, but if the caller knows the workload is enroute already,
    // will retry on cache miss for a configured amount of time - returning the workload
    // when we get it, or nothing if the timeout is exceeded, whichever happens first
    pub async fn wait_for_workload(
        &self,
        wl: &WorkloadInfo,
        deadline: Duration,
    ) -> Option<Arc<Workload>> {
        debug!(%wl, "wait for workload");

        // Take a watch listener *before* checking state (so we don't miss anything)
        let mut wl_sub = self.read().workloads.new_subscriber();

        debug!(%wl, "got sub, waiting for workload");

        if let Some(wl) = self.find_by_info(wl) {
            return Some(wl);
        }

        // We didn't find the workload we expected, so
        // loop until the subscriber wakes us on new workload,
        // or we hit the deadline timeout and give up
        let timeout = tokio::time::sleep(deadline);
        tokio::pin!(timeout);
        loop {
            tokio::select! {
                _ = &mut timeout => {
                    warn!("timed out waiting for workload '{wl}' from xds");
                    break None;
                },
                _ = wl_sub.changed() => {
                    if let Some(wl) = self.find_by_info(wl) {
                        break Some(wl);
                    }
                }
            }
        }
    }

    /// Finds the workload by workload information, as an arc.
    /// Note: this does not currently support on-demand.
    fn find_by_info(&self, wl: &WorkloadInfo) -> Option<Arc<Workload>> {
        self.read().workloads.find_by_info(wl)
    }

    // fetch_workload_by_address looks up a Workload by address.
    // Note this should never be used to lookup the local workload we are running, only the peer.
    // Since the peer connection may come through gateways, NAT, etc, this should only ever be treated
    // as a best-effort.
    pub async fn fetch_workload_by_address(&self, addr: &NetworkAddress) -> Option<Arc<Workload>> {
        // Wait for it on-demand, *if* needed
        debug!(%addr, "fetch workload");
        if let Some(wl) = self.read().workloads.find_address(addr) {
            return Some(wl);
        }
        if !self.supports_on_demand() {
            return None;
        }
        self.fetch_on_demand(addr.to_string().into()).await;
        self.read().workloads.find_address(addr)
    }

    // only support workload
    pub async fn fetch_workload_by_uid(&self, uid: &Strng) -> Option<Arc<Workload>> {
        // Wait for it on-demand, *if* needed
        debug!(%uid, "fetch workload");
        if let Some(wl) = self.read().workloads.find_uid(uid) {
            return Some(wl);
        }
        if !self.supports_on_demand() {
            return None;
        }
        self.fetch_on_demand(uid.clone()).await;
        self.read().workloads.find_uid(uid)
    }

    pub async fn fetch_upstream(
        &self,
        network: Strng,
        source_workload: &Workload,
        addr: SocketAddr,
        resolution_mode: ServiceResolutionMode,
    ) -> Result<Option<Upstream>, Error> {
        self.fetch_address(&network_addr(network.clone(), addr.ip()))
            .await;
        let upstream = {
            self.read()
                .find_upstream(network, source_workload, addr, resolution_mode)
            // Drop the lock
        };
        tracing::trace!(%addr, ?upstream, "fetch_upstream");
        self.finalize_upstream(source_workload, addr, upstream, addr, false)
            .await
    }

    async fn finalize_upstream(
        &self,
        source_workload: &Workload,
        target_address: SocketAddr,
        upstream: Option<(Arc<Workload>, u16, Option<Arc<Service>>)>,
        original_target: SocketAddr,
        through_waypoint: bool,
    ) -> Result<Option<Upstream>, Error> {
        let Some((wl, port, svc)) = upstream else {
            return Ok(None);
        };
        let svc_desc = svc.clone().map(|s| ServiceDescription::from(s.as_ref()));
        let ip_family_restriction = svc.as_ref().and_then(|s| s.ip_families);
        let selected_workload_ip = self
            .pick_workload_destination_or_resolve(
                &wl,
                source_workload,
                target_address,
                ip_family_restriction,
            )
            .await?; // if we can't load balance just return the error
        let res = Upstream {
            workload: wl,
            selected_workload_ip,
            port,
            service_sans: svc.map(|s| s.subject_alt_names.clone()).unwrap_or_default(),
            destination_service: svc_desc,
            original_target,
            through_waypoint,
            hbone_port: self.hbone_port,
        };
        tracing::trace!(?res, "finalize_upstream");
        Ok(Some(res))
    }

    /// Returns destination address, upstream sans, and final sans, for
    /// connecting to a remote workload through a gateway.
    /// Would be nice to return this as an Upstream, but gateways don't necessarily
    /// have workloads. That is, they could just be IPs without a corresponding workload.
    pub async fn fetch_network_gateway(
        &self,
        gw_address: &GatewayAddress,
        source_workload: &Workload,
        original_destination_address: SocketAddr,
    ) -> Result<Upstream, Error> {
        let (res, target_address) = match &gw_address.destination {
            Destination::Address(ip) => {
                let addr = SocketAddr::new(ip.address, gw_address.hbone_mtls_port);
                let us = self.state.read().unwrap().find_upstream(
                    ip.network.clone(),
                    source_workload,
                    addr,
                    ServiceResolutionMode::Standard,
                );
                // If the workload references a network gateway by IP, use that IP as the destination.
                // Note this means that an IPv6 call may be translated to IPv4 if the network
                // gateway is specified as an IPv4 address.
                // For this reason, the Hostname method is preferred which can adapt to the callers IP family.
                (us, addr)
            }
            Destination::Hostname(host) => {
                let state = self.read();
                match state.find_hostname(host) {
                    Some(Address::Service(s)) => {
                        let us = state.find_upstream_from_service(
                            source_workload,
                            gw_address.hbone_mtls_port,
                            ServiceResolutionMode::Standard,
                            s,
                        );
                        // For hostname, use the original_destination_address as the target so we can
                        // adapt to the callers IP family.
                        (us, original_destination_address)
                    }
                    Some(Address::Workload(w)) => {
                        let us = Some((w, gw_address.hbone_mtls_port, None));
                        (us, original_destination_address)
                    }
                    None => {
                        return Err(Error::UnknownNetworkGateway(format!(
                            "network gateway {} not found",
                            host.hostname
                        )));
                    }
                }
            }
        };
        self.finalize_upstream(source_workload, target_address, res, original_destination_address, false)
            .await?
            .ok_or_else(|| {
                Error::UnknownNetworkGateway(format!("network gateway {gw_address:?} not found"))
            })
    }

    async fn fetch_waypoint(
        &self,
        gw_address: &GatewayAddress,
        source_workload: &Workload,
        original_destination_address: SocketAddr,
    ) -> Result<Upstream, Error> {
        // Waypoint can be referred to by an IP or Hostname.
        // Hostname is preferred as it is a more stable identifier.
        let (res, target_address) = match &gw_address.destination {
            Destination::Address(ip) => {
                let addr = SocketAddr::new(ip.address, gw_address.hbone_mtls_port);
                let us = self.read().find_upstream(
                    ip.network.clone(),
                    source_workload,
                    addr,
                    ServiceResolutionMode::Waypoint,
                );
                // If they referenced a waypoint by IP, use that IP as the destination.
                // Note this means that an IPv6 call may be translated to IPv4 if the waypoint is specified
                // as an IPv4 address.
                // For this reason, the Hostname method is preferred which can adapt to the callers IP family.
                (us, addr)
            }
            Destination::Hostname(host) => {
                debug!("waypoint is {}", host);
                let state = self.read();
                match state.find_hostname(host) {
                    Some(Address::Service(s)) => {
                        let us = state.find_upstream_from_service(
                            source_workload,
                            gw_address.hbone_mtls_port,
                            ServiceResolutionMode::Waypoint,
                            s,
                        );
                        // For hostname, use the original_destination_address as the target so we can
                        // adapt to the callers IP family.
                        (us, original_destination_address)
                    }
                    Some(Address::Workload(w)) => {
                        let us = Some((w, gw_address.hbone_mtls_port, None));
                        (us, original_destination_address)
                    }
                    None => {
                        return Err(Error::UnknownWaypoint(format!(
                            "waypoint {} not found",
                            host.hostname
                        )));
                    }
                }
            }
        };
        self.finalize_upstream(source_workload, target_address, res, original_destination_address, true)
            .await?
            .ok_or_else(|| Error::UnknownWaypoint(format!("waypoint {gw_address:?} not found")))
    }

    pub async fn fetch_service_waypoint(
        &self,
        service: &Service,
        source_workload: &Workload,
        original_destination_address: SocketAddr,
    ) -> Result<Option<Upstream>, Error> {
        let Some(gw_address) = &service.waypoint else {
            // no waypoint
            return Ok(None);
        };
        self.fetch_waypoint(gw_address, source_workload, original_destination_address)
            .await
            .map(Some)
    }

    pub async fn fetch_workload_waypoint(
        &self,
        wl: &Workload,
        source_workload: &Workload,
        original_destination_address: SocketAddr,
    ) -> Result<Option<Upstream>, Error> {
        let Some(gw_address) = &wl.waypoint else {
            // no waypoint
            return Ok(None);
        };
        self.fetch_waypoint(gw_address, source_workload, original_destination_address)
            .await
            .map(Some)
    }

    fn translate_service_port(&self, endpoint: &Endpoint, workload: &Workload, service: &Service, service_port: u16) -> Option<u16> {
        let service_target_port = service.ports.get(&service_port).copied().unwrap_or_default();
        if let Some(&ep_target_port) = endpoint.port.get(&service_port) {
            // When endpoint has the port we prefer it
            Some(ep_target_port)
        } else if service_target_port > 0 {
            // otherwise use the port from the service itself
            Some(service_target_port)
        } else if let Some(ApplicationTunnel { port: Some(_), .. }) = workload.application_tunnel {
            // when using app tunnel, we don't require the port to be found on the service at all
            Some(service_port)
        } else {
            None
        }
    }

    /// Fetch upstream for the service in a multicluster-aware way.
    /// We want to support non-uniform waypoint configuration in multicluster scenario,
    /// so that each clsuter can decide on their own whether and how to configure waypoints.
    /// This may result in configurations where the same service uses different waypoint
    /// services in different clusters or uses a waypoint in one cluster but no waypoint in some
    /// other cluster.
    pub async fn fetch_service_upstream(
        &self,
        service: Arc<Service>,
        source: &Workload,
        original_target_address: SocketAddr,
    ) -> Result<Option<Upstream>, Error> {
        // The basic idea is we go over all clusters and for each cluster check if it has a
        // waypoint configured. If it has a waypoint configure we add endpoints of the waypoint
        // service to the list of candidate endpoints. If the cluster does not have a waypoint
        // configured then we add endpoints of the target service in that cluster instead. We load
        // balance over the combined list of endpoints.
        //
        // NOTE: implementing things exactly as described above (e.g., going over the list of
        // clusters and checking each endpoint in that cluster) might not scale that well in a
        // uniform or partially uniform setup as we would check the same service and it's endpoints
        // multiple times doing unnecessary work. So instead this implementation is structured so
        // that each endpoint of each service that we consider is only checked once.
        //
        // TODO: Think through the locking scheme here, in general we probably don't want to hold a
        // lock on state while doing an async operation. On top of that fetch_destination that we
        // use to get waypoint services is an async operation that can't complete until we release
        // the locks (even if we only hold a read lock). That's why we only temporaroly grab locks
        // to resolve workload uids and inside the fetch_destination. That being said, maybe we
        // don't need to grab and release the lock for each endpoint?
        let service_port = original_target_address.port();
        let mut picker = EndpointPicker::new(source, &service);

        // We first check target service endpoints and ignore those that are in clusters with
        // waypoint configured. Once we go over all the endpoints of the service we will not return
        // to it anymore, thus checking service endpoints only once.
        let target_port = service.ports.get(&service_port).copied();

        if target_port.is_some() {
            for ep in service.endpoints.iter() {
                let Some(wl) = self.read().workloads.find_uid(&ep.workload_uid) else {
                    info!("failed to fetch workload for {}", ep.workload_uid);
                    continue;
                };

                let in_network = wl.network == source.network;
                let has_network_gateway = wl.network_gateway.is_some();
                let has_address = !wl.workload_ips.is_empty() || !wl.hostname.is_empty();
                if !has_address {
                    // Workload has no IP. We can only reach it via a network gateway.
                    // WDS is client-agnostic, so we will get a network gateway for a workload
                    // even if it's in the same network; we should never use it.
                    if in_network || !has_network_gateway {
                        info!(
                            "skipping endpoint {} because it does not have an address", ep.workload_uid);
                        continue;
                    }
                }

                if service.waypoints.inner.get(&wl.cluster_id).is_some() {
                    info!("skipping endpoint {} because it's in a cluster with waypoint configured", ep.workload_uid);
                    continue;
                }

                if target_port.unwrap_or_default() == 0 && !ep.port.contains_key(&service_port) {
                    info!("skipping endpoint {}, it does not have service port {}", ep.workload_uid, service_port);
                    continue;
                }

                if let Some(port) = self.translate_service_port(ep, &wl, &service, service_port) {
                    picker.add_direct_endpoint(wl, ep.clone(), port);
                } else {
                    // This will never happen, because we checked above that either service has the
                    // port or endpoint has one.
                    info!("skipping endpoint {}, because port {} is unknown", ep.workload_uid, service_port);
                }
            }
        } else {
            // In single-cluster scenario we would give up here and return None, but in
            // multi-cluster scenario we might still have other clusters that we could consider
            // where we have waypoints and therefore use a slightly different criteria. Log a debug
            // message here and continue to check other clusters.
            info!("service {} does not have port {}", service.hostname, service_port);
        }

        // After we checked the service endpoints, we can check all the waypoints. To avoid
        // checking the same waypoint service multiple times we keep track of what waypoints we
        // already checked.
        //
        // To remove the need to check the same waypoint again, once we started checking a
        // waypoint service we keep checking all endpoints of the waypoint service for all
        // clusters. We just need to ignore clusters where there is no waypoint or a different
        // waypoint is configured.
        let mut visited = HashSet::new();
        for (_, gw) in service.waypoints.inner.iter() {
            if !visited.insert(gw.clone()) {
                // We already considered this waypoint, so skipping it and moving to the next one.
                continue;
            }

            match self.fetch_destination(&gw.destination).await {
                Some(Address::Workload(_)) => {
                    // It does not seem hard to add support for non-service waypoints, but for PoC
                    // I'm going to ignore this case as it's non a very typical setup of Istio.
                    info!("non-service waypoints are not supported yet");
                }
                Some(Address::Service(waypoint)) => {
                    // Given that it's not a service endpoint, but a waypoint endpoint, we use
                    // HBONE port instead.
                    let service_target_port = waypoint.ports.get(&gw.hbone_mtls_port).copied();

                    for ep in waypoint.endpoints.iter() {
                        let Some(wl) = self.read().workloads.find_uid(&ep.workload_uid) else {
                            info!("failed to fetch workload for {}", ep.workload_uid);
                            continue;
                        };

                        let in_network = wl.network == source.network;
                        let has_network_gateway = wl.network_gateway.is_some();
                        let has_address = !wl.workload_ips.is_empty() || !wl.hostname.is_empty();
                        if !has_address {
                            // Workload has no IP. We can only reach it via a network gateway.
                            // WDS is client-agnostic, so we will get a network gateway for a workload
                            // even if it's in the same network; we should never use it.
                            if in_network || !has_network_gateway {
                                info!(
                                    "skipping endpoint {} because it does not have an address",
                                    ep.workload_uid);
                                continue;
                            }
                        }

                        if service_target_port.is_none() && wl.application_tunnel.is_none() {
                            info!("filter waypoint endpoint {}, target port is not defined", ep.workload_uid);
                            continue;
                        }

                        // If in the cluster of this workload we don't have a waypoint or have a
                        // different waypoint, then we should skip this workload as it's not the
                        // right candidate.
                        if service.waypoints.inner.get(&wl.cluster_id) != Some(gw) {
                            info!("skipping endpoint {} because it does not belong to the right waypoint for cluster {}",
                                ep.workload_uid, wl.cluster_id);
                            continue;
                        }

                        if let Some(port) = self.translate_service_port(ep, &wl, &waypoint, gw.hbone_mtls_port) {
                            picker.add_waypoint_endpoint(wl, waypoint.clone(), ep.clone(), port);
                        } else {
                            // This can never happen because we checked before that either service
                            // has a port or the workload has app tunnel and therefore we don't
                            // need a port.
                            info!("skipping endpoint {}, because port {} is unknown", ep.workload_uid, gw.hbone_mtls_port);
                        }
                    }
                }
                None => info!("waypoint {:?} not found", gw.destination),
            };
        }

        if let Some(candidate) = picker.pick_candidate() {
            self.finalize_upstream(
                &source,
                // This address is essentially only used to figure out whether the original request
                // was using IPv6 or IPv4. We want to try and preserve original IP family of the
                // request.
                //
                // When we route request through a waypoint, what we should properly do is to check
                // whether waypoint is IP-addressed or not and if it's we should use that IP
                // address here instead.
                //
                // I'm cutting a corner here somewhat and ignore that logic, but it should be good
                // enough for PoC, because by default we don't use IP addressed waypoints.
                original_target_address,
                Some((candidate.workload.clone(), candidate.port, candidate.waypoint.clone().or(Some(service.clone())))),
                original_target_address,
                candidate.waypoint.is_some(),
            ).await
        } else {
            info!("service {} has no healthy endpoints in any of the clusters", service.hostname);
            Ok(None)
        }
    }

    /// Looks for either a workload or service by the destination. If not found locally,
    /// attempts to fetch on-demand.
    pub async fn fetch_destination(&self, dest: &Destination) -> Option<Address> {
        match dest {
            Destination::Address(addr) => self.fetch_address(addr).await,
            Destination::Hostname(hostname) => self.fetch_hostname(hostname).await,
        }
    }

    /// Looks for the given address to find either a workload or service by IP. If not found
    /// locally, attempts to fetch on-demand.
    pub async fn fetch_address(&self, network_addr: &NetworkAddress) -> Option<Address> {
        // Wait for it on-demand, *if* needed
        debug!(%network_addr.address, "fetch address");
        if let Some(address) = self.read().find_address(network_addr) {
            return Some(address);
        }
        if !self.supports_on_demand() {
            return None;
        }
        // if both cache not found, start on demand fetch
        self.fetch_on_demand(network_addr.to_string().into()).await;
        self.read().find_address(network_addr)
    }

    /// Looks for the given hostname to find either a workload or service by IP. If not found
    /// locally, attempts to fetch on-demand.
    async fn fetch_hostname(&self, hostname: &NamespacedHostname) -> Option<Address> {
        // Wait for it on-demand, *if* needed
        debug!(%hostname, "fetch hostname");
        if let Some(address) = self.read().find_hostname(hostname) {
            return Some(address);
        }
        if !self.supports_on_demand() {
            return None;
        }
        // if both cache not found, start on demand fetch
        self.fetch_on_demand(hostname.to_string().into()).await;
        self.read().find_hostname(hostname)
    }

    pub fn supports_on_demand(&self) -> bool {
        self.demand.is_some()
    }

    /// fetch_on_demand looks up the provided key on-demand and waits for it to return
    pub async fn fetch_on_demand(&self, key: Strng) {
        if let Some(demand) = &self.demand {
            debug!(%key, "sending demand request");
            Box::pin(
                demand
                    .demand(xds::ADDRESS_TYPE, key.clone())
                    .then(|o| o.recv()),
            )
            .await;
            debug!(%key, "on demand ready");
        }
    }
}

#[derive(Eq, PartialEq, Clone, Copy, Debug)]
pub enum ServiceResolutionMode {
    // We are resolving a normal service
    Standard,
    // We are resolving a waypoint proxy
    Waypoint,
}

#[derive(serde::Serialize)]
pub struct ProxyStateManager {
    #[serde(flatten)]
    state: DemandProxyState,

    #[serde(skip_serializing)]
    xds_client: Option<AdsClient>,
}

impl ProxyStateManager {
    pub async fn new(
        config: Arc<config::Config>,
        xds_metrics: xds::Metrics,
        proxy_metrics: Arc<proxy::Metrics>,
        awaiting_ready: tokio::sync::watch::Sender<()>,
        cert_manager: Arc<SecretManager>,
    ) -> anyhow::Result<ProxyStateManager> {
        let cert_fetcher = cert_fetcher::new(&config, cert_manager);
        let state: Arc<RwLock<ProxyState>> = Arc::new(RwLock::new(ProxyState::new(
            config.local_node.as_ref().map(strng::new),
        )));
        let xds_client = if config.xds_address.is_some() {
            let updater = ProxyStateUpdater::new(state.clone(), cert_fetcher.clone());
            let tls_client_fetcher = Box::new(tls::ControlPlaneAuthentication::RootCert(
                config.xds_root_cert.clone(),
            ));
            Some(
                xds::Config::new(config.clone(), tls_client_fetcher)
                    .with_watched_handler::<XdsAddress>(xds::ADDRESS_TYPE, updater.clone())
                    .with_watched_handler::<XdsAuthorization>(xds::AUTHORIZATION_TYPE, updater)
                    .build(xds_metrics, awaiting_ready),
            )
        } else {
            None
        };
        if let Some(cfg) = &config.local_xds_config {
            let local_client = LocalClient {
                local_node: config.local_node.as_ref().map(strng::new),
                cfg: cfg.clone(),
                state: state.clone(),
                cert_fetcher,
            };
            local_client.run().await?;
        }
        let demand = xds_client.as_ref().and_then(AdsClient::demander);
        Ok(ProxyStateManager {
            xds_client,
            state: DemandProxyState::new(
                state,
                demand,
                config.dns_resolver_cfg.clone(),
                config.dns_resolver_opts.clone(),
                proxy_metrics,
                config.inbound_addr.port(),
            ),
        })
    }

    pub fn state(&self) -> DemandProxyState {
        self.state.clone()
    }

    pub async fn run(self) -> anyhow::Result<()> {
        match self.xds_client {
            Some(xds) => xds.run().await.map_err(|e| anyhow::anyhow!(e)),
            None => Ok(()),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::state::service::{EndpointSet, LoadBalancer, LoadBalancerHealthPolicy};
    use crate::state::workload::{HealthStatus, Locality};
    use prometheus_client::registry::Registry;
    use rbac::StringMatch;
    use std::{net::Ipv4Addr, net::SocketAddrV4, time::Duration};

    use self::workload::{ApplicationTunnel, application_tunnel::Protocol as AppProtocol};

    use super::*;
    use crate::test_helpers::helpers::initialize_telemetry;

    use crate::{strng, test_helpers};
    use test_case::test_case;

    #[tokio::test]
    async fn test_wait_for_workload() {
        let mut state = ProxyState::new(None);
        let delayed_wl = Arc::new(test_helpers::test_default_workload());
        state.workloads.insert(delayed_wl.clone());

        let mut registry = Registry::default();
        let metrics = Arc::new(crate::proxy::Metrics::new(&mut registry));
        let mock_proxy_state = DemandProxyState::new(
            Arc::new(RwLock::new(state)),
            None,
            ResolverConfig::default(),
            ResolverOpts::default(),
            metrics,
            15008,
        );

        let want = WorkloadInfo {
            name: delayed_wl.name.to_string(),
            namespace: delayed_wl.namespace.to_string(),
            service_account: delayed_wl.service_account.to_string(),
        };

        test_helpers::assert_eventually(
            Duration::from_secs(1),
            || mock_proxy_state.wait_for_workload(&want, Duration::from_millis(50)),
            Some(delayed_wl),
        )
        .await;
    }

    #[tokio::test]
    async fn test_wait_for_workload_delay_fails() {
        let state = ProxyState::new(None);

        let mut registry = Registry::default();
        let metrics = Arc::new(crate::proxy::Metrics::new(&mut registry));
        let mock_proxy_state = DemandProxyState::new(
            Arc::new(RwLock::new(state)),
            None,
            ResolverConfig::default(),
            ResolverOpts::default(),
            metrics,
            15008,
        );

        let want = WorkloadInfo {
            name: "fake".to_string(),
            namespace: "fake".to_string(),
            service_account: "fake".to_string(),
        };

        test_helpers::assert_eventually(
            Duration::from_millis(10),
            || mock_proxy_state.wait_for_workload(&want, Duration::from_millis(5)),
            None,
        )
        .await;
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn test_wait_for_workload_eventually() {
        initialize_telemetry();
        let state = ProxyState::new(None);
        let wrap_state = Arc::new(RwLock::new(state));
        let not_delayed_wl = Arc::new(Workload {
            workload_ips: vec!["1.2.3.4".parse().unwrap()],
            uid: "uid".into(),
            name: "n".into(),
            namespace: "ns".into(),
            ..test_helpers::test_default_workload()
        });
        let delayed_wl = Arc::new(test_helpers::test_default_workload());

        let mut registry = Registry::default();
        let metrics = Arc::new(crate::proxy::Metrics::new(&mut registry));
        let mock_proxy_state = DemandProxyState::new(
            wrap_state.clone(),
            None,
            ResolverConfig::default(),
            ResolverOpts::default(),
            metrics,
            15008,
        );

        // Some from Address
        let want = WorkloadInfo {
            name: delayed_wl.name.to_string(),
            namespace: delayed_wl.namespace.to_string(),
            service_account: delayed_wl.service_account.to_string(),
        };

        let expected_wl = delayed_wl.clone();
        let t = tokio::spawn(async move {
            test_helpers::assert_eventually(
                Duration::from_millis(500),
                || mock_proxy_state.wait_for_workload(&want, Duration::from_millis(250)),
                Some(expected_wl),
            )
            .await;
        });
        // Send the wrong workload through
        wrap_state.write().unwrap().workloads.insert(not_delayed_wl);
        tokio::time::sleep(Duration::from_millis(100)).await;
        // Send the correct workload through
        wrap_state.write().unwrap().workloads.insert(delayed_wl);
        t.await.expect("should not fail");
    }

    #[tokio::test]
    async fn lookup_address() {
        let mut state = ProxyState::new(None);
        state
            .workloads
            .insert(Arc::new(test_helpers::test_default_workload()));
        state.services.insert(test_helpers::mock_default_service());

        let mut registry = Registry::default();
        let metrics = Arc::new(crate::proxy::Metrics::new(&mut registry));
        let mock_proxy_state = DemandProxyState::new(
            Arc::new(RwLock::new(state)),
            None,
            ResolverConfig::default(),
            ResolverOpts::default(),
            metrics,
            15008,
        );

        // Some from Address
        let dst = Destination::Address(NetworkAddress {
            network: strng::EMPTY,
            address: IpAddr::V4(Ipv4Addr::LOCALHOST),
        });
        test_helpers::assert_eventually(
            Duration::from_secs(5),
            || mock_proxy_state.fetch_destination(&dst),
            Some(Address::Workload(Arc::new(
                test_helpers::test_default_workload(),
            ))),
        )
        .await;

        // Some from Hostname
        let dst = Destination::Hostname(NamespacedHostname {
            namespace: "default".into(),
            hostname: "defaulthost".into(),
        });
        test_helpers::assert_eventually(
            Duration::from_secs(5),
            || mock_proxy_state.fetch_destination(&dst),
            Some(Address::Service(Arc::new(
                test_helpers::mock_default_service(),
            ))),
        )
        .await;

        // None from Address
        let dst = Destination::Address(NetworkAddress {
            network: "".into(),
            address: IpAddr::V4(Ipv4Addr::new(127, 0, 0, 2)),
        });
        test_helpers::assert_eventually(
            Duration::from_secs(5),
            || mock_proxy_state.fetch_destination(&dst),
            None,
        )
        .await;

        // None from Hostname
        let dst = Destination::Hostname(NamespacedHostname {
            namespace: "default".into(),
            hostname: "nothost".into(),
        });
        test_helpers::assert_eventually(
            Duration::from_secs(5),
            || mock_proxy_state.fetch_destination(&dst),
            None,
        )
        .await;
    }

    enum PortMappingTestCase {
        EndpointMapping,
        ServiceMapping,
        AppTunnel,
    }

    impl PortMappingTestCase {
        fn service_mapping(&self) -> HashMap<u16, u16> {
            if let PortMappingTestCase::ServiceMapping = self {
                return HashMap::from([(80, 8080)]);
            }
            HashMap::from([(80, 0)])
        }

        fn endpoint_mapping(&self) -> HashMap<u16, u16> {
            if let PortMappingTestCase::EndpointMapping = self {
                return HashMap::from([(80, 9090)]);
            }
            HashMap::from([])
        }

        fn app_tunnel(&self) -> Option<ApplicationTunnel> {
            if let PortMappingTestCase::AppTunnel = self {
                return Some(ApplicationTunnel {
                    protocol: AppProtocol::PROXY,
                    port: Some(15088),
                });
            }
            None
        }

        fn expected_port(&self) -> u16 {
            match self {
                PortMappingTestCase::ServiceMapping => 8080,
                PortMappingTestCase::EndpointMapping => 9090,
                _ => 80,
            }
        }
    }

    #[test_case(PortMappingTestCase::EndpointMapping; "ep mapping")]
    #[test_case(PortMappingTestCase::ServiceMapping; "svc mapping")]
    #[test_case(PortMappingTestCase::AppTunnel; "app tunnel")]
    #[tokio::test]
    async fn find_upstream_port_mappings(tc: PortMappingTestCase) {
        initialize_telemetry();
        let wl = Workload {
            uid: "cluster1//v1/Pod/default/ep_no_port_mapping".into(),
            name: "ep_no_port_mapping".into(),
            namespace: "default".into(),
            workload_ips: vec![IpAddr::V4(Ipv4Addr::new(192, 168, 0, 1))],
            application_tunnel: tc.app_tunnel(),
            ..test_helpers::test_default_workload()
        };
        let svc = Service {
            name: "test-svc".into(),
            hostname: "example.com".into(),
            namespace: "default".into(),
            vips: vec![NetworkAddress {
                address: "10.0.0.1".parse().unwrap(),
                network: "".into(),
            }],
            endpoints: EndpointSet::from_list([Endpoint {
                workload_uid: "cluster1//v1/Pod/default/ep_no_port_mapping".into(),
                port: tc.endpoint_mapping(),
                status: HealthStatus::Healthy,
            }]),
            ports: tc.service_mapping(),
            ..test_helpers::mock_default_service()
        };

        let mut state = ProxyState::new(None);
        state.workloads.insert(wl.clone().into());
        state.services.insert(svc);

        let mode = match tc {
            PortMappingTestCase::AppTunnel => ServiceResolutionMode::Waypoint,
            _ => ServiceResolutionMode::Standard,
        };

        let (_, port, _) = state
            .find_upstream("".into(), &wl, "10.0.0.1:80".parse().unwrap(), mode)
            .expect("upstream to be found");
        assert_eq!(port, tc.expected_port());
    }

    fn create_workload(dest_uid: u8) -> Workload {
        Workload {
            name: "test".into(),
            namespace: format!("ns{dest_uid}").into(),
            trust_domain: "cluster.local".into(),
            service_account: "defaultacct".into(),
            workload_ips: vec![IpAddr::V4(Ipv4Addr::new(192, 168, 0, dest_uid))],
            uid: format!("{dest_uid}").into(),
            ..test_helpers::test_default_workload()
        }
    }

    fn get_workload(state: &DemandProxyState, dest_uid: u8) -> Arc<Workload> {
        let key: Strng = format!("{dest_uid}").into();
        state.read().workloads.by_uid[&key].clone()
    }

    fn get_rbac_context(
        state: &DemandProxyState,
        dest_uid: u8,
        src_svc_acct: &str,
    ) -> crate::state::ProxyRbacContext {
        let key: Strng = format!("{dest_uid}").into();
        let workload = &state.read().workloads.by_uid[&key];
        crate::state::ProxyRbacContext {
            conn: rbac::Connection {
                src_identity: Some(Identity::Spiffe {
                    trust_domain: "cluster.local".into(),
                    namespace: "default".into(),
                    service_account: src_svc_acct.to_string().into(),
                }),
                src: std::net::SocketAddr::V4(SocketAddrV4::new(
                    Ipv4Addr::new(192, 168, 1, 1),
                    1234,
                )),
                dst_network: "".into(),
                dst: SocketAddr::new(workload.workload_ips[0], 8080),
            },
            dest_workload: get_workload(state, dest_uid),
        }
    }
    fn create_state(state: ProxyState) -> DemandProxyState {
        let mut registry = Registry::default();
        let metrics = Arc::new(crate::proxy::Metrics::new(&mut registry));
        DemandProxyState::new(
            Arc::new(RwLock::new(state)),
            None,
            ResolverConfig::default(),
            ResolverOpts::default(),
            metrics,
            15008,
        )
    }

    // test that we confirm with https://istio.io/latest/docs/reference/config/security/authorization-policy/.
    // We don't test #1 as ztunnel doesn't support custom policies.
    // 1. If there are any CUSTOM policies that match the request, evaluate and deny the request if the evaluation result is deny.
    // 2. If there are any DENY policies that match the request, deny the request.
    // 3. If there are no ALLOW policies for the workload, allow the request.
    // 4. If any of the ALLOW policies match the request, allow the request.
    // 5. Deny the request.
    #[tokio::test]
    async fn assert_rbac_logic_deny_allow() {
        let mut state = ProxyState::new(None);
        state.workloads.insert(Arc::new(create_workload(1)));
        state.workloads.insert(Arc::new(create_workload(2)));
        state.policies.insert(
            "allow".into(),
            rbac::Authorization {
                action: rbac::RbacAction::Allow,
                namespace: "ns1".into(),
                name: "foo".into(),
                rules: vec![
                    // rule1:
                    vec![
                        // from:
                        vec![rbac::RbacMatch {
                            principals: vec![StringMatch::Exact(
                                "cluster.local/ns/default/sa/defaultacct".into(),
                            )],
                            ..Default::default()
                        }],
                    ],
                ],
                scope: rbac::RbacScope::Namespace,
            },
        );
        state.policies.insert(
            "deny".into(),
            rbac::Authorization {
                action: rbac::RbacAction::Deny,
                namespace: "ns1".into(),
                name: "deny".into(),
                rules: vec![
                    // rule1:
                    vec![
                        // from:
                        vec![rbac::RbacMatch {
                            principals: vec![StringMatch::Exact(
                                "cluster.local/ns/default/sa/denyacct".into(),
                            )],
                            ..Default::default()
                        }],
                    ],
                ],
                scope: rbac::RbacScope::Namespace,
            },
        );

        let mock_proxy_state = create_state(state);

        // test workload in ns2. this should work as ns2 doesn't have any policies. this tests:
        // 3. If there are no ALLOW policies for the workload, allow the request.
        assert!(
            mock_proxy_state
                .assert_rbac(&get_rbac_context(&mock_proxy_state, 2, "not-defaultacct"))
                .await
                .is_ok()
        );

        let ctx = get_rbac_context(&mock_proxy_state, 1, "defaultacct");
        // 4. if any allow policies match, allow
        assert!(mock_proxy_state.assert_rbac(&ctx).await.is_ok());

        {
            // test a src workload with unknown svc account. this should fail as we have allow policies,
            // but they don't match.
            // 5. deny the request
            let mut ctx = ctx.clone();
            ctx.conn.src_identity = Some(Identity::Spiffe {
                trust_domain: "cluster.local".into(),
                namespace: "default".into(),
                service_account: "not-defaultacct".into(),
            });

            assert_eq!(
                mock_proxy_state.assert_rbac(&ctx).await.err().unwrap(),
                proxy::AuthorizationRejectionError::NotAllowed
            );
        }
        {
            let mut ctx = ctx.clone();
            ctx.conn.src_identity = Some(Identity::Spiffe {
                trust_domain: "cluster.local".into(),
                namespace: "default".into(),
                service_account: "denyacct".into(),
            });

            // 2. If there are any DENY policies that match the request, deny the request.
            assert_eq!(
                mock_proxy_state.assert_rbac(&ctx).await.err().unwrap(),
                proxy::AuthorizationRejectionError::ExplicitlyDenied("ns1".into(), "deny".into())
            );
        }
    }

    #[tokio::test]
    async fn assert_rbac_with_dest_workload_info() {
        let mut state = ProxyState::new(None);
        state.workloads.insert(Arc::new(create_workload(1)));

        let mock_proxy_state = create_state(state);

        let ctx = get_rbac_context(&mock_proxy_state, 1, "defaultacct");
        assert!(mock_proxy_state.assert_rbac(&ctx).await.is_ok());
    }

    #[tokio::test]
    async fn test_load_balance() {
        initialize_telemetry();
        let mut state = ProxyState::new(None);
        let wl_no_locality = Workload {
            uid: "cluster1//v1/Pod/default/wl_no_locality".into(),
            name: "wl_no_locality".into(),
            namespace: "default".into(),
            trust_domain: "cluster.local".into(),
            service_account: "default".into(),
            workload_ips: vec![IpAddr::V4(Ipv4Addr::new(192, 168, 0, 1))],
            ..test_helpers::test_default_workload()
        };
        let wl_match = Workload {
            uid: "cluster1//v1/Pod/default/wl_match".into(),
            name: "wl_match".into(),
            namespace: "default".into(),
            trust_domain: "cluster.local".into(),
            service_account: "default".into(),
            workload_ips: vec![IpAddr::V4(Ipv4Addr::new(192, 168, 0, 2))],
            network: "network".into(),
            locality: Locality {
                region: "reg".into(),
                zone: "zone".into(),
                subzone: "".into(),
            },
            ..test_helpers::test_default_workload()
        };
        let wl_almost = Workload {
            uid: "cluster1//v1/Pod/default/wl_almost".into(),
            name: "wl_almost".into(),
            namespace: "default".into(),
            trust_domain: "cluster.local".into(),
            service_account: "default".into(),
            workload_ips: vec![IpAddr::V4(Ipv4Addr::new(192, 168, 0, 3))],
            network: "network".into(),
            locality: Locality {
                region: "reg".into(),
                zone: "not-zone".into(),
                subzone: "".into(),
            },
            ..test_helpers::test_default_workload()
        };
        let wl_empty_ip = Workload {
            uid: "cluster1//v1/Pod/default/wl_empty_ip".into(),
            name: "wl_empty_ip".into(),
            namespace: "default".into(),
            trust_domain: "cluster.local".into(),
            service_account: "default".into(),
            workload_ips: vec![], // none!
            network: "network".into(),
            locality: Locality {
                region: "reg".into(),
                zone: "zone".into(),
                subzone: "".into(),
            },
            ..test_helpers::test_default_workload()
        };

        let _ep_almost = Workload {
            uid: "cluster1//v1/Pod/default/ep_almost".into(),
            name: "wl_almost".into(),
            namespace: "default".into(),
            trust_domain: "cluster.local".into(),
            service_account: "default".into(),
            workload_ips: vec![IpAddr::V4(Ipv4Addr::new(192, 168, 0, 4))],
            network: "network".into(),
            locality: Locality {
                region: "reg".into(),
                zone: "other-not-zone".into(),
                subzone: "".into(),
            },
            ..test_helpers::test_default_workload()
        };
        let _ep_no_match = Workload {
            uid: "cluster1//v1/Pod/default/ep_no_match".into(),
            name: "wl_almost".into(),
            namespace: "default".into(),
            trust_domain: "cluster.local".into(),
            service_account: "default".into(),
            workload_ips: vec![IpAddr::V4(Ipv4Addr::new(192, 168, 0, 5))],
            network: "not-network".into(),
            locality: Locality {
                region: "not-reg".into(),
                zone: "unmatched-zone".into(),
                subzone: "".into(),
            },
            ..test_helpers::test_default_workload()
        };
        let endpoints = EndpointSet::from_list([
            Endpoint {
                workload_uid: "cluster1//v1/Pod/default/ep_almost".into(),
                port: HashMap::from([(80u16, 80u16)]),
                status: HealthStatus::Healthy,
            },
            Endpoint {
                workload_uid: "cluster1//v1/Pod/default/ep_no_match".into(),
                port: HashMap::from([(80u16, 80u16)]),
                status: HealthStatus::Healthy,
            },
            Endpoint {
                workload_uid: "cluster1//v1/Pod/default/wl_match".into(),
                port: HashMap::from([(80u16, 80u16)]),
                status: HealthStatus::Healthy,
            },
            Endpoint {
                workload_uid: "cluster1//v1/Pod/default/wl_empty_ip".into(),
                port: HashMap::from([(80u16, 80u16)]),
                status: HealthStatus::Healthy,
            },
        ]);
        let strict_svc = Service {
            endpoints: endpoints.clone(),
            load_balancer: Some(LoadBalancer {
                mode: LoadBalancerMode::Strict,
                routing_preferences: vec![
                    LoadBalancerScopes::Network,
                    LoadBalancerScopes::Region,
                    LoadBalancerScopes::Zone,
                ],
                health_policy: LoadBalancerHealthPolicy::OnlyHealthy,
            }),
            ports: HashMap::from([(80u16, 80u16)]),
            ..test_helpers::mock_default_service()
        };
        let failover_svc = Service {
            endpoints,
            load_balancer: Some(LoadBalancer {
                mode: LoadBalancerMode::Failover,
                routing_preferences: vec![
                    LoadBalancerScopes::Network,
                    LoadBalancerScopes::Region,
                    LoadBalancerScopes::Zone,
                ],
                health_policy: LoadBalancerHealthPolicy::OnlyHealthy,
            }),
            ports: HashMap::from([(80u16, 80u16)]),
            ..test_helpers::mock_default_service()
        };
        state.workloads.insert(Arc::new(wl_no_locality.clone()));
        state.workloads.insert(Arc::new(wl_match.clone()));
        state.workloads.insert(Arc::new(wl_almost.clone()));
        state.workloads.insert(Arc::new(wl_empty_ip.clone()));
        state.services.insert(strict_svc.clone());
        state.services.insert(failover_svc.clone());

        let assert_endpoint = |src: &Workload, svc: &Service, workloads: Vec<&str>, desc: &str| {
            let got = state
                .load_balance(src, svc, 80, ServiceResolutionMode::Standard)
                .map(|(ep, _)| ep.workload_uid.to_string());
            if workloads.is_empty() {
                assert!(got.is_none(), "{}", desc);
            } else {
                let want: Vec<String> = workloads.iter().map(ToString::to_string).collect();
                assert!(want.contains(&got.unwrap()), "{}", desc);
            }
        };
        let assert_not_endpoint =
            |src: &Workload, svc: &Service, uid: &str, tries: usize, desc: &str| {
                for _ in 0..tries {
                    let got = state
                        .load_balance(src, svc, 80, ServiceResolutionMode::Standard)
                        .map(|(ep, _)| ep.workload_uid);
                    assert!(got != Some(strng::new(uid)), "{}", desc);
                }
            };

        assert_endpoint(
            &wl_no_locality,
            &strict_svc,
            vec![],
            "strict no match should not select",
        );
        assert_endpoint(
            &wl_almost,
            &strict_svc,
            vec![],
            "strict no match should not select",
        );
        assert_endpoint(
            &wl_match,
            &strict_svc,
            vec!["cluster1//v1/Pod/default/wl_match"],
            "strict match",
        );

        assert_endpoint(
            &wl_no_locality,
            &failover_svc,
            vec![
                "cluster1//v1/Pod/default/ep_almost",
                "cluster1//v1/Pod/default/ep_no_match",
                "cluster1//v1/Pod/default/wl_match",
            ],
            "failover no match can select any endpoint",
        );
        assert_endpoint(
            &wl_almost,
            &failover_svc,
            vec![
                "cluster1//v1/Pod/default/ep_almost",
                "cluster1//v1/Pod/default/wl_match",
            ],
            "failover almost match can select any close matches",
        );
        assert_endpoint(
            &wl_match,
            &failover_svc,
            vec!["cluster1//v1/Pod/default/wl_match"],
            "failover full match selects closest match",
        );
        assert_not_endpoint(
            &wl_no_locality,
            &failover_svc,
            "cluster1//v1/Pod/default/wl_empty_ip",
            10,
            "failover no match can select any endpoint",
        );
    }
}

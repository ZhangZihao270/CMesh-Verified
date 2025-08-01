include "../../Impl/CausalMesh/Host.dfy"
include "../../Common/Framework/DistributedSystem.s.dfy"

module CM_DistributedSystem_i refines DistributedSystem_s {
  import H_s = Host_i
}

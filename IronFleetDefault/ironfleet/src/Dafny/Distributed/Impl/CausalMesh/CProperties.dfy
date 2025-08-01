include "CTypes.dfy"
include "../../Protocol/CausalMesh/properties.dfy"

module CausalMesh_CProperties_i {
import opened CausalMesh_Properties_i
import opened CausalMesh_CTypes_i

// function method CCausalCut(ccache: CCCache) : bool 
//     requires CCCacheIsValid(ccache)
//     requires (forall k :: k in ccache ==> CMetaValid(ccache[k]))
//     ensures var lr := CausalCut(AbstractifyCCCacheToCCache(ccache)); var cr := CCausalCut(ccache); (cr) == (lr)
// {
//     (forall k :: k in ccache ==> (forall kk :: kk in ccache[k].deps ==> kk in ccache && ((CVCHappendsBefore(ccache[k].deps[kk], ccache[kk].vc)) || (CVCEq(ccache[k].deps[kk], ccache[kk].vc)))))
// }

// function method CReadsDepsAreMet2(icache: CICache, ccache: CCCache, deps: CDependency) : bool 
//     requires CICacheIsValid(icache)
//     requires CCCacheIsValid(ccache)
//     requires CDependencyIsValid(deps)
//     requires CICacheValid(icache)
//     requires CCCacheValid(ccache)
//     requires (forall k :: k in Keys_domain ==> k in icache && k in ccache)
//     requires CDependencyValid(deps)
//     ensures var lr := ReadsDepsAreMet2(AbstractifyCICacheToICache(icache), AbstractifyCCCacheToCCache(ccache), AbstractifyCDependencyToDependency(deps)); var cr := CReadsDepsAreMet2(icache, ccache, deps); (cr) == (lr)
// {
//     (forall k :: k in deps ==> var m := CFoldMetaSet(ccache[k], icache[k], icache.Keys); (CVCEq(deps[k], m.vc)) || (CVCHappendsBefore(deps[k], m.vc)))
// }



}
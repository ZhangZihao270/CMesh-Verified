include "CTypes.dfy"
include "../../Protocol/CausalMesh/pulldeps.dfy"
include "../Common/GenericRefinement.i.dfy"
include "../../Common/Collections/Maps2.i.dfy"
include "../../Common/Collections/Maps.i.dfy"

module CausalMesh_CPullDeps_i {
import opened CausalMesh_CTypes_i
// import opened CausalMesh_Types_i
import opened CausalMesh_PullDeps_i
import opened GenericRefinement_i
import opened Collections__Maps2_i
import opened Collections__Maps_i
import opened CausalMesh_Types_i

function method CAddMetaToMetaMap(todos: map<CKey, CVectorClock>, m: CMeta) : map<CKey, CVectorClock> 
    requires (forall i :: i in todos ==> CVectorClockIsValid(todos[i]))
    requires CMetaIsValid(m)
    requires (forall k :: k in todos ==> CVectorClockValid(todos[k])) //&& todos[k].key == k)
    requires CMetaValid(m)
    ensures var res := CAddMetaToMetaMap(todos, m); m.key in res && (forall k :: k in res ==> CVectorClockValid(res[k]))//&& res[k].key == k)
    ensures 
        var lr := AddMetaToMetaMap(
            map k | k in (set ck | ck in todos) :: AbstractifyCVectorClockToVectorClock(todos[k]), AbstractifyCMetaToMeta(m)); 
        var cr := CAddMetaToMetaMap(todos, m); 
        (forall i :: i in cr ==>  CVectorClockValid(cr[i])) 
        && ( map k | k in (set ck | ck in cr) :: AbstractifyCVectorClockToVectorClock(cr[k]))
             == (lr)
{
    if m.key in todos then 
        todos[m.key := CVCMerge(todos[m.key], m.vc)]
    else 
        todos[m.key := m.vc]
}

// lemma {:axiom} lemma_CICacheValid(icache:CICache, icache2:CICache)
//     ensures |icache.Values| <= |icache2.Values|

    // ensures forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))

// lemma {:axiom} lemma_CICacheValid2(icache:CICache, domain:set<Key>)
//     ensures forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))

// predicate {:opaque} ICacheValid(icache:CICache, domain:set<Key>){
//     forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
// }


method CGetMetasOfAllDeps3(icache: CICache, deps: CDependency, todos: map<CKey, CVectorClock>, ghost domain: set<CKey>) returns (icache':CICache, res:map<CKey, CVectorClock>)
    // requires CICacheIsValid(icache)
    requires CDependencyIsValid(deps)
    requires (forall i :: i in todos ==> /*CKeyIsValid(i) &&*/ CVectorClockIsValid(todos[i]))
    // requires ICacheValid(icache, domain)
    requires (forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain)))
    requires CDependencyValid(deps)
    requires (forall k :: k in todos ==> CVectorClockValid(todos[k]) && k in Keys_domain)//&& todos[k].key == k)
    // requires (forall k :: k in Keys_domain ==> k in icache)
    requires (forall k :: k in deps ==> k in domain)
    // ensures CICacheIsValid(icache')
    ensures (forall k :: k in res ==> k in Keys_domain && CVectorClockValid(res[k]))// && res[k].key == k)
    ensures (forall i :: i in res ==> /*CKeyIsValid(i) &&*/ CVectorClockIsValid(res[i]))
    ensures (forall k :: k in icache' ==> k in Keys_domain && (forall m :: m in icache'[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain)))
    
    // ensures ICacheValid(icache', domain)
    ensures |icache'.Values| <= |icache.Values|
    // ensures 
    //     var lr := GetMetasOfAllDeps(
    //                 AbstractifyCICacheToICache(icache), 
    //                 AbstractifyCDependencyToDependency(deps), 
    //                 AbstractifyMap(todos, AbstractifyCKeyToKey, AbstractifyCMetaToMeta, AbstractifyCKeyToKey), 
    //                 set i | i in domain :: i
    //             ); 
    //     // (AbstractifyMap(res, AbstractifyCKeyToKey, AbstractifyCMetaToMeta, AbstractifyCKeyToKey)) == (lr)
    //     (map k | k in (set ck | ck in res) :: AbstractifyCMetaToMeta(res[k])) == (lr)
    decreases |icache.Values|, |deps|
{
    if |deps| == 0 { 
        icache' := icache;
        res := todos; 
        assert forall k :: k in res ==> k in Keys_domain && CVectorClockValid(res[k]);
        // assert forall k :: k in icache' ==> k in Keys_domain && (forall m :: m in icache'[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain));
    }
    else 
    {
        var k :| k in deps;
        var new_deps := 
            RemoveElt(deps, k); 			
        if k in todos && ((CVCHappendsBefore(deps[k], todos[k])) || (CVCEq(deps[k], todos[k]))) { 
            // icache' := icache;
            // reveal_ICacheValid();
            icache', 
            res := 
                CGetMetasOfAllDeps3(icache, new_deps, todos, domain); 	
            // assume forall k :: k in icache' ==> k in Keys_domain && (forall m :: m in icache'[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain));		 
        }
        else if k in icache
        {
            // reveal_ICacheValid();
            // lemma_CICacheValid2(icache, domain);
            assert (forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain)));
            var metas := 
                (set m | m in icache[k] && ((CVCHappendsBefore(m.vc, deps[k])) || (CVCEq(m.vc, deps[k])))); 				
            if |metas| > 0 { 
                res := todos;
                var initial := 
                    CEmptyMeta(k); 		
                assert forall m :: m in metas ==> CMetaValid(m);			
                var merged := 
                    CFoldMetaSet(initial, metas, domain);			
                var meta := 
                    merged.(vc := deps[k]); 					
                var new_cache := 
                    icache[k := icache[k] - metas]; 
                assert icache[k] >= metas;
                    lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
                    assert |new_cache.Values| < |icache.Values|;

                assert forall k :: k in merged.deps ==> k in domain ;	
                // lemma_CICacheValid(new_cache, domain);				
                var new_icache', res' := 
                    CGetMetasOfAllDeps3(new_cache, merged.deps, todos, domain); 
                // assert CICacheIsValid(new_icache');
                // lemma_CICacheValid(new_icache', domain);
                
                // assert forall k :: k in new_icache' ==> k in Keys_domain && (forall m :: m in new_icache'[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain));
                assert forall k :: k in res' ==> k in Keys_domain && CVectorClockValid(res'[k]); //&& res'[k].key == k;					
                var todos' := 
                    CAddMetaToMetaMap(res', meta); 	
                // lemma_CICacheValid(new_icache', new_cache);
                assert |new_icache'.Values| <= |new_cache.Values|;

                // var i, r := CGetMetasOfAllDeps3(new_icache', new_deps, todos', domain);
                // assert ICacheValid(new_icache', domain);
                icache', 
                res := 
                    CGetMetasOfAllDeps3(new_icache', new_deps, todos', domain);
                // assume forall k :: k in icache' ==> k in Keys_domain && (forall m :: m in icache'[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain));	
                // assert forall k :: k in res ==> k in Keys_domain && CMetaIsValid(res[k]) && res[k].key == k;	
            }
            else 
            {
                var initial := 
                    CEmptyMeta(k); 					
                var meta := 
                    initial.(vc := deps[k]); 					
                var todos' := 
                    CAddMetaToMetaMap(todos, meta); 					
                icache', 
                res := 
                    CGetMetasOfAllDeps3(icache, new_deps, todos', domain);
                assert (forall k :: k in res ==> CVectorClockValid(res[k]));// && res[k].key == k);
                // assume forall k :: k in icache' ==> k in Keys_domain && (forall m :: m in icache'[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain));	
            }
        } 
        else {
            var initial := 
                    CEmptyMeta(k); 					
            var meta := 
                initial.(vc := deps[k]); 					
            var todos' := 
                CAddMetaToMetaMap(todos, meta); 					
            icache', 
            res := 
                CGetMetasOfAllDeps3(icache, new_deps, todos', domain);
            assert (forall k :: k in res ==> CVectorClockValid(res[k]));// && res[k].key == k);
            // assume forall k :: k in icache' ==> k in Keys_domain && (forall m :: m in icache'[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain));	
        }
    }
}
}
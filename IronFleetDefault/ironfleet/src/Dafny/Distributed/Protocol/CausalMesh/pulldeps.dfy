include "../../Common/Collections/Maps.i.dfy"
include "types.dfy"
include "message.dfy"
// include "properties.dfy"
include "../../Common/Collections/Maps2.i.dfy"

module CausalMesh_PullDeps_i {
    import opened Collections__Maps_i
    import opened CausalMesh_Types_i
    import opened CausalMesh_Message_i
    // import opened CausalMesh_Properties_i
    import opened Collections__Maps2_i

    // function AddMetaToMetaMap2(todos:map<Key, Meta>, m:Meta) : (res:map<Key, Meta>)
    //     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    //                 // && forall kk :: kk in todos[k].deps ==> 
    //                 //     VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
    //     requires MetaValid(m)
    //     ensures m.key in res
    //     ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
    //     // ensures forall k :: k in res ==> forall kk :: kk in res[k].deps ==> 
    //     //                 VCHappendsBefore(res[k].deps[kk], res[k].vc) || VCEq(res[k].deps[kk], res[k].vc)
    // {
    //     if m.key in todos then
    //         todos[m.key := MetaMerge(todos[m.key], m)]
    //     else 
    //         todos[m.key := m]
    // }

    function AddMetaToMetaMap(todos:map<Key, VectorClock>, m:Meta) : (res:map<Key, VectorClock>)
        requires forall k :: k in todos ==> VectorClockValid(todos[k])
                    // && forall kk :: kk in todos[k].deps ==> 
                    //     VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
        requires MetaValid(m)
        ensures m.key in res
        ensures forall k :: k in res ==> VectorClockValid(res[k])
        // ensures forall k :: k in res ==> forall kk :: kk in res[k].deps ==> 
        //                 VCHappendsBefore(res[k].deps[kk], res[k].vc) || VCEq(res[k].deps[kk], res[k].vc)
    {
        if m.key in todos then
            todos[m.key := VCMerge(todos[m.key], m.vc)]
        else 
            todos[m.key := m.vc]
    }

    function GetMetasOfAllDeps(icache:ICache, deps:Dependency, todos:map<Key, VectorClock>, domain:set<Key>) : map<Key, VectorClock>
        requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
                    && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
        requires DependencyValid(deps)
        requires forall k :: k in todos ==> VectorClockValid(todos[k]) && k in Keys_domain
        // requires forall k :: k in todos ==> forall kk :: kk in todos[k].deps ==> 
        //                 VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
        // requires CausalCut(todos)
        requires forall k :: k in Keys_domain ==> k in icache // should we have this?
        requires forall k :: k in deps ==> k in domain 

        ensures var res := GetMetasOfAllDeps(icache, deps, todos, domain);
                forall k :: k in res ==> VectorClockValid(res[k]) && k in Keys_domain
        // ensures forall k :: k in todos ==> k in res && (VCHappendsBefore(todos[k].vc, res[k].vc) || VCEq(todos[k].vc, res[k].vc))
        // ensures forall k :: k in deps ==> k in res && (VCHappendsBefore(deps[k], res[k].vc) || VCEq(deps[k], res[k].vc))
        // ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
                        // && forall kk :: kk in res[k].deps ==> 
                        //     VCHappendsBefore(res[k].deps[kk], res[k].vc) || VCEq(res[k].deps[kk], res[k].vc)
        // ensures CausalCut(res)
        decreases |icache.Values|, |deps|
    {
        // map[]
        if |deps| == 0 then 
            todos
        else 
            var k :| k in deps;
            var new_deps := RemoveElt(deps, k);
            if k in todos && (VCHappendsBefore(deps[k], todos[k]) || VCEq(deps[k], todos[k])) then 
                var res := GetMetasOfAllDeps(icache, new_deps, todos, domain);
                res
            else
                var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
                // if exists m :: m in icache[k] && VCEq(m.vc, deps[k]) then 
                if |metas| > 0 then
                    // var m :| m in icache[k] && VCEq(m.vc, deps[k]);
                    var initial := EmptyMeta(k);
                    // assert forall m :: m in metas ==> forall kk :: kk in m.deps ==> kk in domain;
                    var merged := FoldMetaSet(initial, metas, domain);
                    var meta := merged.(vc := deps[k]);
                    // var meta := m;
                    
                    // lemma_FoldMetaBounded(initial, metas, deps[k], domain);
                    // assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));

                    var new_cache := icache[k:= icache[k] - metas];
                    assert icache[k] >= metas;
                    lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
                    assert |new_cache.Values| < |icache.Values|;

                    assert forall k :: k in merged.deps ==> k in domain ;
                    var res := GetMetasOfAllDeps(new_cache, merged.deps, todos, domain);

                    var todos' := AddMetaToMetaMap(res, meta);
                    // assert forall kk :: kk in merged.deps ==> kk in res && (VCHappendsBefore(merged.deps[kk], res[kk].vc) || VCEq(merged.deps[kk], res[kk].vc));
                    // assert merged.deps == meta.deps;
                    // lemma_AddMetaToMetaMap(res, meta);
                    
                    // assert forall k :: k in todos' ==>
                    //         forall kk :: kk in todos'[k].deps ==>
                    //             kk in todos' && (VCHappendsBefore(todos'[k].deps[kk], todos'[kk].vc) || VCEq(todos'[k].deps[kk], todos'[kk].vc));
                    // assert CausalCut(todos');

                    var res' := GetMetasOfAllDeps(icache, new_deps, todos', domain);
                    res'
                else 
                    var initial := EmptyMeta(k);
                    var meta := initial.(vc:=deps[k]);
                    // assert CausalCut(todos);
                   
                    var todos' := AddMetaToMetaMap(todos, meta);
                    
                    var res := GetMetasOfAllDeps(icache, new_deps, todos', domain);
                    res
    }


    lemma {:axiom} lemma_MapRemoveSubsetOfTheValOfKey<K,V>(m:map<K,set<V>>, k:K, s:set<V>)
        requires k in m && m[k] >= s
        ensures |m.Values| > |m[k := m[k] - s].Values|

    // function GetMetasOfAllDeps2(icache:ICache, deps:Dependency, todos:map<Key, Meta>, domain:set<Key>) : map<Key, Meta>
    //     requires forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> MetaValid(m) && m.key == k
    //                 && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain))
    //     requires DependencyValid(deps)
    //     requires forall k :: k in todos ==> MetaValid(todos[k]) && todos[k].key == k 
    //     // requires forall k :: k in todos ==> forall kk :: kk in todos[k].deps ==> 
    //     //                 VCHappendsBefore(todos[k].deps[kk], todos[k].vc) || VCEq(todos[k].deps[kk], todos[k].vc)
    //     // requires CausalCut(todos)
    //     requires forall k :: k in Keys_domain ==> k in icache // should we have this?
    //     requires forall k :: k in deps ==> k in domain 

    //     ensures var res := GetMetasOfAllDeps2(icache, deps, todos, domain);
    //             forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
    //     // ensures forall k :: k in todos ==> k in res && (VCHappendsBefore(todos[k].vc, res[k].vc) || VCEq(todos[k].vc, res[k].vc))
    //     // ensures forall k :: k in deps ==> k in res && (VCHappendsBefore(deps[k], res[k].vc) || VCEq(deps[k], res[k].vc))
    //     // ensures forall k :: k in res ==> MetaValid(res[k]) && res[k].key == k 
    //                     // && forall kk :: kk in res[k].deps ==> 
    //                     //     VCHappendsBefore(res[k].deps[kk], res[k].vc) || VCEq(res[k].deps[kk], res[k].vc)
    //     // ensures CausalCut(res)
    //     decreases |icache.Values|, |deps|
    // {
    //     // map[]
    //     if |deps| == 0 then 
    //         todos
    //     else 
    //         var k :| k in deps;
    //         var new_deps := RemoveElt(deps, k);
    //         if k in todos && (VCHappendsBefore(deps[k], todos[k].vc) || VCEq(deps[k], todos[k].vc)) then 
    //             var res := GetMetasOfAllDeps2(icache, new_deps, todos, domain);
    //             res
    //         else
    //             var metas := set m | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k]));
    //             // if exists m :: m in icache[k] && VCEq(m.vc, deps[k]) then 
    //             if |metas| > 0 then
    //                 // var m :| m in icache[k] && VCEq(m.vc, deps[k]);
    //                 var initial := EmptyMeta(k);
    //                 // assert forall m :: m in metas ==> forall kk :: kk in m.deps ==> kk in domain;
    //                 var merged := FoldMetaSet(initial, metas, domain);
    //                 var meta := merged.(vc := deps[k]);
    //                 // var meta := m;
                    
    //                 // lemma_FoldMetaBounded(initial, metas, deps[k], domain);
    //                 // assert (VCHappendsBefore(merged.vc, meta.vc) || VCEq(merged.vc, meta.vc));

    //                 var new_cache := icache[k:= icache[k] - metas];
    //                 assert icache[k] >= metas;
    //                 lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
    //                 assert |new_cache.Values| < |icache.Values|;

    //                 assert forall k :: k in merged.deps ==> k in domain ;
    //                 var res := GetMetasOfAllDeps2(new_cache, merged.deps, todos, domain);

    //                 var todos' := AddMetaToMetaMap2(res, meta);
    //                 // assert forall kk :: kk in merged.deps ==> kk in res && (VCHappendsBefore(merged.deps[kk], res[kk].vc) || VCEq(merged.deps[kk], res[kk].vc));
    //                 // assert merged.deps == meta.deps;
    //                 // lemma_AddMetaToMetaMap(res, meta);
                    
    //                 // assert forall k :: k in todos' ==>
    //                 //         forall kk :: kk in todos'[k].deps ==>
    //                 //             kk in todos' && (VCHappendsBefore(todos'[k].deps[kk], todos'[kk].vc) || VCEq(todos'[k].deps[kk], todos'[kk].vc));
    //                 // assert CausalCut(todos');

    //                 var res' := GetMetasOfAllDeps2(icache, new_deps, todos', domain);
    //                 res'
    //             else 
    //                 var initial := EmptyMeta(k);
    //                 var meta := initial.(vc:=deps[k]);
    //                 // assert CausalCut(todos);
                   
    //                 var todos' := AddMetaToMetaMap2(todos, meta);
                    
    //                 var res := GetMetasOfAllDeps2(icache, new_deps, todos', domain);
    //                 res
    // }
}
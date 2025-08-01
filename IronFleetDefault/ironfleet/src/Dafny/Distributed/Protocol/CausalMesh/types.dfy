

module CausalMesh_Types_i {

    const Nodes:nat := 3

    const Clients:nat := 5

    const MaxKeys:nat := 1000

    const Keys_domain:set<int> := set i | 0 <= i <= 1000 :: i;

    type Key = int

    type Val = int

    type VectorClock = seq<int>

    predicate VectorClockValid(vc:VectorClock)
    {
        && |vc| == Nodes
        && forall i :: 0 <= i < |vc| ==> vc[i] >= 0
    }

    function EmptyVC() : (res:VectorClock)
        // ensures VectorClockValid(res)
    {
        seq(Nodes, (idx) => 0)
    }

    function VCEq(vc1:VectorClock, vc2:VectorClock) : bool 
        requires VectorClockValid(vc1)
        requires VectorClockValid(vc2)
    {
        forall i :: 0 <= i < |vc1| ==> vc1[i] == vc2[i]
    }

    function VCHappendsBefore(vc1:VectorClock, vc2:VectorClock) : bool 
        requires VectorClockValid(vc1)
        requires VectorClockValid(vc2)
    {
        && !VCEq(vc1, vc2)
        && forall i :: 0 <= i < |vc1| ==> vc1[i] <= vc2[i]
    }

    // lemma lemma_VCRelationIsTransitive(vc:VectorClock, vc1:VectorClock, vc2:VectorClock)
    //     requires VectorClockValid(vc)
    //     requires VectorClockValid(vc2)
    //     requires VectorClockValid(vc1)
    //     requires VCHappendsBefore(vc, vc1) || VCEq(vc, vc1)
    //     requires VCHappendsBefore(vc1, vc2) || VCEq(vc1, vc2)
    //     ensures VCHappendsBefore(vc, vc2) || VCEq(vc, vc2)
    // {

    // }

    // lemma lemma_VCMergePreserveTheRelation(vc1:VectorClock, vc2:VectorClock, vc:VectorClock)
    //     requires VectorClockValid(vc)
    //     requires VectorClockValid(vc2)
    //     requires VectorClockValid(vc1)
    //     requires VCHappendsBefore(vc1, vc) || VCEq(vc1, vc)
    //     requires VCHappendsBefore(vc2, vc) || VCEq(vc2, vc)
    //     ensures VCHappendsBefore(VCMerge(vc1, vc2), vc) || VCEq(VCMerge(vc1, vc2), vc)
    // {

    // }

    function MergeSeqs(s1:seq<int>, s2:seq<int>) : seq<int>
        requires |s1| == |s2|
        ensures var res := MergeSeqs(s1, s2);
                && |res| == |s1|
                && forall i :: 0 <= i < |s1| ==> res[i] == s1[i] || res[i] == s2[i]
        // ensures forall i :: 0 <= i < |s1| ==> s1[i] <= res[i] && s2[i] <= res[i]
        // ensures forall i :: 0 <= i < |s1| ==> res[i] == s1[i] || res[i] == s2[i]
    {   
        if |s1| == 0 then
            []
        else if s1[0] > s2[0] then
            [s1[0]] + MergeSeqs(s1[1..], s2[1..])
        else
            [s2[0]] + MergeSeqs(s1[1..], s2[1..])
    }


    function VCMerge(vc1:VectorClock, vc2:VectorClock) : VectorClock
        requires VectorClockValid(vc1)
        requires VectorClockValid(vc2)
        ensures var res := VCMerge(vc1, vc2);
                VectorClockValid(res)
        // ensures (VCHappendsBefore(vc1, res) || VCEq(vc1, res))
        // ensures (VCHappendsBefore(vc2, res) || VCEq(vc2, res))
    {
        MergeSeqs(vc1, vc2)
    }

    
    type Dependency = map<Key, VectorClock>

    predicate DependencyValid(dep:Dependency)
    {
        forall k :: k in dep ==> k in Keys_domain && VectorClockValid(dep[k])
    }

    function DependencyEq(dep1:Dependency, dep2:Dependency) : bool 
        requires DependencyValid(dep1)
        requires DependencyValid(dep2)
    {
        forall k :: k in dep1 ==> k in dep2 && VCEq(dep1[k], dep2[k])
    }

    function DependencyMerge(dep1:Dependency, dep2:Dependency) : Dependency
        requires DependencyValid(dep1)
        requires DependencyValid(dep2)
        ensures var res := DependencyMerge(dep1, dep2);
                DependencyValid(res)
        // ensures forall k :: k in dep1 ==> k in res 
        // ensures forall k :: k in dep2 ==> k in res
        // ensures res.Keys == dep1.Keys + dep2.Keys
    {
        map k | k in dep1.Keys + dep2.Keys ::
            if k in dep1 && k in dep2 then
                VCMerge(dep1[k], dep2[k])
            else if k in dep1 then
                dep1[k]
            else
                dep2[k]
    }

    function DependencyInsertOrMerge(dep:Dependency, k:Key, vc:VectorClock) : Dependency
        requires DependencyValid(dep)
        requires k in Keys_domain
        requires VectorClockValid(vc)
        // ensures DependencyValid(res)
        // ensures k in res
    {
        if k in dep then
            var d := dep[k := VCMerge(dep[k], vc)];
            // assert DependencyValid(d);
            d
        else 
            dep[k := vc]
    }


    datatype Meta = Meta (
        key : Key,
        // val : Val,
        vc : VectorClock,
        deps : Dependency
    )

    predicate MetaValid(m:Meta) 
    {
        && m.key in Keys_domain
        && VectorClockValid(m.vc)
        && DependencyValid(m.deps)
        // && forall k :: k in m.deps ==> VCHappendsBefore(m.deps[k], m.vc) || VCEq(m.deps[k], m.vc)
    }

    predicate MetaEq(m1:Meta, m2:Meta)
        requires MetaValid(m1)
        requires MetaValid(m2)
    {
        && m1.key == m2.key
        && VCEq(m1.vc, m2.vc)
        && DependencyEq(m1.deps, m2.deps)
    }

    predicate MetaHappensBefore(m1:Meta, m2:Meta)
        requires MetaValid(m1)
        requires MetaValid(m2)
    {
        VCHappendsBefore(m1.vc, m2.vc)
    }

    function MetaMerge(m1:Meta, m2:Meta) : Meta
        requires m1.key == m2.key
        requires MetaValid(m1)
        requires MetaValid(m2)
        ensures var res := MetaMerge(m1, m2);
                MetaValid(res)
    {
        m1.(vc := VCMerge(m1.vc, m2.vc), deps := DependencyMerge(m1.deps, m2.deps))
    }

    function FoldMetaSet(acc: Meta, metas: set<Meta>, domain:set<Key>) : Meta
        requires MetaValid(acc)
        requires forall kk :: kk in acc.deps ==> kk in domain
        requires forall m :: m in metas ==> MetaValid(m) && m.key == acc.key && (forall kk :: kk in m.deps ==> kk in domain)
        ensures var res := FoldMetaSet(acc, metas, domain);
                MetaValid(res)
                && forall kk :: kk in res.deps ==> kk in domain
        // ensures res.key == acc.key
        // // ensures VCHappendsBefore(acc.vc, res.vc) || VCEq(acc.vc, res.vc)
        // // ensures forall m :: m in metas ==> 
        // //         VCHappendsBefore(m.vc, res.vc) || VCEq(m.vc, res.vc);
        // ensures forall kk :: kk in res.deps ==> kk in domain && (VCHappendsBefore(res.deps[kk], res.vc) || VCEq(res.deps[kk], res.vc))
        decreases |metas|
    {
        if |metas| == 0 then
            acc
        else
            var x :| x in metas;
            FoldMetaSet(MetaMerge(acc, x), metas - {x}, domain)
    }

    // function FoldMetaSet2(acc: Meta, metas: set<Meta>) : (res:Meta)
    //     // requires MetaValid(acc)
    //     // // requires forall kk :: kk in acc.deps ==> kk in domain
    //     // requires forall m :: m in metas ==> MetaValid(m) && m.key == acc.key // && (forall kk :: kk in m.deps ==> kk in domain)
    //     // ensures MetaValid(res)
    //     // ensures res.key == acc.key
    //     // ensures VCHappendsBefore(acc.vc, res.vc) || VCEq(acc.vc, res.vc)
    //     // ensures forall m :: m in metas ==> 
    //     //         VCHappendsBefore(m.vc, res.vc) || VCEq(m.vc, res.vc);
    //     // ensures forall kk :: kk in res.deps ==> 
    //     //         //kk in domain 
    //     //         && (VCHappendsBefore(res.deps[kk], res.vc) || VCEq(res.deps[kk], res.vc))
    //     // decreases |metas|
    // {
    //     if |metas| == 0 then
    //         acc
    //     else
    //         var x :| x in metas;
    //         FoldMetaSet2(MetaMerge(acc, x), metas - {x})
    // }

    // // lemma lemma_FoldEmptyMetasResultInEmptyMeta(
    // //     acc: Meta, metas: set<Meta>
    // // )
    // //     requires MetaValid(acc)
    // //     requires forall m :: m in metas ==> MetaValid(m) && m.key == acc.key && m == EmptyMeta(m.key)
    // //     requires acc == EmptyMeta(acc.key)
    // //     ensures var res := FoldMetaSet2(acc, metas);
    // //             res == EmptyMeta(acc.key)
    // // {

    // // }

    // // lemma VCMergeBounded(metas: set<Meta>, bound: VectorClock)
    // //     requires forall m :: m in metas ==> VCHappendsBefore(m.vc, bound) || VCEq(m.vc, bound)
    // //     ensures VCHappendsBefore(FoldMetaSet(metas).vc, bound) || VCEq(FoldMetaSet(metas).vc, bound)
    // // {
    // //     // inductive proof over FoldVC
    // // }

    // // lemma lemma_FoldMetaBounded(acc: Meta, metas: set<Meta>, bound: VectorClock, domain: set<Key>)
    // //     requires MetaValid(acc)
    // //     requires VectorClockValid(bound)
    // //     requires forall kk :: kk in acc.deps ==> kk in domain
    // //     requires forall m :: m in metas ==> MetaValid(m) && m.key == acc.key && (forall kk :: kk in m.deps ==> kk in domain)
    // //     requires VCHappendsBefore(acc.vc, bound) || VCEq(acc.vc, bound)
    // //     requires forall m :: m in metas ==> VCHappendsBefore(m.vc, bound) || VCEq(m.vc, bound)
    // //     ensures  VCHappendsBefore(FoldMetaSet(acc, metas, domain).vc, bound) || VCEq(FoldMetaSet(acc, metas, domain).vc, bound)
    // //     decreases |metas|
    // // {
    // //     if |metas| == 0 {
    // //         return;
    // //     }

    // //     var x :| x in metas;

    // //     // Step 1: prove MetaMerge(acc, x).vc <= bound
    // //     assert VCHappendsBefore(acc.vc, bound) || VCEq(acc.vc, bound);
    // //     assert VCHappendsBefore(x.vc, bound) || VCEq(x.vc, bound);
    // //     assert VCHappendsBefore(MetaMerge(acc, x).vc, bound) || VCEq(MetaMerge(acc, x).vc, bound);

    // //     // Step 2: call induction on smaller set
    // //     lemma_FoldMetaBounded(MetaMerge(acc, x), metas - {x}, bound, domain);
    // // }

    // // lemma {:axiom} lemma_FoldMetaSet2_Decompose(
    // //     acc: Meta,
    // //     metas: set<Meta>,
    // //     m: Meta
    // // )
    // //     requires MetaValid(acc)
    // //     requires MetaValid(m)
    // //     requires forall mm :: mm in metas ==> MetaValid(mm) && mm.key == acc.key
    // //     requires m.key == acc.key
    // //     ensures FoldMetaSet2(acc, metas + {m}) == FoldMetaSet2(FoldMetaSet2(acc, metas), {m})
    // //     decreases |metas|
    // // // {
    // // //     if |metas| == 0 {
    // // //         assert FoldMetaSet2(acc, metas + {m}) == FoldMetaSet2(acc, {m});
    // // //     } else {
    // // //         var x :| x in metas;

    // // //         lemma_FoldMetaSet2_Decompose(MetaMerge(acc, x), metas - {x}, m);

    // // //         // assert FoldMetaSet2(MetaMerge(acc, x), metas-{x}+{m}) == FoldMetaSet2(FoldMetaSet2(MetaMerge(acc,x), metas-{x}), {m});

    // // //         // assert FoldMetaSet2(acc, metas + {m}) ==
    // // //         //        FoldMetaSet2(MetaMerge(acc, x), (metas - {x}) + {m});
    // // //     }
    // // // }


    function FoldVC(acc: VectorClock, vcs: set<VectorClock>) : VectorClock
        requires VectorClockValid(acc)
        requires forall m :: m in vcs ==> VectorClockValid(m)
        ensures var res := FoldVC(acc, vcs);
                VectorClockValid(res)
        // ensures forall vc :: vc in vcs ==> VCHappendsBefore(vc, res) || VCEq(vc, res)
        // ensures VCHappendsBefore(acc, res) || VCEq(acc, res)
        decreases |vcs|
    {
        if |vcs| == 0 then
            acc
        else
            var x :| x in vcs;
            var merged := VCMerge(acc, x);
            // assert VCHappendsBefore(x, merged) || VCEq(x, merged);
            var res := FoldVC(VCMerge(acc, x), vcs - {x});
            res
    }

    function FoldDependency(acc: Dependency, deps: set<Dependency>) : Dependency
        requires DependencyValid(acc)
        requires forall m :: m in deps ==> DependencyValid(m)
        ensures var res := FoldDependency(acc, deps);
                DependencyValid(res)
        decreases |deps|
    {
        if |deps| == 0 then
            acc
        else
            var x :| x in deps;
            FoldDependency(DependencyMerge(acc, x), deps - {x})
    }

    function FoldDependencyFromMetaSet(acc: Dependency, metas: set<Meta>) : Dependency
        requires DependencyValid(acc)
        requires forall m :: m in metas ==> MetaValid(m)
        ensures var res := FoldDependencyFromMetaSet(acc, metas);
                DependencyValid(res)
        decreases |metas|
    {
        if |metas| == 0 then
            acc
        else
            var x :| x in metas;
            FoldDependencyFromMetaSet(DependencyMerge(acc, x.deps), metas - {x})
    }
    
    // // lemma lemma_VCMergeBounded(
    // //     v1: VectorClock,
    // //     v2: VectorClock,
    // //     bound: VectorClock
    // // )
    // //     requires VectorClockValid(v1)
    // //     requires VectorClockValid(v2)
    // //     requires VectorClockValid(bound)
    // //     requires VCHappendsBefore(v1,bound) || VCEq(v1,bound)
    // //     requires VCHappendsBefore(v2,bound) || VCEq(v2,bound)
    // //     ensures VCHappendsBefore(VCMerge(v1,v2), bound) || VCEq(VCMerge(v1,v2), bound)
    // // {

    // // }

    // // lemma lemma_DependencyMergeBounded(
    // //     d1: Dependency,
    // //     d2: Dependency,
    // //     vc: VectorClock
    // // )
    // //     requires DependencyValid(d1)
    // //     requires DependencyValid(d2)
    // //     requires VectorClockValid(vc)
    // //     requires forall k :: k in d1 ==> VCHappendsBefore(d1[k], vc) || VCEq(d1[k], vc)
    // //     requires forall k :: k in d2 ==> VCHappendsBefore(d2[k], vc) || VCEq(d2[k], vc)
    // //     ensures forall k :: k in DependencyMerge(d1, d2) ==> VCHappendsBefore(DependencyMerge(d1,d2)[k], vc) || VCEq(DependencyMerge(d1,d2)[k], vc)
    // // {
    // //     forall k
    // //         ensures k in DependencyMerge(d1,d2) ==> 
    // //                 VCHappendsBefore(DependencyMerge(d1,d2)[k], vc) || VCEq(DependencyMerge(d1,d2)[k], vc)
    // //     {
    // //         if k in d1 && k in d2 {
    // //             var v1 := d1[k];
    // //             var v2 := d2[k];
    // //             assert VCHappendsBefore(v1, vc) || VCEq(v1, vc);
    // //             assert VCHappendsBefore(v2, vc) || VCEq(v2, vc);
    // //             // merge = VCMerge(v1,v2) <= vc
    // //             lemma_VCMergeBounded(v1, v2, vc);
    // //         } else if k in d1 {
    // //             assert VCHappendsBefore(d1[k], vc) || VCEq(d1[k], vc);
    // //         } else if k in d2 {
    // //             assert VCHappendsBefore(d2[k], vc) || VCEq(d2[k], vc);
    // //         }
    // //     }
    // // }


    // // lemma lemma_FoldDependencyFromMetaSet(
    // //     deps:Dependency,
    // //     metas:set<Meta>,
    // //     vc:VectorClock
    // // )
    // //     requires DependencyValid(deps)
    // //     requires forall m :: m in metas ==> MetaValid(m)
    // //     requires VectorClockValid(vc)
    // //     requires forall m :: m in metas ==> VCHappendsBefore(m.vc, vc) || VCEq(m.vc, vc)
    // //     requires forall k :: k in deps ==> VCHappendsBefore(deps[k], vc) || VCEq(deps[k], vc)
    // //     ensures var res := FoldDependencyFromMetaSet(deps, metas);
    // //             forall k :: k in res ==> VCHappendsBefore(res[k], vc) || VCEq(res[k], vc)
    // //     decreases |metas|
    // // {
    // //     if |metas| == 0 {
    // //         var res := FoldDependencyFromMetaSet(deps, metas);
    // //         assert res == deps;
    // //         assert forall k :: k in res ==> VCHappendsBefore(res[k], vc) || VCEq(res[k], vc);
    // //         return;
    // //     }

    // //     var x :| x in metas;
    // //     var merged := DependencyMerge(deps, x.deps);

        
    // //     lemma_DependencyMergeBounded(deps, x.deps, vc);

    // //     lemma_FoldDependencyFromMetaSet(merged, metas - {x}, vc);
    // // }
    

    function EmptyMeta(k:Key) : Meta
        // requires k in Keys_domain
        // ensures MetaValid(res)
    {
        Meta(k, seq(Nodes, (idx) => 0), map[])
    }

    type CCache = map<Key, Meta>

    predicate CCacheValid(c:CCache)
    {
        forall k :: k in c ==> k in Keys_domain && MetaValid(c[k]) && c[k].key == k
    }

    

    function MergeCCache(c1:CCache, c2:CCache) : CCache
        requires CCacheValid(c1)
        requires CCacheValid(c2)
        // ensures CCacheValid(res)
    {
        map k | k in c1.Keys + c2.Keys ::
            if k in c1 && k in c2 then
                MetaMerge(c1[k], c2[k])
            else if k in c1 then
                c1[k]
            else
                c2[k]
    }

    function MergeVCIntoCCache(c1:CCache, c2:map<Key, VectorClock>) : CCache
        requires CCacheValid(c1)
        requires forall k :: k in c2 ==> VectorClockValid(c2[k]) && k in Keys_domain
        ensures CCacheValid(MergeVCIntoCCache(c1, c2))
    {
        map k | k in c1.Keys + c2.Keys ::
            if k in c1 && k in c2 then
                var m := c1[k];
                var new_m := m.(vc := VCMerge(m.vc, c2[k]));
                new_m
            else if k in c1 then
                c1[k]
            else
                var m := EmptyMeta(k);
                m.(vc := c2[k])
    }

    type ICache = map<Key, set<Meta>>

    predicate ICacheValid(c:ICache)
    {
        forall k :: k in c ==> k in Keys_domain && (forall m :: m in c[k] ==> MetaValid(m) && m.key == k 
            && (forall kk :: kk in m.deps ==> kk in c))
    }

    

    predicate NodesAreNext(i:int, j:int)
        requires 0 <= i < Nodes
        requires 0 <= j < Nodes
    {
        if i == Nodes - 1 then
            j == 0 
        else 
            j == i + 1
    }
}
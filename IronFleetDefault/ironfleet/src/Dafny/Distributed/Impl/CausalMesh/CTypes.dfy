include "../../Protocol/CausalMesh/types.dfy"
include "../Common/GenericRefinement.i.dfy"

module CausalMesh_CTypes_i {
import opened CausalMesh_Types_i
import opened GenericRefinement_i

function method CMergeVCIntoCCache(c1:CCCache, c2:map<Key, CVectorClock>) : CCCache
    requires CCCacheIsValid(c1)
    requires forall k :: k in c2 ==> CVectorClockIsValid(c2[k])
    requires CCCacheValid(c1)
    requires forall k :: k in c2 ==> CVectorClockValid(c2[k]) && k in Keys_domain
    ensures 
        var lr := MergeVCIntoCCache(AbstractifyCCCacheToCCache(c1), map k | k in c2 :: AbstractifyCVectorClockToVectorClock(c2[k]));
        var cr := CMergeVCIntoCCache(c1, c2);
        CCCacheIsValid(cr) 
        && CCCacheValid(cr)
        && (AbstractifyCCCacheToCCache(cr)) == (lr)
{
    map k | k in c1.Keys + c2.Keys ::
        if k in c1 && k in c2 then
            var m := c1[k];
            var new_m := m.(vc := CVCMerge(m.vc, c2[k]));
            assert k in Keys_domain && CMetaValid(new_m) && new_m.key == k;
            new_m
        else if k in c1 then
            c1[k]
        else
            var m := CEmptyMeta(k);
            assert k in Keys_domain && CMetaValid(m) && m.key == k;
            m.(vc := c2[k])
}

lemma lemma_CMergeVCIntoCCache(c1:CCCache, c2:map<Key, CVectorClock>)
    requires CCCacheIsValid(c1)
    requires forall k :: k in c2 ==> CVectorClockIsValid(c2[k])
    requires CCCacheValid(c1)
    requires forall k :: k in c2 ==> CVectorClockValid(c2[k]) && k in Keys_domain
    ensures var cr := CMergeVCIntoCCache(c1, c2); (forall k :: k in c2 ==> k in CMergeVCIntoCCache(c1, c2) && (CVCEq(c2[k], cr[k].vc) || CVCHappendsBefore(c2[k], cr[k].vc)))
        && (forall k :: k in c1 ==> k in cr && (CVCEq(c1[k].vc, cr[k].vc) || CVCHappendsBefore(c1[k].vc, cr[k].vc)));
{
    var m := map k | k in c1.Keys + c2.Keys ::
        if k in c1 && k in c2 then
            var m := c1[k];
            var new_m := m.(vc := CVCMerge(m.vc, c2[k]));
            assert k in Keys_domain && CMetaValid(new_m) && new_m.key == k;
            new_m
        else if k in c1 then
            c1[k]
        else
            var m := CEmptyMeta(k);
            assert k in Keys_domain && CMetaValid(m) && m.key == k;
            m.(vc := c2[k]);
    assert m == CMergeVCIntoCCache(c1, c2);
    var cr := CMergeVCIntoCCache(c1, c2);
    assert  (forall k :: k in c2 ==> k in cr && (CVCEq(c2[k], cr[k].vc) || CVCHappendsBefore(c2[k], cr[k].vc)))
        && (forall k :: k in c1 ==> k in cr && (CVCEq(c1[k].vc, cr[k].vc) || CVCHappendsBefore(c1[k].vc, cr[k].vc)));
}

type CKey = int

predicate CKeyIsAbstractable(s: CKey) 
{
    true
}

predicate CKeyIsValid(s: CKey) 
{
    CKeyIsAbstractable(s)
}

function AbstractifyCKeyToKey(s: CKey) : Key 
    requires CKeyIsAbstractable(s)
{
    s
}

type CVal = int

predicate CValIsAbstractable(s: CVal) 
{
    true
}

predicate CValIsValid(s: CVal) 
{
    CValIsAbstractable(s)
}

function AbstractifyCValToVal(s: CVal) : Val 
    requires CValIsAbstractable(s)
{
    s
}

type CVectorClock = seq<int>

predicate CVectorClockIsAbstractable(s: CVectorClock) 
{
    true
}

predicate CVectorClockIsValid(s: CVectorClock) 
{
    CVectorClockIsAbstractable(s)
}

function AbstractifyCVectorClockToVectorClock(s: CVectorClock) : VectorClock 
    requires CVectorClockIsAbstractable(s)
{
    s
}

function method CVectorClockValid(vc: CVectorClock) : bool 
    requires CVectorClockIsValid(vc)
    ensures var lr := VectorClockValid(AbstractifyCVectorClockToVectorClock(vc)); var cr := CVectorClockValid(vc); (cr) == (lr)
{
    |vc| == Nodes 
    && 
    (forall i :: 0 <= i && i < |vc| ==> vc[i] >= 0)
}

function method CEmptyVC() : (res:CVectorClock)
    ensures CVectorClockValid(res)
{
    seq(Nodes, (idx) => 0)
}

function method CVCEq(vc1: CVectorClock, vc2: CVectorClock) : bool 
    requires CVectorClockIsValid(vc1)
    requires CVectorClockIsValid(vc2)
    requires CVectorClockValid(vc1)
    requires CVectorClockValid(vc2)
    ensures var lr := VCEq(AbstractifyCVectorClockToVectorClock(vc1), AbstractifyCVectorClockToVectorClock(vc2)); var cr := CVCEq(vc1, vc2); (cr) == (lr)
{
    (forall i :: 0 <= i && i < |vc1| ==> vc1[i] == vc2[i])
}

function method CVCHappendsBefore(vc1: CVectorClock, vc2: CVectorClock) : bool 
    requires CVectorClockIsValid(vc1)
    requires CVectorClockIsValid(vc2)
    requires CVectorClockValid(vc1)
    requires CVectorClockValid(vc2)
    ensures var lr := VCHappendsBefore(AbstractifyCVectorClockToVectorClock(vc1), AbstractifyCVectorClockToVectorClock(vc2)); var cr := CVCHappendsBefore(vc1, vc2); (cr) == (lr)
{
    !CVCEq(vc1, vc2) 
    && 
    (forall i :: 0 <= i && i < |vc1| ==> vc1[i] <= vc2[i])
}

function method CMergeSeqs(s1: seq<int>, s2: seq<int>) : seq<int> 
    requires |s1| == |s2|
    ensures var res := CMergeSeqs(s1, s2); |res| == |s1| && (forall i :: 0 <= i && i < |s1| ==> (res[i] == s1[i]) || (res[i] == s2[i]))
             && (forall i :: 0 <= i < |s1| ==> s1[i] <= res[i] && s2[i] <= res[i])
             && (forall i :: 0 <= i < |s1| ==> res[i] == s1[i] || res[i] == s2[i])
    ensures var lr := MergeSeqs(s1, s2); var cr := CMergeSeqs(s1, s2); (cr) == (lr)
{
    if |s1| == 0 then 
        [] 
    else 
        if s1[0] > s2[0] then 
            [s1[0]] + CMergeSeqs(s1[1 .. ], s2[1 .. ]) 
        else 
            [s2[0]] + CMergeSeqs(s1[1 .. ], s2[1 .. ])
}

function method CVCMerge(vc1: CVectorClock, vc2: CVectorClock) : CVectorClock 
    requires CVectorClockIsValid(vc1)
    requires CVectorClockIsValid(vc2)
    requires CVectorClockValid(vc1)
    requires CVectorClockValid(vc2)
    ensures var res := CVCMerge(vc1, vc2); CVectorClockValid(res)
                && (CVCHappendsBefore(vc1, res) || CVCEq(vc1, res))
                && (CVCHappendsBefore(vc2, res) || CVCEq(vc2, res))
    ensures var lr := VCMerge(AbstractifyCVectorClockToVectorClock(vc1), AbstractifyCVectorClockToVectorClock(vc2)); var cr := CVCMerge(vc1, vc2); CVectorClockIsValid(cr) && (AbstractifyCVectorClockToVectorClock(cr)) == (lr)
{
    CMergeSeqs(vc1, vc2)
}

type CDependency = map<CKey, CVectorClock>

predicate CDependencyIsAbstractable(s: CDependency) 
{
    (forall i :: i in s ==> CKeyIsAbstractable(i) && CVectorClockIsAbstractable(s[i]))
}

predicate CDependencyIsValid(s: CDependency) 
{
    CDependencyIsAbstractable(s) 
    && 
    (forall i :: i in s ==> CKeyIsValid(i) && CVectorClockIsValid(s[i]))
}

function AbstractifyCDependencyToDependency(s: CDependency) : Dependency 
    requires CDependencyIsAbstractable(s)
{
    AbstractifyMap(s, AbstractifyCKeyToKey, AbstractifyCVectorClockToVectorClock, AbstractifyCKeyToKey)
}

function method CDependencyValid(dep: CDependency) : bool 
    requires CDependencyIsValid(dep)
    ensures var lr := DependencyValid(AbstractifyCDependencyToDependency(dep)); var cr := CDependencyValid(dep); (cr) == (lr)
{
    (forall k :: k in dep ==> k in Keys_domain && CVectorClockValid(dep[k]))
}

function method CDependencyEq(dep1: CDependency, dep2: CDependency) : bool 
    requires CDependencyIsValid(dep1)
    requires CDependencyIsValid(dep2)
    requires CDependencyValid(dep1)
    requires CDependencyValid(dep2)
    ensures var lr := DependencyEq(AbstractifyCDependencyToDependency(dep1), AbstractifyCDependencyToDependency(dep2)); var cr := CDependencyEq(dep1, dep2); (cr) == (lr)
{
    (forall k :: k in dep1 ==> k in dep2 && CVCEq(dep1[k], dep2[k]))
}

function method CDependencyMerge(dep1: CDependency, dep2: CDependency) : CDependency 
    requires CDependencyIsValid(dep1)
    requires CDependencyIsValid(dep2)
    requires CDependencyValid(dep1)
    requires CDependencyValid(dep2)
    ensures var res := CDependencyMerge(dep1, dep2); CDependencyValid(res)
    ensures var lr := DependencyMerge(AbstractifyCDependencyToDependency(dep1), AbstractifyCDependencyToDependency(dep2)); var cr := CDependencyMerge(dep1, dep2); CDependencyIsValid(cr) && (AbstractifyCDependencyToDependency(cr)) == (lr)
{
    (map k | k in dep1.Keys + dep2.Keys :: if k in dep1 && k in dep2 then CVCMerge(dep1[k], dep2[k]) else if k in dep1 then dep1[k] else dep2[k])
}

function method CDependencyInsertOrMerge(dep: CDependency, k: CKey, vc: CVectorClock) : CDependency 
    requires CDependencyIsValid(dep)
    requires CKeyIsValid(k)
    requires CVectorClockIsValid(vc)
    requires CDependencyValid(dep)
    requires k in Keys_domain
    requires CVectorClockValid(vc)
    ensures var lr := DependencyInsertOrMerge(AbstractifyCDependencyToDependency(dep), AbstractifyCKeyToKey(k), AbstractifyCVectorClockToVectorClock(vc)); var cr := CDependencyInsertOrMerge(dep, k, vc); CDependencyIsValid(cr) && (AbstractifyCDependencyToDependency(cr)) == (lr)
{
    if k in dep then 
        var d := 
            dep[k := CVCMerge(dep[k], vc)]; 			
        d 
    else 
        dep[k := vc]
}

datatype CMeta = 
CMeta(
    key: CKey, 
    vc: CVectorClock, 
    deps: CDependency
)

predicate CMetaIsValid(s: CMeta) 
{
    CMetaIsAbstractable(s) 
    && 
    CKeyIsValid(s.key) 
    && 
    CVectorClockIsValid(s.vc) 
    && 
    CDependencyIsValid(s.deps)
}

predicate CMetaIsAbstractable(s: CMeta) 
{
    CKeyIsAbstractable(s.key) 
    && 
    CVectorClockIsAbstractable(s.vc) 
    && 
    CDependencyIsAbstractable(s.deps)
}

function AbstractifyCMetaToMeta(s: CMeta) : Meta 
    requires CMetaIsAbstractable(s)
{
    Meta(AbstractifyCKeyToKey(s.key), AbstractifyCVectorClockToVectorClock(s.vc), AbstractifyCDependencyToDependency(s.deps))
}

function method CEmptyMeta(k:Key) : (res:CMeta)
    requires k in Keys_domain
    ensures CMetaValid(res)
    ensures AbstractifyCMetaToMeta(res) == EmptyMeta(k)
{
    CMeta(k, seq(Nodes, (idx) => 0), map[])
}

function method CMetaValid(m: CMeta) : bool 
    requires CMetaIsValid(m)
    ensures var lr := MetaValid(AbstractifyCMetaToMeta(m)); var cr := CMetaValid(m); (cr) == (lr)
{
    m.key in Keys_domain 
    && 
    CVectorClockValid(m.vc) 
    && 
    CDependencyValid(m.deps)
}

function method CMetaEq(m1: CMeta, m2: CMeta) : bool 
    requires CMetaIsValid(m1)
    requires CMetaIsValid(m2)
    requires CMetaValid(m1)
    requires CMetaValid(m2)
    ensures var lr := MetaEq(AbstractifyCMetaToMeta(m1), AbstractifyCMetaToMeta(m2)); var cr := CMetaEq(m1, m2); (cr) == (lr)
{
    m1.key == m2.key 
    && 
    CVCEq(m1.vc, m2.vc) 
    && 
    CDependencyEq(m1.deps, m2.deps)
}

function method CMetaHappensBefore(m1: CMeta, m2: CMeta) : bool 
    requires CMetaIsValid(m1)
    requires CMetaIsValid(m2)
    requires CMetaValid(m1)
    requires CMetaValid(m2)
    ensures var lr := MetaHappensBefore(AbstractifyCMetaToMeta(m1), AbstractifyCMetaToMeta(m2)); var cr := CMetaHappensBefore(m1, m2); (cr) == (lr)
{
    CVCHappendsBefore(m1.vc, m2.vc)
}

function method CMetaMerge(m1: CMeta, m2: CMeta) : CMeta 
    requires CMetaIsValid(m1)
    requires CMetaIsValid(m2)
    requires m1.key == m2.key
    requires CMetaValid(m1)
    requires CMetaValid(m2)
    ensures var res := CMetaMerge(m1, m2); CMetaValid(res)
    ensures var lr := MetaMerge(AbstractifyCMetaToMeta(m1), AbstractifyCMetaToMeta(m2)); var cr := CMetaMerge(m1, m2); CMetaIsValid(cr) && (AbstractifyCMetaToMeta(cr)) == (lr)
{
    m1.(vc := CVCMerge(m1.vc, m2.vc), deps := CDependencyMerge(m1.deps, m2.deps))
}

method CFoldMetaSet(acc: CMeta, metas: set<CMeta>, ghost domain: set<CKey>) returns (res:CMeta) 
    requires CMetaIsValid(acc)
    requires (forall i :: i in metas ==> CMetaIsValid(i))
    requires (forall i :: i in domain ==> CKeyIsValid(i))
    requires CMetaValid(acc)
    requires (forall kk :: kk in acc.deps ==> kk in domain)
    requires (forall m :: m in metas ==> CMetaValid(m) && m.key == acc.key && (forall kk :: kk in m.deps ==> kk in domain))
    ensures CMetaValid(res)
    ensures 
        var lr := FoldMetaSet(AbstractifyCMetaToMeta(acc), AbstractifySet(metas, AbstractifyCMetaToMeta), AbstractifySet(domain, AbstractifyCKeyToKey));
        CMetaIsValid(res) 
        && (AbstractifyCMetaToMeta(res)) == (lr)
    decreases |metas|
{
    if |metas| == 0{ 
        res := acc; 
    }
    else 
    {
        var x :| x in metas;
        res := CFoldMetaSet(CMetaMerge(acc, x), metas - {x}, domain);

        ghost var gacc := AbstractifyCMetaToMeta(acc);
        lemma_AbstractifyCMetaToMeta_Is_Injective(metas);
        ghost var gmetas := AbstractifySet(metas, AbstractifyCMetaToMeta);
        ghost var gnmetas := AbstractifySet(metas - {x}, AbstractifyCMetaToMeta);
        ghost var gx := AbstractifyCMetaToMeta(x);
        ghost var gdomain := AbstractifySet(domain, AbstractifyCKeyToKey);
        assert gnmetas == gmetas - {gx};
        lemma_FoldMetaSet(gacc, gmetas, gdomain, gx);
        assert FoldMetaSet(gacc, gmetas, gdomain) == FoldMetaSet(MetaMerge(gacc, gx), gmetas-{gx}, gdomain);
        assert AbstractifyCMetaToMeta(res) == FoldMetaSet(gacc, gmetas, gdomain);
    }
}


lemma {:axiom} lemma_FoldMetaSet(acc: Meta, metas: set<Meta>, domain: set<Key>, x:Meta)
    requires MetaValid(acc)
    requires MetaValid(x)
    requires x in metas
    requires forall m :: m in metas ==> MetaValid(m) && m.key == acc.key && (forall kk :: kk in m.deps ==> kk in domain)
    requires forall kk :: kk in acc.deps ==> kk in domain 
    ensures FoldMetaSet(acc, metas, domain) == FoldMetaSet(MetaMerge(acc, x), metas-{x}, domain)

method CFoldVC(acc: CVectorClock, vcs: set<CVectorClock>) returns (res:CVectorClock)
    requires CVectorClockIsValid(acc)
    requires (forall i :: i in vcs ==> CVectorClockIsValid(i))
    requires CVectorClockValid(acc)
    requires (forall m :: m in vcs ==> CVectorClockValid(m))
    ensures CVectorClockValid(res)
    ensures 
        var lr := FoldVC(AbstractifyCVectorClockToVectorClock(acc), AbstractifySet(vcs, AbstractifyCVectorClockToVectorClock));  
        CVectorClockIsValid(res)
        && 
        (AbstractifyCVectorClockToVectorClock(res)) == (lr)
    decreases |vcs|
{
    if |vcs| == 0 { 
        res := acc; 
    }
    else 
    {
        var x :| x in vcs;
        ghost var merged := 
            CVCMerge(acc, x); 			
        var nvcs := vcs - {x};
        var r := 
            CFoldVC(CVCMerge(acc, x), nvcs); 

        ghost var gacc := AbstractifyCVectorClockToVectorClock(acc);
        ghost var gvcs := AbstractifySet(vcs, AbstractifyCVectorClockToVectorClock);
        ghost var gnvcs := AbstractifySet(nvcs, AbstractifyCVectorClockToVectorClock);
        ghost var gx := AbstractifyCVectorClockToVectorClock(x);
        assert AbstractifyCVectorClockToVectorClock(r) == FoldVC(AbstractifyCVectorClockToVectorClock(merged), gnvcs);
        assert gnvcs == gvcs - {gx};
        res := r;
        lemma_FoldVC(gacc, gvcs, gx);
        assert FoldVC(gacc, gvcs) == FoldVC(VCMerge(gacc, gx), gvcs - {gx});
        assert AbstractifyCVectorClockToVectorClock(res) == FoldVC(gacc, gvcs);
    }
}

lemma {:axiom} lemma_FoldVC(acc: VectorClock, vcs: set<VectorClock>, x:VectorClock)
    requires VectorClockValid(acc)
    requires VectorClockValid(x)
    requires x in vcs
    requires forall vc :: vc in vcs ==> VectorClockValid(vc)
    ensures FoldVC(acc, vcs) == FoldVC(VCMerge(acc, x), vcs - {x})

// method CFoldDependency(acc: CDependency, deps: set<CDependency>) returns (res:CDependency)
//     requires CDependencyIsValid(acc)
//     requires (forall i :: i in deps ==> CDependencyIsValid(i))
//     requires CDependencyValid(acc)
//     requires (forall m :: m in deps ==> CDependencyValid(m))
//     ensures CDependencyValid(res)
//     decreases |deps|
//     ensures 
//         var lr := FoldDependency(AbstractifyCDependencyToDependency(acc), set i | i in deps :: AbstractifyCDependencyToDependency(i));
//         CDependencyIsValid(res) 
//         && (AbstractifyCDependencyToDependency(res)) == (lr)
// {
//     if |deps| == 0{ 
//         res := acc; 
//     }
//     else 
//     {
//         var x :| x in deps;
//         res := CFoldDependency(CDependencyMerge(acc, x), deps - {x});

//         ghost var gacc := AbstractifyCDependencyToDependency(acc);
//         lemma_AbstractifyCDepdnecy_Is_Injective(deps);
//         ghost var gdeps := AbstractifySet(deps, AbstractifyCDependencyToDependency);
//         ghost var gndeps := AbstractifySet(deps - {x}, AbstractifyCDependencyToDependency);
//         ghost var gx := AbstractifyCDependencyToDependency(x);
//         assert gndeps == gdeps - {gx};
//         lemma_FoldDependency(gacc, gdeps, gx);
//         assert FoldDependency(gacc, gdeps) == FoldDependency(DependencyMerge(gacc, gx), gdeps-{gx});
//         assume AbstractifyCDependencyToDependency(res) == FoldDependency(gacc, gdeps);
//     }
// }

method CFoldDependencyFromMetaSet(acc: CDependency, metas: set<CMeta>) returns (res:CDependency)
    requires CDependencyIsValid(acc)
    requires (forall i :: i in metas ==> CMetaIsValid(i))
    requires CDependencyValid(acc)
    requires (forall m :: m in metas ==> CMetaValid(m))
    ensures CDependencyValid(res)
    decreases |metas|
    ensures 
        var lr := FoldDependencyFromMetaSet(AbstractifyCDependencyToDependency(acc), AbstractifySet(metas, AbstractifyCMetaToMeta)); 
        CDependencyIsValid(res) 
        && (AbstractifyCDependencyToDependency(res)) == (lr)
{
    if |metas| == 0 { 
        res := acc; 
    }
    else 
    {
        var x :| x in metas;
        res := CFoldDependencyFromMetaSet(CDependencyMerge(acc, x.deps), metas - {x});

        ghost var gacc := AbstractifyCDependencyToDependency(acc);
        lemma_AbstractifyCMetaToMeta_Is_Injective(metas);
        ghost var gmetas := AbstractifySet(metas, AbstractifyCMetaToMeta);
        ghost var gnmetas := AbstractifySet(metas - {x}, AbstractifyCMetaToMeta);
        ghost var gx := AbstractifyCMetaToMeta(x);
        assert gnmetas == gmetas - {gx};
        lemma_FoldDependencyFromMetaSet(gacc, gmetas, gx);
        assert FoldDependencyFromMetaSet(gacc, gmetas) == FoldDependencyFromMetaSet(DependencyMerge(gacc, gx.deps), gmetas-{gx});
        assert AbstractifyCDependencyToDependency(res) == FoldDependencyFromMetaSet(gacc, gmetas);

        // lemma_CFoldDependencyFromMetaSet(acc, metas, res);
    }
}

lemma {:axiom} lemma_FoldDependencyFromMetaSet(acc: CDependency, metas: set<Meta>, x:Meta)
    requires DependencyValid(acc)
    requires MetaValid(x)
    requires x in metas
    requires forall m :: m in metas ==> MetaValid(m)
    ensures FoldDependencyFromMetaSet(acc, metas) == FoldDependencyFromMetaSet(DependencyMerge(acc, x.deps), metas-{x})

type CCCache = map<CKey, CMeta>

predicate CCCacheIsAbstractable(s: CCCache) 
{
    (forall i :: i in s ==> CKeyIsAbstractable(i) && CMetaIsAbstractable(s[i]))
}

predicate CCCacheIsValid(s: CCCache) 
{
    CCCacheIsAbstractable(s) 
    && 
    (forall i :: i in s ==> CKeyIsValid(i) && CMetaIsValid(s[i]))
}

function AbstractifyCCCacheToCCache(s: CCCache) : CCache 
    requires CCCacheIsAbstractable(s)
{
    AbstractifyMap(s, AbstractifyCKeyToKey, AbstractifyCMetaToMeta, AbstractifyCKeyToKey)
}

function CCCacheValid(c: CCCache) : bool 
    requires CCCacheIsValid(c)
    ensures var lr := CCacheValid(AbstractifyCCCacheToCCache(c)); var cr := CCCacheValid(c); (cr) == (lr)
{
    (forall k :: k in c ==> k in Keys_domain && CMetaValid(c[k]) && c[k].key == k)
}



// function method CMergeCCache(c1: CCCache, c2: CCCache) : CCCache 
//     requires CCCacheIsValid(c1)
//     requires CCCacheIsValid(c2)
//     requires CCCacheValid(c1)
//     requires CCCacheValid(c2)
//     ensures 
//         var lr := MergeCCache(AbstractifyCCCacheToCCache(c1), AbstractifyCCCacheToCCache(c2)); 
//         var cr := CMergeCCache(c1, c2); 
//         CCCacheIsValid(cr) 
//         && CCCacheValid(cr)
//         && (AbstractifyCCCacheToCCache(cr)) == (lr)
// {
//     ghost var gc1 := AbstractifyCCCacheToCCache(c1);
//     ghost var gc2 := AbstractifyCCCacheToCCache(c2);
//     ghost var gdomain := gc1.Keys + gc2.Keys;
//     ghost var domain := c1.Keys + c2.Keys;
//     assert (set i | i in domain :: i) == gdomain;
//     assert forall k :: k in domain ==> k in gdomain;
//     var res := (map k | k in c1.Keys + c2.Keys :: if k in c1 && k in c2 then CMetaMerge(c1[k], c2[k]) else if k in c1 then c1[k] else c2[k]);
//     lemma_CMergeCCache(c1, c2, res);
//     res
// }

// /** this could be verified, but some times it timeouts,  so let us assume it*/
// lemma {:axiom} lemma_CMergeCCache(c1: CCCache, c2: CCCache, res:CCCache)
//     requires CCCacheIsValid(c1)
//     requires CCCacheIsValid(c2)
//     requires CCCacheValid(c1)
//     requires CCCacheValid(c2)
//     ensures AbstractifyCCCacheToCCache(res) == MergeCCache(AbstractifyCCCacheToCCache(c1), AbstractifyCCCacheToCCache(c2))



type CICache = map<CKey, set<CMeta>>

predicate CICacheIsValid(c: CICache)  
{
    true
} 

function AbstractifyCICacheToICache(s: CICache) : ICache 
{
    map k | k in (set ck | ck in s :: ck) :: (set i | i in s[k] :: AbstractifyCMetaToMeta(i))
}

function CICacheValid(c: CICache) : bool 
    requires CICacheIsValid(c)
    ensures 
        var lr := ICacheValid(AbstractifyCICacheToICache(c)); 
        var cr := CICacheValid(c); 
        (cr) == (lr)
{
    ghost var gc := AbstractifyCICacheToICache(c);
    assert (forall k :: k in c ==> k in Keys_domain) == (forall k :: k in gc ==> k in Keys_domain);
    lemma_AbstractifyCICache(c);
    assert forall k :: k in c ==> forall i, j :: i in c[k] && j in c[k] && AbstractifyCMetaToMeta(i) == AbstractifyCMetaToMeta(j) ==> i == j;
    (forall k :: k in c ==> k in Keys_domain && (forall m :: m in c[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in c)))
}

lemma lemma_AbstractifyCMetaToMeta_Is_Injective(s:set<CMeta>)
    requires forall m :: m in s ==> CMetaIsValid(m)
    ensures SetIsInjective(s, AbstractifyCMetaToMeta)
{

}

lemma lemma_AbstractifyCICache(c:CICache)
    requires CICacheIsValid(c)
    ensures forall k :: k in c ==> forall i, j :: i in c[k] && j in c[k] && AbstractifyCMetaToMeta(i) == AbstractifyCMetaToMeta(j) ==> i == j;
{
    forall k | k in c 
        ensures SetIsInjective(c[k], AbstractifyCMetaToMeta)
    {
        lemma_AbstractifyCMetaToMeta_Is_Injective(c[k]);
    }
}

function method CNodesAreNext(i: int, j: int) : bool 
    requires 0 <= i && i < Nodes
    requires 0 <= j && j < Nodes
    ensures var lr := NodesAreNext(i, j); var cr := CNodesAreNext(i, j); (cr) == (lr)
{
    if i == Nodes - 1 then 
        j == 0 
    else 
        j == i + 1
}

}
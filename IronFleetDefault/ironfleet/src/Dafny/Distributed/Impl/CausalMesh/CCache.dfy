include "CPulldeps.dfy"
include "CMessage.dfy"
include "../../Protocol/CausalMesh/cache.dfy"
include "../Common/GenericRefinement.i.dfy"
include "../../Common/Native/Io.s.dfy"
include "../Common/NodeIdentity.i.dfy"

module CausalMesh_CCache_i {
import opened CausalMesh_CTypes_i
// import opened CausalMesh_Types_i
import opened CausalMesh_CMessage_i
import opened CausalMesh_Message_i
// import opened CausalMesh_CProperties_i
import opened CausalMesh_CPullDeps_i
import opened CausalMesh_PullDeps_i
import opened CausalMesh_Cache_i
import opened GenericRefinement_i
import opened Native__Io_s
import opened Common__NodeIdentity_i
import opened Environment_s
import opened CausalMesh_Types_i
import opened Collections__Maps_i

method CReceiveRead(s: CServer, p: CPacket) returns (s':CServer, sp:seq<CPacket>) 
    requires CServerIsValid(s)
    requires CPacketIsValid(p)
    requires p.msg.CMessage_Read?
    requires CServerValid(s)
    requires CPacketValid(p)
    ensures CServerIsValid(s') 
    // ensures (forall i :: i in sp ==> CPacketIsValid(i)) 
    ensures forall i :: 0 <= i < |sp| ==> CPacketIsAbstractable(sp[i])
    ensures ReceiveRead(AbstractifyCServerToServer(s), AbstractifyCServerToServer(s'), AbstractifyCPacketToPacket(p), AbstractifyCPacketSeq(sp))
{
    // print "Process Read", p.msg.opn_read, "start\n";
    // var t1 := 
    ghost var gs := AbstractifyCServerToServer(s);
    ghost var gp := AbstractifyCPacketToPacket(p);
        var new_icache, new_ccache := 
            CPullDeps3(s.icache, s.ccache, p.msg.deps_read); 	
        ghost var (gnew_icache, gnew_ccache) := PullDeps3(gs.icache, gs.ccache, gp.msg.deps_read);
        assert AbstractifyCICacheToICache(new_icache) == gnew_icache;
        assert AbstractifyCCCacheToCCache(new_ccache) == gnew_ccache;
        if p.msg.key_read !in new_ccache {
            new_ccache := new_ccache[p.msg.key_read := CEmptyMeta(p.msg.key_read)];
        } else {
            new_ccache := new_ccache;
        }
        // assert 		
         var t1 := 
            s.(icache := new_icache, ccache := new_ccache); 
        // var gnew_ccache' := if gp.msg.key_read !in gnew_ccache then
        //     gnew_ccache[gp.msg.key_read := EmptyMeta(gp.msg.key_read)]
        // else 
        //     gnew_ccache;
        
        // ghost var gs' := gs.(icache := gnew_icache, ccache := gnew_ccache');
        // assert AbstractifyCServerToServer(t1) == gs';			
        var rep := 
            CPacket(p.src, s.endpoint, CMessage_Read_Reply(p.msg.opn_read, p.msg.key_read, new_ccache[p.msg.key_read].vc, map[])); 			
        // (t1, t2); 		
        assert CDependencyIsValid(map[]);
        // assert CMessageIsValid(CMessage_Read_Reply(p.msg.opn_read, p.msg.key_read, new_ccache[p.msg.key_read].vc, map[]));
        // assert CPacketIsAbstractable(rep);
        // assert CMessageIsValid(rep.msg);
        lemma_AbstractifyEndpointToID(rep.src, gs.id);
        lemma_AbstractifyEndpointToID(rep.dst, gp.src);
        // assert AbstractifyEndPointToID(rep.src) == gs.id;
        // assert AbstractifyEndPointToID(rep.dst) == gp.src;
        lemma_AbstractifyEmptyDependency(map[]);
        // assert AbstractifyCDependencyToDependency(map[]) == map[];
        assert AbstractifyCPacketToPacket(rep) == LPacket(gp.src, gs.id, 
                        Message_Read_Reply(
                            gp.msg.opn_read,
                            gp.msg.key_read,
                            gnew_ccache[gp.msg.key_read].vc,
                            map[]
                        )
                    );
    
    s' := t1;
    sp := [rep];
    // assert AbstractifyCServerToServer(t1) == gs';	
    // assert AbstractifyCPacketToPacket(sp[0]) == LPacket(gp.src, gs.id, 
    //                     Message_Read_Reply(
    //                         gp.msg.opn_read,
    //                         gp.msg.key_read,
    //                         gnew_ccache[gp.msg.key_read].vc,
    //                         map[]
    //                     )
    //                 );
    // assert CPacketIsAbstractable(sp[0]);
    // assert |sp| == 1;
    lemma_PacketSeqIsAbstractable(sp, LPacket(gp.src, gs.id, 
                        Message_Read_Reply(
                            gp.msg.opn_read,
                            gp.msg.key_read,
                            gnew_ccache[gp.msg.key_read].vc,
                            map[]
                        )));
    // print "Process Read", p.msg.opn_read, " end\n";
}

lemma lemma_AbstractifyEmptyDependency(dep:CDependency)
    requires dep == map[]
    ensures AbstractifyCDependencyToDependency(dep) == map[]
{

}

lemma lemma_PacketSeqIsAbstractable(sp:seq<CPacket>, p:Packet)
    requires |sp| == 1
    requires CPacketIsAbstractable(sp[0])
    requires AbstractifyCPacketToPacket(sp[0]) == p
    ensures forall i :: 0 <= i < |sp| ==> CPacketIsAbstractable(sp[i])
    ensures AbstractifyCPacketSeq(sp) == [p]
{

}

// method FilterSatisfiedDependency(dep:CDependency, ccache:CCCache) returns (res:CDependency)
//     requires CCCacheIsValid(ccache) && CCCacheValid(ccache)
//     requires CDependencyValid(dep) && CDependencyIsValid(dep)
//     ensures CDependencyValid(res)
//     decreases |dep|
// {
//     if |dep| == 0 { 
//         res := map[];
//     } else {
//         var k :| k in dep;
//         var new_dep := RemoveElt(dep, k);
//         var rest := FilterSatisfiedDependency(new_dep, ccache);
//         if k in ccache && (CVCEq(dep[k], ccache[k].vc) || CVCHappendsBefore(dep[k], ccache[k].vc)) {
//             res := rest;
//         } else {
//             res := rest[k:=dep[k]];
//         }
//     }
// }

// method FilterSatisfiedDependency1(dep: CDependency, ccache: CCCache) returns (res: CDependency)
//     requires CCCacheIsValid(ccache) && CCCacheValid(ccache)
//     requires CDependencyValid(dep) && CDependencyIsValid(dep)
//     ensures CDependencyValid(res) && CDependencyIsValid(res)
//     // 确保结果只包含未满足的依赖
//     // ensures forall k :: k in res ==> k in dep && dep[k] == res[k]
//     // ensures forall k :: k in res ==> k !in ccache || (!CVCEq(dep[k], ccache[k].vc) && !CVCHappendsBefore(dep[k], ccache[k].vc))
// {
//     res := map[];
//     var remaining := dep;
    
//     while |remaining| > 0
//         invariant forall k :: k in remaining ==> k in dep
//         invariant CDependencyValid(remaining) && CDependencyIsValid(remaining)
//         invariant CDependencyValid(res) && CDependencyIsValid(res)
//         // invariant remaining.Keys !! res.Keys  // 剩余和结果的键不重复
//         // invariant remaining.Keys + res.Keys <= dep.Keys
//         // // 所有在res中的键都是未满足的依赖
//         // invariant forall k :: k in res ==> k in dep && dep[k] == res[k]
//         // invariant forall k :: k in res ==> k !in ccache || (!CVCEq(dep[k], ccache[k].vc) && !CVCHappendsBefore(dep[k], ccache[k].vc))
//         decreases |remaining|
//     {
//         // 选择一个键来处理
//         var k :| k in remaining;
//         ghost var m := remaining;
        
//         // 从剩余中移除这个键
//         remaining := map key | key in remaining && key != k :: remaining[key];
//         assert forall kk :: kk in remaining ==> kk in m;
//         assert k in m && k !in remaining;
//         lemma_map(remaining, m);
//         assert |remaining| < |m|;
//         assert CDependencyValid(remaining) && CDependencyIsValid(remaining);
        
//         // 检查这个依赖是否已满足
//         if k in ccache && (CVCEq(dep[k], ccache[k].vc) || CVCHappendsBefore(dep[k], ccache[k].vc)) {
//             // 依赖已满足，不添加到结果中
//             // assert CDependencyValid(res) && CDependencyIsValid(res);
//         } else {
//             // 依赖未满足，添加到结果中
//             assert CDependencyValid(res) && CDependencyIsValid(res);
//             assert CVectorClockIsValid(dep[k]) && CVectorClockValid(dep[k]);
//             res := res[k := dep[k]];
//             assert CDependencyValid(res) && CDependencyIsValid(res);
//         }
//     }
//     // lemma_deps(res);
// }

// lemma {:axiom} lemma_deps(dep:CDependency)
//     ensures CDependencyValid(dep) && CDependencyIsValid(dep)

// lemma {:axiom} lemma_map(m1:CDependency, m2:CDependency)
//     ensures |m1| < |m2|

method FilterSatisfiedDependency2(dep: CDependency, ccache: CCCache) returns (res: CDependency)
    requires CCCacheIsValid(ccache) && CCCacheValid(ccache)
    requires CDependencyValid(dep) && CDependencyIsValid(dep)
    ensures CDependencyValid(res) && CDependencyIsValid(res)
    ensures forall k :: k in res ==> k in dep && dep[k] == res[k] && CVCEq(dep[k], res[k])
    ensures forall k :: k in res ==> k !in ccache || (!CVCEq(dep[k], ccache[k].vc) && !CVCHappendsBefore(dep[k], ccache[k].vc))
    ensures forall k :: k in dep && k !in res ==> k in ccache && (CVCEq(dep[k], ccache[k].vc) || CVCHappendsBefore(dep[k], ccache[k].vc))
{
    res := map k | k in dep && 
              (k !in ccache || 
               (!CVCEq(dep[k], ccache[k].vc) && !CVCHappendsBefore(dep[k], ccache[k].vc)))
           :: dep[k];
}

lemma lemma_VCSSatisfiedInCacheMustSatisfiedInNewCache(deps:CDependency, deps2:CDependency, ccache:CCCache, ccache':CCCache)
    requires CDependencyValid(deps) && CDependencyValid(deps2) && CCCacheValid(ccache) && CCCacheValid(ccache')
    requires forall k :: k in deps2 ==> k in deps && CVCEq(deps[k], deps2[k])
    requires forall k :: k in deps && k !in deps2 ==> k in ccache && (CVCEq(deps[k], ccache[k].vc) || CVCHappendsBefore(deps[k], ccache[k].vc))
    requires forall k :: k in ccache ==> k in ccache' && (CVCEq(ccache[k].vc, ccache'[k].vc) || CVCHappendsBefore(ccache[k].vc, ccache'[k].vc))
    requires forall k :: k in deps2 ==> k in ccache' && (CVCEq(deps2[k], ccache'[k].vc) || CVCHappendsBefore(deps2[k], ccache'[k].vc))
    ensures forall k :: k in deps && k !in deps2 ==> k in ccache' && (CVCEq(deps[k], ccache'[k].vc) || CVCHappendsBefore(deps[k], ccache'[k].vc))
    ensures forall k :: k in deps && k in deps2 ==> k in ccache' && (CVCEq(deps[k], ccache'[k].vc) || CVCHappendsBefore(deps[k], ccache'[k].vc))
    ensures forall k :: k in deps ==> k in ccache' && (CVCEq(deps[k], ccache'[k].vc) || CVCHappendsBefore(deps[k], ccache'[k].vc))
{

}


method CReceiveRead_I1(s: CServer, p: CPacket) returns (s':CServer, sp:seq<CPacket>) 
    requires CServerIsValid(s)
    requires CPacketIsValid(p)
    requires p.msg.CMessage_Read?
    requires CServerValid(s)
    requires CPacketValid(p)
    ensures CServerIsValid(s') 
    // // ensures (forall i :: i in sp ==> CPacketIsValid(i)) 
    ensures forall i :: 0 <= i < |sp| ==> CPacketIsAbstractable(sp[i])
    // ensures ReceiveRead(AbstractifyCServerToServer(s), AbstractifyCServerToServer(s'), AbstractifyCPacketToPacket(p), AbstractifyCPacketSeq(sp))
{
    // print "Process Read", p.msg.opn_read, "start\n";
    // var t1 := 
    ghost var gs := AbstractifyCServerToServer(s);
    ghost var gp := AbstractifyCPacketToPacket(p);

    var new_dep := FilterSatisfiedDependency2(p.msg.deps_read, s.ccache);
    assert forall k :: k in new_dep ==> k in p.msg.deps_read && CVCEq(new_dep[k], p.msg.deps_read[k]);

    assert forall k :: k in new_dep ==> (k in s.ccache ==> (!CVCEq(p.msg.deps_read[k], s.ccache[k].vc) && !CVCHappendsBefore(p.msg.deps_read[k], s.ccache[k].vc)));
    assert forall k :: k in p.msg.deps_read && k !in new_dep ==> k in s.ccache && (CVCEq(p.msg.deps_read[k], s.ccache[k].vc) || CVCHappendsBefore(p.msg.deps_read[k], s.ccache[k].vc));

    var new_icache, new_ccache := 
        CPullDeps3(s.icache, s.ccache, new_dep); 	

    assert forall k :: k in new_dep ==> (k in new_ccache && (CVCEq(new_dep[k], new_ccache[k].vc) || CVCHappendsBefore(new_dep[k], new_ccache[k].vc)));
    assert forall k :: k in s.ccache ==> k in new_ccache && (CVCEq(s.ccache[k].vc, new_ccache[k].vc) || CVCHappendsBefore(s.ccache[k].vc, new_ccache[k].vc));
    lemma_VCSSatisfiedInCacheMustSatisfiedInNewCache(p.msg.deps_read, new_dep, s.ccache, new_ccache);

    assert forall k :: k in p.msg.deps_read ==> (k in new_ccache && (CVCEq(p.msg.deps_read [k], new_ccache[k].vc) || CVCHappendsBefore(p.msg.deps_read [k], new_ccache[k].vc)));

    ghost var (gnew_icache, gnew_ccache) := PullDeps3(gs.icache, gs.ccache, gp.msg.deps_read);
    assert AbstractifyCICacheToICache(new_icache) == gnew_icache;
    lemma_ReceiveRead_I1(new_ccache, gnew_ccache);
    assert AbstractifyCCCacheToCCache(new_ccache) == gnew_ccache;


    if p.msg.key_read !in new_ccache {
        new_ccache := new_ccache[p.msg.key_read := CEmptyMeta(p.msg.key_read)];
    } 
    // else {
    //     new_ccache := new_ccache;
    // }
    // assert 		
        var t1 := 
        s.(icache := new_icache, ccache := new_ccache); 
    var gnew_ccache' := if gp.msg.key_read !in gnew_ccache then
        gnew_ccache[gp.msg.key_read := EmptyMeta(gp.msg.key_read)]
    else 
        gnew_ccache;
    
    ghost var gs' := gs.(icache := gnew_icache, ccache := gnew_ccache');
    assert AbstractifyCServerToServer(t1) == gs';			
    var rep := 
        CPacket(p.src, s.endpoint, CMessage_Read_Reply(p.msg.opn_read, p.msg.key_read, new_ccache[p.msg.key_read].vc, map[])); 			
    // (t1, t2); 		
    assert CDependencyIsValid(map[]);
    assert CMessageIsValid(CMessage_Read_Reply(p.msg.opn_read, p.msg.key_read, new_ccache[p.msg.key_read].vc, map[]));
    assert CPacketIsAbstractable(rep);
    assert CMessageIsValid(rep.msg);
    lemma_AbstractifyEndpointToID(rep.src, gs.id);
    lemma_AbstractifyEndpointToID(rep.dst, gp.src);
    // assert AbstractifyEndPointToID(rep.src) == gs.id;
    // assert AbstractifyEndPointToID(rep.dst) == gp.src;
    lemma_AbstractifyEmptyDependency(map[]);
    // // assert AbstractifyCDependencyToDependency(map[]) == map[];
    assert AbstractifyCPacketToPacket(rep) == LPacket(gp.src, gs.id, 
                    Message_Read_Reply(
                        gp.msg.opn_read,
                        gp.msg.key_read,
                        gnew_ccache[gp.msg.key_read].vc,
                        map[]
                    )
                );

    s' := t1;
    sp := [rep];
    // assert AbstractifyCServerToServer(t1) == gs';	
    // assert AbstractifyCPacketToPacket(sp[0]) == LPacket(gp.src, gs.id, 
    //                     Message_Read_Reply(
    //                         gp.msg.opn_read,
    //                         gp.msg.key_read,
    //                         gnew_ccache[gp.msg.key_read].vc,
    //                         map[]
    //                     )
    //                 );
    assert CPacketIsAbstractable(sp[0]);
    assert |sp| == 1;
    lemma_PacketSeqIsAbstractable(sp, LPacket(gp.src, gs.id, 
                        Message_Read_Reply(
                            gp.msg.opn_read,
                            gp.msg.key_read,
                            gnew_ccache[gp.msg.key_read].vc,
                            map[]
                        )));
    // print "Process Read", p.msg.opn_read, " end\n";
    // lemma_ReceiveRead_I1(s, p, s', sp);
}

lemma {:axiom} lemma_ReceiveRead_I1(ccache:CCCache, gccache:CCache)
    requires CCCacheIsValid(ccache)
    ensures AbstractifyCCCacheToCCache(ccache) == gccache


method CReceivePropagate(s: CServer, p: CPacket) returns (s':CServer, sp:seq<CPacket>) 
    requires CServerIsValid(s)
    requires CPacketIsValid(p)
    requires p.msg.CMessage_Propagation?
    requires CServerValid(s)
    requires CPacketValid(p)
    ensures CServerIsValid(s') // && (forall i :: i in sp ==> CPacketIsValid(i)) 
    ensures forall i :: 0 <= i < |sp| ==> CPacketIsValid(sp[i])
    ensures ReceivePropagate(AbstractifyCServerToServer(s), AbstractifyCServerToServer(s'), AbstractifyCPacketToPacket(p), AbstractifyCPacketSeq(sp))
{
    ghost var gs := AbstractifyCServerToServer(s);
    ghost var gp := AbstractifyCPacketToPacket(p);
    // var t1 := 
        if s.next == p.msg.start { 
            // var t1 := 
                if p.msg.round == 2 { 
                    assert gs.next == gp.msg.start;
                    assert gp.msg.round == 2;
                    // var t1 := 
                        var vcs := 
                            p.msg.meta.vc; 							
                        // var t1 := 
                            var new_gvc := 
                                CVCMerge(s.gvc, vcs); 								
                            // var t1 := 
                                var new_deps := 
                                    p.msg.meta.deps; 									
                                // var t1 := 
                                    var new_icache, new_ccache := 
                                        CPullDeps3(s.icache, s.ccache, new_deps); 	
                                    ghost var (gnew_icache, gnew_ccache) := PullDeps3(gs.icache, gs.ccache, gp.msg.meta.deps);
                                    assert AbstractifyCICacheToICache(new_icache) == gnew_icache;
                                    assert AbstractifyCCCacheToCCache(new_ccache) == gnew_ccache;									
                                    // // var t1 := 
                                        var new_ccache' := 
                                            CInsertIntoCCache(new_ccache, p.msg.meta); 	
                                        ghost var gnew_ccache' := InsertIntoCCache(gnew_ccache, gp.msg.meta);	
                                        assert AbstractifyCCCacheToCCache(new_ccache') == gnew_ccache';								
                                        // var t1 := 
                                            var new_icache' := 
                                                CAddMetaToICache(new_icache, p.msg.meta); 
                                            ghost var gnew_icache' := AddMetaToICache(gnew_icache, gp.msg.meta);
                                            assert AbstractifyCICacheToICache(new_icache') == gnew_icache';							
                                            // var t1 := 
                                            s' :=
                                                s.(gvc := new_gvc, icache := new_icache', ccache := new_ccache'); 
                                            assert AbstractifyCServerToServer(s') == gs.(gvc := AbstractifyCVectorClockToVectorClock(new_gvc), icache := AbstractifyCICacheToICache(new_icache'), ccache := AbstractifyCCCacheToCCache(new_ccache'));								
                                            // var t2 := 
                                            sp :=
                                                []; 	
                                            assert AbstractifyCPacketSeq(sp) == [];	
                                            assert ReceivePropagate(gs, AbstractifyCServerToServer(s'), gp, AbstractifyCPacketSeq(sp));
                    // //                         (t1, t2); 											
                    // //                     (t1.1, t1.0); 										
                    // //                 (t1.1, t1.0); 									
                    // //             (t1.1, t1.0); 								
                    // //         (t1.1, t1.0); 							
                    // //     (t1.1, t1.0); 						
                    // // (t1.1, t1.0) 
                
                }   
                else
                { 
                    assert gs.next == gp.msg.start;
                    assert gp.msg.round != 2; 
                    // var t1 := 
                        var new_icache := 
                            CAddMetaToICache(s.icache, p.msg.meta); 
                        							
                        // var t1 := 
                            s' :=
                            s.(icache := new_icache); 							
                        // var t2 := 
                            ghost var gs' := AbstractifyCServerToServer(s');
                            assert gs' == gs.(icache := AbstractifyCICacheToICache(new_icache));
                        
                            var propagate :=
                            CPacket(s.next_endpoint, s.endpoint, p.msg.(round := 2)); 	
                            lemma_AbstractifyEndpointToID(propagate.src, gs.id);
                            lemma_AbstractifyEndpointToID(propagate.dst, gs.next);
                            assert AbstractifyEndPointToID(propagate.src) == gs.id;
                            assert AbstractifyEndPointToID(propagate.dst) == gs.next;	
                            assert AbstractifyCMessageToMessage(propagate.msg) == gp.msg.(round := 2);
                            // assert AbstractifyEndPointToID(propagate.src) == gs.id;
                            assert AbstractifyCPacketToPacket(propagate) == LPacket(gs.next, gs.id, gp.msg.(round := 2));

                            sp := [propagate];
                            assert AbstractifyCPacketSeq(sp) == [LPacket(gs.next, gs.id, gp.msg.(round := 2))];
                            assert ReceivePropagate(gs, AbstractifyCServerToServer(s'), gp, AbstractifyCPacketSeq(sp));
                    //     (t1, t2); 						
                    // (t1.1, t1.0); 	
                }			
            // (t1.1, t1.0) 
        }
        else 
        {
            // var t1 := 
                var new_icache := 
                    CAddMetaToICache(s.icache, p.msg.meta); 					
                // var t1 := 
                s' :=
                    s.(icache := new_icache); 					
                // var t2 := 
                var propagate :=
                    CPacket(s.next_endpoint, s.endpoint, p.msg); 
                lemma_AbstractifyEndpointToID(propagate.src, gs.id);
                lemma_AbstractifyEndpointToID(propagate.dst, gs.next);
                assert AbstractifyEndPointToID(propagate.src) == gs.id;
                assert AbstractifyEndPointToID(propagate.dst) == gs.next;	

                sp := [propagate];
                assert AbstractifyCPacketSeq(sp) == [LPacket(gs.next, gs.id, gp.msg)];
                assert ReceivePropagate(gs, AbstractifyCServerToServer(s'), gp, AbstractifyCPacketSeq(sp));
                assert ReceivePropagate(gs, AbstractifyCServerToServer(s'), gp, AbstractifyCPacketSeq(sp));
            //     (t1, t2); 				
            // (t1.1, t1.0); 
        }		
    // (t1.1, t1.0)
}

lemma {:axiom} lemma_CReceiveWrite(s: CServer, p: CPacket, s':CServer, sp:seq<CPacket>)
    requires CServerIsValid(s)
    requires CPacketIsValid(p)
    requires p.msg.CMessage_Write?
    requires CServerValid(s)
    requires CPacketValid(p)
    requires CServerIsValid(s') 
    requires (forall i :: 0 <= i < |sp| ==> CPacketIsValid(sp[i])) 
    ensures ReceiveWrite(AbstractifyCServerToServer(s), AbstractifyCServerToServer(s'), AbstractifyCPacketToPacket(p), AbstractifyCPacketSeq(sp))

method CReceiveWrite(s: CServer, p: CPacket) returns (s':CServer, sp:seq<CPacket>) 
    requires CServerIsValid(s)
    requires CPacketIsValid(p)
    requires p.msg.CMessage_Write?
    requires CServerValid(s)
    requires CPacketValid(p)
    ensures CServerIsValid(s') 
    ensures (forall i :: 0 <= i < |sp| ==> CPacketIsValid(sp[i])) 
    ensures ReceiveWrite(AbstractifyCServerToServer(s), AbstractifyCServerToServer(s'), AbstractifyCPacketToPacket(p), AbstractifyCPacketSeq(sp))
{
    // print "Process Write", p.msg.opn_write, "\n";
    // s' := s;
    // sp := [];
    ghost var gs := AbstractifyCServerToServer(s);
    ghost var gp := AbstractifyCPacketToPacket(p);
    // var t1 := 
        assert forall k :: k in p.msg.local ==> CMetaValid(p.msg.local[k]) && CMetaIsValid(p.msg.local[k]);
        var local_metas := 
            (set m | m in p.msg.local.Values); 	
        assert forall m :: m in local_metas ==> CMetaValid(m) && CMetaIsValid(m);
        ghost var glocal_metas := set m | m in gp.msg.local.Values;
        lemma_AbstractifyCMetaToMeta_Is_Injective(local_metas);
        // assume (set m | m in local_metas :: AbstractifyCMetaToMeta(m)) == glocal_metas;
        var vcs_local := set m | m in local_metas :: m.vc;
        assert forall vc :: vc in vcs_local ==> CVectorClockValid(vc);
        ghost var gvcs_local := set m | m in local_metas :: m.vc;
        // assume SetIsInjective(vcs_local, AbstractifyCVectorClockToVectorClock);
        // assume (set vc | vc in vcs_local :: AbstractifyCVectorClockToVectorClock(vc)) == gvcs_local;
        var vcs_deps := set k | k in p.msg.deps_write :: p.msg.deps_write[k];	
        ghost var gvcs_deps := set k | k in gp.msg.deps_write :: gp.msg.deps_write[k];
        // assume (set vc | vc in vcs_deps :: AbstractifyCVectorClockToVectorClock(vc)) == gvcs_deps;
        // // var t1 := 
            var merged_vc := 
                CFoldVC(s.gvc, vcs_local); 			
            // ghost var gmerged_vc := FoldVC(gs.gvc, gvcs_local);
            // var t1 := 
                var merged_vc2 := 
                    CFoldVC(merged_vc, vcs_deps); 					
                // var t1 := 
                    var new_vc := 
                        CAdvanceVC(merged_vc2, s.id); 						
                    // var t1 := 
                        var merged_deps := 
                            CFoldDependencyFromMetaSet(p.msg.deps_write, local_metas); 							
        //                 // var t1 := 
                            var meta := 
                                CMeta(p.msg.key_write, new_vc, merged_deps); 								
        //                     // var t1 := 
                                // var new_local_metas := 
                                //     local_metas + {meta}; 	
                                assert CMetaIsValid(meta) && CMetaValid(meta);	
                                assert forall m :: m in local_metas ==> CMetaIsValid(m) && CMetaValid(m);	
                                lemma_AddNewMeta(local_metas, meta);	
        //                         // var t1 := 
                                // assert CICacheIsValid(s.icache) && CICacheIsValid(s.icache);
                                // assert forall m :: m in new_local_metas ==> CMetaIsValid(m) && CMetaValid(m);//(forall k :: k in m.deps ==> k in c);
                                    var new_icache := 
                                        // CAddMetasToICache(s.icache, new_local_metas); 
                                        CAddMetaToICache(s.icache, meta);										
        //                             // var t1 := 
                                        var wreply := 
                                            CPacket(p.src, s.endpoint, CMessage_Write_Reply(p.msg.opn_write, p.msg.key_write, new_vc)); 
                                        assert CPacketIsValid(wreply);	
                                        lemma_AbstractifyEndpointToID(wreply.src, gs.id);
                                        lemma_AbstractifyEndpointToID(wreply.dst, gp.src);
                                        assert AbstractifyEndPointToID(wreply.src) == gs.id;
                                        assert AbstractifyEndPointToID(wreply.dst) == gp.src;
                                        assert AbstractifyCPacketToPacket(wreply) == LPacket(gp.src, gs.id, Message_Write_Reply(gp.msg.opn_write, gp.msg.key_write, AbstractifyCVectorClockToVectorClock(new_vc)));					
        //                                 // var t1 := 
                                            var propagate := 
                                                CPacket(s.next_endpoint, s.endpoint, CMessage_Propagation(p.msg.key_write, meta, s.id, 1)); 
                                            assert CPacketIsValid(propagate);		
                                            lemma_AbstractifyEndpointToID(propagate.src, gs.id);
                                            lemma_AbstractifyEndpointToID(propagate.dst, gs.next);	
                                            assert AbstractifyEndPointToID(propagate.src) == gs.id;
                                            assert AbstractifyEndPointToID(propagate.dst) == gs.next;
                                            assert AbstractifyCPacketToPacket(propagate) == LPacket(gs.next, gs.id, Message_Propagation(gp.msg.key_write, AbstractifyCMetaToMeta(meta), gs.id, 1));									
        //                                     // var t1 := 
                                            s' :=
                                                s.(gvc := new_vc, icache := new_icache); 		
                                            ghost var gs' := AbstractifyCServerToServer(s');
                                            assert gs' == gs.(gvc := AbstractifyCVectorClockToVectorClock(new_vc), icache := AbstractifyCICacheToICache(new_icache));							
        //                                     // var t2 := 
                                            sp :=
                                                [wreply] + [propagate]; 
                                            lemma_PacketSeqIsValid(wreply, propagate, LPacket(gp.src, gs.id, Message_Write_Reply(gp.msg.opn_write, gp.msg.key_write, AbstractifyCVectorClockToVectorClock(new_vc))), LPacket(gs.next, gs.id, Message_Propagation(gp.msg.key_write, AbstractifyCMetaToMeta(meta), gs.id, 1)));
                                            assert forall i :: 0 <= i < |sp| ==> CPacketIsValid(sp[i]);
                                            assert AbstractifyCPacketSeq(sp) == 
                                                [LPacket(gp.src, gs.id, Message_Write_Reply(gp.msg.opn_write, gp.msg.key_write, AbstractifyCVectorClockToVectorClock(new_vc)))] + 
                                                [LPacket(gs.next, gs.id, Message_Propagation(gp.msg.key_write, AbstractifyCMetaToMeta(meta), gs.id, 1))];
                                            lemma_CReceiveWrite(s, p, s', sp);
                                            // assert ReceiveWrite(AbstractifyCServerToServer(s), AbstractifyCServerToServer(s'), AbstractifyCPacketToPacket(p), AbstractifyCPacketSeq(sp));


                                            // assert forall p :: p in sp ==> CPacketIsAbstractable(p);
                                            // assert forall p :: p in sp ==> EndPointIsValid(p.src) && EndPointIsValid(p.dst);										
    //                                         (t1, t2); 											
    //                                     (t1.1, t1.0); 										
    //                                 (t1.1, t1.0); 									
    //                             (t1.1, t1.0); 								
    //                         (t1.1, t1.0); 							
    //                     (t1.1, t1.0); 						
    //                 (t1.1, t1.0); 					
    //             (t1.1, t1.0); 				
    //         (t1.1, t1.0); 			
    //     (t1.1, t1.0); 		
    // (t1.1, t1.0)
    // print "Write end", p.msg.opn_write, "\n";
}

lemma lemma_VCTransitive(m:CMessage, vc:CVectorClock)
    requires m.CMessage_Write?
    requires CMessageValid(m)
    requires CVectorClockValid(vc)
    requires CVCEq(m.mvc, vc) || CVCHappendsBefore(m.mvc, vc)
    ensures (forall k :: k in m.deps_write ==> CVCEq(m.deps_write[k], vc) || CVCHappendsBefore(m.deps_write[k], vc))
    ensures (forall k :: k in m.local ==> CVCEq(m.local[k].vc, vc) || CVCHappendsBefore(m.local[k].vc, vc))
{

}

method CReceiveWrite_I1(s: CServer, p: CPacket) returns (s':CServer, sp:seq<CPacket>) 
    requires CServerIsValid(s)
    requires CPacketIsValid(p)
    requires p.msg.CMessage_Write?
    requires CServerValid(s)
    requires CPacketValid(p)
    ensures CServerIsValid(s') 
    ensures (forall i :: 0 <= i < |sp| ==> CPacketIsValid(sp[i])) 
    // ensures ReceiveWrite(AbstractifyCServerToServer(s), AbstractifyCServerToServer(s'), AbstractifyCPacketToPacket(p), AbstractifyCPacketSeq(sp))
{
    ghost var gs := AbstractifyCServerToServer(s);
    ghost var gp := AbstractifyCPacketToPacket(p);
    // var t1 := 
        assert forall k :: k in p.msg.local ==> CMetaValid(p.msg.local[k]) && CMetaIsValid(p.msg.local[k]);
        var vcs_deps := set k | k in p.msg.deps_write :: p.msg.deps_write[k];	
        // ghost var gvcs_deps := set k | k in gp.msg.deps_write :: gp.msg.deps_write[k];
        
        assert (forall k :: k in p.msg.deps_write ==> CVCEq(p.msg.deps_write[k], p.msg.mvc) || CVCHappendsBefore(p.msg.deps_write[k], p.msg.mvc));
        assert (forall k :: k in p.msg.local ==> CVCEq(p.msg.local[k].vc, p.msg.mvc) || CVCHappendsBefore(p.msg.local[k].vc, p.msg.mvc));
            var merged_vc := 
                CVCMerge(s.gvc, p.msg.mvc); 			
            assert CVCEq(p.msg.mvc, merged_vc) || CVCHappendsBefore(p.msg.mvc, merged_vc);
            lemma_VCTransitive(p.msg, merged_vc);
            assert (forall k :: k in p.msg.deps_write ==> CVCEq(p.msg.deps_write[k], merged_vc) || CVCHappendsBefore(p.msg.deps_write[k], merged_vc));
            assert (forall k :: k in p.msg.local ==> CVCEq(p.msg.local[k].vc, merged_vc) || CVCHappendsBefore(p.msg.local[k].vc, merged_vc));
                    var new_vc := 
                        CAdvanceVC(merged_vc, s.id); 						
                    // var t1 := 
                        // ghost var local_metas := 
                        //     (set m | m in p.msg.local.Values); 	
                        // ghost var merged_deps := 
                        //     CFoldDependencyFromMetaSet(p.msg.deps_write, local_metas); 							
        //                 // var t1 := 
                            var meta := 
                                // CMeta(p.msg.key_write, new_vc, merged_deps); 	
                                CMeta(p.msg.key_write, new_vc, p.msg.deps_write);		
                            assert forall k :: k in p.msg.local ==> k in p.msg.deps_write && (CVCEq(p.msg.local[k].vc, p.msg.deps_write[k]) || CVCHappendsBefore(p.msg.local[k].vc, p.msg.deps_write[k]));				
        //                     // var t1 := 
                                // var new_local_metas := 
                                //     local_metas + {meta}; 	
                                assert CMetaIsValid(meta) && CMetaValid(meta);	
                                // assert forall m :: m in local_metas ==> CMetaIsValid(m) && CMetaValid(m);	
                                // lemma_AddNewMeta(local_metas, meta);	
        //                         // var t1 := 
                                // assert CICacheIsValid(s.icache) && CICacheIsValid(s.icache);
                                // assert forall m :: m in new_local_metas ==> CMetaIsValid(m) && CMetaValid(m);//(forall k :: k in m.deps ==> k in c);
                                    var new_icache := 
                                        CAddMetaToICache(s.icache, meta); 										
        //                             // var t1 := 
                                        var wreply := 
                                            CPacket(p.src, s.endpoint, CMessage_Write_Reply(p.msg.opn_write, p.msg.key_write, new_vc)); 
                                        assert CPacketIsValid(wreply);	
                                        lemma_AbstractifyEndpointToID(wreply.src, gs.id);
                                        lemma_AbstractifyEndpointToID(wreply.dst, gp.src);
                                        assert AbstractifyEndPointToID(wreply.src) == gs.id;
                                        assert AbstractifyEndPointToID(wreply.dst) == gp.src;
                                        assert AbstractifyCPacketToPacket(wreply) == LPacket(gp.src, gs.id, Message_Write_Reply(gp.msg.opn_write, gp.msg.key_write, AbstractifyCVectorClockToVectorClock(new_vc)));					
        //                                 // var t1 := 
                                            var propagate := 
                                                CPacket(s.next_endpoint, s.endpoint, CMessage_Propagation(p.msg.key_write, meta, s.id, 1)); 
                                            assert CPacketIsValid(propagate);		
                                            lemma_AbstractifyEndpointToID(propagate.src, gs.id);
                                            lemma_AbstractifyEndpointToID(propagate.dst, gs.next);	
                                            assert AbstractifyEndPointToID(propagate.src) == gs.id;
                                            assert AbstractifyEndPointToID(propagate.dst) == gs.next;
                                            assert AbstractifyCPacketToPacket(propagate) == LPacket(gs.next, gs.id, Message_Propagation(gp.msg.key_write, AbstractifyCMetaToMeta(meta), gs.id, 1));									
        //                                     // var t1 := 
                                            s' :=
                                                s.(gvc := new_vc, icache := new_icache); 		
                                            ghost var gs' := AbstractifyCServerToServer(s');
                                            // assert gs' == gs.(gvc := AbstractifyCVectorClockToVectorClock(new_vc), icache := AbstractifyCICacheToICache(new_icache));							
        //                                     // var t2 := 
                                            sp :=
                                                [wreply] + [propagate]; 
                                            lemma_PacketSeqIsValid(wreply, propagate, LPacket(gp.src, gs.id, Message_Write_Reply(gp.msg.opn_write, gp.msg.key_write, AbstractifyCVectorClockToVectorClock(new_vc))), LPacket(gs.next, gs.id, Message_Propagation(gp.msg.key_write, AbstractifyCMetaToMeta(meta), gs.id, 1)));
                                            assert forall i :: 0 <= i < |sp| ==> CPacketIsValid(sp[i]);
                                            assert AbstractifyCPacketSeq(sp) == 
                                                [LPacket(gp.src, gs.id, Message_Write_Reply(gp.msg.opn_write, gp.msg.key_write, AbstractifyCVectorClockToVectorClock(new_vc)))] + 
                                                [LPacket(gs.next, gs.id, Message_Propagation(gp.msg.key_write, AbstractifyCMetaToMeta(meta), gs.id, 1))];
                                            // lemma_CReceiveWrite(s, p, s', sp);
                                            // assert ReceiveWrite(AbstractifyCServerToServer(s), AbstractifyCServerToServer(s'), AbstractifyCPacketToPacket(p), AbstractifyCPacketSeq(sp));


                                            // assert forall p :: p in sp ==> CPacketIsAbstractable(p);
                                            // assert forall p :: p in sp ==> EndPointIsValid(p.src) && EndPointIsValid(p.dst);										
    //                                         (t1, t2); 											
    //                                     (t1.1, t1.0); 										
    //                                 (t1.1, t1.0); 									
    //                             (t1.1, t1.0); 								
    //                         (t1.1, t1.0); 							
    //                     (t1.1, t1.0); 						
    //                 (t1.1, t1.0); 					
    //             (t1.1, t1.0); 				
    //         (t1.1, t1.0); 			
    //     (t1.1, t1.0); 		
    // (t1.1, t1.0)
    // print "Write end", p.msg.opn_write, "\n";
}

lemma lemma_PacketSeqIsValid(p1:CPacket, p2:CPacket, lp1:Packet, lp2:Packet)
    requires CPacketIsValid(p1)
    requires CPacketIsValid(p2)
    requires AbstractifyCPacketToPacket(p1) == lp1
    requires AbstractifyCPacketToPacket(p2) == lp2
    ensures var sp := [p1] + [p2]; forall i :: 0 <= i < |sp| ==> CPacketIsValid(sp[i])
    ensures var sp := [p1] + [p2]; AbstractifyCPacketSeq(sp) == [lp1] + [lp2]
{

}

lemma lemma_AddNewMeta(s:set<CMeta>, m:CMeta)
    requires CMetaValid(m) && CMetaIsValid(m)
    requires forall m :: m in s ==> CMetaValid(m) && CMetaIsValid(m)
    ensures forall x :: x in s + {m} ==> CMetaValid(x) && CMetaIsValid(x)
{
    forall x | x in s + {m}
        ensures CMetaValid(x) && CMetaIsValid(x)
    {
        if x in s {
        } else {
        }
    }
    assert forall x :: x in s + {m} ==> CMetaValid(x) && CMetaIsValid(x);
}


function method CCircle(id: int, nodes: int) : int 
    requires 0 <= id && id < nodes
    ensures var i := CCircle(id, nodes); 0 <= i && i < nodes
    ensures var lr := Circle(id, nodes); var cr := CCircle(id, nodes); (cr) == (lr)
{
    if nodes == 1 then 
        id 
    else 
        if id == nodes - 1 then 
            0 
        else 
            id + 1
}

function method CInsertIntoCCache(c: CCCache, m: CMeta) : CCCache 
    requires CCCacheIsValid(c)
    requires CMetaIsValid(m)
    requires CCCacheValid(c)
    requires CMetaValid(m)
    ensures var lr := InsertIntoCCache(AbstractifyCCCacheToCCache(c), AbstractifyCMetaToMeta(m)); var cr := CInsertIntoCCache(c, m); CCCacheIsValid(cr) && (AbstractifyCCCacheToCCache(cr)) == (lr)
{
    if m.key in c then 
        c[m.key := CMetaMerge(c[m.key], m)] 
    else 
        c[m.key := m]
}

method CAddMetasToICache(c: CICache, metas: set<CMeta>) returns (res:CICache)
    requires CICacheIsValid(c)
    requires (forall i :: i in metas ==> CMetaIsValid(i))
    requires CICacheValid(c)
    requires (forall m :: m in metas ==> CMetaValid(m) && (forall k :: k in m.deps ==> k in c))
    decreases |metas|
    ensures CICacheValid(res)
    ensures CICacheIsValid(res)
    ensures SetIsInjective(metas, AbstractifyCMetaToMeta)
    ensures 
        var lr := AddMetasToICache(AbstractifyCICacheToICache(c), AbstractifySet(metas, AbstractifyCMetaToMeta)); 
        // CICacheIsValid(res) && CICacheValid(res)
        (AbstractifyCICacheToICache(res)) == (lr)
{
    if |metas| == 0 { 
        res := c;
        assert AbstractifyCICacheToICache(res) == AddMetasToICache(AbstractifyCICacheToICache(c), AbstractifySet(metas, AbstractifyCMetaToMeta));
    } 
    else 
    {
        var m :| m in metas;
        var new_metas := 
            metas - {m}; 			
        res := CAddMetasToICache(CAddMetaToICache(c, m), new_metas);

        ghost var gacc := AbstractifyCICacheToICache(c);
        lemma_AbstractifyCMetaToMeta_Is_Injective(metas);
        ghost var gmetas := AbstractifySet(metas, AbstractifyCMetaToMeta);
        ghost var gnmetas := AbstractifySet(metas - {m}, AbstractifyCMetaToMeta);
        ghost var gx := AbstractifyCMetaToMeta(m);
        assert gnmetas == gmetas - {gx};
        lemma_CAddMetasToICache(gacc, gmetas, gx);
        assert AddMetasToICache(gacc, gmetas) == AddMetasToICache(AddMetaToICache(gacc, gx), gmetas-{gx});
        assert AbstractifyCICacheToICache(res) == AddMetasToICache(gacc, gmetas);

        // lemma_AbstractifyCMetaToMeta_Is_Injective(metas);
        // lemma_CAddMetasToICache(c, metas, res);        
        // ghost var gmetas := AbstractifySet(metas, AbstractifyCMetaToMeta);
        // assert AbstractifyCICacheToICache(res) == AddMetasToICache(AbstractifyCICacheToICache(c), AbstractifySet(metas, AbstractifyCMetaToMeta));
    }
}

lemma {:axiom} lemma_CAddMetasToICache(c: ICache, metas: set<Meta>, x:Meta)
    requires ICacheValid(c)
    requires (forall i :: i in metas ==> MetaValid(i) && forall k :: k in i.deps ==> k in c)
    requires MetaValid(x) && forall k :: k in x.deps ==> k in c
    ensures AddMetasToICache(c, metas) == AddMetasToICache(AddMetaToICache(c, x), metas-{x})

// lemma {:axiom} lemma_CAddMetasToICache(c: CICache, metas: set<CMeta>, res:CICache)
//     requires CICacheIsValid(c)
//     requires (forall i :: i in metas ==> CMetaIsValid(i))
//     requires CICacheValid(c)
//     requires (forall m :: m in metas ==> CMetaValid(m) && (forall k :: k in m.deps ==> k in c))
//     requires CICacheIsValid(c)
//     ensures AbstractifyCICacheToICache(res) == AddMetasToICache(AbstractifyCICacheToICache(c), AbstractifySet(metas, AbstractifyCMetaToMeta))

function method CAddMetaToICache(c: CICache, m: CMeta) : CICache 
    requires CICacheIsValid(c)
    requires CMetaIsValid(m)
    requires CICacheValid(c)
    requires CMetaValid(m)
    requires (forall k :: k in m.deps ==> k in c)
    ensures 
        var lr := AddMetaToICache(AbstractifyCICacheToICache(c), AbstractifyCMetaToMeta(m)); 
        var cr := CAddMetaToICache(c, m); 
        CICacheIsValid(cr) 
        && (AbstractifyCICacheToICache(cr)) == (lr)
{
    ghost var gm := AbstractifyCMetaToMeta(m);
    ghost var gc := AbstractifyCICacheToICache(c);
    assert m.key == gm.key;
    if m.key in c then 
        assert gm.key in gc;
        var r := c[m.key := c[m.key] + {m}];
        ghost var ms := {m};
        ghost var gms := {gm};
        assert (set i | i in ms :: AbstractifyCMetaToMeta(i)) == gms;
        ghost var ms2 := c[m.key] + {m};
        ghost var gms2 := gc[gm.key] + {gm};
        assert (set i | i in ms2 :: AbstractifyCMetaToMeta(i)) == gms2;
        lemma_CAddMetaToICache(c, m, r);
        // assert AbstractifyCICacheToICache(r) == gc[gm.key := gc[gm.key] + {gm}];
        r 
    else 
        var r := c[m.key := {m}];
        ghost var ms := {m};
        ghost var gms := {gm};
        assert (set i | i in ms :: AbstractifyCMetaToMeta(i)) == gms;
        lemma_CAddMetaToICache(c, m, r);
        // assert AbstractifyCICacheToICache(r) == gc[gm.key := {gm}];
        r
}

/** we dont need this one, but somehow, it can be verified on local environemnt, but not on servers */
lemma {:axiom} lemma_CAddMetaToICache(c: CICache, m: CMeta, res:CICache)
    requires CICacheIsValid(c)
    requires CMetaIsValid(m)
    requires CICacheValid(c)
    requires CMetaValid(m)
    requires (forall k :: k in m.deps ==> k in c)
    requires CICacheIsValid(res)
    ensures  AbstractifyCICacheToICache(res) == AddMetaToICache(AbstractifyCICacheToICache(c), AbstractifyCMetaToMeta(m))

method CPullDeps3(icache: CICache, ccache: CCCache, deps: CDependency) returns (icache':CICache, ccache':CCCache) 
    requires CICacheIsValid(icache)
    requires CCCacheIsValid(ccache)
    requires CDependencyIsValid(deps)
    requires CICacheValid(icache)
    requires CCCacheValid(ccache)
    requires (forall k :: k in Keys_domain ==> k in icache && k in ccache)
    requires (forall k :: k in ccache ==> k in icache)
    requires CDependencyValid(deps)
    ensures CICacheValid(icache') 
    ensures 
        var (lr0, lr1) := PullDeps3(AbstractifyCICacheToICache(icache), AbstractifyCCCacheToCCache(ccache), AbstractifyCDependencyToDependency(deps)); 
        CICacheIsValid(icache') && CCCacheIsValid(ccache') 
        && (AbstractifyCICacheToICache(icache'), AbstractifyCCCacheToCCache(ccache')) == (lr0, lr1)
    ensures (forall k :: k in deps ==> k in ccache' && (CVCEq(deps[k], ccache'[k].vc) || CVCHappendsBefore(deps[k], ccache'[k].vc)))
    ensures (forall k :: k in ccache ==> k in ccache' && (CVCEq(ccache[k].vc, ccache'[k].vc) || CVCHappendsBefore(ccache[k].vc, ccache'[k].vc)))
{
    ghost var gicache := AbstractifyCICacheToICache(icache);
    ghost var gccache := AbstractifyCCCacheToCCache(ccache);
    ghost var gdeps := AbstractifyCDependencyToDependency(deps);
    ghost var (gicache', gccache') := PullDeps3(gicache, gccache, gdeps);
    ghost var domain := 
        icache.Keys + deps.Keys; 	
    ghost var gdomain := gicache.Keys + gdeps.Keys;
    assert gdomain == domain;
    // assert forall k :: k in icache ==> k in Keys_domain;// && (forall m :: m in icache[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain));
    var new_icache, todos := 
        CGetMetasOfAllDeps3(icache, deps, map[], domain);

    
    ghost var gtodos := GetMetasOfAllDeps(gicache, gdeps, map[], gdomain);
    lemma_CGetMetasOfAllDeps(icache, deps, map[], domain, todos);
    assert (forall k :: k in deps ==> k in todos && CVCEq(deps[k], todos[k]));

    assert AbstractifyMap(todos, AbstractifyCKeyToKey, AbstractifyCVectorClockToVectorClock, AbstractifyCKeyToKey) == gtodos;
    var new_cache := 
        CMergeVCIntoCCache(ccache, todos); 
    lemma_CMergeVCIntoCCache(ccache, todos);
    
    assert (forall k :: k in todos ==> k in new_cache && (CVCEq(todos[k], new_cache[k].vc) || CVCHappendsBefore(todos[k], new_cache[k].vc)));
    assert (forall k :: k in deps ==> k in new_cache && (CVCEq(deps[k], new_cache[k].vc) || CVCHappendsBefore(deps[k], new_cache[k].vc)));
    assert (forall k :: k in ccache ==> k in new_cache && (CVCEq(ccache[k].vc, new_cache[k].vc) || CVCHappendsBefore(ccache[k].vc, new_cache[k].vc)));

    gccache' := MergeVCIntoCCache(gccache, gtodos);
    assert CCCacheValid(new_cache);	
    icache' := new_icache;
    ccache' := new_cache;
    assert CCCacheValid(ccache');
    assert CICacheIsValid(icache');
    assert CCCacheIsValid(ccache');
    lemma_CPullDeps3(icache,new_icache,ccache', gccache');
    assert AbstractifyCICacheToICache(icache') == gicache';
    assert AbstractifyCCCacheToCCache(ccache') == gccache';
}

lemma {:axiom} lemma_CPullDeps3(icache:CICache, icache':CICache, ccache:CCCache, ccache':CCache)
    ensures icache == icache'
    ensures AbstractifyCCCacheToCCache(ccache) == ccache'

lemma {:axiom} lemma_CGetMetasOfAllDeps(icache: CICache, deps: CDependency, todos: map<CKey, CVectorClock>, domain: set<CKey>, res:map<CKey, CVectorClock>)
    requires CICacheIsValid(icache)
    requires CDependencyIsValid(deps)
    requires (forall i :: i in todos ==> /*CKeyIsValid(i) &&*/ CVectorClockIsValid(todos[i]))
    requires (forall k :: k in icache ==> k in Keys_domain && (forall m :: m in icache[k] ==> CMetaValid(m) && m.key == k && (forall kk :: kk in m.deps ==> kk in domain && kk in Keys_domain)))
    requires CDependencyValid(deps)
    requires (forall k :: k in todos ==> CVectorClockValid(todos[k]) && k in Keys_domain)
    requires (forall k :: k in Keys_domain ==> k in icache)
    requires (forall k :: k in deps ==> k in domain)
    requires (forall k :: k in res ==> k in Keys_domain && CVectorClockValid(res[k]))// && res[k].key == k)
    requires (forall i :: i in res ==> /*CKeyIsValid(i) &&*/ CVectorClockIsValid(res[i]))
    ensures CICacheValid(icache)
    ensures  (forall k :: k in deps ==> k in todos && CVCEq(deps[k], todos[k]))
    ensures AbstractifyMap(res, AbstractifyCKeyToKey, AbstractifyCVectorClockToVectorClock, AbstractifyCKeyToKey) == GetMetasOfAllDeps(AbstractifyCICacheToICache(icache), AbstractifyCDependencyToDependency(deps), map[], AbstractifyCICacheToICache(icache).Keys + AbstractifyCDependencyToDependency(deps).Keys)

function method CAdvanceVC(vc: CVectorClock, i: int) : CVectorClock 
    requires CVectorClockIsValid(vc)
    requires CVectorClockValid(vc)
    requires 0 <= i && i < Nodes
    ensures var res := CAdvanceVC(vc, i); CVectorClockValid(res)
    ensures var lr := AdvanceVC(AbstractifyCVectorClockToVectorClock(vc), i); var cr := CAdvanceVC(vc, i); CVectorClockIsValid(cr) && (AbstractifyCVectorClockToVectorClock(cr)) == (lr)
{
    vc[i := vc[i] + 1]
}

datatype CServer = 
	CServer(
		id: int, 
        endpoint: EndPoint,
		gvc: CVectorClock, 
		next: int, 
        next_endpoint: EndPoint,
		icache: CICache, 
		ccache: CCCache
	)

predicate CServerIsValid(s: CServer) 
{
    CServerIsAbstractable(s) 
    && 
    CVectorClockIsValid(s.gvc) 
    && 
    CICacheIsValid(s.icache) 
    && 
    CCCacheIsValid(s.ccache)
    && 
    EndPointIsValid(s.endpoint)
    && 
    EndPointIsValid(s.next_endpoint)
}

predicate CServerIsAbstractable(s: CServer) 
{
    CVectorClockIsAbstractable(s.gvc) 
    // && 
    // CICacheIsAbstractable(s.icache) 
    && 
    CCCacheIsAbstractable(s.ccache)
}

function AbstractifyCServerToServer(s: CServer) : Server 
    // requires CServerIsAbstractable(s)
{
    Server(s.id, AbstractifyCVectorClockToVectorClock(s.gvc), s.next, AbstractifyCICacheToICache(s.icache), AbstractifyCCCacheToCCache(s.ccache))
}

function CServerValid(s: CServer) : bool 
    requires CServerIsValid(s)
    ensures var lr := ServerValid(AbstractifyCServerToServer(s)); 
    var cr := CServerValid(s); 
    (cr) == (lr)
{
    0 <= s.id && s.id < Nodes 
    && 
    0 <= s.next && s.next < Nodes 
    && 
    s.next == CCircle(s.id, Nodes) 
    && 
    CVectorClockValid(s.gvc) 
    && 
    CICacheValid(s.icache) 
    && 
    CCCacheValid(s.ccache) 
    && 
    (forall k :: k in Keys_domain ==> k in s.icache && k in s.ccache) 
    && 
    (forall k :: k in s.ccache ==> k in s.icache)
}

function method CInitICache() : CICache 
    ensures var lr := InitICache(); var cr := CInitICache(); CICacheIsValid(cr) 
        && (AbstractifyCICacheToICache(cr)) == (lr)
{    
    // var r := (map k | k in Keys_domain :: {});
    // assert forall k :: k in r ==> (set i | i in r[k] :: AbstractifyCMetaToMeta(i)) == {};
    // r
    map[]
}

function method CInitCCache() : CCCache 
    ensures var lr := InitCCache(); var cr := CInitCCache(); CCCacheIsValid(cr) && (AbstractifyCCCacheToCCache(cr)) == (lr)
{
    // (map k | k in Keys_domain :: CEmptyMeta(k))
    map[]
}


function method CServerInit(id: int, endpoints:seq<EndPoint>) : CServer 
    requires 0 <= id && id < Nodes
    requires |endpoints| == Nodes
    requires forall e :: e in endpoints ==> EndPointIsValid(e)
    ensures var s := CServerInit(id, endpoints); CServerIsValid(s) && ServerInit(AbstractifyCServerToServer(s), id)
{
    var t1 := 
        id; 		
    var t2 := 
        CCircle(id, Nodes); 		
    var t3 :=
        CEmptyVC(); 		
    var t4 := 
        CInitICache(); 		
    var t5 := 
        CInitCCache(); 	
    var end := 
        endpoints[id];	
    var next_end := endpoints[t2];
    CServer(t1, end, t3, t2, next_end, t4, t5)
}

// method CServerInit(id: int, endpoints:seq<EndPoint>) returns (s:CServer)
//     requires 0 <= id && id < Nodes
//     requires |endpoints| == Nodes
//     requires forall e :: e in endpoints ==> EndPointIsValid(e)
//     ensures CServerIsValid(s) && ServerInit(AbstractifyCServerToServer(s), id)
//     ensures s.endpoint == endpoints[id]
//     ensures s.next_endpoint == endpoints[s.next]
// {
//     print "init server\n";
//     var t1 := 
//         id; 		
//     var t2 := 
//         CCircle(id, Nodes); 		
//     var t3 :=
//         CEmptyVC(); 		
//     var t4 := 
//         CInitICache(); 		
//     var t5 := 
//         CInitCCache(); 	
//     var end := 
//         endpoints[id];	
//     var next_end := endpoints[t2];
//     s := CServer(t1, end, t3, t2, next_end, t4, t5);
//     print "init server finish\n";
// }



lemma {:axiom} lemma_AbstractifyEndpointToID(e:EndPoint, id:int)
    ensures AbstractifyEndPointToID(e) == id



}
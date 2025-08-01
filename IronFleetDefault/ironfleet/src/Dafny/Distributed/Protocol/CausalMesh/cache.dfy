include "../../Common/Collections/Maps.i.dfy"
include "types.dfy"
include "message.dfy"
include "properties.dfy"
include "pulldeps.dfy"

module CausalMesh_Cache_i {
    import opened Collections__Maps_i
    import opened CausalMesh_Types_i
    import opened CausalMesh_Message_i
    import opened CausalMesh_Properties_i
    import opened CausalMesh_PullDeps_i
    import opened Environment_s

    function Circle(id:int, nodes:int) : (i:int)
        requires 0 <= id < nodes
        ensures 0 <= i < nodes
    {
        if nodes == 1 then 
            id
        else if id == nodes - 1 then
            0
        else
            id + 1
    }

    function InsertIntoCCache(c:CCache, m:Meta) : CCache
        requires CCacheValid(c)
        requires MetaValid(m)
        // ensures CCacheValid(res)
        // ensures m.key in res
        // ensures VCHappendsBefore(m.vc, res[m.key].vc) || VCEq(m.vc, res[m.key].vc)
        // // ensures forall k :: k in c && k != m.key ==> k in res && VCEq(c[k].vc, res[k].vc)
        // ensures forall k :: k in res && k != m.key ==> k in c && VCEq(c[k].vc, res[k].vc)
        // ensures if m.key in c then  res[m.key].vc == VCMerge(m.vc, c[m.key].vc)  else res[m.key].vc == m.vc
    {
        if m.key in c then
            c[m.key := MetaMerge(c[m.key], m)]
        else 
            c[m.key := m]
    }

    function AddMetaToICache(c:ICache, m:Meta) : ICache
        requires ICacheValid(c)
        requires MetaValid(m)
        requires forall k :: k in m.deps ==> k in c
        // ensures m.key in res
        // ensures m in res[m.key]
        // ensures forall k :: k in c ==> k in res && forall m :: m in c[k] ==> m in res[k]
        // ensures ICacheValid(res)
    {
        if m.key in c then
            c[m.key := c[m.key] + {m}]
        else
            c[m.key := {m}]
    }

    function AddMetasToICache(c:ICache, metas:set<Meta>) : ICache
        requires ICacheValid(c)
        requires forall m :: m in metas ==> MetaValid(m) && forall k :: k in m.deps ==> k in c
        // ensures ICacheValid(res)
        // // ensures forall m :: m in metas ==> m.key in res && m in res[m.key]
        decreases |metas|
    {
        if |metas| == 0 then 
            c
        else 
            var m :| m in metas;
            var new_metas := metas - {m};
            AddMetasToICache(AddMetaToICache(c, m), new_metas)
    }

    // function PullDeps4(icache:ICache, ccache:CCache, deps:Dependency) : (c:(ICache, CCache))
    //     requires ICacheValid(icache)
    //     requires CCacheValid(ccache)
    //     // requires CausalCut(ccache)
    //     // requires VectorClockValid(vc)
    //     // requires forall k :: k in ccache ==> VCHappendsBefore(ccache[k].vc, vc) || VCEq(ccache[k].vc, vc)
    //     requires forall k :: k in Keys_domain ==> k in icache && k in ccache
    //     requires forall k :: k in ccache ==> k in icache
    //     requires DependencyValid(deps)
    //     requires forall k :: k in deps ==> k in icache 
    //     ensures ICacheValid(c.0)
    //     ensures CCacheValid(c.1)
    //     // ensures forall k :: k in deps ==> k in c.0 && k in c.1
    //     ensures forall k :: k in icache ==> k in c.0
    //     ensures forall k :: k in ccache ==> k in c.1
    //     // ensures forall k :: k in c.1 ==> VCHappendsBefore(c.1[k].vc, vc) || VCEq(c.1[k].vc, vc)
    //     // ensures CausalCut(c.1)
    // {
    //     var domain := icache.Keys + deps.Keys;
    //     var todos := GetMetasOfAllDeps2(icache, deps, map[], domain);

    //     var new_cache := MergeCCache(ccache, todos);
    //     (icache, new_cache)
    // }

    function PullDeps3(icache:ICache, ccache:CCache, deps:Dependency) : (c:(ICache, CCache))
        requires ICacheValid(icache)
        requires CCacheValid(ccache)
        // requires CausalCut(ccache)
        // requires VectorClockValid(vc)
        // requires forall k :: k in ccache ==> VCHappendsBefore(ccache[k].vc, vc) || VCEq(ccache[k].vc, vc)
        requires forall k :: k in Keys_domain ==> k in icache && k in ccache
        requires forall k :: k in ccache ==> k in icache
        requires DependencyValid(deps)
        requires forall k :: k in deps ==> k in icache 
        ensures ICacheValid(c.0)
        ensures CCacheValid(c.1)
        // ensures forall k :: k in deps ==> k in c.0 && k in c.1
        ensures forall k :: k in icache ==> k in c.0
        ensures forall k :: k in ccache ==> k in c.1
        // ensures forall k :: k in c.1 ==> VCHappendsBefore(c.1[k].vc, vc) || VCEq(c.1[k].vc, vc)
        // ensures CausalCut(c.1)
    {
        var domain := icache.Keys + deps.Keys;
        var todos := GetMetasOfAllDeps(icache, deps, map[], domain);

        var new_cache := MergeVCIntoCCache(ccache, todos);
        (icache, new_cache)
    }


    // function FoldMetaIntoICache(icache: ICache, metas: set<Meta>): ICache
    //     requires ICacheValid(icache)
    //     requires forall m :: m in metas ==> MetaValid(m) && (forall kk :: kk in m.deps ==> kk in Keys_domain && kk in icache)
    //     decreases |metas|
    // {
    //     if metas == {} then 
    //         icache
    //     else 
    //         var m: Meta :| m in metas;
    //         FoldMetaIntoICache(AddMetaToICache(icache, m), metas - {m})
    // }


    function AdvanceVC(vc:VectorClock, i:int) : (res:VectorClock)
        requires VectorClockValid(vc)
        requires 0 <= i < Nodes 
        ensures VectorClockValid(res)
    {
        vc[i:=vc[i]+1]
    }

    /** Actions */
    datatype Server = Server(
        id : int,
        gvc : VectorClock,
        next : int,
        icache : ICache,
        ccache : CCache
        // pvc : VectorClock
    )

    predicate ServerValid(s:Server)
    {
        && 0 <= s.id < Nodes
        && 0 <= s.next < Nodes
        && s.next == Circle(s.id, Nodes)
        && VectorClockValid(s.gvc)
        // && VectorClockValid(s.pvc)
        && ICacheValid(s.icache)
        && CCacheValid(s.ccache)
        // && CausalCut(s.ccache)
        // && (forall k :: k in s.ccache ==> VCHappendsBefore(s.ccache[k].vc, s.pvc) || VCEq(s.ccache[k].vc, s.pvc))
        && (forall k :: k in Keys_domain ==> k in s.icache && k in s.ccache)
        && (forall k :: k in s.ccache ==> k in s.icache)
    }

    function InitICache(): ICache
    {
        // map k | k in Keys_domain :: {}
        map[]
    }

    function InitCCache(): CCache
    {
        // map k | k in Keys_domain :: EmptyMeta(k)
        map[]
    }

    predicate ServerInit(s:Server, id:int)
        requires 0 <= id < Nodes
    {
        && s.id == id
        && s.next == Circle(id, Nodes)
        && s.gvc == EmptyVC()
        // && s.pvc == EmptyVC()
        && s.icache == InitICache()
        && s.ccache == InitCCache()
    }

    predicate ReceiveRead(s:Server, s':Server, p:Packet, sp:seq<Packet>)
        requires p.msg.Message_Read?
        requires ServerValid(s)
        requires PacketValid(p)
    {
        // var new_pvc := if (VCHappendsBefore(p.msg.pvc_read, s.pvc)) then s.pvc else VCMerge(s.pvc, p.msg.pvc_read);
        var (new_icache, new_ccache) := PullDeps3(s.icache, s.ccache, p.msg.deps_read);
        var new_ccache' := if p.msg.key_read !in new_ccache then
            new_ccache[p.msg.key_read := EmptyMeta(p.msg.key_read)]
        else 
            new_ccache;
        // assert forall k :: k in new_ccache ==> VCHappendsBefore(new_ccache[k].vc, new_pvc) || VCEq(new_ccache[k].vc, new_pvc);
        && s' == s.(icache := new_icache, ccache := new_ccache)
        && sp == [LPacket(p.src, s.id, 
                        Message_Read_Reply(
                            p.msg.opn_read,
                            p.msg.key_read,
                            new_ccache[p.msg.key_read].vc,
                            // new_ccache[p.msg.key_read].deps
                            map[]
                        )
                    )]
    }


    predicate ReceiveWrite(s: Server, s': Server, p: Packet, sp: seq<Packet>)
        requires p.msg.Message_Write?
        requires ServerValid(s)
        requires PacketValid(p)
    {
        assert forall k :: k in p.msg.local ==> MetaValid(p.msg.local[k]);
        var local_metas := set m | m in p.msg.local.Values;
        assert forall m :: m in local_metas ==> MetaValid(m);
        var vcs_local := set m | m in local_metas :: m.vc;
        assert forall vc :: vc in vcs_local ==> VectorClockValid(vc);
        var vcs_deps := set k | k in p.msg.deps_write :: p.msg.deps_write[k];

        var merged_vc := FoldVC(s.gvc, vcs_local);

        var merged_vc2 := FoldVC(merged_vc, vcs_deps);

        var new_vc := AdvanceVC(merged_vc2, s.id);

        var merged_deps := FoldDependencyFromMetaSet(p.msg.deps_write, local_metas);

        var meta := Meta(p.msg.key_write, new_vc, merged_deps);

        var new_local_metas := local_metas + {meta};

        var new_icache := AddMetasToICache(s.icache, new_local_metas);
        
        // var new_pvc := if (VCHappendsBefore(p.msg.pvc_write, s.pvc)) then s.pvc else VCMerge(s.pvc, p.msg.pvc_write);

        var wreply := LPacket(p.src, s.id, Message_Write_Reply(p.msg.opn_write, p.msg.key_write, new_vc));
        var propagate := LPacket(s.next, s.id, Message_Propagation(p.msg.key_write, meta, s.id, 1));

        
        && s' == s.(gvc := new_vc, icache := new_icache)
        && sp == [wreply] + [propagate]
    }

    predicate ReceivePropagate(s:Server, s':Server, p:Packet, sp:seq<Packet>)
        requires p.msg.Message_Propagation?
        requires ServerValid(s)
        requires PacketValid(p)
    {
        if s.next == p.msg.start then
            if p.msg.round == 2 then
                var vcs := p.msg.meta.vc;
                var new_gvc := VCMerge(s.gvc, vcs);
                var new_deps := p.msg.meta.deps;

                // var new_pvc := if (VCHappendsBefore(p.msg.meta.vc, s.pvc)) then s.pvc else VCMerge(s.pvc, p.msg.meta.vc);

                var (new_icache, new_ccache) := PullDeps3(s.icache, s.ccache, new_deps);

                var new_ccache' := InsertIntoCCache(new_ccache, p.msg.meta);
                var new_icache' := AddMetaToICache(new_icache, p.msg.meta);

                && s' == s.(gvc := new_gvc, icache := new_icache', ccache := new_ccache')
                && sp == []
            else
                var new_icache := AddMetaToICache(s.icache, p.msg.meta);
                && s' == s.(icache := new_icache)
                && sp == [LPacket(s.next, s.id, p.msg.(round := 2))]
        else 
            var new_icache := AddMetaToICache(s.icache, p.msg.meta);
            && s' == s.(icache := new_icache)
            && sp == [LPacket(s.next, s.id, p.msg)]
    }


    /** Client */
    datatype Client = Client(
        id : int,
        opn : int,
        local : map<Key, Meta>,
        deps : Dependency
        // ghost pvc : VectorClock
    )

    predicate ClientValid(c:Client)
    {
        && Nodes <= c.id < Nodes + Clients
        && (forall k :: k in c.local ==> k in Keys_domain && MetaValid(c.local[k]) && c.local[k].key == k)
        && DependencyValid(c.deps)
        // && VectorClockValid(c.pvc)
    }

    predicate ClientInit(c:Client, id:int)
        requires Nodes <= id < Nodes + Clients
    {
        && c.opn == 0
        && c.id == id
        && c.local == map[]
        && c.deps == map[]
        // && c.pvc == EmptyVC()
    }

    predicate SendRead(c:Client, c':Client, sp:seq<Packet>)
        requires ClientValid(c)
    {
        var k :| 0 <= k < MaxKeys as int;
        
        if k in c.local then 
            && c' == c.(opn := c.opn + 1)
            && sp == []
        else 
            var server :| 0 <= server < Nodes as int;
            && c' == c.(opn := c.opn + 1)
            && sp == [LPacket(c.id, server, Message_Read(c.opn, k, c.deps/*, c.pvc*/))]
    }

    predicate ReceiveReadReply(c:Client, c':Client, p:Packet, sp:seq<Packet>)
        requires ClientValid(c)
        requires p.msg.Message_Read_Reply?
        requires PacketValid(p)
        // requires p.msg.opn_rreply == c.opn
    {
        var m := Meta(p.msg.key_rreply, p.msg.vc_rreply, p.msg.deps_rreply);
        // var new_pvc := if (VCHappendsBefore(p.msg.pvc_rreply, c.pvc)) then c.pvc else VCMerge(c.pvc, p.msg.pvc_rreply);

        && c' == c.(/*local := c.local[p.msg.key_rreply := m],*/ deps := DependencyInsertOrMerge(c.deps, p.msg.key_rreply, p.msg.vc_rreply)/*, pvc := new_pvc*/)
        && sp == []
    }

    predicate SendWrite(c:Client, c':Client, sp:seq<Packet>)
        // requires ClientValid(c)
    {
        var k :| 0 <= k < MaxKeys as int;
        var server :| 0 <= server < Nodes as int;
        && c' == c.(opn := c.opn + 1)
        && sp == [LPacket(c.id, server, Message_Write(c.opn + 1, k, c.deps, c.local/*, c.pvc*/))]
    }

    predicate ReceiveWriteReply(c:Client, c':Client, p:Packet, sp:seq<Packet>)
        requires ClientValid(c)
        requires p.msg.Message_Write_Reply?
        requires PacketValid(p)
    {
        var k := p.msg.key_wreply;
        var vc := p.msg.vc_wreply;
        // var new_pvc := if (VCHappendsBefore(p.msg.pvc_wreply, c.pvc)) then c.pvc else VCMerge(c.pvc, p.msg.pvc_wreply);

        var m := Meta(k, vc, c.deps);
        && c' == c.(local := c.local[k := m]/*, pvc := new_pvc*/)
        && sp == []
    }

    // function ExtractSentPacketsFromIos(ios:seq<CMIo>) : seq<Packet>
    //     ensures forall p :: p in ExtractSentPacketsFromIos(ios) <==> LIoOpSend(p) in ios
    // {
    //     if |ios| == 0 then
    //         []
    //     else if ios[0].LIoOpSend? then
    //         [ios[0].s] + ExtractSentPacketsFromIos(ios[1..])
    //     else
    //         ExtractSentPacketsFromIos(ios[1..])
    // }

    // predicate ServerProcessPacket(s:Server, s':Server, ios:seq<CMIo>)
    //     requires ServerValid(s)
    //     requires |ios| >= 1
    //     requires ios[0].LIoOpReceive?
    //     requires PacketValid(ios[0].r)
    //     requires var msg := ios[0].r.msg; 
    //             msg.Message_Read? || msg.Message_Write? || msg.Message_Propagation?
    // {
    //     && (forall io :: io in ios[1..] ==> io.LIoOpSend?)
    //     && var sent_packets := ExtractSentPacketsFromIos(ios);
    //         match ios[0].r.msg 
    //             case Message_Read(_,_,_,_) => ReceiveRead(s, s', ios[0].r, sent_packets)
    //             case Message_Write(_,_,_,_,_) => ReceiveWrite(s, s', ios[0].r, sent_packets)
    //             case Message_Propagation(_,_,_,_) => ReceivePropagate(s, s', ios[0].r, sent_packets)
    // }

    // predicate NextProcessPacket(s:Server, s':Server, c:Client, c':Client, ios:seq<CMIo>)
    //     requires ServerValid(s)
    //     requires ClientValid(c)
    // {
    //     && |ios| >= 1
    //     && if ios[0].LIoOpTimeoutReceive? then
    //         s' == s && |ios| == 1
    //         else
    //         (&& ios[0].LIoOpReceive?
    //         && if ios[0].r.msg.Message_Read? || ios[0].r.msg.Message_Write? || ios[0].r.msg.Message_Propagation? then
    //             ServerProcessPacket(s, s', ios)
    //            else
    //             ClientProcessPacket(c, c', ios)
    //         )
    // }

    // predicate ServerNextProcessPacket(s:Server, s':Server, ios:seq<CMIo>)
    //     requires ServerValid(s)
    // {
    //     && |ios| >= 1
    //     && if ios[0].LIoOpTimeoutReceive? then
    //         s' == s && |ios| == 1
    //        else
    //         (&& ios[0].LIoOpReceive?
    //          && PacketValid(ios[0].r)
    //         && if ios[0].r.msg.Message_Read? || ios[0].r.msg.Message_Write? || ios[0].r.msg.Message_Propagation? then
    //             ServerProcessPacket(s, s', ios)
    //            else
    //             s' == s && |ios| == 1
    //         )
    // }

    // datatype LServer = LServer(s:Server)

    // predicate LServerInit(s:LServer, id:int)
    //     requires 0 <= id < Nodes
    // {
    //     && ServerInit(s.s, id)
    //     // && s.nextActionIndex == 0
    // }

    // predicate LServerNext(s:LServer, s':LServer, ios:seq<CMIo>)
    // {
    //     && ServerValid(s.s)
    //     && ServerNextProcessPacket(s.s, s'.s, ios)
    // }


    // predicate ClientProcessPacket(s:Client, s':Client, ios:seq<CMIo>)
    //     requires ClientValid(s)
    //     requires |ios| >= 1
    //     requires ios[0].LIoOpReceive?
    //     requires PacketValid(ios[0].r)
    //     requires var msg := ios[0].r.msg;
    //             msg.Message_Read_Reply? || msg.Message_Write_Reply?
    // {
    //     && (forall io :: io in ios[1..] ==> io.LIoOpSend?)
    //     && var sent_packets := ExtractSentPacketsFromIos(ios);
    //         match ios[0].r.msg 
    //             case Message_Read_Reply(_,_,_,_,_) => ReceiveReadReply(s, s', ios[0].r, sent_packets)
    //             case Message_Write_Reply(_,_,_,_) => ReceiveWriteReply(s, s', ios[0].r, sent_packets)
    // }

    // predicate ClientNextProcessPacket(s:Client, s':Client, ios:seq<CMIo>)
    //     requires ClientValid(s)
    // {
    //     && |ios| >= 1
    //     && if ios[0].LIoOpTimeoutReceive? then
    //         s' == s && |ios| == 1
    //        else
    //         (&& ios[0].LIoOpReceive?
    //         && PacketValid(ios[0].r)
    //         && if ios[0].r.msg.Message_Read_Reply? || ios[0].r.msg.Message_Write_Reply? then
    //             ClientProcessPacket(s, s', ios)
    //            else
    //             s' == s && |ios| == 1
    //         )
    // }

    // predicate SpontaneousIos(ios:seq<CMIo>, clocks:int)
    //     requires 0<=clocks<=1
    // {
    //     && clocks <= |ios|
    //     && (forall i :: 0<=i<clocks ==> ios[i].LIoOpReadClock?)
    //     && (forall i :: clocks<=i<|ios| ==> ios[i].LIoOpSend?)
    // }

    // predicate ClientNoReceiveNext(s:Client, s':Client, nextActionIndex:int, ios:seq<CMIo>)
    //     requires ClientValid(s)
    // {
    //     var sent_packets := ExtractSentPacketsFromIos(ios);

    //     if nextActionIndex == 1 then 
    //         && SpontaneousIos(ios, 0)
    //         && SendRead(s, s', sent_packets)
    //     else 
    //         && nextActionIndex == 2
    //         && SpontaneousIos(ios, 0)
    //         && SendWrite(s, s', sent_packets)
    // }

    // datatype LClient = LClient(c:Client, nextActionIndex:int)

    // predicate LClientInit(s:LClient, id:int)
    //     requires Nodes <= id < Nodes + Clients
    // {
    //     && ClientInit(s.c, id)
    //     && s.nextActionIndex == 0
    // }

    // predicate LClientNext(s:LClient, s':LClient, ios:seq<CMIo>)
    // {
    //     && ClientValid(s.c)
    //     && s'.nextActionIndex == (s.nextActionIndex + 1) % 3
    //     && if s.nextActionIndex == 0 then 
    //         ClientNextProcessPacket(s.c, s'.c, ios)
    //        else 
    //         ClientNoReceiveNext(s.c, s'.c, s.nextActionIndex, ios)
    // }

}
include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "Network.dfy"
include "ServerImpl.dfy"

module CausalMesh_ServerImplMain_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened Common__UdpClient_i
import opened CausalMesh_ServerImpl_i
import opened CausalMesh_Network_i
import opened CausalMesh_CMessage_i
import opened CausalMesh_CCache_i
import opened CausalMesh_Types_i

method Replica_Next_ProcessPacketX(r:ServerImpl)
  returns (ok:bool/*, ghost UdpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>*/)
  requires r.Valid()
//   requires CConfigurationIsValid(r.replica.constants.all.config)
  //  requires Replica_Next_Process_AppStateSupply_Preconditions(r.replica,r.cpacket)
  modifies r.Repr//, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
  ensures r.Repr == old(r.Repr)
  ensures r.netClient != null
  ensures ok == UdpClientOk(r.netClient)
//   ensures r.Env().Valid() && r.Env().ok.ok() ==> ok
//   ensures r.Env() == old(r.Env());
  ensures ok ==> 
            && r.Valid()
            // && r.nextActionIndex == old(r.nextActionIndex)
            // && (|| Q_LReplica_Next_ProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
            //     || (&& IosReflectIgnoringUnsendable(UdpEventLog)
            //        && old(r.AbstractifyToLReplica()) == r.AbstractifyToLReplica()))
            // && RawIoConsistentWithSpecIO(UdpEventLog, ios)
            // && OnlySentMarshallableData(UdpEventLog)
            // && old(r.Env().udp.history()) + UdpEventLog == r.Env().udp.history()
{
//   ghost var old_net_history := r.Env().udp.history();
  // var start_time := Time.GetDebugTimeTicks();
  var rr;
//   ghost var receive_event;
  // print ("Replica_Next_ProcessPacket: Enter\n");
  // print ("Replica_Next_ProcessPacket: Calling Receive for a packet\n");
  rr/*, receive_event*/ := Receive(r.netClient, r.localAddr, r.msg_grammar);
  //var receive_packet_time := Time.GetDebugTimeTicks();
  //RecordTimingSeq("Replica_Next_Receive", start_time, receive_packet_time);
//   assert r.Env()==old(r.Env());

  // print "Receive packet\n";

  if (rr.RRFail?) {
    ok := false;
    //var end_time := Time.GetDebugTimeTicks();
    //RecordTimingSeq("Replica_Next_ProcessPacket_fail", start_time, end_time);
    return;
  } else if (rr.RRTimeout?) {
    ok := true;
    ReplicaNextProcessPacketTimeout(r);
    //var end_time := Time.GetDebugTimeTicks();
    //RecordTimingSeq("Replica_Next_ProcessPacket_timeout", start_time, end_time);
  } else {
    lemma_PacketValid(rr.cpacket);
    assert CPacketIsValid(rr.cpacket) && CPacketValid(rr.cpacket);
    var marshallable := true;
    if !marshallable {
      ok := true;
    //   UdpEventLog, ios := ReplicaNextProcessPacketUnmarshallable(r, old_net_history, rr, receive_event);
    } else if (rr.cpacket.msg.CMessage_Read?) {
      ok /*, UdpEventLog, ios*/ := ServerNextProcessRead(r, rr.cpacket/*, old_net_history, rr, receive_event*/);
    } else if (rr.cpacket.msg.CMessage_Write?) {
      ok /*, UdpEventLog, ios*/ := ServerNextProcessWrite(r, rr.cpacket/*, old_net_history, rr, receive_event*/);
    } else if (rr.cpacket.msg.CMessage_Propagation?) {
      ok /*, UdpEventLog, ios*/ := ServerNextProcessPropagation(r, rr.cpacket/*, old_net_history, rr, receive_event*/);
    } else {
      ok := true;
    }
  }
  //print ("Replica_Next_ProcessPacket: Exit\n");
}

method {:timeLimitMultiplier 2} ReplicaNextMainProcessPacketX(r:ServerImpl)
returns (ok:bool/*, ghost netEventLog:seq<UdpEvent>, ghost ios:seq<CMIo>*/)
requires r.Valid()
// requires r.nextActionIndex == 0
modifies r.Repr//, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
ensures r.Repr == old(r.Repr) 
ensures r.netClient != null
// ensures r.Env().Valid() && r.Env().ok.ok() ==> ok
// ensures r.Env() == old(r.Env());
ensures ok ==>
            && r.Valid()
            // && (|| Q_LScheduler_Next(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), ios)
            //     || HostNextIgnoreUnsendable(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), netEventLog))
            // && RawIoConsistentWithSpecIO(netEventLog, ios)
            // && OnlySentMarshallableData(netEventLog)
            // && old(r.Env().udp.history()) + netEventLog == r.Env().udp.history()
{
    // ghost var replica_old := old(r.AbstractifyToLReplica());
    // ghost var scheduler_old := old(r.AbstractifyToLScheduler());

    // assert scheduler_old.nextActionIndex == 0;

    // //print ("Replica_Next_main Enter\n");
    // assert scheduler_old.replica == replica_old;
    ok/*, netEventLog, ios*/ := Replica_Next_ProcessPacketX(r);
    if (!ok) { return; }

    // assert r.Valid();

    // // Mention unchanged predicates over mutable state in the old heap.
    // ghost var net_client_old := r.netClient;
    // ghost var net_addr_old := r.netClient.LocalEndPoint();
    // assert UdpClientIsValid(net_client_old);

    // ghost var replica := r.AbstractifyToLReplica();
    // r.nextActionIndex := 1;
    // ghost var scheduler := r.AbstractifyToLScheduler();

    // Mention unchanged predicates over mutable state in the new heap.
    // assert net_client_old == r.netClient;
    // assert UdpClientIsValid(r.netClient);
    // assert net_addr_old == r.netClient.LocalEndPoint();

    // assert r.Valid();

    // calc {
    //     scheduler.nextActionIndex;
    //     r.nextActionIndex as int;
    //     1;
    //     { lemma_mod_auto(LReplicaNumActions()); }
    //     (1)%LReplicaNumActions();
    //     (scheduler_old.nextActionIndex+1)%LReplicaNumActions();
    // }

    // if Q_LReplica_Next_ProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios) {
    //     lemma_EstablishQLSchedulerNext(replica_old, replica, ios, scheduler_old, scheduler);
    //     assert Q_LScheduler_Next(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), ios);
    // }
    // else {
    //     assert IosReflectIgnoringUnsendable(netEventLog);
    //     assert old(r.AbstractifyToLReplica()) == r.AbstractifyToLReplica();
    //     assert HostNextIgnoreUnsendable(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), netEventLog);
    // }
} 

method Server_Next_main(r:ServerImpl)
    returns (ok:bool/*, ghost netEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>*/)
    requires r.Valid()
    modifies r.Repr//, r.cur_req_set, r.prev_req_set, r.reply_cache_mutable
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    // ensures r.Env().Valid() && r.Env().ok.ok() ==> ok
    // ensures r.Env() == old(r.Env());
    ensures ok ==>
              && r.Valid()
            //   && (|| Q_LScheduler_Next(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), ios)
            //       || HostNextIgnoreUnsendable(old(r.AbstractifyToLScheduler()), r.AbstractifyToLScheduler(), netEventLog))
            //   && RawIoConsistentWithSpecIO(netEventLog, ios)
            //   && OnlySentMarshallableData(netEventLog)
            //   && old(r.Env().udp.history()) + netEventLog == r.Env().udp.history()
  {
    // //print ("Replica_Next_main Enter\n");
    // if r.nextActionIndex == 0 {
      ok/*, netEventLog, ios*/ := ReplicaNextMainProcessPacketX(r);
    // }
    // else if r.nextActionIndex == 1 || r.nextActionIndex == 2 || r.nextActionIndex == 4 || r.nextActionIndex == 5 || r.nextActionIndex == 6 {
    //   ok, netEventLog, ios := ReplicaNextMainNoClock(r);
    // }
    // else if (r.nextActionIndex == 3 || 7 <= r.nextActionIndex <= 9) {
    //   ok, netEventLog, ios := ReplicaNextMainReadClock(r);
    // }
    // //print ("Replica_Next_main Exit\n");
  }

lemma {:axiom} lemma_PacketValid(p:CPacket)
    ensures CPacketIsValid(p) && CPacketValid(p)

// method {:timeLimitMultiplier 2} DeliverPacketSequence(r:ServerImpl, packets:seq<CPacket>) returns (ok:bool/*, ghost netEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>*/)
// //   requires r.Valid()
// //   requires packets.PacketSequence?
// //   requires OutboundPacketsIsValid(packets)
// //   requires OutboundPacketsIsAbstractable(packets)
// //   requires OutboundPacketsHasCorrectSrc(packets, r.replica.constants.all.config.replica_ids[r.replica.constants.my_index])
//   requires r.Valid()
//   requires UdpClientIsValid(r.netClient)
//   requires r.netClient.LocalEndPoint() == r.localAddr
//   modifies r.Repr
//   ensures r.Repr == old(r.Repr)
//   ensures r.netClient != null
//   ensures ok == UdpClientOk(r.netClient)
// //   ensures r.Env() == old(r.Env())
//   ensures r.server == old(r.server)
// //   ensures ok ==>
// //           && r.Valid()
// //           && r.nextActionIndex == old(r.nextActionIndex)
// //           && AllIosAreSends(ios)
// //           && AbstractifyOutboundCPacketsToSeqOfRslPackets(packets) == ExtractSentPacketsFromIos(ios)
// //           && OnlySentMarshallableData(netEventLog)
// //           && RawIoConsistentWithSpecIO(netEventLog, ios)
// //           && old(r.Env().udp.history()) + netEventLog == r.Env().udp.history()
// {
//   ok/*, netEventLog*/ := SendPacketSequence(r.netClient, packets, r.localAddr);
//   if (!ok) { print("ReplicaImplDelivery: send packetseq fail\n"); return; }
// }

method DeliverPackets(r:ServerImpl, packets:seq<CPacket>) returns (ok:bool/*, ghost netEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>*/)
  requires r.Valid()
//   requires UdpClientIsValid(r.netClient)
//   requires r.netClient.LocalEndPoint() == r.localAddr  
  modifies r.Repr
  ensures r.Repr == old(r.Repr)
  ensures r.netClient != null
  ensures ok == UdpClientOk(r.netClient)
//   ensures r.Env() == old(r.Env())
  ensures r.server == old(r.server)
{
    ok := SendPacketSequence(r.netClient, packets, r.localAddr);
}

// lemma {:axiom} lemma_ProcessPacket(s:ServerImpl)
//     ensures UdpClientIsValid(s.netClient)
//     ensures s.netClient.LocalEndPoint() == s.localAddr

// method ServerNextProcessRead(
//     s:ServerImpl,
//     cpacket:CPacket
// ) returns (
//     ok:bool
// )
//     requires cpacket.msg.CMessage_Read?
//     requires s.Valid()
//     requires CPacketIsValid(cpacket)
//     requires CPacketValid(cpacket)
//     requires CServerIsValid(s.server) && CServerValid(s.server)
//     // requires UdpClientIsValid(s.netClient)
//     // requires s.netClient.LocalEndPoint() == s.localAddr
//     modifies s.Repr
//     ensures s.Repr==old(s.Repr)
//     ensures s.netClient != null
//     ensures ok == UdpClientOk(s.netClient)
//     ensures ok ==> s.Valid()
// {
//     assert UdpClientIsValid(old(s.netClient));
//     var sent_packets;
//     s.server, sent_packets := CReceiveRead(s.server, cpacket);
//     assert s.netClient == old(s.netClient);
//     assert s.localAddr == old(s.localAddr);
//     // lemma_ProcessPacket(s);
//     // assert UdpClientIsValid(s.netClient);
//     // assert s.netClient.LocalEndPoint() == s.localAddr;
//     ok := DeliverPackets(s, sent_packets);
//     // if (!ok) { return; }
// }

lemma {:axiom} lemma_test(r:ServerImpl)
    ensures r.Valid()
    ensures UdpClientIsValid(r.netClient)
    // ensures 

method {:fuel CServerIsValid,0,0} {:timeLimitMultiplier 2} ServerNextProcessRead(
  r:ServerImpl,
  cpacket:CPacket
  /*ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo*/
  ) returns (
  ok:bool
  /*ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>*/
  )
  requires r.Valid()
  requires cpacket.msg.CMessage_Read?
  requires CPacketIsValid(cpacket)
  requires CPacketValid(cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr) // do not create new instance
  ensures r.netClient != null 
  ensures ok == UdpClientOk(r.netClient)
  ensures ok ==>
            && r.Valid()
{
  // print "Process Read\n";
  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.LocalEndPoint();
  assert UdpClientIsValid(net_client_old);

  var sent_packets;
  // r.server, sent_packets := CReceiveRead(r.server, cpacket);
  r.server, sent_packets := CReceiveRead_I1(r.server, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
//   assert UdpClientIsValid(r.netClient);
//   assert net_addr_old == r.netClient.LocalEndPoint();

  lemma_test(r);
  assert r.Valid();
  ok/*, send_events, send_ios*/ := DeliverPackets(r, sent_packets);
  lemma_test(r);
//   if (!ok) { return; }
}

method {:fuel CServerIsValid,0,0} {:timeLimitMultiplier 2} ServerNextProcessWrite(
  r:ServerImpl,
  cpacket:CPacket
  /*ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo*/
  ) returns (
  ok:bool
  /*ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>*/
  )
  requires r.Valid()
  requires cpacket.msg.CMessage_Write?
  requires CPacketIsValid(cpacket)
  requires CPacketValid(cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr) // do not create new instance
  ensures r.netClient != null 
  ensures ok == UdpClientOk(r.netClient)
  ensures ok ==>
            && r.Valid()
{
  // print "Process Write\n";
  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.LocalEndPoint();
  assert UdpClientIsValid(net_client_old);

  var sent_packets;
  // r.server, sent_packets := CReceiveWrite(r.server, cpacket);
  r.server, sent_packets := CReceiveWrite_I1(r.server, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
//   assert UdpClientIsValid(r.netClient);
//   assert net_addr_old == r.netClient.LocalEndPoint();

  lemma_test(r);
  assert r.Valid();
  ok/*, send_events, send_ios*/ := DeliverPackets(r, sent_packets);
  lemma_test(r);
//   if (!ok) { return; }
}

method {:fuel CServerIsValid,0,0} {:timeLimitMultiplier 2} ServerNextProcessPropagation(
  r:ServerImpl,
  cpacket:CPacket
  /*ghost old_net_history:seq<UdpEvent>,
  ghost receive_event:UdpEvent,
  ghost receive_io:RslIo*/
  ) returns (
  ok:bool
  /*ghost UdpEventLog:seq<UdpEvent>,
  ghost ios:seq<RslIo>*/
  )
  requires r.Valid()
  requires cpacket.msg.CMessage_Propagation?
  requires CPacketIsValid(cpacket)
  requires CPacketValid(cpacket)
  modifies r.Repr
  ensures r.Repr==old(r.Repr) // do not create new instance
  ensures r.netClient != null 
  ensures ok == UdpClientOk(r.netClient)
  ensures ok ==>
            && r.Valid()
{
  // print "Process Propagation\n";
  // Mention unchanged predicates over mutable state in the old heap.
  ghost var net_client_old := r.netClient;
  ghost var net_addr_old := r.netClient.LocalEndPoint();
  assert UdpClientIsValid(net_client_old);

  var sent_packets;
  r.server, sent_packets := CReceivePropagate(r.server, cpacket);

  // Mention unchanged predicates over mutable state in the new heap.
  assert net_client_old == r.netClient;
//   assert UdpClientIsValid(r.netClient);
//   assert net_addr_old == r.netClient.LocalEndPoint();

  lemma_test(r);
  assert r.Valid();
  ok/*, send_events, send_ios*/ := DeliverPackets(r, sent_packets);
  lemma_test(r);
//   if (!ok) { return; }
}

method ReplicaNextProcessPacketTimeout(r:ServerImpl/*, ghost old_net_history:seq<UdpEvent>, ghost timeout_event:UdpEvent*/)
//   returns (ghost UdpEventLog:seq<UdpEvent>, ghost ios:seq<RslIo>)
  requires r.Valid()
//   requires r.Env().udp.history() == old_net_history + [ timeout_event ]
//   requires timeout_event.LIoOpTimeoutReceive?
//   ensures  Q_LReplica_Next_ProcessPacket(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios)
//   ensures  RawIoConsistentWithSpecIO(UdpEventLog, ios)
//   ensures  old_net_history + UdpEventLog == r.Env().udp.history()
//   ensures  OnlySentMarshallableData(UdpEventLog)
{
//   ios := [ LIoOpTimeoutReceive() ];
//   UdpEventLog := [ timeout_event ];
//   lemma_EstablishQLReplicaNextProcessPacketFromTimeout(old(r.AbstractifyToLReplica()), r.AbstractifyToLReplica(), ios);
}





}
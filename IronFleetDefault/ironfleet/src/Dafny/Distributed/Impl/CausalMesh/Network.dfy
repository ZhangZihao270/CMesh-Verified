include "../Common/UdpClient.i.dfy"
include "PacketParsing.dfy"

module CausalMesh_Network_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Common__GenericMarshalling_i
import opened Common__NodeIdentity_i
import opened Common__UdpClient_i
import opened Common__Util_i
import opened CausalMesh_PacketParsing_i
import opened Logic__Option_i
import opened Environment_s
import opened CausalMesh_CMessage_i
import opened CausalMesh_Types_i

datatype ReceiveResult = RRFail() | RRTimeout() | RRPacket(cpacket:CPacket)

method GetEndPoint(ipe:IPEndPoint) returns (ep:EndPoint)
  ensures ep == ipe.EP()
  ensures EndPointIsValidIPV4(ep)
{
  var addr := ipe.GetAddress();
  var port := ipe.GetPort();
  ep := EndPoint(addr[..], port);
}

method{:timeLimitMultiplier 2} Receive(udpClient:UdpClient, localAddr:EndPoint, msg_grammar:G) returns (rr:ReceiveResult)
  requires UdpClientIsValid(udpClient)
  requires udpClient.LocalEndPoint() == localAddr
  //requires KnownSendersMatchConfig(config)
//   requires CConfigurationIsValid(config)
  requires msg_grammar == CMessage_grammar()
  modifies UdpClientRepr(udpClient)
  ensures udpClient.env == old(udpClient.env)
  ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
  ensures UdpClientOk(udpClient) <==> !rr.RRFail?
  ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient)
  ensures !rr.RRFail? ==>
            && udpClient.IsOpen()
            // && old(udpClient.env.udp.history()) + [udpEvent] == udpClient.env.udp.history()
//   ensures rr.RRTimeout? ==> udpEvent.LIoOpTimeoutReceive?;
  ensures rr.RRPacket? ==>
            // && udpEvent.LIoOpReceive?
            // && UdpPacketIsAbstractable(udpEvent.r)
            && CPacketIsAbstractable(rr.cpacket)
            // && CMessageIs64Bit(rr.cpacket.msg)
            && EndPointIsValidIPV4(rr.cpacket.src)
            // && AbstractifyCPacketToRslPacket(rr.cpacket) == AbstractifyUdpPacketToRslPacket(udpEvent.r)
            // && rr.cpacket.msg == PaxosDemarshallData(udpEvent.r.msg)
            // && PaxosEndPointIsValid(rr.cpacket.src, config)
{
  var timeout := 0;
  ghost var old_udp_history := udpClient.env.udp.history();
  var ok, timedOut, remote, buffer := udpClient.Receive(timeout);

  if (!ok) {
    rr := RRFail();
    return;
  }

  if (timedOut) {
    rr := RRTimeout();
    // udpEvent := LIoOpTimeoutReceive(); 
    return;
  }

  // print "Receive a packet\n";

//   udpEvent := LIoOpReceive(LPacket(udpClient.LocalEndPoint(), remote.EP(), buffer[..]));
//   assert udpClient.env.udp.history() == old_udp_history + [udpEvent];
  var start_time := Time.GetDebugTimeTicks();
//   lemma_CMessageGrammarValid();
  var cmessage := DemarshallData(buffer, msg_grammar);
  var end_time := Time.GetDebugTimeTicks();
//   RecordTimingSeq("PaxosDemarshallDataMethod", start_time, end_time);

  var srcEp := GetEndPoint(remote);
  var cpacket := CPacket(localAddr, srcEp, cmessage);
  rr := RRPacket(cpacket);
//   assert udpClient.env.udp.history() == old_udp_history + [udpEvent];

//   if cmessage.CMessage_Invalid? {
//     RecordTimingSeq("DemarshallMessage_Invalid", start_time, end_time);
//   } else if cmessage.CMessage_Request? {
//     RecordTimingSeq("DemarshallMessage_Request", start_time, end_time);
//   } else if cmessage.CMessage_1a? {
//     RecordTimingSeq("DemarshallMessage_1a", start_time, end_time);
//   } else if cmessage.CMessage_1b? {
//     RecordTimingSeq("DemarshallMessage_1b", start_time, end_time);
//   } else if cmessage.CMessage_2a? {
//     // if |cmessage.val_2a| > 0{
//     //   var req := cmessage.val_2a[0];
//     //   // if start_time > req.ntime {
//     //       print "req ", req.seqno, " receive 2a at ", start_time, "\n";
//     //   // }
//     // }
//     RecordTimingSeq("DemarshallMessage_2a", start_time, end_time);
//   } else if cmessage.CMessage_2b? {
//     RecordTimingSeq("DemarshallMessage_2b", start_time, end_time);
//   } else if cmessage.CMessage_Heartbeat? {
//     RecordTimingSeq("DemarshallMessage_Heartbeat", start_time, end_time);
//   } else if cmessage.CMessage_Reply? {
//     RecordTimingSeq("DemarshallMessage_Reply", start_time, end_time);
//   } else if cmessage.CMessage_AppStateRequest? {
//     RecordTimingSeq("DemarshallMessage_AppStateRequest", start_time, end_time);
//   } else if cmessage.CMessage_AppStateSupply? {
//     RecordTimingSeq("DemarshallMessage_AppStateSupply", start_time, end_time);
//   } else if cmessage.CMessage_StartingPhase2? {
//     RecordTimingSeq("DemarshallMessage_StartingPhase2", start_time, end_time);
//   }

//   assert EndPointIsValidIPV4(udpClient.LocalEndPoint());
//   // assert PaxosEndPointIsValid(rr.cpacket.src, config);
//   assert AbstractifyCPacketToRslPacket(rr.cpacket) == AbstractifyUdpPacketToRslPacket(udpEvent.r);
}


// method SendPacket(udpClient:UdpClient, packets:OutboundPackets, ghost localAddr_:EndPoint) returns (ok:bool, ghost udpEventLog:seq<UdpEvent>)
//   requires UdpClientIsValid(udpClient)
//   requires packets.OutboundPacket?
//   requires OutboundPacketsIsValid(packets)
//   requires udpClient.LocalEndPoint() == localAddr_
//   requires OutboundPacketsHasCorrectSrc(packets, localAddr_)
//   modifies UdpClientRepr(udpClient)
//   ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient)
//   ensures udpClient.env == old(udpClient.env)
//   ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
//   ensures UdpClientOk(udpClient) <==> ok
//   ensures ok ==> && UdpClientIsValid(udpClient)
//                  && udpClient.IsOpen()
//                  && old(udpClient.env.udp.history()) + udpEventLog == udpClient.env.udp.history()
//                  && OnlySentMarshallableData(udpEventLog)
//                  && SendLogReflectsPacket(udpEventLog, packets.p)
// {
//   var j:uint64 := 0;
//   udpEventLog := [];
//   ok := true;
//   var opt_packet := packets.p;

//   if opt_packet.None? {

//   } else {
//     var cpacket := opt_packet.v;

//     ghost var udpEventLog_old := udpEventLog;

//     // Construct the remote address
//     var dstEp:EndPoint := cpacket.dst;
//     var dstAddrAry := seqToArrayOpt(dstEp.addr);
//     var remote;
//     ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, udpClient.env);
//     if (!ok) { return; }

//     assert CMessageIsAbstractable(cpacket.msg);
//     assert Marshallable(cpacket.msg);
//     var marshall_start_time := Time.GetDebugTimeTicks();
//     var buffer := PaxosMarshall(cpacket.msg);
//     var marshall_end_time := Time.GetDebugTimeTicks();
//     RecordTimingSeq("SendBatch_PaxosMarshall", marshall_start_time, marshall_end_time);

//     ghost var data := buffer[..];
//     assert BufferRefinementAgreesWithMessageRefinement(cpacket.msg, data);

//     ok := udpClient.Send(remote, buffer);
//     if (!ok) { return; }

//     ghost var udpEvent := LIoOpSend(LPacket(remote.EP(), udpClient.LocalEndPoint(), buffer[..]));
//     ghost var udp := udpEvent.s;

//     calc {
//       AbstractifyCPacketToRslPacket(cpacket);
//       LPacket(AbstractifyEndPointToNodeIdentity(cpacket.dst), AbstractifyEndPointToNodeIdentity(cpacket.src), AbstractifyCMessageToRslMessage(cpacket.msg));
//       LPacket(AbstractifyEndPointToNodeIdentity(udp.dst), AbstractifyEndPointToNodeIdentity(udp.src), AbstractifyCMessageToRslMessage(cpacket.msg));
//       AbstractifyBufferToRslPacket(udp.src, udp.dst, data);
//       AbstractifyBufferToRslPacket(udp.src, udp.dst, udp.msg);
//       AbstractifyUdpPacketToRslPacket(udpEvent.s);
//     }
//     assert SendLogEntryReflectsPacket(udpEvent, cpacket);
//     udpEventLog := [udpEvent];
//   }
// }


method{:timeLimitMultiplier 2} SendPacketSequence(udpClient:UdpClient, packets:seq<CPacket>, ghost localAddr_:EndPoint) returns (ok:bool)
  requires UdpClientIsValid(udpClient)
//   requires OutboundPacketsIsValid(packets)
//   requires packets.PacketSequence?
  requires udpClient.LocalEndPoint() == localAddr_
//   requires OutboundPacketsHasCorrectSrc(packets, localAddr_)
  modifies UdpClientRepr(udpClient)
  ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient)
  ensures udpClient.env == old(udpClient.env)
  ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
  ensures UdpClientOk(udpClient) <==> ok
  ensures ok ==>
            && UdpClientIsValid(udpClient)
            && udpClient.IsOpen()
            // && old(udpClient.env.udp.history()) + udpEventLog == udpClient.env.udp.history()
            // && OnlySentMarshallableData(udpEventLog)
            // && SendLogReflectsPacketSeq(udpEventLog, packets.s)
{
  var cpackets := packets;
  var j:int := 0;
//   udpEventLog := [];
  ok := true;
    
//   ghost var udpEventLog_old := udpEventLog;
//   ghost var udpClientEnvHistory_old := old(udpClient.env.udp.history());
  var i:int := 0;

  while i < |cpackets| as int
    invariant old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient)
    invariant udpClient.env == old(udpClient.env)
    invariant udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
    invariant UdpClientOk(udpClient) <==> ok
    invariant ok ==> ( UdpClientIsValid(udpClient) && udpClient.IsOpen())
    // invariant ok ==> udpClientEnvHistory_old + udpEventLog == udpClient.env.udp.history()
    // invariant (i == 0) ==> |udpEventLog| == 0
    // invariant (0 < i as int < |cpackets|) ==> |udpEventLog| == |cpackets[0..i]|
    // invariant (0 < i as int < |cpackets|) ==> SendLogReflectsPacketSeq(udpEventLog, cpackets[0..i]);
    // invariant (i as int >= |cpackets|) ==> SendLogReflectsPacketSeq(udpEventLog, cpackets);
    // invariant OnlySentMarshallableData(udpEventLog)
  {
    var cpacket := cpackets[i];
    // Construct the remote address
    var dstEp:EndPoint := cpacket.dst;
    assert cpacket in cpackets;
    // assert OutboundPacketsIsValid(packets);

    if |dstEp.addr| < 0x1_0000_0000_0000_0000 {

        var dstAddrAry := seqToArrayOpt(dstEp.addr);
        var remote;
        ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, udpClient.env);
        if (!ok) { return; }

        // assert CMessageIsAbstractable(cpacket.msg);
            
        // assert Marshallable(cpacket.msg);
        var buffer := MarshallData(cpacket.msg);

        // ghost var data := buffer[..];
        // assert BufferRefinementAgreesWithMessageRefinement(cpacket.msg, data);
        if buffer.Length <= 0xFFFF_FFFF_FFFF_FFFF {
            ok := udpClient.Send(remote, buffer);
            if (!ok) { return; }
        } else {
            print "Packet is too large\n";
        }
    } else {
        print "Dst has wrong adress\n";
    }

    // ghost var udpEvent := LIoOpSend(LPacket(remote.EP(), udpClient.LocalEndPoint(), buffer[..]));
    // ghost var udp := udpEvent.s;

    // calc {
    //   AbstractifyCPacketToRslPacket(cpacket);
    //   LPacket(AbstractifyEndPointToNodeIdentity(cpacket.dst), AbstractifyEndPointToNodeIdentity(cpacket.src), AbstractifyCMessageToRslMessage(cpacket.msg));
    //   LPacket(AbstractifyEndPointToNodeIdentity(udp.dst), AbstractifyEndPointToNodeIdentity(udp.src), AbstractifyCMessageToRslMessage(cpacket.msg));
    //   AbstractifyBufferToRslPacket(udp.src, udp.dst, data);
    //   AbstractifyBufferToRslPacket(udp.src, udp.dst, udp.msg);
    //   AbstractifyUdpPacketToRslPacket(udpEvent.s);
    // }
        
    // assert SendLogEntryReflectsPacket(udpEvent, cpacket);
        
    // udpEventLog := udpEventLog + [udpEvent];
    // assert cpackets[0..(i as int+1)] == cpackets[0..i as int] + [cpacket];
    // assert SendLogReflectsPacketSeq(udpEventLog, cpackets[0..(i as int+1)]);
    i := i + 1;
  }
}
}
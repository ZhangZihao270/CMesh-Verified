include "../../Common/Collections/Seqs.i.dfy"
include "../../../Libraries/Math/mod_auto.i.dfy"
include "CCache.dfy"
include "Network.dfy"

module CausalMesh_ServerImpl_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Seqs_i
import opened Math__mod_auto_i
import opened Common__GenericMarshalling_i
import opened Common__UdpClient_i
import opened Common__Util_i
// import opened Common__UpperBound_i
import opened CausalMesh_CCache_i
import opened CausalMesh_PacketParsing_i
import opened CausalMesh_CTypes_i
import opened CausalMesh_CMessage_i
import opened CausalMesh_Types_i

class ServerImpl
{
    var server:CServer;
    var netClient:UdpClient?;
    var localAddr:EndPoint;
    var msg_grammar:G;

    ghost var Repr : set<object>;

    constructor()
    {
        netClient := null;
    }

    predicate Valid()
      reads this
      reads if netClient != null then UdpClientIsValid.reads(netClient) else {}
    {
    //   && CReplicaIsAbstractable(replica)
      && CServerIsValid(server)
      && CServerValid(server)

    //   && (0 <= nextActionIndex as int < 10)
      && netClient != null
      && UdpClientIsValid(netClient)
      && netClient.LocalEndPoint() == localAddr
      && netClient.LocalEndPoint() == server.endpoint
         // && CReplicaIsValid(replica)
      && Repr == { this } + UdpClientRepr(netClient)
      && msg_grammar == CMessage_grammar()
    }

    method ConstructUdpClient(ep:EndPoint, ghost env_:HostEnvironment) returns (ok:bool, client:UdpClient?)
      requires env_.Valid() && env_.ok.ok()
    //   requires CReplicaConstantsIsValid(constants)
      requires EndPointIsValidIPV4(ep)
      modifies env_.ok
      ensures ok ==> && client != null
                     && UdpClientIsValid(client)
                     && client.LocalEndPoint() == ep
                     && client.env == env_
    {
      var my_ep := ep;
      var ip_byte_array := new byte[|my_ep.addr|];
      assert EndPointIsValidIPV4(my_ep);
      seqIntoArrayOpt(my_ep.addr, ip_byte_array);
      var ip_endpoint;
      ok, ip_endpoint := IPEndPoint.Construct(ip_byte_array, my_ep.port, env_);
      if !ok { return; }
      ok, client := UdpClient.Construct(ip_endpoint, env_);
      if ok {
        calc {
          client.LocalEndPoint();
          ip_endpoint.EP();
          my_ep;
        }
      }
    }

    method Server_Init(id:int, eps:seq<EndPoint>,  ghost env_:HostEnvironment) returns (ok:bool)
        requires env_.Valid() && env_.ok.ok()
        requires 0 <= id < |eps|
        requires |eps| == Nodes
        requires forall ep :: ep in eps ==> EndPointIsValidIPV4(ep)
        // requires CReplicaConstantsIsValid(constants)
        // requires WellFormedLConfiguration(AbstractifyCReplicaConstantsToLReplicaConstants(constants).all.config)
        modifies this, netClient
        modifies env_.ok

        ensures ok ==>
                    // && Valid()
                    // && Env() == env_
                    && 0 <= this.server.next < Nodes
                    && this.server.endpoint == eps[id]
                    && this.server.next_endpoint == eps[this.server.next]
                    // && LSchedulerInit(AbstractifyToLScheduler(), AbstractifyCReplicaConstantsToLReplicaConstants(constants))
    {
        // print "Construct udp client\n";
        ok, netClient := ConstructUdpClient(eps[id], env_);
        // print "Construct udp client finish\n";

        if (ok)
        {
            // print "Start initilize server\n";
            server := CServerInit(id, eps);
            // print "Initialize server finish\n";
            localAddr := eps[id];
            // print "Initialize server finish\n";
            this.msg_grammar := CMessage_grammar();
            // print "Initialize server finish\n";

            // var vc1 := [1, 2, 3];
            // var vc2 := [4, 5, 6];
            // var deps := map[10 := vc1, 20 := vc2];
            // var read := CMessage_Read(100, 200, deps);
            // var data := MarshallData(read);
            // print "Dafny serialized data: ", data[..], "\n";
            // print "Dafny data length: ", |data[..]|, " bytes\n";
            // var read2 := DemarshallData(data, CMessage_grammar());
            // if read2.CMessage_Read? {
            // print "read2.opn_read: ", read2.opn_read, "\n";
            // print "read2.key_read: ", read2.key_read, "\n";
            // print "read2.deps_read: ", read2.deps_read, "\n";
            // }


            // var meta := CMeta(100, vc1, deps);
            // var local := map[100 := meta];
            // var write := CMessage_Write(100, 200, deps, local);
            // var data2 := MarshallData(write);
            // print "Dafny serialized data: ", data2[..], "\n";
            // print "Dafny data length: ", |data2[..]|, " bytes\n";
            // var write2 := DemarshallData(data2, CMessage_grammar());
            // if write2.CMessage_Write? {
            // print "write2.opn_write: ", write2.opn_write, "\n";
            // print "write2.key_write: ", write2.key_write, "\n";
            // print "write2.deps_write: ", write2.deps_write, "\n";
            // print "write2.local: ", write2.local, "\n";
            // }

            // var propagate := CMessage_Propagation(100, meta, 2, 1);
            // var data3 := MarshallData(propagate);
            // print "Dafny serialized data: ", data3[..], "\n";
            // print "Dafny data length: ", |data3[..]|, " bytes\n";
            // var propagate2 := DemarshallData(data3, CMessage_grammar());
            // if propagate2.CMessage_Propagation? {
            //   print "pro2.key: ", propagate2.key, "\n";
            //   print "pro2.meta: ", propagate2.meta, "\n";
            //   print "pro2.start: ", propagate2.start, "\n";
            //   print "pro2.round: ", propagate2.round, "\n";
            // }
        }
    }
}


}
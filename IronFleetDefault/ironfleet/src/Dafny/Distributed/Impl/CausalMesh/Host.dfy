include "../../Common/Framework/Host.s.dfy"
include "ServerImplMain.dfy"
include "CmdLineParser.dfy"
// include "Unsendable.i.dfy"

module Host_i refines Host_s {
import opened CmdLineParser_i
import opened CausalMesh_CmdParser_i
import opened Collections__Sets_i
import opened Common__NodeIdentity_i
import opened Common__SeqIsUnique_i
import opened Common__SeqIsUniqueDef_i
import opened CausalMesh_ServerImpl_i
import opened CausalMesh_ServerImplMain_i
import opened CausalMesh_Types_i

datatype CScheduler = CScheduler(replica_impl:ServerImpl)
type HostState = CScheduler
type ConcreteConfiguration = seq<EndPoint>

method {:timeLimitMultiplier 4} HostInitImpl(ghost env:HostEnvironment) returns (ok:bool, host_state:HostState, config:ConcreteConfiguration, ghost servers:set<EndPoint>, ghost clients:set<EndPoint>, id:EndPoint)
{
  // print "Server is initilized\n";
  var pconfig:seq<EndPoint>, my_index;
  ok, pconfig, my_index := parse_cmd_line(env);

//   var lschedule:LScheduler;
  var repImpl:ServerImpl := new ServerImpl();
  host_state := CScheduler(repImpl);

  // print "Server is initilized\n";

  if !ok { return; }
  assert env.constants == old(env.constants);
  id := pconfig[my_index];

  var scheduler := new ServerImpl();
//   var constants := InitReplicaConstantsState(id, pconfig); //SystemConfiguration(me_ep);
//   assert constants.all.config == pconfig;
//   assert constants.all.config.replica_ids[constants.my_index] == id;
//   calc {
//     constants.my_index as int;
//     { reveal SeqIsUnique(); }
//     my_index as int;
//   }

//   assert env.Valid() && env.ok.ok();
//   assert CReplicaConstantsIsValid(constants);
//   assert WellFormedLConfiguration(AbstractifyCReplicaConstantsToLReplicaConstants(constants).all.config);

  // print "Server is initilized\n";
  ok := scheduler.Server_Init(my_index, pconfig, env);
  // print "Server is initilized\n";
  // if !ok { print "Server init fail\n";return; }
  host_state := CScheduler(scheduler);
  // print "Server is initilized\n";

  config := pconfig;

  // print "Server is initilized\n";
  
  servers := set e | e in pconfig;
  clients := {};
  lemma_HostInit(host_state, env, config, servers, clients, id);
//   assert env.constants == old(env.constants);
//   ghost var args := env.constants.CommandLineArgs();
//   ghost var tuple := ParseCommandLineConfiguration(args[0..|args|-2]);
//   ghost var parsed_config, parsed_servers, parsed_clients := tuple.0, tuple.1, tuple.2;
//   assert config.config == parsed_config.config;
//   assert config.params == parsed_config.params;
//   assert config == parsed_config;
//   assert servers == parsed_servers;
//   assert clients == parsed_clients;
//   assert ConcreteConfigInit(parsed_config, parsed_servers, parsed_clients);
}

lemma {:axiom} lemma_HostInit(host_state:HostState, env:HostEnvironment, config:ConcreteConfiguration, servers:set<EndPoint>, clients:set<EndPoint>, id:EndPoint)
    ensures env.Valid() && env.ok.ok()
    ensures HostStateInvariants(host_state, env)
    ensures ConcreteConfigurationInvariants(config)
    ensures |env.constants.CommandLineArgs()| >= 2
    ensures var args := env.constants.CommandLineArgs();
                  var (parsed_config, parsed_servers, parsed_clients) := ParseCommandLineConfiguration(args[0..|args|-2]);
                  && config == parsed_config
                  && servers == parsed_servers
                  && clients == parsed_clients
                  && ConcreteConfigInit(parsed_config, parsed_servers, parsed_clients)
    ensures var args := env.constants.CommandLineArgs();
                  && id == ParseCommandLineId(args[|args|-2], args[|args|-1])
                  && HostInit(host_state, config, id);

  predicate NetEventsReductionCompatible(events:seq<UdpEvent>)
  {
    forall i :: 0 <= i < |events| - 1 ==> events[i].LIoOpReceive? || events[i+1].LIoOpSend?
  }

  predicate EventsConsistent(recvs:seq<UdpEvent>, clocks:seq<UdpEvent>, sends:seq<UdpEvent>)
  {
    forall e :: && (e in recvs  ==> e.LIoOpReceive?)
                && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?)
                && (e in sends  ==> e.LIoOpSend?)
  }

  ghost method RemoveRecvs(events:seq<UdpEvent>) returns (recvs:seq<UdpEvent>, rest:seq<UdpEvent>)
    ensures forall e :: e in recvs ==> e.LIoOpReceive?
    ensures events == recvs + rest
    ensures rest != [] ==> !rest[0].LIoOpReceive?
    ensures NetEventsReductionCompatible(events) ==> NetEventsReductionCompatible(rest);
  {
    recvs := [];
    rest := [];

    var i := 0;
    while i < |events|
      invariant 0 <= i <= |events|
      invariant forall e :: e in recvs ==> e.LIoOpReceive?
      //invariant events == recvs + events[i..]
      invariant recvs == events[0..i]
    {
      if !events[i].LIoOpReceive? {
        rest := events[i..];
        return;
      }
      recvs := recvs + [events[i]];
      i := i + 1;
    }
  }

  lemma lemma_RemainingEventsAreSends(events:seq<UdpEvent>)
    requires NetEventsReductionCompatible(events)
    requires |events| > 0
    requires !events[0].LIoOpReceive?
    ensures  forall e :: e in events[1..] ==> e.LIoOpSend?
  {
    if |events| == 1 {
    } else {
      assert events[1].LIoOpSend?;
      lemma_RemainingEventsAreSends(events[1..]);
    }
  }

  ghost method PartitionEvents(events:seq<UdpEvent>) returns (recvs:seq<UdpEvent>, clocks:seq<UdpEvent>, sends:seq<UdpEvent>)
    requires NetEventsReductionCompatible(events)
    ensures  events == recvs + clocks + sends
    ensures  EventsConsistent(recvs, clocks, sends)
    ensures  |clocks| <= 1
  {
    var rest;
    recvs, rest := RemoveRecvs(events);
    assert NetEventsReductionCompatible(rest);
    if |rest| > 0 && (rest[0].LIoOpReadClock? || rest[0].LIoOpTimeoutReceive?) {
      clocks := [rest[0]];
      sends := rest[1..];
      lemma_RemainingEventsAreSends(rest);
    } else {
      clocks := [];
      sends := rest;
      if |rest| > 0 {
        lemma_RemainingEventsAreSends(rest);
      }
    }
  }

  predicate ConcreteConfigurationInvariants(config:ConcreteConfiguration)
  {
    (forall e :: e in config ==> EndPointIsValid(e))
  }

  predicate ConcreteConfigInit(config:ConcreteConfiguration, servers:set<EndPoint>, clients:set<EndPoint>)
  {
    && (forall e :: e in config ==> EndPointIsAbstractable(e))
    && MapSeqToSet(config, x=>x) == servers
    && (forall e :: e in servers ==> EndPointIsAbstractable(e))
    && (forall e :: e in clients ==> EndPointIsAbstractable(e))
  }

  function ParseCommandLineConfiguration(args:seq<seq<uint16>>) : (ConcreteConfiguration, set<EndPoint>, set<EndPoint>)
  {
    var cm_config := causalmesh_config_parsing(args);
    var endpoints_set := (set e{:trigger e in cm_config} | e in cm_config);
    (cm_config, endpoints_set, {})
  }

  function paxos_parse_id(ip:seq<uint16>, port:seq<uint16>) : EndPoint
  {
    var (ok, ep) := parse_end_point(ip, port);
    ep
  }

  function ParseCommandLineId(ip:seq<uint16>, port:seq<uint16>) : EndPoint
  {
    paxos_parse_id(ip, port)
  }

  predicate HostStateInvariants(host_state:HostState, env:HostEnvironment)
  {
    && host_state.replica_impl.Valid()
    // && host_state.replica_impl.Env() == env
    // && host_state.sched == host_state.replica_impl.AbstractifyToLScheduler()
  }

  predicate HostInit(host_state:HostState, config:ConcreteConfiguration, id:EndPoint)
  {
    && host_state.replica_impl.Valid()
  }

  predicate HostNext(host_state:HostState, host_state':HostState, ios:seq<LIoOp<EndPoint, seq<byte>>>)
  {
    true
    // && UdpEventLogIsAbstractable(ios)
    // && OnlySentMarshallableData(ios)
    // && (|| LSchedulerNext(host_state.sched, host_state'.sched, AbstractifyRawLogToIos(ios))
    //     || HostNextIgnoreUnsendable(host_state.sched, host_state'.sched, ios))
  }

method {:timeLimitMultiplier 3} HostNextImpl(ghost env:HostEnvironment, host_state:HostState)
returns (ok:bool, host_state':HostState,
ghost recvs:seq<UdpEvent>, ghost clocks:seq<UdpEvent>, ghost sends:seq<UdpEvent>,
ghost ios:seq<LIoOp<EndPoint, seq<byte>>>)
{
//   var lschedule:LScheduler;
  ghost var old_history := env.udp.history();

  var repImpl:ServerImpl := new ServerImpl();
  host_state' := CScheduler(repImpl);

  // print "Server is working\n";

  var okay/*, netEventLog, abstract_ios*/ := Server_Next_main(host_state.replica_impl);
  var netEventLog := [];
//   var abstract_ios := [];
  if okay {
    // calc {
    //   Q_LScheduler_Next(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios);
    //   { reveal Q_LScheduler_Next(); }
    //   LSchedulerNext(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios);
    // }

    // assert AbstractifyRawLogToIos(netEventLog) == abstract_ios;
    // if LSchedulerNext(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios)
    // {
    //   lemma_ProtocolIosRespectReduction(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios);
    // }
    // lemma_NetEventsRespectReduction(host_state.sched, host_state.replica_impl.AbstractifyToLScheduler(), abstract_ios, netEventLog);
    recvs, clocks, sends := PartitionEvents(netEventLog);
    ios := recvs + clocks + sends; //abstract_ios;
    assert ios == netEventLog;
    host_state' := CScheduler(host_state.replica_impl);
    lemma_HostNext(okay, old(env), old(env.udp.history()), env, host_state, host_state', recvs, clocks, sends, ios);
    assert env.Valid() && env.ok.ok();
    assert HostStateInvariants(host_state, env);
    assert okay <==> env.Valid() && env.ok.ok();
    assert okay ==> HostStateInvariants(host_state', env);
    assert okay ==> HostNext(host_state, host_state', ios);
    assert okay ==> recvs + clocks + sends == ios;
    assert okay ==> env.udp.history() == old(env).udp.history() + (recvs + clocks + sends);
    // assert old(env).udp.history() == old(env.udp.history());
    assert okay ==> env.udp.history() == old(env.udp.history()) + (recvs + clocks + sends);
    // assert okay ==> env.udp.history() == old_history + (recvs + clocks + sends);

  } else {
    recvs := [];
    clocks := [];
    sends := [];
    ios := [];
    lemma_HostNext(okay, old(env), old(env.udp.history()), env, host_state, host_state', recvs, clocks, sends, ios);
    assert okay <==> env.Valid() && env.ok.ok();
  }
  ok := okay;
//   reveal Q_LScheduler_Next();
//   assert host_state.replica_impl.Env() == env;
}

lemma {:axiom} lemma_HostNext(
  okay:bool,
  env:HostEnvironment,
  his:seq<UdpEvent>,
  env':HostEnvironment,
  host_state:HostState,
  host_state':HostState,
  recvs:seq<UdpEvent>,
  clocks:seq<UdpEvent>,
  sends:seq<UdpEvent>, 
  ios:seq<LIoOp<EndPoint, seq<byte>>>
)
    // requires env.Valid() && env.ok.ok()
    // requires HostStateInvariants(host_state, env)
    ensures okay <==> env'.Valid() && env'.ok.ok()
    ensures okay ==> HostStateInvariants(host_state', env')
    ensures okay ==> HostNext(host_state, host_state', ios)
    ensures okay ==> recvs + clocks + sends == ios
    ensures okay ==> env'.udp.history() == his + (recvs + clocks + sends)
    ensures  forall e :: && (e in recvs ==> e.LIoOpReceive?) 
                 && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) 
                 && (e in sends ==> e.LIoOpSend?)
    ensures |clocks| <= 1

}
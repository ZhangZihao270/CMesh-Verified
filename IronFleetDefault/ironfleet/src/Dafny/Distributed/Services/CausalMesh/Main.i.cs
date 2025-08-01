// Dafny program Main.i.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 3.13.1.50302
// Command Line Options: /compile:0 /spillTargetCode:3 /noVerify src/Dafny/Distributed/Services/CausalMesh/Main.i.dfy
// Main.i.dfy


module Main_i refines Main_s {

  import opened Native__NativeTypes_s

  import opened Host = Host_i

  import opened DS_s = CM_DistributedSystem_i

  import opened Concrete_NodeIdentity_i

  import opened Collections__Maps2_s

  import opened Collections__Sets_i

  import opened Common__GenericMarshalling_i

  import opened Common__NodeIdentity_i

  import opened Common__SeqIsUniqueDef_i

  import opened Environment_s

  import opened Math__mod_auto_i
  method {:main} Main(ghost env: HostEnvironment)
    requires env.Valid() && env.ok.ok()
    requires env.udp.history() == []
    requires |env.constants.CommandLineArgs()| >= 2
    modifies set x: object {:trigger DS_s.H_s.ArbitraryObject(x)} | DS_s.H_s.ArbitraryObject(x)
    decreases *
  {
    var ok, host_state, config, servers, clients, id := DS_s.H_s.HostInitImpl(env);
    assert ok ==> DS_s.H_s.HostInit(host_state, config, id);
    while ok
      invariant ok ==> DS_s.H_s.HostStateInvariants(host_state, env)
      invariant ok ==> env.Valid() && env.ok.ok()
      decreases *
    {
      ghost var old_udp_history := env.udp.history();
      ghost var old_state := host_state;
      ghost var recvs, clocks, sends, ios;
      ok, host_state, recvs, clocks, sends, ios := DS_s.H_s.HostNextImpl(env, host_state);
      if ok {
        assert DS_s.H_s.HostNext(old_state, host_state, ios);
        assert recvs + clocks + sends == ios;
        assert env.udp.history() == old_udp_history + recvs + clocks + sends;
        assert forall e: LIoOp<EndPoint, seq<byte>> {:trigger e.LIoOpSend?} {:trigger e in sends} {:trigger e.LIoOpTimeoutReceive?} {:trigger e.LIoOpReadClock?} {:trigger e in clocks} {:trigger e.LIoOpReceive?} {:trigger e in recvs} :: (e in recvs ==> e.LIoOpReceive?) && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) && (e in sends ==> e.LIoOpSend?);
        assert |clocks| <= 1;
      }
    }
  }

  import opened Native__Io_s

  import opened AS_s : AbstractService_s

  import opened Collections__Seqs_s
}

abstract module Main_s {

  import opened Native__Io_s

  import opened DS_s : DistributedSystem_s

  import opened AS_s : AbstractService_s

  import opened Collections__Seqs_s
  method {:main} Main(ghost env: HostEnvironment)
    requires env.Valid() && env.ok.ok()
    requires env.udp.history() == []
    requires |env.constants.CommandLineArgs()| >= 2
    modifies set x: object {:trigger DS_s.H_s.ArbitraryObject(x)} | DS_s.H_s.ArbitraryObject(x)
    decreases *
  {
    var ok, host_state, config, servers, clients, id := DS_s.H_s.HostInitImpl(env);
    assert ok ==> DS_s.H_s.HostInit(host_state, config, id);
    while ok
      invariant ok ==> DS_s.H_s.HostStateInvariants(host_state, env)
      invariant ok ==> env.Valid() && env.ok.ok()
      decreases *
    {
      ghost var old_udp_history := env.udp.history();
      ghost var old_state := host_state;
      ghost var recvs, clocks, sends, ios;
      ok, host_state, recvs, clocks, sends, ios := DS_s.H_s.HostNextImpl(env, host_state);
      if ok {
        assert DS_s.H_s.HostNext(old_state, host_state, ios);
        assert recvs + clocks + sends == ios;
        assert env.udp.history() == old_udp_history + recvs + clocks + sends;
        assert forall e: LIoOp<EndPoint, seq<byte>> {:trigger e.LIoOpSend?} {:trigger e in sends} {:trigger e.LIoOpTimeoutReceive?} {:trigger e.LIoOpReadClock?} {:trigger e in clocks} {:trigger e.LIoOpReceive?} {:trigger e in recvs} :: (e in recvs ==> e.LIoOpReceive?) && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) && (e in sends ==> e.LIoOpSend?);
        assert |clocks| <= 1;
      }
    }
  }
}

module Native__Io_s {

  import opened Native__NativeTypes_s

  import opened Environment_s
  class HostEnvironment {
    ghost var constants: HostConstants
    ghost var ok: OkState
    ghost var now: NowState
    ghost var udp: UdpState
    ghost var files: FileSystemState

    constructor {:axiom} ()
      requires false

    predicate Valid()
      reads this
      decreases {this}
    {
      true
    }
  }

  class HostConstants {
    constructor {:axiom} ()
      requires false

    function {:axiom} LocalAddress(): seq<byte>
      reads this
      decreases {this}

    function {:axiom} CommandLineArgs(): seq<seq<uint16>>
      reads this
      decreases {this}

    static method {:axiom} NumCommandLineArgs(ghost env: HostEnvironment) returns (n: uint32)
      requires env.Valid()
      ensures n as int == |env.constants.CommandLineArgs()|
      decreases env

    static method {:axiom} GetCommandLineArg(i: uint64, ghost env: HostEnvironment) returns (arg: array<uint16>)
      requires env.Valid()
      requires 0 <= i as int < |env.constants.CommandLineArgs()|
      ensures fresh(arg)
      ensures arg[..] == env.constants.CommandLineArgs()[i]
      decreases i, env
  }

  class OkState {
    constructor {:axiom} ()
      requires false

    function {:axiom} ok(): bool
      reads this
      decreases {this}
  }

  class NowState {
    constructor {:axiom} ()
      requires false

    function {:axiom} now(): int
      reads this
      decreases {this}
  }

  class Time {
    static method {:axiom} GetTime(ghost env: HostEnvironment) returns (t: uint64)
      requires env.Valid()
      modifies env.now, env.udp
      ensures t as int == env.now.now()
      ensures AdvanceTime(old(env.now.now()), env.now.now(), 0)
      ensures env.udp.history() == old(env.udp.history()) + [LIoOpReadClock(t as int)]
      decreases env

    static method {:axiom} GetDebugTimeTicks() returns (t: uint64)

    static method {:axiom} RecordTiming(name: array<char>, time: uint64)
      decreases name, time
  }

  datatype EndPoint = EndPoint(addr: seq<byte>, port: uint16)

  type UdpPacket = LPacket<EndPoint, seq<byte>>

  type UdpEvent = LIoOp<EndPoint, seq<byte>>

  class UdpState {
    constructor {:axiom} ()
      requires false

    function {:axiom} history(): seq<UdpEvent>
      reads this
      decreases {this}
  }

  class IPEndPoint {
    ghost var env: HostEnvironment

    function {:axiom} Address(): seq<byte>
      reads this
      decreases {this}

    function {:axiom} Port(): uint16
      reads this
      decreases {this}

    function EP(): EndPoint
      reads this
      decreases {this}
    {
      EndPoint(Address(), Port())
    }

    constructor {:axiom} ()
      requires false

    method {:axiom} GetAddress() returns (addr: array<byte>)
      ensures fresh(addr)
      ensures addr[..] == Address()
      ensures addr.Length == 4

    function method {:axiom} GetPort(): uint16
      reads this
      ensures GetPort() == Port()
      decreases {this}

    static method {:axiom} Construct(ipAddress: array<byte>, port: uint16, ghost env: HostEnvironment)
        returns (ok: bool, ep: IPEndPoint)
      requires env.Valid()
      modifies env.ok
      ensures env.ok.ok() == ok
      ensures ok ==> fresh(ep) && ep.env == env && ep.Address() == ipAddress[..] && ep.Port() == port
      decreases ipAddress, port, env
  }

  class UdpClient {
    ghost var env: HostEnvironment

    function {:axiom} LocalEndPoint(): EndPoint
      reads this
      decreases {this}

    function {:axiom} IsOpen(): bool
      reads this
      decreases {this}

    constructor {:axiom} ()
      requires false

    static method {:axiom} Construct(localEP: IPEndPoint, ghost env: HostEnvironment)
        returns (ok: bool, udp: UdpClient?)
      requires env.Valid()
      requires env.ok.ok()
      modifies env.ok
      ensures env.ok.ok() == ok
      ensures ok ==> fresh(udp) && udp.env == env && udp.IsOpen() && udp.LocalEndPoint() == localEP.EP()
      decreases localEP, env

    method {:axiom} Close() returns (ok: bool)
      requires env.Valid()
      requires env.ok.ok()
      requires this.IsOpen()
      modifies this, env.ok
      ensures env == old(env)
      ensures env.ok.ok() == ok

    method {:axiom} Receive(timeLimit: int32)
        returns (ok: bool, timedOut: bool, remote: IPEndPoint, buffer: array<byte>)
      requires env.Valid()
      requires env.ok.ok()
      requires IsOpen()
      requires timeLimit >= 0
      requires timeLimit as int * 1000 < 2147483648
      modifies this, env.ok, env.now, env.udp
      ensures env == old(env)
      ensures env.ok.ok() == ok
      ensures AdvanceTime(old(env.now.now()), env.now.now(), timeLimit as int)
      ensures LocalEndPoint() == old(LocalEndPoint())
      ensures ok ==> IsOpen()
      ensures ok ==> timedOut ==> env.udp.history() == old(env.udp.history()) + [LIoOpTimeoutReceive()]
      ensures ok ==> !timedOut ==> fresh(remote) && fresh(buffer) && env.udp.history() == old(env.udp.history()) + [LIoOpReceive(LPacket(LocalEndPoint(), remote.EP(), buffer[..]))] && buffer.Length < 18446744073709551616
      decreases timeLimit

    method {:axiom} Send(remote: IPEndPoint, buffer: array<byte>) returns (ok: bool)
      requires env.Valid()
      requires env.ok.ok()
      requires IsOpen()
      requires buffer.Length <= MaxPacketSize()
      modifies this, env.ok, env.udp
      ensures env == old(env)
      ensures env.ok.ok() == ok
      ensures LocalEndPoint() == old(LocalEndPoint())
      ensures ok ==> IsOpen()
      ensures ok ==> env.udp.history() == old(env.udp.history()) + [LIoOpSend(LPacket(remote.EP(), LocalEndPoint(), buffer[..]))]
      decreases remote, buffer
  }

  class FileSystemState { }

  class MutableSet<T(==,0,!new)> {
    static function method {:axiom} SetOf(s: MutableSet<T>): set<T>
      reads s
      decreases {s}, s

    static method {:axiom} EmptySet() returns (s: MutableSet<T>)
      ensures SetOf(s) == {}
      ensures fresh(s)

    constructor {:axiom} ()
      requires false

    method {:axiom} Size() returns (size: int)
      ensures size == |SetOf(this)|

    method {:axiom} SizeModest() returns (size: uint64)
      requires |SetOf(this)| < 18446744073709551616
      ensures size as int == |SetOf(this)|

    method {:axiom} Contains(x: T) returns (contains: bool)
      ensures contains == (x in SetOf(this))

    method {:axiom} Add(x: T)
      modifies this
      ensures SetOf(this) == old(SetOf(this)) + {x}

    method {:axiom} AddSet(s: MutableSet<T>)
      modifies this
      ensures SetOf(this) == old(SetOf(this)) + old(SetOf(s))
      decreases s

    method {:axiom} TransferSet(s: MutableSet<T>)
      modifies this, s
      ensures SetOf(this) == old(SetOf(s))
      ensures SetOf(s) == {}
      decreases s

    method {:axiom} Remove(x: T)
      modifies this
      ensures SetOf(this) == old(SetOf(this)) - {x}

    method {:axiom} RemoveAll()
      modifies this
      ensures SetOf(this) == {}
  }

  class MutableMap<K(==), V> {
    static function method {:axiom} MapOf(m: MutableMap<K, V>): map<K, V>
      reads m
      decreases {m}, m

    static method {:axiom} EmptyMap() returns (m: MutableMap<K, V>)
      ensures MapOf(m) == map[]
      ensures fresh(m)

    static method {:axiom} FromMap(dafny_map: map<K, V>) returns (m: MutableMap<K, V>)
      ensures MapOf(m) == dafny_map
      ensures fresh(m)
      decreases dafny_map

    constructor {:axiom} ()
      requires false

    function method {:axiom} Size(): int
      reads this
      ensures this.Size() == |MapOf(this)|
      decreases {this}

    method {:axiom} SizeModest() returns (size: uint64)
      requires |MapOf(this)| < 18446744073709551616
      ensures size as int == |MapOf(this)|

    method {:axiom} Contains(key: K) returns (contains: bool)
      ensures contains == (key in MapOf(this))

    method {:axiom} TryGetValue(key: K) returns (contains: bool, val: V)
      ensures contains == (key in MapOf(this))
      ensures contains ==> val == MapOf(this)[key]

    method {:axiom} Set(key: K, val: V)
      modifies this
      ensures MapOf(this) == old(MapOf(this))[key := val]

    method {:axiom} Remove(key: K)
      modifies this
      ensures MapOf(this) == map k: K {:trigger old(MapOf(this))[k]} {:trigger k in old(MapOf(this))} | k != key && k in old(MapOf(this)) :: old(MapOf(this))[k]
  }

  class Arrays {
    static method {:axiom} CopySeqIntoArray<A>(src: seq<A>, srcIndex: uint64, dst: array<A>, dstIndex: uint64, len: uint64)
      requires srcIndex as int + len as int <= |src|
      requires dstIndex as int + len as int <= dst.Length
      modifies dst
      ensures forall i: int {:trigger old(dst[..])[i]} {:trigger dst[i]} :: 0 <= i < dst.Length ==> dst[i] == if dstIndex as int <= i < dstIndex as int + len as int then src[i - dstIndex as int + srcIndex as int] else old(dst[..])[i]
      ensures forall i: int {:trigger src[i]} :: srcIndex as int <= i < srcIndex as int + len as int ==> src[i] == dst[i - srcIndex as int + dstIndex as int]
      decreases src, srcIndex, dst, dstIndex, len
  }

  function {:axiom} realTimeBound(): int

  predicate AdvanceTime(oldTime: int, newTime: int, delay: int)
    decreases oldTime, newTime, delay
  {
    oldTime <= newTime < oldTime + delay + realTimeBound()
  }

  function MaxPacketSize(): int
  {
    18446744073709551615
  }
}

module Native__NativeTypes_s {
  newtype {:nativeType ""sbyte""} sbyte = i: int
    | -128 <= i < 128

  newtype {:nativeType ""byte""} byte = i: int
    | 0 <= i < 256

  newtype {:nativeType ""short""} int16 = i: int
    | -32768 <= i < 32768

  newtype {:nativeType ""ushort""} uint16 = i: int
    | 0 <= i < 65536

  newtype {:nativeType ""int""} int32 = i: int
    | -2147483648 <= i < 2147483648

  newtype {:nativeType ""uint""} uint32 = i: int
    | 0 <= i < 4294967296

  newtype {:nativeType ""long""} int64 = i: int
    | -9223372036854775808 <= i < 9223372036854775808

  newtype {:nativeType ""ulong""} uint64 = i: int
    | 0 <= i < 18446744073709551616

  newtype {:nativeType ""sbyte""} nat8 = i: int
    | 0 <= i < 128

  newtype {:nativeType ""short""} nat16 = i: int
    | 0 <= i < 32768

  newtype {:nativeType ""int""} nat32 = i: int
    | 0 <= i < 2147483648

  newtype {:nativeType ""long""} nat64 = i: int
    | 0 <= i < 9223372036854775808
}

module Environment_s {

  import opened Collections__Maps2_s

  import opened Temporal__Temporal_s
  datatype LPacket<IdType, MessageType(==)> = LPacket(dst: IdType, src: IdType, msg: MessageType)

  datatype LIoOp<IdType, MessageType(==)> = LIoOpSend(s: LPacket<IdType, MessageType>) | LIoOpReceive(r: LPacket<IdType, MessageType>) | LIoOpTimeoutReceive | LIoOpReadClock(t: int)

  datatype LEnvStep<IdType, MessageType(==)> = LEnvStepHostIos(actor: IdType, ios: seq<LIoOp<IdType, MessageType>>) | LEnvStepDeliverPacket(p: LPacket<IdType, MessageType>) | LEnvStepAdvanceTime | LEnvStepStutter

  datatype LHostInfo<IdType, MessageType(==)> = LHostInfo(queue: seq<LPacket<IdType, MessageType>>)

  datatype LEnvironment<IdType, MessageType(==)> = LEnvironment(time: int, sentPackets: set<LPacket<IdType, MessageType>>, hostInfo: map<IdType, LHostInfo<IdType, MessageType>>, nextStep: LEnvStep<IdType, MessageType>)

  predicate IsValidLIoOp<IdType, MessageType>(io: LIoOp<IdType, MessageType>, actor: IdType, e: LEnvironment<IdType, MessageType>)
    decreases io, e
  {
    match io
    case LIoOpSend(s) =>
      s.src == actor
    case LIoOpReceive(r) =>
      r.dst == actor
    case LIoOpTimeoutReceive() =>
      true
    case LIoOpReadClock(t) =>
      true
  }

  predicate LIoOpOrderingOKForAction<IdType, MessageType>(io1: LIoOp<IdType, MessageType>, io2: LIoOp<IdType, MessageType>)
    decreases io1, io2
  {
    io1.LIoOpReceive? || io2.LIoOpSend?
  }

  predicate LIoOpSeqCompatibleWithReduction<IdType, MessageType>(ios: seq<LIoOp<IdType, MessageType>>)
    decreases ios
  {
    forall i: int {:trigger ios[i], ios[i + 1]} :: 
      0 <= i < |ios| - 1 ==>
        LIoOpOrderingOKForAction(ios[i], ios[i + 1])
  }

  predicate IsValidLEnvStep<IdType, MessageType>(e: LEnvironment<IdType, MessageType>, step: LEnvStep<IdType, MessageType>)
    decreases e, step
  {
    match step
    case LEnvStepHostIos(actor, ios) =>
      (forall io: LIoOp<IdType, MessageType> {:trigger IsValidLIoOp(io, actor, e)} {:trigger io in ios} :: 
        io in ios ==>
          IsValidLIoOp(io, actor, e)) &&
      LIoOpSeqCompatibleWithReduction(ios)
    case LEnvStepDeliverPacket(p) =>
      p in e.sentPackets
    case LEnvStepAdvanceTime() =>
      true
    case LEnvStepStutter() =>
      true
  }

  predicate LEnvironment_Init<IdType, MessageType>(e: LEnvironment<IdType, MessageType>)
    decreases e
  {
    |e.sentPackets| == 0 &&
    e.time >= 0
  }

  predicate LEnvironment_PerformIos<IdType, MessageType>(e: LEnvironment<IdType, MessageType>, e': LEnvironment<IdType, MessageType>, actor: IdType, ios: seq<LIoOp<IdType, MessageType>>)
    decreases e, e', ios
  {
    e'.sentPackets == e.sentPackets + (set io: LIoOp<IdType, MessageType> {:trigger io.s} {:trigger io.LIoOpSend?} {:trigger io in ios} | io in ios && io.LIoOpSend? :: io.s) &&
    (forall io: LIoOp<IdType, MessageType> {:trigger io.r} {:trigger io.LIoOpReceive?} {:trigger io in ios} :: 
      io in ios &&
      io.LIoOpReceive? ==>
        io.r in e.sentPackets) &&
    e'.time == e.time
  }

  predicate LEnvironment_AdvanceTime<IdType, MessageType>(e: LEnvironment<IdType, MessageType>, e': LEnvironment<IdType, MessageType>)
    decreases e, e'
  {
    e'.time > e.time &&
    e'.sentPackets == e.sentPackets
  }

  predicate LEnvironment_Stutter<IdType, MessageType>(e: LEnvironment<IdType, MessageType>, e': LEnvironment<IdType, MessageType>)
    decreases e, e'
  {
    e'.time == e.time &&
    e'.sentPackets == e.sentPackets
  }

  predicate LEnvironment_Next<IdType, MessageType>(e: LEnvironment<IdType, MessageType>, e': LEnvironment<IdType, MessageType>)
    decreases e, e'
  {
    IsValidLEnvStep(e, e.nextStep) &&
    match e.nextStep case LEnvStepHostIos(actor, ios) => LEnvironment_PerformIos(e, e', actor, ios) case LEnvStepDeliverPacket(p) => LEnvironment_Stutter(e, e') case LEnvStepAdvanceTime => LEnvironment_AdvanceTime(e, e') case LEnvStepStutter => LEnvironment_Stutter(e, e')
  }

  function {:opaque} {:fuel 0, 0} EnvironmentNextTemporal<IdType, MessageType>(b: Behavior<LEnvironment<IdType, MessageType>>): temporal
    requires imaptotal(b)
    ensures forall i: int {:trigger sat(i, EnvironmentNextTemporal(b))} :: sat(i, EnvironmentNextTemporal(b)) <==> LEnvironment_Next(b[i], b[nextstep(i)])
  {
    stepmap(imap i: int {:trigger nextstep(i)} | true :: LEnvironment_Next(b[i], b[nextstep(i)]))
  }

  predicate LEnvironment_BehaviorSatisfiesSpec<IdType, MessageType>(b: Behavior<LEnvironment<IdType, MessageType>>)
  {
    imaptotal(b) &&
    LEnvironment_Init(b[0]) &&
    sat(0, always(EnvironmentNextTemporal(b)))
  }
}

module Collections__Maps2_s {
  function method mapdomain<KT, VT>(m: map<KT, VT>): set<KT>
    decreases m
  {
    set k: KT {:trigger k in m} | k in m :: k
  }

  function method mapremove<KT, VT>(m: map<KT, VT>, k: KT): map<KT, VT>
    decreases m
  {
    map ki: KT {:trigger m[ki]} {:trigger ki in m} | ki in m && ki != k :: m[ki]
  }

  predicate imaptotal<KT(!new), VT>(m: imap<KT, VT>)
  {
    forall k: KT {:trigger m[k]} {:trigger k in m} :: 
      k in m
  }
}

module Temporal__Temporal_s {

  import opened Collections__Maps2_s
  type temporal = imap<int, bool>

  type Behavior<S> = imap<int, S>

  function stepmap(f: imap<int, bool>): temporal
    ensures forall i: int {:trigger f[i]} {:trigger sat(i, stepmap(f))} {:trigger i in f} :: i in f ==> sat(i, stepmap(f)) == f[i]
  {
    f
  }

  predicate sat(s: int, t: temporal)
    decreases s
  {
    s in t &&
    t[s]
  }

  function {:opaque} {:fuel 0, 0} and(x: temporal, y: temporal): temporal
    ensures forall i: int {:trigger sat(i, and(x, y))} :: sat(i, and(x, y)) == (sat(i, x) && sat(i, y))
  {
    stepmap(imap i: int {:trigger sat(i, y)} {:trigger sat(i, x)} | true :: sat(i, x) && sat(i, y))
  }

  function {:opaque} {:fuel 0, 0} or(x: temporal, y: temporal): temporal
    ensures forall i: int {:trigger sat(i, or(x, y))} :: sat(i, or(x, y)) == (sat(i, x) || sat(i, y))
  {
    stepmap(imap i: int {:trigger sat(i, y)} {:trigger sat(i, x)} | true :: sat(i, x) || sat(i, y))
  }

  function {:opaque} {:fuel 0, 0} imply(x: temporal, y: temporal): temporal
    ensures forall i: int {:trigger sat(i, imply(x, y))} :: sat(i, imply(x, y)) == (sat(i, x) ==> sat(i, y))
  {
    stepmap(imap i: int {:trigger sat(i, y)} {:trigger sat(i, x)} | true :: sat(i, x) ==> sat(i, y))
  }

  function {:opaque} {:fuel 0, 0} equiv(x: temporal, y: temporal): temporal
    ensures forall i: int {:trigger sat(i, equiv(x, y))} :: sat(i, equiv(x, y)) == (sat(i, x) <==> sat(i, y))
  {
    stepmap(imap i: int {:trigger sat(i, y)} {:trigger sat(i, x)} | true :: sat(i, x) <==> sat(i, y))
  }

  function {:opaque} {:fuel 0, 0} not(x: temporal): temporal
    ensures forall i: int {:trigger sat(i, not(x))} :: sat(i, not(x)) == !sat(i, x)
  {
    stepmap(imap i: int {:trigger sat(i, x)} | true :: !sat(i, x))
  }

  function nextstep(i: int): int
    decreases i
  {
    i + 1
  }

  function {:opaque} {:fuel 0, 0} next(x: temporal): temporal
    ensures forall i: int {:trigger sat(i, next(x))} :: sat(i, next(x)) == sat(nextstep(i), x)
  {
    stepmap(imap i: int {:trigger nextstep(i)} | true :: sat(nextstep(i), x))
  }

  function {:opaque} {:fuel 0, 0} always(x: temporal): temporal
  {
    stepmap(imap i: int {:trigger sat(i, always(x))} | true :: forall j: int {:trigger sat(j, x)} :: i <= j ==> sat(j, x))
  }

  function {:opaque} {:fuel 0, 0} eventual(x: temporal): temporal
  {
    stepmap(imap i: int {:trigger sat(i, eventual(x))} | true :: exists j: int {:trigger sat(j, x)} :: i <= j && sat(j, x))
  }
}

abstract module DistributedSystem_s {

  import H_s : Host_s

  import opened Collections__Maps2_s

  import opened Native__Io_s

  import opened Environment_s

  import opened Native__NativeTypes_s
  datatype DS_State = DS_State(config: H_s.ConcreteConfiguration, environment: LEnvironment<EndPoint, seq<byte>>, servers: map<EndPoint, H_s.HostState>, clients: set<EndPoint>)

  predicate ValidPhysicalAddress(endPoint: EndPoint)
    decreases endPoint
  {
    |endPoint.addr| == 4 &&
    0 <= endPoint.port <= 65535
  }

  predicate ValidPhysicalPacket(p: LPacket<EndPoint, seq<byte>>)
    decreases p
  {
    ValidPhysicalAddress(p.src) &&
    ValidPhysicalAddress(p.dst) &&
    |p.msg| < 18446744073709551616
  }

  predicate ValidPhysicalIo(io: LIoOp<EndPoint, seq<byte>>)
    decreases io
  {
    (io.LIoOpReceive? ==>
      ValidPhysicalPacket(io.r)) &&
    (io.LIoOpSend? ==>
      ValidPhysicalPacket(io.s))
  }

  predicate ValidPhysicalEnvironmentStep(step: LEnvStep<EndPoint, seq<byte>>)
    decreases step
  {
    step.LEnvStepHostIos? ==>
      forall io: LIoOp<EndPoint, seq<byte>> {:trigger io in step.ios} {:trigger ValidPhysicalIo(io)} :: 
        io in step.ios ==>
          ValidPhysicalIo(io)
  }

  predicate DS_Init(s: DS_State, config: H_s.ConcreteConfiguration)
    reads *
    decreases {}, s
  {
    s.config == config &&
    H_s.ConcreteConfigInit(s.config, mapdomain(s.servers), s.clients) &&
    LEnvironment_Init(s.environment) &&
    forall id: EndPoint {:trigger s.servers[id]} {:trigger id in s.servers} :: 
      id in s.servers ==>
        _default.HostInit(s.servers[id], config, id)
  }

  predicate DS_NextOneServer(s: DS_State, s': DS_State, id: EndPoint, ios: seq<LIoOp<EndPoint, seq<byte>>>)
    requires id in s.servers
    reads *
    decreases {}, s, s', id, ios
  {
    id in s'.servers &&
    H_s.HostNext(s.servers[id], s'.servers[id], ios) &&
    s'.servers == s.servers[id := s'.servers[id]]
  }

  predicate DS_Next(s: DS_State, s': DS_State)
    reads *
    decreases {}, s, s'
  {
    s'.config == s.config &&
    s'.clients == s.clients &&
    LEnvironment_Next(s.environment, s'.environment) &&
    ValidPhysicalEnvironmentStep(s.environment.nextStep) &&
    if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers then DS_NextOneServer(s, s', s.environment.nextStep.actor, s.environment.nextStep.ios) else s'.servers == s.servers
  }
}

abstract module Host_s {

  import opened Native__Io_s

  import opened Environment_s

  import opened Native__NativeTypes_s
  type HostState

  type ConcreteConfiguration

  predicate HostInit(host_state: HostState, config: ConcreteConfiguration, id: EndPoint)
    reads *
    decreases {}, id

  predicate HostNext(host_state: HostState, host_state': HostState, ios: seq<LIoOp<EndPoint, seq<byte>>>)
    reads *
    decreases {}, ios

  predicate ConcreteConfigInit(config: ConcreteConfiguration, servers: set<EndPoint>, clients: set<EndPoint>)
    decreases servers, clients

  predicate HostStateInvariants(host_state: HostState, env: HostEnvironment)
    reads *
    decreases {}, env

  predicate ConcreteConfigurationInvariants(config: ConcreteConfiguration)

  function ParseCommandLineConfiguration(args: seq<seq<uint16>>): (ConcreteConfiguration, set<EndPoint>, set<EndPoint>)
    decreases args

  function ParseCommandLineId(ip: seq<uint16>, port: seq<uint16>): EndPoint
    decreases ip, port

  predicate ArbitraryObject(o: object)
    decreases o
  {
    true
  }

  method HostInitImpl(ghost env: HostEnvironment)
      returns (ok: bool, host_state: HostState, config: ConcreteConfiguration, ghost servers: set<EndPoint>, ghost clients: set<EndPoint>, id: EndPoint)
    requires env.Valid()
    requires env.ok.ok()
    requires |env.constants.CommandLineArgs()| >= 2
    modifies set x: object {:trigger ArbitraryObject(x)} | ArbitraryObject(x)
    ensures ok ==> env.Valid() && env.ok.ok()
    ensures ok ==> |env.constants.CommandLineArgs()| >= 2
    ensures ok ==> HostStateInvariants(host_state, env)
    ensures ok ==> ConcreteConfigurationInvariants(config)
    ensures ok ==> var args: seq<seq<uint16>> := env.constants.CommandLineArgs(); var (parsed_config: ConcreteConfiguration, parsed_servers: set<EndPoint>, parsed_clients: set<EndPoint>) := ParseCommandLineConfiguration(args[0 .. |args| - 2]); config == parsed_config && servers == parsed_servers && clients == parsed_clients && ConcreteConfigInit(parsed_config, parsed_servers, parsed_clients)
    ensures ok ==> var args: seq<seq<uint16>> := env.constants.CommandLineArgs(); id == ParseCommandLineId(args[|args| - 2], args[|args| - 1]) && HostInit(host_state, config, id)
    decreases env

  method HostNextImpl(ghost env: HostEnvironment, host_state: HostState)
      returns (ok: bool, host_state': HostState, ghost recvs: seq<UdpEvent>, ghost clocks: seq<UdpEvent>, ghost sends: seq<UdpEvent>, ghost ios: seq<LIoOp<EndPoint, seq<byte>>>)
    requires env.Valid() && env.ok.ok()
    requires HostStateInvariants(host_state, env)
    modifies set x: object {:trigger ArbitraryObject(x)} | ArbitraryObject(x)
    ensures ok <==> env.Valid() && env.ok.ok()
    ensures ok ==> HostStateInvariants(host_state', env)
    ensures ok ==> HostNext(host_state, host_state', ios)
    ensures ok ==> recvs + clocks + sends == ios
    ensures ok ==> env.udp.history() == old(env.udp.history()) + (recvs + clocks + sends)
    ensures forall e: LIoOp<EndPoint, seq<byte>> {:trigger e.LIoOpSend?} {:trigger e in sends} {:trigger e.LIoOpTimeoutReceive?} {:trigger e.LIoOpReadClock?} {:trigger e in clocks} {:trigger e.LIoOpReceive?} {:trigger e in recvs} :: (e in recvs ==> e.LIoOpReceive?) && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) && (e in sends ==> e.LIoOpSend?)
    ensures |clocks| <= 1
    decreases env
}

abstract module AbstractService_s {

  import opened Native__Io_s

  import opened Environment_s

  import opened Native__NativeTypes_s
  type ServiceState

  predicate Service_Init(s: ServiceState, serverAddresses: set<EndPoint>)
    decreases serverAddresses

  predicate Service_Next(s: ServiceState, s': ServiceState)

  predicate Service_Correspondence(concretePkts: set<LPacket<EndPoint, seq<byte>>>, serviceState: ServiceState)
    decreases concretePkts
}

module Collections__Seqs_s {
  function last<T>(s: seq<T>): T
    requires |s| > 0
    decreases s
  {
    s[|s| - 1]
  }

  function all_but_last<T>(s: seq<T>): seq<T>
    requires |s| > 0
    ensures |all_but_last(s)| == |s| - 1
    decreases s
  {
    s[..|s| - 1]
  }
}

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
  datatype CScheduler = CScheduler(replica_impl: ServerImpl)

  type HostState = CScheduler

  type ConcreteConfiguration = seq<EndPoint>

  method {:timeLimitMultiplier 4} /*{:_timeLimit 40}*/ HostInitImpl(ghost env: HostEnvironment)
      returns (ok: bool, host_state: HostState, config: ConcreteConfiguration, ghost servers: set<EndPoint>, ghost clients: set<EndPoint>, id: EndPoint)
    requires env.Valid()
    requires env.ok.ok()
    requires |env.constants.CommandLineArgs()| >= 2
    modifies set x: object {:trigger ArbitraryObject(x)} | ArbitraryObject(x)
    ensures ok ==> env.Valid() && env.ok.ok()
    ensures ok ==> |env.constants.CommandLineArgs()| >= 2
    ensures ok ==> HostStateInvariants(host_state, env)
    ensures ok ==> ConcreteConfigurationInvariants(config)
    ensures ok ==> var args: seq<seq<uint16>> := env.constants.CommandLineArgs(); var (parsed_config: ConcreteConfiguration, parsed_servers: set<EndPoint>, parsed_clients: set<EndPoint>) := ParseCommandLineConfiguration(args[0 .. |args| - 2]); config == parsed_config && servers == parsed_servers && clients == parsed_clients && ConcreteConfigInit(parsed_config, parsed_servers, parsed_clients)
    ensures ok ==> var args: seq<seq<uint16>> := env.constants.CommandLineArgs(); id == ParseCommandLineId(args[|args| - 2], args[|args| - 1]) && HostInit(host_state, config, id)
    decreases env
  {
    var pconfig: seq<EndPoint>, my_index;
    ok, pconfig, my_index := parse_cmd_line(env);
    var repImpl: ServerImpl := new ServerImpl();
    host_state := CScheduler(repImpl);
    if !ok {
      return;
    }
    assert env.constants == old(env.constants);
    id := pconfig[my_index];
    var scheduler := new ServerImpl();
    ok := scheduler.Server_Init(my_index, pconfig, env);
    host_state := CScheduler(scheduler);
    config := pconfig;
    servers := set e: EndPoint {:trigger e in pconfig} | e in pconfig;
    clients := {};
    lemma_HostInit(host_state, env, config, servers, clients, id);
  }

  lemma {:axiom} lemma_HostInit(host_state: HostState, env: HostEnvironment, config: ConcreteConfiguration, servers: set<EndPoint>, clients: set<EndPoint>, id: EndPoint)
    ensures env.Valid() && env.ok.ok()
    ensures HostStateInvariants(host_state, env)
    ensures ConcreteConfigurationInvariants(config)
    ensures |env.constants.CommandLineArgs()| >= 2
    ensures ghost var args: seq<seq<uint16>> := env.constants.CommandLineArgs(); var (parsed_config: ConcreteConfiguration, parsed_servers: set<EndPoint>, parsed_clients: set<EndPoint>) := ParseCommandLineConfiguration(args[0 .. |args| - 2]); config == parsed_config && servers == parsed_servers && clients == parsed_clients && ConcreteConfigInit(parsed_config, parsed_servers, parsed_clients)
    ensures ghost var args: seq<seq<uint16>> := env.constants.CommandLineArgs(); id == ParseCommandLineId(args[|args| - 2], args[|args| - 1]) && HostInit(host_state, config, id)
    decreases host_state, env, config, servers, clients, id

  predicate NetEventsReductionCompatible(events: seq<UdpEvent>)
    decreases events
  {
    forall i: int, _t#0: int {:trigger events[_t#0], events[i]} | _t#0 == i + 1 :: 
      0 <= i &&
      i < |events| - 1 ==>
        events[i].LIoOpReceive? || events[_t#0].LIoOpSend?
  }

  predicate EventsConsistent(recvs: seq<UdpEvent>, clocks: seq<UdpEvent>, sends: seq<UdpEvent>)
    decreases recvs, clocks, sends
  {
    forall e: LIoOp<EndPoint, seq<byte>> {:trigger e.LIoOpSend?} {:trigger e in sends} {:trigger e.LIoOpTimeoutReceive?} {:trigger e.LIoOpReadClock?} {:trigger e in clocks} {:trigger e.LIoOpReceive?} {:trigger e in recvs} :: 
      (e in recvs ==>
        e.LIoOpReceive?) &&
      (e in clocks ==>
        e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) &&
      (e in sends ==>
        e.LIoOpSend?)
  }

  ghost method RemoveRecvs(events: seq<UdpEvent>) returns (recvs: seq<UdpEvent>, rest: seq<UdpEvent>)
    ensures forall e: LIoOp<EndPoint, seq<byte>> {:trigger e.LIoOpReceive?} {:trigger e in recvs} :: e in recvs ==> e.LIoOpReceive?
    ensures events == recvs + rest
    ensures rest != [] ==> !rest[0].LIoOpReceive?
    ensures NetEventsReductionCompatible(events) ==> NetEventsReductionCompatible(rest)
    decreases events
  {
    recvs := [];
    rest := [];
    ghost var i := 0;
    while i < |events|
      invariant 0 <= i <= |events|
      invariant forall e: LIoOp<EndPoint, seq<byte>> {:trigger e.LIoOpReceive?} {:trigger e in recvs} :: e in recvs ==> e.LIoOpReceive?
      invariant recvs == events[0 .. i]
      decreases |events| - i
    {
      if !events[i].LIoOpReceive? {
        rest := events[i..];
        return;
      }
      recvs := recvs + [events[i]];
      i := i + 1;
    }
  }

  lemma lemma_RemainingEventsAreSends(events: seq<UdpEvent>)
    requires NetEventsReductionCompatible(events)
    requires |events| > 0
    requires !events[0].LIoOpReceive?
    ensures forall e: LIoOp<EndPoint, seq<byte>> {:trigger e.LIoOpSend?} {:trigger e in events[1..]} :: e in events[1..] ==> e.LIoOpSend?
    decreases events
  {
  }

  ghost method PartitionEvents(events: seq<UdpEvent>)
      returns (recvs: seq<UdpEvent>, clocks: seq<UdpEvent>, sends: seq<UdpEvent>)
    requires NetEventsReductionCompatible(events)
    ensures events == recvs + clocks + sends
    ensures EventsConsistent(recvs, clocks, sends)
    ensures |clocks| <= 1
    decreases events
  {
    ghost var rest;
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

  predicate ConcreteConfigurationInvariants(config: ConcreteConfiguration)
    decreases config
  {
    forall e: EndPoint {:trigger EndPointIsValid(e)} {:trigger e in config} :: 
      e in config ==>
        EndPointIsValid(e)
  }

  predicate ConcreteConfigInit(config: ConcreteConfiguration, servers: set<EndPoint>, clients: set<EndPoint>)
    decreases config, servers, clients
  {
    (forall e: EndPoint {:trigger EndPointIsAbstractable(e)} {:trigger e in config} :: 
      e in config ==>
        EndPointIsAbstractable(e)) &&
    MapSeqToSet(config, (x: EndPoint) => x) == servers &&
    (forall e: EndPoint {:trigger EndPointIsAbstractable(e)} {:trigger e in servers} :: 
      e in servers ==>
        EndPointIsAbstractable(e)) &&
    forall e: EndPoint {:trigger EndPointIsAbstractable(e)} {:trigger e in clients} :: 
      e in clients ==>
        EndPointIsAbstractable(e)
  }

  function ParseCommandLineConfiguration(args: seq<seq<uint16>>): (ConcreteConfiguration, set<EndPoint>, set<EndPoint>)
    decreases args
  {
    ghost var cm_config: seq<EndPoint> := causalmesh_config_parsing(args);
    ghost var endpoints_set: set<EndPoint> := set e: EndPoint {:trigger e in cm_config} | e in cm_config;
    (cm_config, endpoints_set, {})
  }

  function paxos_parse_id(ip: seq<uint16>, port: seq<uint16>): EndPoint
    decreases ip, port
  {
    var (ok: bool, ep: EndPoint) := parse_end_point(ip, port);
    ep
  }

  function ParseCommandLineId(ip: seq<uint16>, port: seq<uint16>): EndPoint
    decreases ip, port
  {
    paxos_parse_id(ip, port)
  }

  predicate HostStateInvariants(host_state: HostState, env: HostEnvironment)
    reads *
    decreases {}, host_state, env
  {
    true &&
    host_state.replica_impl.Valid()
  }

  predicate HostInit(host_state: HostState, config: ConcreteConfiguration, id: EndPoint)
    reads *
    decreases {}, host_state, config, id
  {
    true &&
    host_state.replica_impl.Valid()
  }

  predicate HostNext(host_state: HostState, host_state': HostState, ios: seq<LIoOp<EndPoint, seq<byte>>>)
    reads *
    decreases {}, host_state, host_state', ios
  {
    true
  }

  method {:timeLimitMultiplier 3} /*{:_timeLimit 30}*/ HostNextImpl(ghost env: HostEnvironment, host_state: HostState)
      returns (ok: bool, host_state': HostState, ghost recvs: seq<UdpEvent>, ghost clocks: seq<UdpEvent>, ghost sends: seq<UdpEvent>, ghost ios: seq<LIoOp<EndPoint, seq<byte>>>)
    requires env.Valid() && env.ok.ok()
    requires HostStateInvariants(host_state, env)
    modifies set x: object {:trigger ArbitraryObject(x)} | ArbitraryObject(x)
    ensures ok <==> env.Valid() && env.ok.ok()
    ensures ok ==> HostStateInvariants(host_state', env)
    ensures ok ==> HostNext(host_state, host_state', ios)
    ensures ok ==> recvs + clocks + sends == ios
    ensures ok ==> env.udp.history() == old(env.udp.history()) + (recvs + clocks + sends)
    ensures forall e: LIoOp<EndPoint, seq<byte>> {:trigger e.LIoOpSend?} {:trigger e in sends} {:trigger e.LIoOpTimeoutReceive?} {:trigger e.LIoOpReadClock?} {:trigger e in clocks} {:trigger e.LIoOpReceive?} {:trigger e in recvs} :: (e in recvs ==> e.LIoOpReceive?) && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) && (e in sends ==> e.LIoOpSend?)
    ensures |clocks| <= 1
    decreases env, host_state
  {
    ghost var old_history := env.udp.history();
    var repImpl: ServerImpl := new ServerImpl();
    host_state' := CScheduler(repImpl);
    var okay := Server_Next_main(host_state.replica_impl);
    var netEventLog := [];
    if okay {
      recvs, clocks, sends := PartitionEvents(netEventLog);
      ios := recvs + clocks + sends;
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
      assert okay ==> env.udp.history() == old(env.udp.history()) + (recvs + clocks + sends);
    } else {
      recvs := [];
      clocks := [];
      sends := [];
      ios := [];
      lemma_HostNext(okay, old(env), old(env.udp.history()), env, host_state, host_state', recvs, clocks, sends, ios);
      assert okay <==> env.Valid() && env.ok.ok();
    }
    ok := okay;
  }

  lemma {:axiom} lemma_HostNext(okay: bool, env: HostEnvironment, his: seq<UdpEvent>, env': HostEnvironment, host_state: HostState, host_state': HostState, recvs: seq<UdpEvent>, clocks: seq<UdpEvent>, sends: seq<UdpEvent>, ios: seq<LIoOp<EndPoint, seq<byte>>>)
    ensures okay <==> env'.Valid() && env'.ok.ok()
    ensures okay ==> HostStateInvariants(host_state', env')
    ensures okay ==> HostNext(host_state, host_state', ios)
    ensures okay ==> recvs + clocks + sends == ios
    ensures okay ==> env'.udp.history() == his + (recvs + clocks + sends)
    ensures forall e: LIoOp<EndPoint, seq<byte>> {:trigger e.LIoOpSend?} {:trigger e in sends} {:trigger e.LIoOpTimeoutReceive?} {:trigger e.LIoOpReadClock?} {:trigger e in clocks} {:trigger e.LIoOpReceive?} {:trigger e in recvs} :: (e in recvs ==> e.LIoOpReceive?) && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) && (e in sends ==> e.LIoOpSend?)
    ensures |clocks| <= 1
    decreases okay, env, his, env', host_state, host_state', recvs, clocks, sends, ios

  predicate ArbitraryObject(o: object)
    decreases o
  {
    true
  }

  import opened Native__Io_s

  import opened Environment_s

  import opened Native__NativeTypes_s
}

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
  method Replica_Next_ProcessPacketX(r: ServerImpl) returns (ok: bool)
    requires r.Valid()
    modifies r.Repr
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok == UdpClientOk(r.netClient)
    ensures ok ==> true && r.Valid()
    decreases r
  {
    var rr;
    rr := Receive(r.netClient, r.localAddr, r.msg_grammar);
    if rr.RRFail? {
      ok := false;
      return;
    } else if rr.RRTimeout? {
      ok := true;
      ReplicaNextProcessPacketTimeout(r);
    } else {
      lemma_PacketValid(rr.cpacket);
      assert CPacketIsValid(rr.cpacket) && CPacketValid(rr.cpacket);
      var marshallable := true;
      if !marshallable {
        ok := true;
      } else if rr.cpacket.msg.CMessage_Read? {
        ok := ServerNextProcessRead(r, rr.cpacket);
      } else if rr.cpacket.msg.CMessage_Write? {
        ok := ServerNextProcessWrite(r, rr.cpacket);
      } else if rr.cpacket.msg.CMessage_Propagation? {
        ok := ServerNextProcessPropagation(r, rr.cpacket);
      } else {
        ok := true;
      }
    }
  }

  method {:timeLimitMultiplier 2} /*{:_timeLimit 20}*/ ReplicaNextMainProcessPacketX(r: ServerImpl) returns (ok: bool)
    requires r.Valid()
    modifies r.Repr
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok ==> true && r.Valid()
    decreases r
  {
    ok := Replica_Next_ProcessPacketX(r);
    if !ok {
      return;
    }
  }

  method Server_Next_main(r: ServerImpl) returns (ok: bool)
    requires r.Valid()
    modifies r.Repr
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok ==> true && r.Valid()
    decreases r
  {
    ok := ReplicaNextMainProcessPacketX(r);
  }

  lemma {:axiom} lemma_PacketValid(p: CPacket)
    ensures CPacketIsValid(p) && CPacketValid(p)
    decreases p

  method DeliverPackets(r: ServerImpl, packets: seq<CPacket>) returns (ok: bool)
    requires r.Valid()
    modifies r.Repr
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok == UdpClientOk(r.netClient)
    ensures r.server == old(r.server)
    decreases r, packets
  {
    ok := SendPacketSequence(r.netClient, packets, r.localAddr);
  }

  lemma {:axiom} lemma_test(r: ServerImpl)
    ensures r.Valid()
    ensures UdpClientIsValid(r.netClient)
    decreases r

  method {:fuel CServerIsValid, 0, 0} {:timeLimitMultiplier 2} /*{:_timeLimit 20}*/ ServerNextProcessRead(r: ServerImpl, cpacket: CPacket) returns (ok: bool)
    requires r.Valid()
    requires cpacket.msg.CMessage_Read?
    requires CPacketIsValid(cpacket)
    requires CPacketValid(cpacket)
    modifies r.Repr
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok == UdpClientOk(r.netClient)
    ensures ok ==> true && r.Valid()
    decreases r, cpacket
  {
    ghost var net_client_old := r.netClient;
    ghost var net_addr_old := r.netClient.LocalEndPoint();
    assert UdpClientIsValid(net_client_old);
    var sent_packets;
    r.server, sent_packets := CReceiveRead_I1(r.server, cpacket);
    assert net_client_old == r.netClient;
    lemma_test(r);
    assert r.Valid();
    ok := DeliverPackets(r, sent_packets);
    lemma_test(r);
  }

  method {:fuel CServerIsValid, 0, 0} {:timeLimitMultiplier 2} /*{:_timeLimit 20}*/ ServerNextProcessWrite(r: ServerImpl, cpacket: CPacket) returns (ok: bool)
    requires r.Valid()
    requires cpacket.msg.CMessage_Write?
    requires CPacketIsValid(cpacket)
    requires CPacketValid(cpacket)
    modifies r.Repr
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok == UdpClientOk(r.netClient)
    ensures ok ==> true && r.Valid()
    decreases r, cpacket
  {
    ghost var net_client_old := r.netClient;
    ghost var net_addr_old := r.netClient.LocalEndPoint();
    assert UdpClientIsValid(net_client_old);
    var sent_packets;
    r.server, sent_packets := CReceiveWrite_I1(r.server, cpacket);
    assert net_client_old == r.netClient;
    lemma_test(r);
    assert r.Valid();
    ok := DeliverPackets(r, sent_packets);
    lemma_test(r);
  }

  method {:fuel CServerIsValid, 0, 0} {:timeLimitMultiplier 2} /*{:_timeLimit 20}*/ ServerNextProcessPropagation(r: ServerImpl, cpacket: CPacket) returns (ok: bool)
    requires r.Valid()
    requires cpacket.msg.CMessage_Propagation?
    requires CPacketIsValid(cpacket)
    requires CPacketValid(cpacket)
    modifies r.Repr
    ensures r.Repr == old(r.Repr)
    ensures r.netClient != null
    ensures ok == UdpClientOk(r.netClient)
    ensures ok ==> true && r.Valid()
    decreases r, cpacket
  {
    ghost var net_client_old := r.netClient;
    ghost var net_addr_old := r.netClient.LocalEndPoint();
    assert UdpClientIsValid(net_client_old);
    var sent_packets;
    r.server, sent_packets := CReceivePropagate(r.server, cpacket);
    assert net_client_old == r.netClient;
    lemma_test(r);
    assert r.Valid();
    ok := DeliverPackets(r, sent_packets);
    lemma_test(r);
  }

  method ReplicaNextProcessPacketTimeout(r: ServerImpl)
    requires r.Valid()
    decreases r
  {
  }
}

module Collections__Seqs_i {

  import opened Collections__Seqs_s

  import opened Collections__Multisets_s
  lemma SeqAdditionIsAssociative<T>(a: seq<T>, b: seq<T>, c: seq<T>)
    ensures a + (b + c) == a + b + c
    decreases a, b, c
  {
  }

  predicate ItemAtPositionInSeq<T>(s: seq<T>, v: T, idx: int)
    decreases s, idx
  {
    0 <= idx < |s| &&
    s[idx] == v
  }

  predicate method CItemAtPositionInSeq<T(==)>(s: seq<T>, v: T, idx: int)
    decreases s, idx
  {
    0 <= idx < |s| &&
    s[idx] == v
  }

  lemma Lemma_ItemInSeqAtASomePosition<T>(s: seq<T>, v: T)
    requires v in s
    ensures exists idx: int {:trigger ItemAtPositionInSeq(s, v, idx)} :: ItemAtPositionInSeq(s, v, idx)
    decreases s
  {
  }

  function method FindIndexInSeq<T(==)>(s: seq<T>, v: T): int
    ensures var r: int := FindIndexInSeq(s, v); if r >= 0 then r < |s| && s[r] == v else v !in s
    decreases s
  {
    if |s| == 0 then
      -1
    else if s[0] == v then
      0
    else
      var r: int := FindIndexInSeq(s[1..], v); if r == -1 then -1 else r + 1
  }

  lemma Lemma_IdenticalSingletonSequencesHaveIdenticalElement<T>(x: T, y: T)
    requires [x] == [y]
    ensures x == y
  {
  }

  function SeqCat<T>(seqs: seq<seq<T>>): seq<T>
    decreases seqs
  {
    if |seqs| == 0 then
      []
    else
      seqs[0] + SeqCat(seqs[1..])
  }

  function SeqCatRev<T>(seqs: seq<seq<T>>): seq<T>
    decreases seqs
  {
    if |seqs| == 0 then
      []
    else
      SeqCatRev(all_but_last(seqs)) + last(seqs)
  }

  lemma /*{:_induction A, B}*/ lemma_SeqCat_adds<T>(A: seq<seq<T>>, B: seq<seq<T>>)
    ensures SeqCat(A + B) == SeqCat(A) + SeqCat(B)
    decreases A, B
  {
  }

  lemma /*{:_induction A, B}*/ lemma_SeqCatRev_adds<T>(A: seq<seq<T>>, B: seq<seq<T>>)
    ensures SeqCatRev(A + B) == SeqCatRev(A) + SeqCatRev(B)
    decreases A, B
  {
  }

  lemma /*{:_induction seqs}*/ lemma_SeqCat_equivalent<T>(seqs: seq<seq<T>>)
    ensures SeqCat(seqs) == SeqCatRev(seqs)
    decreases seqs
  {
  }

  predicate Sorted_COperationNumber_seq(a: seq<int>, low: int, high: int)
    requires 0 <= low <= high <= |a|
    decreases a, low, high
  {
    forall i: int, j: int {:trigger a[j], a[i]} :: 
      low <= i < j < high ==>
        a[i] <= a[j]
  }

  predicate NeighborSorted_COperationNumber_seq(a: seq<int>, low: int, high: int)
    requires 0 <= low <= high <= |a|
    decreases a, low, high
  {
    forall i: int {:trigger a[i - 1], a[i]} :: 
      low < i < high ==>
        a[i - 1] <= a[i]
  }

  method InsertSort(a: seq<int>) returns (sorted: seq<int>)
    ensures forall i: int, j: int {:trigger sorted[j], sorted[i]} :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    ensures Sorted_COperationNumber_seq(sorted, 0, |sorted|)
    ensures |a| == |sorted|
    ensures multiset(a) == multiset(sorted)
    decreases a
  {
    if |a| <= 1 {
      sorted := a;
      assert |a| == |sorted|;
      assert multiset(a) == multiset(sorted);
    } else {
      var last := a[|a| - 1];
      var rest := a[..|a| - 1];
      assert rest + [last] == a;
      assert multiset(a) == multiset([last]) + multiset(rest);
      var sortedRest := InsertSort(rest);
      assert multiset(sortedRest) == multiset(rest);
      assert |sortedRest| == |rest|;
      sorted := Insert(sortedRest, last);
      assert multiset(sorted) == multiset(sortedRest) + multiset([last]);
    }
  }

  method Insert(sortedSeq: seq<int>, value: int) returns (newSeq: seq<int>)
    requires forall i: int, j: int {:trigger sortedSeq[j], sortedSeq[i]} :: 0 <= i < j < |sortedSeq| ==> sortedSeq[i] <= sortedSeq[j]
    ensures forall i: int, j: int {:trigger newSeq[j], newSeq[i]} :: 0 <= i < j < |newSeq| ==> newSeq[i] <= newSeq[j]
    ensures |newSeq| == |sortedSeq| + 1
    ensures multiset(newSeq) == multiset(sortedSeq) + multiset([value])
    ensures |newSeq| > 0
    decreases sortedSeq, value
  {
    if |sortedSeq| == 0 {
      newSeq := [value];
    } else {
      if value <= sortedSeq[0] {
        newSeq := [value] + sortedSeq;
      } else {
        var res := Insert(sortedSeq[1..], value);
        assert multiset(res) == multiset(sortedSeq[1..]) + multiset([value]);
        assert forall i: int, j: int {:trigger res[j], res[i]} :: 0 <= i < j < |res| ==> res[i] <= res[j];
        newSeq := [sortedSeq[0]] + res;
        assert multiset(newSeq) == multiset([sortedSeq[0]]) + multiset(res);
        assert multiset(newSeq) == multiset([sortedSeq[0]]) + multiset(sortedSeq[1..]) + multiset([value]);
        assert sortedSeq == [sortedSeq[0]] + sortedSeq[1..];
        assert multiset(sortedSeq) == multiset([sortedSeq[0]]) + multiset(sortedSeq[1..]);
        assert multiset(res) == multiset(sortedSeq[1..]) + multiset([value]);
        assert multiset(res) == multiset(sortedSeq[1..]) + multiset([value]);
        ghost var ss := sortedSeq[1..] + [value];
        assert multiset(ss) == multiset(res);
        MultisetContains(ss, res);
      }
    }
  }
}

module Collections__Multisets_s {
  function RestrictMultiset<S(!new)>(m: multiset<S>, f: S -> bool): multiset<S>
    requires forall x: S {:trigger f.requires(x)} :: f.requires(x)
    reads set _x0: S, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    ensures RestrictMultiset(m, f) <= m
    ensures forall x: S {:trigger m[x]} {:trigger f(x)} {:trigger RestrictMultiset(m, f)[x]} :: RestrictMultiset(m, f)[x] == if f(x) then m[x] else 0
    decreases set _x0: S, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj, m
  {
    if |m| == 0 then
      multiset{}
    else
      ghost var x: S :| x in m; ghost var m_without_x: multiset<S> := m[x := 0]; if f(x) then RestrictMultiset(m_without_x, f)[x := m[x]] else RestrictMultiset(m_without_x, f)
  }

  lemma MultisetContains(ss: seq<int>, res: seq<int>)
    requires multiset(ss) == multiset(res)
    ensures forall j: int {:trigger res[j]} :: 0 <= j < |res| ==> res[j] in ss
    decreases ss, res
  {
  }
}

module Math__mod_auto_i {

  import opened Math__mod_auto_proofs_i

  import opened Math__div_nonlinear_i

  import opened Math__mul_nonlinear_i

  import opened Math__mul_i
  predicate eq_mod(x: int, y: int, n: int)
    requires n > 0
    decreases x, y, n
  {
    (x - y) % n == 0
  }

  predicate ModAuto(n: int)
    requires n > 0
    decreases n
  {
    n % n == -n % n == 0 &&
    (forall x: int {:trigger x % n % n} :: 
      x % n % n == x % n) &&
    (forall x: int {:trigger x % n} :: 
      0 <= x < n <==> x % n == x) &&
    (forall x: int, y: int {:trigger (x + y) % n} :: 
      ghost var z: int := x % n + y % n; (0 <= z < n && (x + y) % n == z) || (n <= z < n + n && (x + y) % n == z - n)) &&
    forall x: int, y: int {:trigger (x - y) % n} :: 
      ghost var z: int := x % n - y % n; (0 <= z < n && (x - y) % n == z) || (-n <= z < 0 && (x - y) % n == z + n)
  }

  lemma lemma_QuotientAndRemainderUnique(x: int, q: int, r: int, n: int)
    requires n > 0
    requires 0 <= r < n
    requires x == q * n + r
    ensures q == x / n
    ensures r == x % n
    decreases if q > 0 then q else -q
  {
  }

  lemma lemma_mod_auto(n: int)
    requires n > 0
    ensures ModAuto(n)
    decreases n
  {
  }

  predicate TModAutoLe(x: int, y: int)
    decreases x, y
  {
    x <= y
  }

  lemma lemma_mod_auto_induction(n: int, x: int, f: int -> bool)
    requires n > 0
    requires ModAuto(n) ==> (forall i: int {:trigger TModAutoLe(0, i)} :: TModAutoLe(0, i) && i < n ==> f(i)) && (forall i: int {:trigger TModAutoLe(0, i)} :: TModAutoLe(0, i) && f(i) ==> f(i + n)) && forall i: int {:trigger TModAutoLe(i + 1, n)} :: TModAutoLe(i + 1, n) && f(i) ==> f(i - n)
    ensures ModAuto(n)
    ensures f(x)
    decreases n, x
  {
  }

  lemma lemma_mod_auto_induction_forall(n: int, f: int -> bool)
    requires n > 0
    requires ModAuto(n) ==> (forall i: int {:trigger TModAutoLe(0, i)} :: TModAutoLe(0, i) && i < n ==> f(i)) && (forall i: int {:trigger TModAutoLe(0, i)} :: TModAutoLe(0, i) && f(i) ==> f(i + n)) && forall i: int {:trigger TModAutoLe(i + 1, n)} :: TModAutoLe(i + 1, n) && f(i) ==> f(i - n)
    ensures ModAuto(n)
    ensures forall i: int {:trigger f(i)} :: f(i)
    decreases n
  {
  }
}

module Math__mod_auto_proofs_i {

  import opened Math__mul_auto_i

  import opened Math__mul_nonlinear_i

  import opened Math__mul_i

  import opened Math__div_nonlinear_i
  lemma lemma_mod_induction_helper(n: int, f: int -> bool, x: int)
    requires n > 0
    requires forall i: int {:trigger f(i)} :: 0 <= i < n ==> f(i)
    requires forall i: int {:trigger f(i), f(i + n)} :: i >= 0 && f(i) ==> f(i + n)
    requires forall i: int {:trigger f(i), f(i - n)} :: i < n && f(i) ==> f(i - n)
    ensures f(x)
    decreases if x >= n then x else -x
  {
  }

  lemma lemma_mod_induction_forall(n: int, f: int -> bool)
    requires n > 0
    requires forall i: int {:trigger f(i)} :: 0 <= i < n ==> f(i)
    requires forall i: int {:trigger f(i), f(i + n)} :: i >= 0 && f(i) ==> f(i + n)
    requires forall i: int {:trigger f(i), f(i - n)} :: i < n && f(i) ==> f(i - n)
    ensures forall i: int {:trigger f(i)} :: f(i)
    decreases n
  {
  }

  lemma lemma_mod_induction_forall2(n: int, f: (int, int) -> bool)
    requires n > 0
    requires forall i: int, j: int {:trigger f(i, j)} :: 0 <= i < n && 0 <= j < n ==> f(i, j)
    requires forall i: int, j: int {:trigger f(i, j), f(i + n, j)} :: i >= 0 && f(i, j) ==> f(i + n, j)
    requires forall i: int, j: int {:trigger f(i, j), f(i, j + n)} :: j >= 0 && f(i, j) ==> f(i, j + n)
    requires forall i: int, j: int {:trigger f(i, j), f(i - n, j)} :: i < n && f(i, j) ==> f(i - n, j)
    requires forall i: int, j: int {:trigger f(i, j), f(i, j - n)} :: j < n && f(i, j) ==> f(i, j - n)
    ensures forall i: int, j: int {:trigger f(i, j)} :: f(i, j)
    decreases n
  {
  }

  lemma lemma_mod_auto_basics(n: int)
    requires n > 0
    ensures forall x: int {:trigger (x + n) % n} :: (x + n) % n == x % n
    ensures forall x: int {:trigger (x - n) % n} :: (x - n) % n == x % n
    ensures forall x: int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1
    ensures forall x: int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1
    ensures forall x: int {:trigger x % n} :: 0 <= x < n <==> x % n == x
    decreases n
  {
  }
}

module Math__mul_auto_i {

  import opened Math__mul_auto_proofs_i
  predicate MulAuto()
  {
    (forall x: int, y: int {:trigger x * y} :: 
      x * y == y * x) &&
    (forall x: int, y: int, z: int {:trigger (x + y) * z} :: 
      (x + y) * z == x * z + y * z) &&
    forall x: int, y: int, z: int {:trigger (x - y) * z} :: 
      (x - y) * z == x * z - y * z
  }

  lemma lemma_mul_auto()
    ensures MulAuto()
  {
  }

  predicate TMulAutoLe(x: int, y: int)
    decreases x, y
  {
    x <= y
  }

  lemma lemma_mul_auto_induction(x: int, f: int -> bool)
    requires MulAuto() ==> f(0) && (forall i: int {:trigger TMulAutoLe(0, i)} :: TMulAutoLe(0, i) && f(i) ==> f(i + 1)) && forall i: int {:trigger TMulAutoLe(i, 0)} :: TMulAutoLe(i, 0) && f(i) ==> f(i - 1)
    ensures MulAuto()
    ensures f(x)
    decreases x
  {
  }

  lemma lemma_mul_auto_induction_forall(f: int -> bool)
    requires MulAuto() ==> f(0) && (forall i: int {:trigger TMulAutoLe(0, i)} :: TMulAutoLe(0, i) && f(i) ==> f(i + 1)) && forall i: int {:trigger TMulAutoLe(i, 0)} :: TMulAutoLe(i, 0) && f(i) ==> f(i - 1)
    ensures MulAuto()
    ensures forall i: int {:trigger f(i)} :: f(i)
  {
  }
}

module Math__mul_auto_proofs_i {

  import opened Math__mul_nonlinear_i
  lemma lemma_mul_induction_helper(f: int -> bool, x: int)
    requires f(0)
    requires forall i: int {:trigger f(i), f(i + 1)} :: i >= 0 && f(i) ==> f(i + 1)
    requires forall i: int {:trigger f(i), f(i - 1)} :: i <= 0 && f(i) ==> f(i - 1)
    ensures f(x)
    decreases if x >= 0 then x else -x
  {
  }

  lemma lemma_mul_induction_forall(f: int -> bool)
    requires f(0)
    requires forall i: int {:trigger f(i), f(i + 1)} :: i >= 0 && f(i) ==> f(i + 1)
    requires forall i: int {:trigger f(i), f(i - 1)} :: i <= 0 && f(i) ==> f(i - 1)
    ensures forall i: int {:trigger f(i)} :: f(i)
  {
  }

  lemma lemma_mul_auto_commutes()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
  {
  }

  lemma lemma_mul_auto_succ()
    ensures forall x: int, y: int {:trigger (x + 1) * y} :: (x + 1) * y == x * y + y
    ensures forall x: int, y: int {:trigger (x - 1) * y} :: (x - 1) * y == x * y - y
  {
  }

  lemma lemma_mul_auto_distributes()
    ensures forall x: int, y: int, z: int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z
    ensures forall x: int, y: int, z: int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z
  {
  }
}

module Math__mul_nonlinear_i {
  lemma lemma_mul_strictly_positive(x: int, y: int)
    ensures 0 < x && 0 < y ==> 0 < x * y
    decreases x, y
  {
  }

  lemma lemma_mul_nonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
    decreases x, y
  {
  }

  lemma lemma_mul_is_associative(x: int, y: int, z: int)
    ensures x * y * z == x * y * z
    decreases x, y, z
  {
  }

  lemma lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    decreases x, y, z
  {
  }

  lemma lemma_mul_ordering(x: int, y: int)
    requires 0 < x
    requires 0 < y
    requires 0 <= x * y
    ensures x <= x * y && y <= x * y
    decreases x, y
  {
  }

  lemma lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires x < y
    requires z > 0
    ensures x * z < y * z
    decreases x, y, z
  {
  }

  lemma lemma_mul_by_zero_is_zero(x: int)
    ensures 0 * x == 0
    ensures x * 0 == 0
    decreases x
  {
  }
}

module Math__mul_i {

  import opened Math__mul_nonlinear_i

  import opened Math__mul_auto_i
  function mul(x: int, y: int): int
    decreases x, y
  {
    x * y
  }

  function mul_recursive(x: int, y: int): int
    decreases x, y
  {
    if x >= 0 then
      mul_pos(x, y)
    else
      -1 * mul_pos(-1 * x, y)
  }

  function {:opaque} {:fuel 0, 0} mul_pos(x: int, y: int): int
    requires x >= 0
    decreases x, y
  {
    if x == 0 then
      0
    else
      y + mul_pos(x - 1, y)
  }

  lemma lemma_mul_is_mul_recursive(x: int, y: int)
    ensures x * y == mul_recursive(x, y)
    decreases x, y
  {
  }

  lemma /*{:_induction x, y}*/ lemma_mul_is_mul_pos(x: int, y: int)
    requires x >= 0
    ensures x * y == mul_pos(x, y)
    decreases x, y
  {
  }

  lemma lemma_mul_basics(x: int)
    ensures 0 * x == 0
    ensures x * 0 == 0
    ensures 1 * x == x
    ensures x * 1 == x
    decreases x
  {
  }

  lemma lemma_mul_is_commutative(x: int, y: int)
    ensures x * y == y * x
    decreases x, y
  {
  }

  lemma lemma_mul_ordering_general()
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y && 0 <= x * y ==> x <= x * y) && (0 < x && 0 < y && 0 <= x * y ==> y <= x * y)
  {
  }

  lemma lemma_mul_is_mul_boogie(x: int, y: int)
    decreases x, y
  {
  }

  lemma lemma_mul_inequality(x: int, y: int, z: int)
    requires x <= y
    requires z >= 0
    ensures x * z <= y * z
    decreases x, y, z
  {
  }

  lemma lemma_mul_upper_bound(x: int, x_bound: int, y: int, y_bound: int)
    requires x <= x_bound
    requires y <= y_bound
    requires 0 <= x
    requires 0 <= y
    ensures x * y <= x_bound * y_bound
    decreases x, x_bound, y, y_bound
  {
  }

  lemma lemma_mul_strict_upper_bound(x: int, x_bound: int, y: int, y_bound: int)
    requires x < x_bound
    requires y < y_bound
    requires 0 <= x
    requires 0 <= y
    ensures x * y < x_bound * y_bound
    decreases x, x_bound, y, y_bound
  {
  }

  lemma lemma_mul_left_inequality(x: int, y: int, z: int)
    requires x > 0
    ensures y <= z ==> x * y <= x * z
    ensures y < z ==> x * y < x * z
    decreases x, y, z
  {
  }

  lemma lemma_mul_strict_inequality_converse(x: int, y: int, z: int)
    requires x * z < y * z
    requires z >= 0
    ensures x < y
    decreases x, y, z
  {
  }

  lemma lemma_mul_inequality_converse(x: int, y: int, z: int)
    requires x * z <= y * z
    requires z > 0
    ensures x <= y
    decreases x, y, z
  {
  }

  lemma lemma_mul_equality_converse(x: int, y: int, z: int)
    requires x * z == y * z
    requires 0 < z
    ensures x == y
    decreases x, y, z
  {
  }

  lemma lemma_mul_is_distributive_add_other_way(x: int, y: int, z: int)
    ensures (y + z) * x == y * x + z * x
    decreases x, y, z
  {
  }

  lemma lemma_mul_is_distributive_sub(x: int, y: int, z: int)
    ensures x * (y - z) == x * y - x * z
    decreases x, y, z
  {
  }

  lemma lemma_mul_is_distributive(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    ensures x * (y - z) == x * y - x * z
    ensures (y + z) * x == y * x + z * x
    ensures (y - z) * x == y * x - z * x
    ensures x * (y + z) == (y + z) * x
    ensures x * (y - z) == (y - z) * x
    ensures x * y == y * x
    ensures x * z == z * x
    decreases x, y, z
  {
  }

  lemma lemma_mul_strictly_increases(x: int, y: int)
    requires 1 < x
    requires 0 < y
    ensures y < x * y
    decreases x, y
  {
  }

  lemma lemma_mul_increases(x: int, y: int)
    requires 0 < x
    requires 0 < y
    ensures y <= x * y
    decreases x, y
  {
  }

  lemma lemma_mul_nonnegative(x: int, y: int)
    requires 0 <= x
    requires 0 <= y
    ensures 0 <= x * y
    decreases x, y
  {
  }

  lemma lemma_mul_unary_negation(x: int, y: int)
    ensures -x * y == -(x * y) == x * -y
    decreases x, y
  {
  }

  lemma lemma_mul_one_to_one_pos(m: int, x: int, y: int)
    requires 0 < m
    requires m * x == m * y
    ensures x == y
    decreases m, x, y
  {
  }

  lemma lemma_mul_one_to_one(m: int, x: int, y: int)
    requires m != 0
    requires m * x == m * y
    ensures x == y
    decreases m, x, y
  {
  }

  lemma lemma_mul_is_mul_recursive_forall()
    ensures forall x: int, y: int {:trigger mul_recursive(x, y)} :: x * y == mul_recursive(x, y)
  {
  }

  lemma lemma_mul_basics_forall()
    ensures forall x: int {:trigger 0 * x} :: 0 * x == 0
    ensures forall x: int {:trigger x * 0} :: x * 0 == 0
    ensures forall x: int {:trigger 1 * x} :: 1 * x == x
    ensures forall x: int {:trigger x * 1} :: x * 1 == x
  {
  }

  lemma lemma_mul_is_commutative_forall()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
  {
  }

  lemma lemma_mul_ordering_forall()
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y && 0 <= x * y ==> x <= x * y) && (0 < x && 0 < y && 0 <= x * y ==> y <= x * y)
  {
  }

  lemma lemma_mul_strict_inequality_forall()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
  {
  }

  lemma lemma_mul_inequality_forall()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
  {
  }

  lemma lemma_mul_strict_inequality_converse_forall()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z < y * z && z >= 0 ==> x < y
  {
  }

  lemma lemma_mul_inequality_converse_forall()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z <= y * z && z > 0 ==> x <= y
  {
  }

  lemma lemma_mul_is_distributive_add_forall()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
  {
  }

  lemma lemma_mul_is_distributive_sub_forall()
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
  {
  }

  lemma lemma_mul_is_distributive_forall()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
  {
  }

  lemma lemma_mul_is_associative_forall()
    ensures forall x: int, y: int, z: int {:trigger x * y * z} {:trigger x * y * z} :: x * y * z == x * y * z
  {
  }

  lemma lemma_mul_nonzero_forall()
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
  {
  }

  lemma lemma_mul_nonnegative_forall()
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
  {
  }

  lemma lemma_mul_unary_negation_forall()
    ensures forall x: int, y: int {:trigger -x * y} {:trigger x * -y} :: -x * y == -(x * y) && -(x * y) == x * -y
  {
  }

  lemma lemma_mul_strictly_increases_forall()
    ensures forall x: int, y: int {:trigger x * y} :: 1 < x && 0 < y ==> y < x * y
  {
  }

  lemma lemma_mul_increases_forall()
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> y <= x * y
  {
  }

  lemma lemma_mul_strictly_positive_forall()
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> 0 < x * y
  {
  }

  lemma lemma_mul_one_to_one_forall()
    ensures forall m: int, x: int, y: int {:trigger m * x, m * y} :: m != 0 && m * x == m * y ==> x == y
  {
  }

  lemma lemma_mul_by_zero_is_zero_forall()
    ensures forall x: int {:trigger 0 * x} {:trigger x * 0} :: x * 0 == 0 * x && 0 * x == 0
  {
  }

  lemma lemma_mul_properties()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
    ensures forall x: int {:trigger x * 1} {:trigger 1 * x} :: x * 1 == 1 * x && 1 * x == x
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
    ensures forall x: int, y: int, z: int {:trigger x * y * z} {:trigger x * y * z} :: x * y * z == x * y * z
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y && 0 <= x * y ==> x <= x * y) && (0 < x && 0 < y && 0 <= x * y ==> y <= x * y)
    ensures forall x: int, y: int {:trigger x * y} :: 1 < x && 0 < y ==> y < x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> y <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> 0 < x * y
  {
  }

  function INTERNAL_mul_recursive(x: int, y: int): int
    decreases x, y
  {
    mul_recursive(x, y)
  }
}

module Math__div_nonlinear_i {
  lemma lemma_div_of_0(d: int)
    requires d != 0
    ensures 0 / d == 0
    decreases d
  {
  }

  lemma lemma_div_by_self(d: int)
    requires d != 0
    ensures d / d == 1
    decreases d
  {
  }

  lemma lemma_small_div()
    ensures forall d: int, x: int {:trigger x / d} :: 0 <= x < d && d > 0 ==> x / d == 0
  {
  }

  lemma lemma_mod_of_zero_is_zero(m: int)
    requires 0 < m
    ensures 0 % m == 0
    decreases m
  {
  }

  lemma lemma_fundamental_div_mod(x: int, d: int)
    requires d != 0
    ensures x == d * x / d + x % d
    decreases x, d
  {
  }

  lemma lemma_0_mod_anything()
    ensures forall m: int {:trigger 0 % m} :: m > 0 ==> 0 % m == 0
  {
  }

  lemma lemma_small_mod(x: nat, m: nat)
    requires x < m
    requires 0 < m
    ensures x % m == x
    decreases x, m
  {
  }

  lemma lemma_mod_range(x: int, m: int)
    requires m > 0
    ensures 0 <= x % m < m
    decreases x, m
  {
  }

  lemma lemma_real_div_gt(x: real, y: real)
    requires x > y
    requires x >= 0.0
    requires y > 0.0
    ensures x / y > 1 as real
    decreases x, y
  {
  }
}

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
  datatype ReceiveResult = RRFail | RRTimeout | RRPacket(cpacket: CPacket)

  method GetEndPoint(ipe: IPEndPoint) returns (ep: EndPoint)
    ensures ep == ipe.EP()
    ensures EndPointIsValidIPV4(ep)
    decreases ipe
  {
    var addr := ipe.GetAddress();
    var port := ipe.GetPort();
    ep := EndPoint(addr[..], port);
  }

  method {:timeLimitMultiplier 2} /*{:_timeLimit 20}*/ Receive(udpClient: UdpClient, localAddr: EndPoint, msg_grammar: G)
      returns (rr: ReceiveResult)
    requires UdpClientIsValid(udpClient)
    requires udpClient.LocalEndPoint() == localAddr
    requires msg_grammar == CMessage_grammar()
    modifies UdpClientRepr(udpClient)
    ensures udpClient.env == old(udpClient.env)
    ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
    ensures UdpClientOk(udpClient) <==> !rr.RRFail?
    ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient)
    ensures !rr.RRFail? ==> true && udpClient.IsOpen()
    ensures rr.RRPacket? ==> CPacketIsAbstractable(rr.cpacket) && EndPointIsValidIPV4(rr.cpacket.src)
    decreases udpClient, localAddr, msg_grammar
  {
    var timeout := 0;
    ghost var old_udp_history := udpClient.env.udp.history();
    var ok, timedOut, remote, buffer := udpClient.Receive(timeout);
    if !ok {
      rr := RRFail();
      return;
    }
    if timedOut {
      rr := RRTimeout();
      return;
    }
    var start_time := Time.GetDebugTimeTicks();
    var cmessage := DemarshallData(buffer, msg_grammar);
    var end_time := Time.GetDebugTimeTicks();
    var srcEp := GetEndPoint(remote);
    var cpacket := CPacket(localAddr, srcEp, cmessage);
    rr := RRPacket(cpacket);
  }

  method {:timeLimitMultiplier 2} /*{:_timeLimit 20}*/ SendPacketSequence(udpClient: UdpClient, packets: seq<CPacket>, ghost localAddr_: EndPoint)
      returns (ok: bool)
    requires UdpClientIsValid(udpClient)
    requires udpClient.LocalEndPoint() == localAddr_
    modifies UdpClientRepr(udpClient)
    ensures old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient)
    ensures udpClient.env == old(udpClient.env)
    ensures udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
    ensures UdpClientOk(udpClient) <==> ok
    ensures ok ==> UdpClientIsValid(udpClient) && udpClient.IsOpen()
    decreases udpClient, packets, localAddr_
  {
    var cpackets := packets;
    var j: int := 0;
    ok := true;
    var i: int := 0;
    while i < |cpackets| as int
      invariant old(UdpClientRepr(udpClient)) == UdpClientRepr(udpClient)
      invariant udpClient.env == old(udpClient.env)
      invariant udpClient.LocalEndPoint() == old(udpClient.LocalEndPoint())
      invariant UdpClientOk(udpClient) <==> ok
      invariant ok ==> UdpClientIsValid(udpClient) && udpClient.IsOpen()
      decreases |cpackets| as int - i
    {
      var cpacket := cpackets[i];
      var dstEp: EndPoint := cpacket.dst;
      assert cpacket in cpackets;
      if |dstEp.addr| < 18446744073709551616 {
        var dstAddrAry := seqToArrayOpt(dstEp.addr);
        var remote;
        ok, remote := IPEndPoint.Construct(dstAddrAry, dstEp.port, udpClient.env);
        if !ok {
          return;
        }
        var buffer := MarshallData(cpacket.msg);
        if buffer.Length <= 18446744073709551615 {
          ok := udpClient.Send(remote, buffer);
          if !ok {
            return;
          }
        } else {
          print ""Packet is too large\n"";
        }
      } else {
        print ""Dst has wrong adress\n"";
      }
      i := i + 1;
    }
  }
}

module Common__UdpClient_i {

  import opened Native__Io_s
  function Workaround_CastHostEnvironmentToObject(env: HostEnvironment): object
    decreases env
  {
    env
  }

  function Workaround_CastOkStateToObject(okState: OkState): object
    decreases okState
  {
    okState
  }

  function Workaround_CastNowStateToObject(nowState: NowState): object
    decreases nowState
  {
    nowState
  }

  function Workaround_CastUdpStateToObject(udpState: UdpState): object
    decreases udpState
  {
    udpState
  }

  function Workaround_CastIPEndPointToObject(ip: IPEndPoint): object
    decreases ip
  {
    ip
  }

  function Workaround_CastUdpClientToObject(udpc: UdpClient?): object?
    decreases udpc
  {
    udpc
  }

  function HostEnvironmentDefaultFrame(env: HostEnvironment): set<object>
    reads env, {env.now}, {env.ok}, {env.udp}, {env}
    decreases {env.now} + {env.ok} + {env.udp} + {env} + {env}, env
  {
    {Workaround_CastOkStateToObject(env.ok), Workaround_CastNowStateToObject(env.now), Workaround_CastUdpStateToObject(env.udp)}
  }

  function UdpClientRepr(udpc: UdpClient?): set<object?>
    reads udpc, if udpc != null then HostEnvironmentDefaultFrame.reads(udpc.env) else {}
    decreases (if udpc != null then HostEnvironmentDefaultFrame.reads(udpc.env) else {}) + {udpc}, udpc
  {
    {Workaround_CastUdpClientToObject(udpc)} + if udpc != null then HostEnvironmentDefaultFrame(udpc.env) else {}
  }

  predicate HostEnvironmentIsValid(env: HostEnvironment)
    reads env, env.Valid.reads(), env.ok.ok.reads()
    decreases env.Valid.reads() + env.ok.ok.reads() + {env}, env
  {
    env.Valid() &&
    env.ok.ok()
  }

  predicate UdpClientOk(udpc: UdpClient?)
    reads udpc, if udpc != null then HostEnvironmentDefaultFrame.reads(udpc.env) else {}
    decreases (if udpc != null then HostEnvironmentDefaultFrame.reads(udpc.env) else {}) + {udpc}, udpc
  {
    udpc != null &&
    udpc.env.ok.ok()
  }

  function method EndPointIsValidIPV4(endPoint: EndPoint): bool
    decreases endPoint
  {
    |endPoint.addr| == 4 &&
    0 <= endPoint.port <= 65535
  }

  predicate UdpClientIsValid(udpc: UdpClient?)
    reads UdpClientRepr(udpc), if udpc != null then HostEnvironmentIsValid.reads(udpc.env) else {}
    decreases UdpClientRepr(udpc) + if udpc != null then HostEnvironmentIsValid.reads(udpc.env) else {}, udpc
  {
    udpc != null &&
    udpc.IsOpen() &&
    HostEnvironmentIsValid(udpc.env) &&
    EndPointIsValidIPV4(udpc.LocalEndPoint())
  }

  predicate EndPointsAreValidIPV4(eps: seq<EndPoint>)
    decreases eps
  {
    forall i: int {:trigger eps[i]} :: 
      0 <= i < |eps| ==>
        EndPointIsValidIPV4(eps[i])
  }
}

module CausalMesh_PacketParsing_i {

  import opened Native__Io_s

  import opened Native__NativeTypes_s

  import opened Collections__Maps_i

  import opened Common__GenericMarshalling_i

  import opened Common__NodeIdentity_i

  import opened Common__UdpClient_i

  import opened Common__Util_i

  import opened Environment_s

  import opened Math__mul_i

  import opened Math__mul_nonlinear_i

  import opened CausalMesh_CTypes_i

  import opened CausalMesh_CMessage_i

  import opened CausalMesh_Types_i
  function method EndPoint_grammar(): G
  {
    GUint64
  }

  function method CVectorClock_grammar(): G
  {
    GArray(GUint64)
  }

  function method CDependency_grammar(): G
  {
    GArray(GTuple([GUint64, CVectorClock_grammar()]))
  }

  function method CMeta_grammar(): G
  {
    GTuple([GUint64, CVectorClock_grammar(), CDependency_grammar()])
  }

  function method CLocal_grammar(): G
  {
    GArray(GTuple([GUint64, CMeta_grammar()]))
  }

  function method CMessage_Read_grmamar(): G
  {
    GTuple([GUint64, GUint64, CDependency_grammar()])
  }

  function method CMessage_ReadReply_grammar(): G
  {
    GTuple([GUint64, GUint64, CVectorClock_grammar(), CDependency_grammar()])
  }

  function method CMessage_Write_grammar(): G
  {
    GTuple([GUint64, GUint64, CDependency_grammar(), CLocal_grammar(), CVectorClock_grammar()])
  }

  function method CMessage_WriteReply_grammar(): G
  {
    GTuple([GUint64, GUint64, CVectorClock_grammar()])
  }

  function method CMessage_Propagate_grammar(): G
  {
    GTuple([GUint64, CMeta_grammar(), GUint64, GUint64])
  }

  function method CMessage_grammar(): G
  {
    GTaggedUnion([CMessage_Read_grmamar(), CMessage_ReadReply_grammar(), CMessage_Write_grammar(), CMessage_WriteReply_grammar(), CMessage_Propagate_grammar()])
  }

  method MarshallEndPoint(c: EndPoint) returns (val: V)
    requires EndPointIsValidIPV4(c)
    ensures ValInGrammar(val, EndPoint_grammar())
    ensures ValidVal(val)
    ensures parse_EndPoint(val) == c
    decreases c
  {
    val := VUint64(ConvertEndPointToUint64(c));
    lemma_Uint64EndPointRelationships();
  }

  function method parse_EndPoint(val: V): EndPoint
    requires ValInGrammar(val, EndPoint_grammar())
    ensures EndPointIsAbstractable(parse_EndPoint(val))
    decreases val
  {
    if val.u <= 281474976710655 then
      ConvertUint64ToEndPoint(val.u)
    else
      EndPoint([0, 0, 0, 0], 0)
  }

  lemma {:axiom} lemma_VCLength(c: CVectorClock)
    ensures |c| < 18446744073709551615
    decreases c

  method MarshallCVectorClock(c: CVectorClock) returns (val: V)
    ensures ValInGrammar(val, CVectorClock_grammar())
    decreases c
  {
    lemma_VCLength(c);
    assert |c| < 18446744073709551615;
    var vcs := new V[|c| as uint64];
    var i: uint64 := 0;
    while i < |c| as uint64
      invariant 0 <= i as int <= |c|
      invariant forall j: uint64 {:trigger vcs[j]} :: 0 <= j < i ==> ValInGrammar(vcs[j], CVectorClock_grammar().elt)
      decreases |c| as uint64 as int - i as int
    {
      var single := 0;
      if 0 <= c[i] < 18446744073709551615 {
        single := c[i] as uint64;
      } else {
        single := 18446744073709551615;
        print ""Marshall CVectorClock overflow\n"";
      }
      vcs[i] := VUint64(single);
      i := i + 1;
    }
    val := VArray(vcs[..]);
    assert ValInGrammar(val, CVectorClock_grammar());
  }

  function method parse_CVectorClock(val: V): CVectorClock
    requires ValInGrammar(val, CVectorClock_grammar())
    decreases |val.a|
  {
    assert val.VArray?;
    assert forall v: V {:trigger ValInGrammar(v, CVectorClock_grammar().elt)} {:trigger v in val.a} :: v in val.a ==> ValInGrammar(v, CVectorClock_grammar().elt);
    assert forall i: V {:trigger i.VUint64?} {:trigger i in val.a} :: i in val.a ==> i.VUint64?;
    if |val.a| == 0 then
      []
    else
      var c: int := val.a[0].u as int; var restVal: V := VArray(val.a[1..]); var rest: CVectorClock := parse_CVectorClock(restVal); [c] + rest
  }

  predicate method Uint64InRange(i: int)
    decreases i
  {
    0 <= i < 18446744073709551615
  }

  predicate method CDependencyInRange(d: CDependency)
    decreases d
  {
    forall k: int {:trigger Uint64InRange(k)} {:trigger k in d} :: 
      k in d ==>
        Uint64InRange(k)
  }

  method MarshallCDependency(d: CDependency) returns (val: V)
    ensures ValInGrammar(val, CDependency_grammar())
    decreases |d|
  {
    if CDependencyInRange(d) {
      if |d| == 0 {
        val := VArray([]);
      } else {
        var k :| k in d;
        var kk := 0;
        if 0 <= k < 18446744073709551615 {
          kk := k as uint64;
        } else {
          kk := 18446744073709551615;
          print ""Marshall CDependency overflow\n"";
        }
        var marshalled_k := VUint64(kk);
        var marshalled_vc := MarshallCVectorClock(d[k]);
        var remainder := RemoveElt(d, k);
        var marshalled_remainder := MarshallCDependency(remainder);
        assert ValInGrammar(marshalled_remainder, CDependency_grammar());
        assert ValInGrammar(VTuple([marshalled_k, marshalled_vc]), CDependency_grammar().elt);
        val := VArray([VTuple([marshalled_k, marshalled_vc])] + marshalled_remainder.a);
        assert ValInGrammar(val, CDependency_grammar());
      }
    } else {
      val := VArray([]);
      print ""Marshall CDependency overflow\n"";
    }
  }

  function method parse_CDependency(val: V): CDependency
    requires ValInGrammar(val, CDependency_grammar())
    decreases |val.a|
  {
    if |val.a| == 0 then
      map[]
    else
      var tuple: V := val.a[0]; assert ValInGrammar(tuple, CDependency_grammar().elt); var k: int := tuple.t[0].u as int; var vc: CVectorClock := parse_CVectorClock(tuple.t[1]); var others: CDependency := parse_CDependency(VArray(val.a[1..])); var m: map<CKey, CVectorClock> := others[k := vc]; m
  }

  method MarshallCMeta(m: CMeta) returns (val: V)
    ensures ValInGrammar(val, CMeta_grammar())
    decreases m
  {
    var kk := 0;
    if 0 <= m.key < 18446744073709551615 {
      kk := m.key as uint64;
    } else {
      kk := 18446744073709551615;
      print ""Marshall CMeta overflow\n"";
    }
    var marshalled_k := VUint64(kk);
    var marshalled_vc := MarshallCVectorClock(m.vc);
    assert ValInGrammar(marshalled_vc, CVectorClock_grammar());
    var marshalled_dep := MarshallCDependency(m.deps);
    assert ValInGrammar(marshalled_dep, CDependency_grammar());
    val := VTuple([marshalled_k, marshalled_vc, marshalled_dep]);
    assert ValInGrammar(val, CMeta_grammar());
  }

  function method parse_CMeta(val: V): CMeta
    requires ValInGrammar(val, CMeta_grammar())
    decreases val
  {
    assert ValInGrammar(val, CMeta_grammar());
    CMeta(val.t[0].u as int, parse_CVectorClock(val.t[1]), parse_CDependency(val.t[2]))
  }

  predicate method LocalInRange(d: map<int, CMeta>)
    decreases d
  {
    forall k: int {:trigger Uint64InRange(k)} {:trigger k in d} :: 
      k in d ==>
        Uint64InRange(k)
  }

  method MarshallLocal(m: map<int, CMeta>) returns (val: V)
    ensures ValInGrammar(val, CLocal_grammar())
    decreases m
  {
    if LocalInRange(m) {
      if |m| == 0 {
        val := VArray([]);
      } else {
        var k :| k in m;
        var kk := 0;
        if 0 <= k < 18446744073709551615 {
          kk := k as uint64;
        } else {
          kk := 18446744073709551615;
          print ""Marshall Local overflow\n"";
        }
        var marshalled_k := VUint64(kk);
        var marshalled_meta := MarshallCMeta(m[k]);
        var remainder := RemoveElt(m, k);
        var marshalled_remainder := MarshallLocal(remainder);
        assert ValInGrammar(VTuple([marshalled_k, marshalled_meta]), CLocal_grammar().elt);
        val := VArray([VTuple([marshalled_k, marshalled_meta])] + marshalled_remainder.a);
      }
    } else {
      val := VArray([]);
      print ""Marshall Local overflow\n"";
    }
  }

  function method parse_Local(val: V): map<int, CMeta>
    requires ValInGrammar(val, CLocal_grammar())
    decreases |val.a|
  {
    if |val.a| == 0 then
      map[]
    else
      assert ValInGrammar(val, CLocal_grammar()); var tuple: V := val.a[0]; assert ValInGrammar(tuple, CLocal_grammar().elt); var k: int := tuple.t[0].u as int; var m: CMeta := parse_CMeta(tuple.t[1]); var others: map<int, CMeta> := parse_Local(VArray(val.a[1..])); var r: map<int, CMeta> := others[k := m]; r
  }

  predicate method MsgReadInRange(c: CMessage)
    requires c.CMessage_Read?
    decreases c
  {
    Uint64InRange(c.opn_read) &&
    Uint64InRange(c.key_read)
  }

  method MarshallRead(c: CMessage) returns (val: V)
    requires c.CMessage_Read?
    ensures ValInGrammar(val, CMessage_Read_grmamar())
    decreases c
  {
    var opn: uint64 := 0;
    if 0 <= c.opn_read < 18446744073709551615 {
      opn := c.opn_read as uint64;
    } else {
      opn := 18446744073709551615;
      print ""Marshall Message Read overflow\n"";
    }
    var kk: uint64 := 0;
    if 0 <= c.key_read < 18446744073709551615 {
      kk := c.key_read as uint64;
    } else {
      kk := 18446744073709551615;
      print ""Marshall Message Read overflow\n"";
    }
    var deps := MarshallCDependency(c.deps_read);
    val := VTuple([VUint64(opn), VUint64(kk), deps]);
  }

  function method parse_Read(val: V): CMessage
    requires ValInGrammar(val, CMessage_Read_grmamar())
    decreases val
  {
    assert ValInGrammar(val, CMessage_Read_grmamar());
    CMessage_Read(val.t[0].u as int, val.t[1].u as int, parse_CDependency(val.t[2]))
  }

  method MarshallReadReply(c: CMessage) returns (val: V)
    requires c.CMessage_Read_Reply?
    ensures ValInGrammar(val, CMessage_ReadReply_grammar())
    decreases c
  {
    var opn: uint64 := 0;
    if 0 <= c.opn_rreply < 18446744073709551615 {
      opn := c.opn_rreply as uint64;
    } else {
      opn := 18446744073709551615;
      print ""Marshall Message Read Reply overflow\n"";
    }
    var kk: uint64 := 0;
    if 0 <= c.key_rreply < 18446744073709551615 {
      kk := c.key_rreply as uint64;
    } else {
      kk := 18446744073709551615;
      print ""Marshall Message Read Reply overflow\n"";
    }
    var vc := MarshallCVectorClock(c.vc_rreply);
    var deps := MarshallCDependency(c.deps_rreply);
    val := VTuple([VUint64(opn), VUint64(kk), vc, deps]);
  }

  function method parse_ReadReply(val: V): CMessage
    requires ValInGrammar(val, CMessage_ReadReply_grammar())
    decreases val
  {
    assert ValInGrammar(val, CMessage_ReadReply_grammar());
    CMessage_Read_Reply(val.t[0].u as int, val.t[1].u as int, parse_CVectorClock(val.t[2]), parse_CDependency(val.t[3]))
  }

  method MarshallWrite(c: CMessage) returns (val: V)
    requires c.CMessage_Write?
    ensures ValInGrammar(val, CMessage_Write_grammar())
    decreases c
  {
    var opn: uint64 := 0;
    if 0 <= c.opn_write < 18446744073709551615 {
      opn := c.opn_write as uint64;
    } else {
      opn := 18446744073709551615;
      print ""Marshall Message Write overflow\n"";
    }
    var kk: uint64 := 0;
    if 0 <= c.key_write < 18446744073709551615 {
      kk := c.key_write as uint64;
    } else {
      kk := 18446744073709551615;
      print ""Marshall Message Write overflow\n"";
    }
    var local := MarshallLocal(c.local);
    var deps := MarshallCDependency(c.deps_write);
    var vc := MarshallCVectorClock(c.mvc);
    val := VTuple([VUint64(opn), VUint64(kk), deps, local, vc]);
  }

  function method parse_Write(val: V): CMessage
    requires ValInGrammar(val, CMessage_Write_grammar())
    decreases val
  {
    assert ValInGrammar(val, CMessage_Write_grammar());
    CMessage_Write(val.t[0].u as int, val.t[1].u as int, parse_CDependency(val.t[2]), parse_Local(val.t[3]), parse_CVectorClock(val.t[4]))
  }

  method MarshallWriteReply(c: CMessage) returns (val: V)
    requires c.CMessage_Write_Reply?
    ensures ValInGrammar(val, CMessage_WriteReply_grammar())
    decreases c
  {
    var opn: uint64 := 0;
    if 0 <= c.opn_wreply < 18446744073709551615 {
      opn := c.opn_wreply as uint64;
    } else {
      opn := 18446744073709551615;
      print ""Marshall Message Write Reply overflow\n"";
    }
    var kk: uint64 := 0;
    if 0 <= c.key_wreply < 18446744073709551615 {
      kk := c.key_wreply as uint64;
    } else {
      kk := 18446744073709551615;
      print ""Marshall Message Write Reply overflow\n"";
    }
    var vc := MarshallCVectorClock(c.vc_wreply);
    val := VTuple([VUint64(opn), VUint64(kk), vc]);
  }

  function method parse_WriteReply(val: V): CMessage
    requires ValInGrammar(val, CMessage_WriteReply_grammar())
    decreases val
  {
    assert ValInGrammar(val, CMessage_WriteReply_grammar());
    CMessage_Write_Reply(val.t[0].u as int, val.t[1].u as int, parse_CVectorClock(val.t[2]))
  }

  method MarshallPropagation(c: CMessage) returns (val: V)
    requires c.CMessage_Propagation?
    ensures ValInGrammar(val, CMessage_Propagate_grammar())
    decreases c
  {
    var kk: uint64 := 0;
    if 0 <= c.key < 18446744073709551615 {
      kk := c.key as uint64;
    } else {
      kk := 18446744073709551615;
      print ""Marshall Message Propagation overflow\n"";
    }
    var start: uint64 := 0;
    if 0 <= c.start < 18446744073709551615 {
      start := c.start as uint64;
    } else {
      start := 18446744073709551615;
      print ""Marshall Message Propagation overflow\n"";
    }
    var round: uint64 := 0;
    if 0 <= c.round < 18446744073709551615 {
      round := c.round as uint64;
    } else {
      round := 18446744073709551615;
      print ""Marshall Message Propagation overflow\n"";
    }
    var m := MarshallCMeta(c.meta);
    val := VTuple([VUint64(kk), m, VUint64(start), VUint64(round)]);
  }

  function method parse_Propagation(val: V): CMessage
    requires ValInGrammar(val, CMessage_Propagate_grammar())
    decreases val
  {
    assert ValInGrammar(val, CMessage_Propagate_grammar());
    CMessage_Propagation(val.t[0].u as int, parse_CMeta(val.t[1]), val.t[2].u as int, val.t[3].u as int)
  }

  function method parse_Message(val: V): CMessage
    requires ValInGrammar(val, CMessage_grammar())
    decreases val
  {
    if val.c == 0 then
      parse_Read(val.val)
    else if val.c == 1 then
      parse_ReadReply(val.val)
    else if val.c == 2 then
      parse_Write(val.val)
    else if val.c == 3 then
      parse_WriteReply(val.val)
    else if val.c == 4 then
      parse_Propagation(val.val)
    else
      assert false; parse_Read(val)
  }

  lemma {:axiom} lemma_DemarshallData(data: array<byte>, msg_grammar: G)
    ensures data.Length < 18446744073709551616
    ensures ValidGrammar(msg_grammar)
    decreases data, msg_grammar

  method DemarshallData(data: array<byte>, msg_grammar: G) returns (msg: CMessage)
    requires msg_grammar == CMessage_grammar()
    decreases data, msg_grammar
  {
    lemma_DemarshallData(data, msg_grammar);
    assert data.Length < 18446744073709551616;
    assert ValidGrammar(msg_grammar);
    var success, val := Demarshall(data, msg_grammar);
    if success {
      assert ValInGrammar(val, msg_grammar);
      msg := parse_Message(val);
    } else {
      print ""Parse message fail\n"";
    }
  }

  method MarshallMessage(c: CMessage) returns (val: V)
    ensures ValInGrammar(val, CMessage_grammar())
    decreases c
  {
    if c.CMessage_Read? {
      var msg := MarshallRead(c);
      val := VCase(0, msg);
    } else if c.CMessage_Read_Reply? {
      var msg := MarshallReadReply(c);
      val := VCase(1, msg);
    } else if c.CMessage_Write? {
      var msg := MarshallWrite(c);
      val := VCase(2, msg);
    } else if c.CMessage_Write_Reply? {
      var msg := MarshallWriteReply(c);
      val := VCase(3, msg);
    } else if c.CMessage_Propagation? {
      var msg := MarshallPropagation(c);
      val := VCase(4, msg);
    }
  }

  lemma {:axiom} lemma_MarshallData(val: V)
    ensures ValidVal(val)
    ensures 0 <= SizeOfV(val) < 18446744073709551616
    decreases val

  method MarshallData(msg: CMessage) returns (data: array<byte>)
    decreases msg
  {
    var val := MarshallMessage(msg);
    lemma_MarshallData(val);
    data := Marshall(val, CMessage_grammar());
  }
}

module CausalMesh_CTypes_i {

  import opened CausalMesh_Types_i

  import opened GenericRefinement_i
  type CKey = int

  type CVal = int

  type CVectorClock = seq<int>

  type CDependency = map<CKey, CVectorClock>

  datatype CMeta = CMeta(key: CKey, vc: CVectorClock, deps: CDependency)

  type CCCache = map<CKey, CMeta>

  type CICache = map<CKey, set<CMeta>>

  function method CMergeVCIntoCCache(c1: CCCache, c2: map<Key, CVectorClock>): CCCache
    requires CCCacheIsValid(c1)
    requires forall k: int {:trigger c2[k]} {:trigger k in c2} :: k in c2 ==> CVectorClockIsValid(c2[k])
    requires CCCacheValid(c1)
    requires forall k: int {:trigger k in Keys_domain} {:trigger c2[k]} {:trigger k in c2} :: (k in c2 ==> CVectorClockValid(c2[k])) && (k in c2 ==> k in Keys_domain)
    ensures var lr: CCache := MergeVCIntoCCache(AbstractifyCCCacheToCCache(c1), map k: int {:trigger c2[k]} {:trigger k in c2} | k in c2 :: AbstractifyCVectorClockToVectorClock(c2[k])); var cr: CCCache := CMergeVCIntoCCache(c1, c2); CCCacheIsValid(cr) && CCCacheValid(cr) && AbstractifyCCCacheToCCache(cr) == lr
    decreases c1, c2
  {
    map k: int {:trigger CEmptyMeta(k)} {:trigger c2[k]} {:trigger c1[k]} {:trigger k in c2} {:trigger k in c1} {:trigger k in c1.Keys + c2.Keys} | k in c1.Keys + c2.Keys :: if k in c1 && k in c2 then var m: CMeta := c1[k]; var new_m: CMeta := m.(vc := CVCMerge(m.vc, c2[k])); assert k in Keys_domain && CMetaValid(new_m) && new_m.key == k; new_m else if k in c1 then c1[k] else var m: CMeta := CEmptyMeta(k); assert k in Keys_domain && CMetaValid(m) && m.key == k; m.(vc := c2[k])
  }

  lemma lemma_CMergeVCIntoCCache(c1: CCCache, c2: map<Key, CVectorClock>)
    requires CCCacheIsValid(c1)
    requires forall k: int {:trigger c2[k]} {:trigger k in c2} :: k in c2 ==> CVectorClockIsValid(c2[k])
    requires CCCacheValid(c1)
    requires forall k: int {:trigger k in Keys_domain} {:trigger c2[k]} {:trigger k in c2} :: (k in c2 ==> CVectorClockValid(c2[k])) && (k in c2 ==> k in Keys_domain)
    ensures ghost var cr: CCCache := CMergeVCIntoCCache(c1, c2); (forall k: int {:trigger cr[k]} {:trigger c2[k]} {:trigger k in CMergeVCIntoCCache(c1, c2)} {:trigger k in c2} :: (k in c2 ==> k in CMergeVCIntoCCache(c1, c2)) && (k in c2 ==> CVCEq(c2[k], cr[k].vc) || CVCHappendsBefore(c2[k], cr[k].vc))) && forall k: int {:trigger cr[k]} {:trigger c1[k]} {:trigger k in cr} {:trigger k in c1} :: (k in c1 ==> k in cr) && (k in c1 ==> CVCEq(c1[k].vc, cr[k].vc) || CVCHappendsBefore(c1[k].vc, cr[k].vc))
    decreases c1, c2
  {
  }

  predicate CKeyIsAbstractable(s: CKey)
    decreases s
  {
    true
  }

  predicate CKeyIsValid(s: CKey)
    decreases s
  {
    CKeyIsAbstractable(s)
  }

  function AbstractifyCKeyToKey(s: CKey): Key
    requires CKeyIsAbstractable(s)
    decreases s
  {
    s
  }

  predicate CValIsAbstractable(s: CVal)
    decreases s
  {
    true
  }

  predicate CValIsValid(s: CVal)
    decreases s
  {
    CValIsAbstractable(s)
  }

  function AbstractifyCValToVal(s: CVal): Val
    requires CValIsAbstractable(s)
    decreases s
  {
    s
  }

  predicate CVectorClockIsAbstractable(s: CVectorClock)
    decreases s
  {
    true
  }

  predicate CVectorClockIsValid(s: CVectorClock)
    decreases s
  {
    CVectorClockIsAbstractable(s)
  }

  function AbstractifyCVectorClockToVectorClock(s: CVectorClock): VectorClock
    requires CVectorClockIsAbstractable(s)
    decreases s
  {
    s
  }

  function method CVectorClockValid(vc: CVectorClock): bool
    requires CVectorClockIsValid(vc)
    ensures var lr: bool := VectorClockValid(AbstractifyCVectorClockToVectorClock(vc)); var cr: bool := CVectorClockValid(vc); cr == lr
    decreases vc
  {
    |vc| == Nodes &&
    forall i: int {:trigger vc[i]} :: 
      0 <= i &&
      i < |vc| ==>
        vc[i] >= 0
  }

  function method CEmptyVC(): (res: CVectorClock)
    ensures CVectorClockValid(res)
  {
    seq(Nodes, (idx: int) => 0)
  }

  function method CVCEq(vc1: CVectorClock, vc2: CVectorClock): bool
    requires CVectorClockIsValid(vc1)
    requires CVectorClockIsValid(vc2)
    requires CVectorClockValid(vc1)
    requires CVectorClockValid(vc2)
    ensures var lr: bool := VCEq(AbstractifyCVectorClockToVectorClock(vc1), AbstractifyCVectorClockToVectorClock(vc2)); var cr: bool := CVCEq(vc1, vc2); cr == lr
    decreases vc1, vc2
  {
    forall i: int {:trigger vc2[i]} {:trigger vc1[i]} :: 
      0 <= i &&
      i < |vc1| ==>
        vc1[i] == vc2[i]
  }

  function method CVCHappendsBefore(vc1: CVectorClock, vc2: CVectorClock): bool
    requires CVectorClockIsValid(vc1)
    requires CVectorClockIsValid(vc2)
    requires CVectorClockValid(vc1)
    requires CVectorClockValid(vc2)
    ensures var lr: bool := VCHappendsBefore(AbstractifyCVectorClockToVectorClock(vc1), AbstractifyCVectorClockToVectorClock(vc2)); var cr: bool := CVCHappendsBefore(vc1, vc2); cr == lr
    decreases vc1, vc2
  {
    !CVCEq(vc1, vc2) &&
    forall i: int {:trigger vc2[i]} {:trigger vc1[i]} :: 
      0 <= i &&
      i < |vc1| ==>
        vc1[i] <= vc2[i]
  }

  function method CMergeSeqs(s1: seq<int>, s2: seq<int>): seq<int>
    requires |s1| == |s2|
    ensures var res: seq<int> := CMergeSeqs(s1, s2); |res| == |s1| && (forall i: int {:trigger s2[i]} {:trigger s1[i]} {:trigger res[i]} :: 0 <= i && i < |s1| ==> res[i] == s1[i] || res[i] == s2[i]) && (forall i: int {:trigger s2[i]} {:trigger res[i]} {:trigger s1[i]} :: (0 <= i < |s1| ==> s1[i] <= res[i]) && (0 <= i < |s1| ==> s2[i] <= res[i])) && forall i: int {:trigger s2[i]} {:trigger s1[i]} {:trigger res[i]} :: 0 <= i < |s1| ==> res[i] == s1[i] || res[i] == s2[i]
    ensures var lr: seq<int> := MergeSeqs(s1, s2); var cr: seq<int> := CMergeSeqs(s1, s2); cr == lr
    decreases s1, s2
  {
    if |s1| == 0 then
      []
    else if s1[0] > s2[0] then
      [s1[0]] + CMergeSeqs(s1[1..], s2[1..])
    else
      [s2[0]] + CMergeSeqs(s1[1..], s2[1..])
  }

  function method CVCMerge(vc1: CVectorClock, vc2: CVectorClock): CVectorClock
    requires CVectorClockIsValid(vc1)
    requires CVectorClockIsValid(vc2)
    requires CVectorClockValid(vc1)
    requires CVectorClockValid(vc2)
    ensures var res: CVectorClock := CVCMerge(vc1, vc2); CVectorClockValid(res) && (CVCHappendsBefore(vc1, res) || CVCEq(vc1, res)) && (CVCHappendsBefore(vc2, res) || CVCEq(vc2, res))
    ensures var lr: VectorClock := VCMerge(AbstractifyCVectorClockToVectorClock(vc1), AbstractifyCVectorClockToVectorClock(vc2)); var cr: CVectorClock := CVCMerge(vc1, vc2); CVectorClockIsValid(cr) && AbstractifyCVectorClockToVectorClock(cr) == lr
    decreases vc1, vc2
  {
    CMergeSeqs(vc1, vc2)
  }

  predicate CDependencyIsAbstractable(s: CDependency)
    decreases s
  {
    forall i: int {:trigger s[i]} {:trigger CKeyIsAbstractable(i)} {:trigger i in s} :: 
      (i in s ==>
        CKeyIsAbstractable(i)) &&
      (i in s ==>
        CVectorClockIsAbstractable(s[i]))
  }

  predicate CDependencyIsValid(s: CDependency)
    decreases s
  {
    CDependencyIsAbstractable(s) &&
    forall i: int {:trigger s[i]} {:trigger CKeyIsValid(i)} {:trigger i in s} :: 
      (i in s ==>
        CKeyIsValid(i)) &&
      (i in s ==>
        CVectorClockIsValid(s[i]))
  }

  function AbstractifyCDependencyToDependency(s: CDependency): Dependency
    requires CDependencyIsAbstractable(s)
    decreases s
  {
    AbstractifyMap(s, AbstractifyCKeyToKey, AbstractifyCVectorClockToVectorClock, AbstractifyCKeyToKey)
  }

  function method CDependencyValid(dep: CDependency): bool
    requires CDependencyIsValid(dep)
    ensures var lr: bool := DependencyValid(AbstractifyCDependencyToDependency(dep)); var cr: bool := CDependencyValid(dep); cr == lr
    decreases dep
  {
    forall k: int {:trigger dep[k]} {:trigger k in Keys_domain} {:trigger k in dep} :: 
      (k in dep ==>
        k in Keys_domain) &&
      (k in dep ==>
        CVectorClockValid(dep[k]))
  }

  function method CDependencyEq(dep1: CDependency, dep2: CDependency): bool
    requires CDependencyIsValid(dep1)
    requires CDependencyIsValid(dep2)
    requires CDependencyValid(dep1)
    requires CDependencyValid(dep2)
    ensures var lr: bool := DependencyEq(AbstractifyCDependencyToDependency(dep1), AbstractifyCDependencyToDependency(dep2)); var cr: bool := CDependencyEq(dep1, dep2); cr == lr
    decreases dep1, dep2
  {
    forall k: int {:trigger dep2[k]} {:trigger dep1[k]} {:trigger k in dep2} {:trigger k in dep1} :: 
      (k in dep1 ==>
        k in dep2) &&
      (k in dep1 ==>
        CVCEq(dep1[k], dep2[k]))
  }

  function method CDependencyMerge(dep1: CDependency, dep2: CDependency): CDependency
    requires CDependencyIsValid(dep1)
    requires CDependencyIsValid(dep2)
    requires CDependencyValid(dep1)
    requires CDependencyValid(dep2)
    ensures var res: CDependency := CDependencyMerge(dep1, dep2); CDependencyValid(res)
    ensures var lr: Dependency := DependencyMerge(AbstractifyCDependencyToDependency(dep1), AbstractifyCDependencyToDependency(dep2)); var cr: CDependency := CDependencyMerge(dep1, dep2); CDependencyIsValid(cr) && AbstractifyCDependencyToDependency(cr) == lr
    decreases dep1, dep2
  {
    map k: int {:trigger dep2[k]} {:trigger dep1[k]} {:trigger k in dep2} {:trigger k in dep1} {:trigger k in dep1.Keys + dep2.Keys} | k in dep1.Keys + dep2.Keys :: if k in dep1 && k in dep2 then CVCMerge(dep1[k], dep2[k]) else if k in dep1 then dep1[k] else dep2[k]
  }

  function method CDependencyInsertOrMerge(dep: CDependency, k: CKey, vc: CVectorClock): CDependency
    requires CDependencyIsValid(dep)
    requires CKeyIsValid(k)
    requires CVectorClockIsValid(vc)
    requires CDependencyValid(dep)
    requires k in Keys_domain
    requires CVectorClockValid(vc)
    ensures var lr: Dependency := DependencyInsertOrMerge(AbstractifyCDependencyToDependency(dep), AbstractifyCKeyToKey(k), AbstractifyCVectorClockToVectorClock(vc)); var cr: CDependency := CDependencyInsertOrMerge(dep, k, vc); CDependencyIsValid(cr) && AbstractifyCDependencyToDependency(cr) == lr
    decreases dep, k, vc
  {
    if k in dep then
      var d: map<CKey, CVectorClock> := dep[k := CVCMerge(dep[k], vc)];
      d
    else
      dep[k := vc]
  }

  predicate CMetaIsValid(s: CMeta)
    decreases s
  {
    CMetaIsAbstractable(s) &&
    CKeyIsValid(s.key) &&
    CVectorClockIsValid(s.vc) &&
    CDependencyIsValid(s.deps)
  }

  predicate CMetaIsAbstractable(s: CMeta)
    decreases s
  {
    CKeyIsAbstractable(s.key) &&
    CVectorClockIsAbstractable(s.vc) &&
    CDependencyIsAbstractable(s.deps)
  }

  function AbstractifyCMetaToMeta(s: CMeta): Meta
    requires CMetaIsAbstractable(s)
    decreases s
  {
    Meta(AbstractifyCKeyToKey(s.key), AbstractifyCVectorClockToVectorClock(s.vc), AbstractifyCDependencyToDependency(s.deps))
  }

  function method CEmptyMeta(k: Key): (res: CMeta)
    requires k in Keys_domain
    ensures CMetaValid(res)
    ensures AbstractifyCMetaToMeta(res) == EmptyMeta(k)
    decreases k
  {
    CMeta(k, seq(Nodes, (idx: int) => 0), map[])
  }

  function method CMetaValid(m: CMeta): bool
    requires CMetaIsValid(m)
    ensures var lr: bool := MetaValid(AbstractifyCMetaToMeta(m)); var cr: bool := CMetaValid(m); cr == lr
    decreases m
  {
    m.key in Keys_domain &&
    CVectorClockValid(m.vc) &&
    CDependencyValid(m.deps)
  }

  function method CMetaEq(m1: CMeta, m2: CMeta): bool
    requires CMetaIsValid(m1)
    requires CMetaIsValid(m2)
    requires CMetaValid(m1)
    requires CMetaValid(m2)
    ensures var lr: bool := MetaEq(AbstractifyCMetaToMeta(m1), AbstractifyCMetaToMeta(m2)); var cr: bool := CMetaEq(m1, m2); cr == lr
    decreases m1, m2
  {
    m1.key == m2.key &&
    CVCEq(m1.vc, m2.vc) &&
    CDependencyEq(m1.deps, m2.deps)
  }

  function method CMetaHappensBefore(m1: CMeta, m2: CMeta): bool
    requires CMetaIsValid(m1)
    requires CMetaIsValid(m2)
    requires CMetaValid(m1)
    requires CMetaValid(m2)
    ensures var lr: bool := MetaHappensBefore(AbstractifyCMetaToMeta(m1), AbstractifyCMetaToMeta(m2)); var cr: bool := CMetaHappensBefore(m1, m2); cr == lr
    decreases m1, m2
  {
    CVCHappendsBefore(m1.vc, m2.vc)
  }

  function method CMetaMerge(m1: CMeta, m2: CMeta): CMeta
    requires CMetaIsValid(m1)
    requires CMetaIsValid(m2)
    requires m1.key == m2.key
    requires CMetaValid(m1)
    requires CMetaValid(m2)
    ensures var res: CMeta := CMetaMerge(m1, m2); CMetaValid(res)
    ensures var lr: Meta := MetaMerge(AbstractifyCMetaToMeta(m1), AbstractifyCMetaToMeta(m2)); var cr: CMeta := CMetaMerge(m1, m2); CMetaIsValid(cr) && AbstractifyCMetaToMeta(cr) == lr
    decreases m1, m2
  {
    m1.(vc := CVCMerge(m1.vc, m2.vc), deps := CDependencyMerge(m1.deps, m2.deps))
  }

  method CFoldMetaSet(acc: CMeta, metas: set<CMeta>, ghost domain: set<CKey>)
      returns (res: CMeta)
    requires CMetaIsValid(acc)
    requires forall i: CMeta {:trigger CMetaIsValid(i)} {:trigger i in metas} :: i in metas ==> CMetaIsValid(i)
    requires forall i: int {:trigger CKeyIsValid(i)} {:trigger i in domain} :: i in domain ==> CKeyIsValid(i)
    requires CMetaValid(acc)
    requires forall kk: int {:trigger kk in domain} {:trigger kk in acc.deps} :: kk in acc.deps ==> kk in domain
    requires forall m: CMeta {:trigger m.deps} {:trigger m.key} {:trigger CMetaValid(m)} {:trigger m in metas} :: (m in metas ==> CMetaValid(m)) && (m in metas ==> m.key == acc.key) && (m in metas ==> forall kk: int {:trigger kk in domain} {:trigger kk in m.deps} :: kk in m.deps ==> kk in domain)
    ensures CMetaValid(res)
    ensures var lr: Meta := FoldMetaSet(AbstractifyCMetaToMeta(acc), AbstractifySet(metas, AbstractifyCMetaToMeta), AbstractifySet(domain, AbstractifyCKeyToKey)); CMetaIsValid(res) && AbstractifyCMetaToMeta(res) == lr
    decreases |metas|
  {
    if |metas| == 0 {
      res := acc;
    } else {
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
      assert FoldMetaSet(gacc, gmetas, gdomain) == FoldMetaSet(MetaMerge(gacc, gx), gmetas - {gx}, gdomain);
      assert AbstractifyCMetaToMeta(res) == FoldMetaSet(gacc, gmetas, gdomain);
    }
  }

  lemma {:axiom} lemma_FoldMetaSet(acc: Meta, metas: set<Meta>, domain: set<Key>, x: Meta)
    requires MetaValid(acc)
    requires MetaValid(x)
    requires x in metas
    requires forall m: Meta {:trigger m.deps} {:trigger m.key} {:trigger MetaValid(m)} {:trigger m in metas} :: (m in metas ==> MetaValid(m)) && (m in metas ==> m.key == acc.key) && (m in metas ==> forall kk: int {:trigger kk in domain} {:trigger kk in m.deps} :: kk in m.deps ==> kk in domain)
    requires forall kk: int {:trigger kk in domain} {:trigger kk in acc.deps} :: kk in acc.deps ==> kk in domain
    ensures FoldMetaSet(acc, metas, domain) == FoldMetaSet(MetaMerge(acc, x), metas - {x}, domain)
    decreases acc, metas, domain, x

  method CFoldVC(acc: CVectorClock, vcs: set<CVectorClock>) returns (res: CVectorClock)
    requires CVectorClockIsValid(acc)
    requires forall i: CVectorClock {:trigger CVectorClockIsValid(i)} {:trigger i in vcs} :: i in vcs ==> CVectorClockIsValid(i)
    requires CVectorClockValid(acc)
    requires forall m: CVectorClock {:trigger CVectorClockValid(m)} {:trigger m in vcs} :: m in vcs ==> CVectorClockValid(m)
    ensures CVectorClockValid(res)
    ensures var lr: VectorClock := FoldVC(AbstractifyCVectorClockToVectorClock(acc), AbstractifySet(vcs, AbstractifyCVectorClockToVectorClock)); CVectorClockIsValid(res) && AbstractifyCVectorClockToVectorClock(res) == lr
    decreases |vcs|
  {
    if |vcs| == 0 {
      res := acc;
    } else {
      var x :| x in vcs;
      ghost var merged := CVCMerge(acc, x);
      var nvcs := vcs - {x};
      var r := CFoldVC(CVCMerge(acc, x), nvcs);
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

  lemma {:axiom} lemma_FoldVC(acc: VectorClock, vcs: set<VectorClock>, x: VectorClock)
    requires VectorClockValid(acc)
    requires VectorClockValid(x)
    requires x in vcs
    requires forall vc: VectorClock {:trigger VectorClockValid(vc)} {:trigger vc in vcs} :: vc in vcs ==> VectorClockValid(vc)
    ensures FoldVC(acc, vcs) == FoldVC(VCMerge(acc, x), vcs - {x})
    decreases acc, vcs, x

  method CFoldDependencyFromMetaSet(acc: CDependency, metas: set<CMeta>) returns (res: CDependency)
    requires CDependencyIsValid(acc)
    requires forall i: CMeta {:trigger CMetaIsValid(i)} {:trigger i in metas} :: i in metas ==> CMetaIsValid(i)
    requires CDependencyValid(acc)
    requires forall m: CMeta {:trigger CMetaValid(m)} {:trigger m in metas} :: m in metas ==> CMetaValid(m)
    ensures CDependencyValid(res)
    ensures var lr: Dependency := FoldDependencyFromMetaSet(AbstractifyCDependencyToDependency(acc), AbstractifySet(metas, AbstractifyCMetaToMeta)); CDependencyIsValid(res) && AbstractifyCDependencyToDependency(res) == lr
    decreases |metas|
  {
    if |metas| == 0 {
      res := acc;
    } else {
      var x :| x in metas;
      res := CFoldDependencyFromMetaSet(CDependencyMerge(acc, x.deps), metas - {x});
      ghost var gacc := AbstractifyCDependencyToDependency(acc);
      lemma_AbstractifyCMetaToMeta_Is_Injective(metas);
      ghost var gmetas := AbstractifySet(metas, AbstractifyCMetaToMeta);
      ghost var gnmetas := AbstractifySet(metas - {x}, AbstractifyCMetaToMeta);
      ghost var gx := AbstractifyCMetaToMeta(x);
      assert gnmetas == gmetas - {gx};
      lemma_FoldDependencyFromMetaSet(gacc, gmetas, gx);
      assert FoldDependencyFromMetaSet(gacc, gmetas) == FoldDependencyFromMetaSet(DependencyMerge(gacc, gx.deps), gmetas - {gx});
      assert AbstractifyCDependencyToDependency(res) == FoldDependencyFromMetaSet(gacc, gmetas);
    }
  }

  lemma {:axiom} lemma_FoldDependencyFromMetaSet(acc: CDependency, metas: set<Meta>, x: Meta)
    requires DependencyValid(acc)
    requires MetaValid(x)
    requires x in metas
    requires forall m: Meta {:trigger MetaValid(m)} {:trigger m in metas} :: m in metas ==> MetaValid(m)
    ensures FoldDependencyFromMetaSet(acc, metas) == FoldDependencyFromMetaSet(DependencyMerge(acc, x.deps), metas - {x})
    decreases acc, metas, x

  predicate CCCacheIsAbstractable(s: CCCache)
    decreases s
  {
    forall i: int {:trigger s[i]} {:trigger CKeyIsAbstractable(i)} {:trigger i in s} :: 
      (i in s ==>
        CKeyIsAbstractable(i)) &&
      (i in s ==>
        CMetaIsAbstractable(s[i]))
  }

  predicate CCCacheIsValid(s: CCCache)
    decreases s
  {
    CCCacheIsAbstractable(s) &&
    forall i: int {:trigger s[i]} {:trigger CKeyIsValid(i)} {:trigger i in s} :: 
      (i in s ==>
        CKeyIsValid(i)) &&
      (i in s ==>
        CMetaIsValid(s[i]))
  }

  function AbstractifyCCCacheToCCache(s: CCCache): CCache
    requires CCCacheIsAbstractable(s)
    decreases s
  {
    AbstractifyMap(s, AbstractifyCKeyToKey, AbstractifyCMetaToMeta, AbstractifyCKeyToKey)
  }

  function CCCacheValid(c: CCCache): bool
    requires CCCacheIsValid(c)
    ensures ghost var lr: bool := CCacheValid(AbstractifyCCCacheToCCache(c)); ghost var cr: bool := CCCacheValid(c); cr == lr
    decreases c
  {
    forall k: int {:trigger c[k]} {:trigger k in Keys_domain} {:trigger k in c} :: 
      (k in c ==>
        k in Keys_domain) &&
      (k in c ==>
        CMetaValid(c[k])) &&
      (k in c ==>
        c[k].key == k)
  }

  predicate CICacheIsValid(c: CICache)
    decreases c
  {
    true
  }

  function AbstractifyCICacheToICache(s: CICache): ICache
    decreases s
  {
    map k: int {:trigger s[k]} | k in set ck: int {:trigger ck in s} | ck in s :: ck :: set i: CMeta {:trigger AbstractifyCMetaToMeta(i)} {:trigger i in s[k]} | i in s[k] :: AbstractifyCMetaToMeta(i)
  }

  function CICacheValid(c: CICache): bool
    requires CICacheIsValid(c)
    ensures ghost var lr: bool := ICacheValid(AbstractifyCICacheToICache(c)); ghost var cr: bool := CICacheValid(c); cr == lr
    decreases c
  {
    ghost var gc: ICache := AbstractifyCICacheToICache(c);
    assert (forall k: int {:trigger k in Keys_domain} {:trigger k in c} :: k in c ==> k in Keys_domain) == forall k: int {:trigger k in Keys_domain} {:trigger k in gc} :: k in gc ==> k in Keys_domain;
    lemma_AbstractifyCICache(c);
    assert forall k: int {:trigger c[k]} {:trigger k in c} :: k in c ==> forall i: CMeta, j: CMeta {:trigger AbstractifyCMetaToMeta(j), AbstractifyCMetaToMeta(i)} {:trigger AbstractifyCMetaToMeta(j), i in c[k]} {:trigger AbstractifyCMetaToMeta(i), j in c[k]} {:trigger j in c[k], i in c[k]} :: i in c[k] && j in c[k] && AbstractifyCMetaToMeta(i) == AbstractifyCMetaToMeta(j) ==> i == j;
    forall k: int {:trigger c[k]} {:trigger k in Keys_domain} {:trigger k in c} :: 
      (k in c ==>
        k in Keys_domain) &&
      (k in c ==>
        forall m: CMeta {:trigger m.deps} {:trigger m.key} {:trigger CMetaValid(m)} {:trigger m in c[k]} :: 
          (m in c[k] ==>
            CMetaValid(m)) &&
          (m in c[k] ==>
            m.key == k) &&
          (m in c[k] ==>
            forall kk: int {:trigger kk in c} {:trigger kk in m.deps} :: 
              kk in m.deps ==>
                kk in c))
  }

  lemma lemma_AbstractifyCMetaToMeta_Is_Injective(s: set<CMeta>)
    requires forall m: CMeta {:trigger CMetaIsValid(m)} {:trigger m in s} :: m in s ==> CMetaIsValid(m)
    ensures SetIsInjective(s, AbstractifyCMetaToMeta)
    decreases s
  {
  }

  lemma lemma_AbstractifyCICache(c: CICache)
    requires CICacheIsValid(c)
    ensures forall k: int {:trigger c[k]} {:trigger k in c} :: k in c ==> forall i: CMeta, j: CMeta {:trigger AbstractifyCMetaToMeta(j), AbstractifyCMetaToMeta(i)} {:trigger AbstractifyCMetaToMeta(j), i in c[k]} {:trigger AbstractifyCMetaToMeta(i), j in c[k]} {:trigger j in c[k], i in c[k]} :: i in c[k] && j in c[k] && AbstractifyCMetaToMeta(i) == AbstractifyCMetaToMeta(j) ==> i == j
    decreases c
  {
  }

  function method CNodesAreNext(i: int, j: int): bool
    requires 0 <= i && i < Nodes
    requires 0 <= j && j < Nodes
    ensures var lr: bool := NodesAreNext(i, j); var cr: bool := CNodesAreNext(i, j); cr == lr
    decreases i, j
  {
    if i == Nodes - 1 then
      j == 0
    else
      j == i + 1
  }
}

module CausalMesh_Types_i {
  type Key = int

  type Val = int

  type VectorClock = seq<int>

  type Dependency = map<Key, VectorClock>

  datatype Meta = Meta(key: Key, vc: VectorClock, deps: Dependency)

  type CCache = map<Key, Meta>

  type ICache = map<Key, set<Meta>>

  const Nodes: nat := 3
  const Clients: nat := 5
  const MaxKeys: nat := 1000
  const Keys_domain: set<int> := set i: int | 0 <= i <= 1000 :: i

  predicate VectorClockValid(vc: VectorClock)
    decreases vc
  {
    |vc| == Nodes &&
    forall i: int {:trigger vc[i]} :: 
      0 <= i < |vc| ==>
        vc[i] >= 0
  }

  function EmptyVC(): (res: VectorClock)
  {
    seq(Nodes, (idx: int) => 0)
  }

  function VCEq(vc1: VectorClock, vc2: VectorClock): bool
    requires VectorClockValid(vc1)
    requires VectorClockValid(vc2)
    decreases vc1, vc2
  {
    forall i: int {:trigger vc2[i]} {:trigger vc1[i]} :: 
      0 <= i < |vc1| ==>
        vc1[i] == vc2[i]
  }

  function VCHappendsBefore(vc1: VectorClock, vc2: VectorClock): bool
    requires VectorClockValid(vc1)
    requires VectorClockValid(vc2)
    decreases vc1, vc2
  {
    !VCEq(vc1, vc2) &&
    forall i: int {:trigger vc2[i]} {:trigger vc1[i]} :: 
      0 <= i < |vc1| ==>
        vc1[i] <= vc2[i]
  }

  function MergeSeqs(s1: seq<int>, s2: seq<int>): seq<int>
    requires |s1| == |s2|
    ensures ghost var res: seq<int> := MergeSeqs(s1, s2); |res| == |s1| && forall i: int {:trigger s2[i]} {:trigger s1[i]} {:trigger res[i]} :: 0 <= i < |s1| ==> res[i] == s1[i] || res[i] == s2[i]
    decreases s1, s2
  {
    if |s1| == 0 then
      []
    else if s1[0] > s2[0] then
      [s1[0]] + MergeSeqs(s1[1..], s2[1..])
    else
      [s2[0]] + MergeSeqs(s1[1..], s2[1..])
  }

  function VCMerge(vc1: VectorClock, vc2: VectorClock): VectorClock
    requires VectorClockValid(vc1)
    requires VectorClockValid(vc2)
    ensures ghost var res: VectorClock := VCMerge(vc1, vc2); VectorClockValid(res)
    decreases vc1, vc2
  {
    MergeSeqs(vc1, vc2)
  }

  predicate DependencyValid(dep: Dependency)
    decreases dep
  {
    forall k: int {:trigger dep[k]} {:trigger k in Keys_domain} {:trigger k in dep} :: 
      (k in dep ==>
        k in Keys_domain) &&
      (k in dep ==>
        VectorClockValid(dep[k]))
  }

  function DependencyEq(dep1: Dependency, dep2: Dependency): bool
    requires DependencyValid(dep1)
    requires DependencyValid(dep2)
    decreases dep1, dep2
  {
    forall k: int {:trigger dep2[k]} {:trigger dep1[k]} {:trigger k in dep2} {:trigger k in dep1} :: 
      (k in dep1 ==>
        k in dep2) &&
      (k in dep1 ==>
        VCEq(dep1[k], dep2[k]))
  }

  function DependencyMerge(dep1: Dependency, dep2: Dependency): Dependency
    requires DependencyValid(dep1)
    requires DependencyValid(dep2)
    ensures ghost var res: Dependency := DependencyMerge(dep1, dep2); DependencyValid(res)
    decreases dep1, dep2
  {
    map k: int {:trigger dep2[k]} {:trigger dep1[k]} {:trigger k in dep2} {:trigger k in dep1} {:trigger k in dep1.Keys + dep2.Keys} | k in dep1.Keys + dep2.Keys :: if k in dep1 && k in dep2 then VCMerge(dep1[k], dep2[k]) else if k in dep1 then dep1[k] else dep2[k]
  }

  function DependencyInsertOrMerge(dep: Dependency, k: Key, vc: VectorClock): Dependency
    requires DependencyValid(dep)
    requires k in Keys_domain
    requires VectorClockValid(vc)
    decreases dep, k, vc
  {
    if k in dep then
      ghost var d: map<Key, VectorClock> := dep[k := VCMerge(dep[k], vc)];
      d
    else
      dep[k := vc]
  }

  predicate MetaValid(m: Meta)
    decreases m
  {
    m.key in Keys_domain &&
    VectorClockValid(m.vc) &&
    DependencyValid(m.deps)
  }

  predicate MetaEq(m1: Meta, m2: Meta)
    requires MetaValid(m1)
    requires MetaValid(m2)
    decreases m1, m2
  {
    m1.key == m2.key &&
    VCEq(m1.vc, m2.vc) &&
    DependencyEq(m1.deps, m2.deps)
  }

  predicate MetaHappensBefore(m1: Meta, m2: Meta)
    requires MetaValid(m1)
    requires MetaValid(m2)
    decreases m1, m2
  {
    VCHappendsBefore(m1.vc, m2.vc)
  }

  function MetaMerge(m1: Meta, m2: Meta): Meta
    requires m1.key == m2.key
    requires MetaValid(m1)
    requires MetaValid(m2)
    ensures ghost var res: Meta := MetaMerge(m1, m2); MetaValid(res)
    decreases m1, m2
  {
    m1.(vc := VCMerge(m1.vc, m2.vc), deps := DependencyMerge(m1.deps, m2.deps))
  }

  function FoldMetaSet(acc: Meta, metas: set<Meta>, domain: set<Key>): Meta
    requires MetaValid(acc)
    requires forall kk: int {:trigger kk in domain} {:trigger kk in acc.deps} :: kk in acc.deps ==> kk in domain
    requires forall m: Meta {:trigger m.deps} {:trigger m.key} {:trigger MetaValid(m)} {:trigger m in metas} :: (m in metas ==> MetaValid(m)) && (m in metas ==> m.key == acc.key) && (m in metas ==> forall kk: int {:trigger kk in domain} {:trigger kk in m.deps} :: kk in m.deps ==> kk in domain)
    ensures ghost var res: Meta := FoldMetaSet(acc, metas, domain); MetaValid(res) && forall kk: int {:trigger kk in domain} {:trigger kk in res.deps} :: kk in res.deps ==> kk in domain
    decreases |metas|
  {
    if |metas| == 0 then
      acc
    else
      ghost var x: Meta :| x in metas; FoldMetaSet(MetaMerge(acc, x), metas - {x}, domain)
  }

  function FoldVC(acc: VectorClock, vcs: set<VectorClock>): VectorClock
    requires VectorClockValid(acc)
    requires forall m: VectorClock {:trigger VectorClockValid(m)} {:trigger m in vcs} :: m in vcs ==> VectorClockValid(m)
    ensures ghost var res: VectorClock := FoldVC(acc, vcs); VectorClockValid(res)
    decreases |vcs|
  {
    if |vcs| == 0 then
      acc
    else
      ghost var x: seq<int> :| x in vcs; ghost var merged: VectorClock := VCMerge(acc, x); ghost var res: VectorClock := FoldVC(VCMerge(acc, x), vcs - {x}); res
  }

  function FoldDependency(acc: Dependency, deps: set<Dependency>): Dependency
    requires DependencyValid(acc)
    requires forall m: Dependency {:trigger DependencyValid(m)} {:trigger m in deps} :: m in deps ==> DependencyValid(m)
    ensures ghost var res: Dependency := FoldDependency(acc, deps); DependencyValid(res)
    decreases |deps|
  {
    if |deps| == 0 then
      acc
    else
      ghost var x: map<Key, VectorClock> :| x in deps; FoldDependency(DependencyMerge(acc, x), deps - {x})
  }

  function FoldDependencyFromMetaSet(acc: Dependency, metas: set<Meta>): Dependency
    requires DependencyValid(acc)
    requires forall m: Meta {:trigger MetaValid(m)} {:trigger m in metas} :: m in metas ==> MetaValid(m)
    ensures ghost var res: Dependency := FoldDependencyFromMetaSet(acc, metas); DependencyValid(res)
    decreases |metas|
  {
    if |metas| == 0 then
      acc
    else
      ghost var x: Meta :| x in metas; FoldDependencyFromMetaSet(DependencyMerge(acc, x.deps), metas - {x})
  }

  function EmptyMeta(k: Key): Meta
    decreases k
  {
    Meta(k, seq(Nodes, (idx: int) => 0), map[])
  }

  predicate CCacheValid(c: CCache)
    decreases c
  {
    forall k: int {:trigger c[k]} {:trigger k in Keys_domain} {:trigger k in c} :: 
      (k in c ==>
        k in Keys_domain) &&
      (k in c ==>
        MetaValid(c[k])) &&
      (k in c ==>
        c[k].key == k)
  }

  function MergeCCache(c1: CCache, c2: CCache): CCache
    requires CCacheValid(c1)
    requires CCacheValid(c2)
    decreases c1, c2
  {
    map k: int {:trigger c2[k]} {:trigger c1[k]} {:trigger k in c2} {:trigger k in c1} {:trigger k in c1.Keys + c2.Keys} | k in c1.Keys + c2.Keys :: if k in c1 && k in c2 then MetaMerge(c1[k], c2[k]) else if k in c1 then c1[k] else c2[k]
  }

  function MergeVCIntoCCache(c1: CCache, c2: map<Key, VectorClock>): CCache
    requires CCacheValid(c1)
    requires forall k: int {:trigger k in Keys_domain} {:trigger c2[k]} {:trigger k in c2} :: (k in c2 ==> VectorClockValid(c2[k])) && (k in c2 ==> k in Keys_domain)
    ensures CCacheValid(MergeVCIntoCCache(c1, c2))
    decreases c1, c2
  {
    map k: int {:trigger EmptyMeta(k)} {:trigger c2[k]} {:trigger c1[k]} {:trigger k in c2} {:trigger k in c1} {:trigger k in c1.Keys + c2.Keys} | k in c1.Keys + c2.Keys :: if k in c1 && k in c2 then ghost var m: Meta := c1[k]; ghost var new_m: Meta := m.(vc := VCMerge(m.vc, c2[k])); new_m else if k in c1 then c1[k] else ghost var m: Meta := EmptyMeta(k); m.(vc := c2[k])
  }

  predicate ICacheValid(c: ICache)
    decreases c
  {
    forall k: int {:trigger c[k]} {:trigger k in Keys_domain} {:trigger k in c} :: 
      (k in c ==>
        k in Keys_domain) &&
      (k in c ==>
        forall m: Meta {:trigger m.deps} {:trigger m.key} {:trigger MetaValid(m)} {:trigger m in c[k]} :: 
          (m in c[k] ==>
            MetaValid(m)) &&
          (m in c[k] ==>
            m.key == k) &&
          (m in c[k] ==>
            forall kk: int {:trigger kk in c} {:trigger kk in m.deps} :: 
              kk in m.deps ==>
                kk in c))
  }

  predicate NodesAreNext(i: int, j: int)
    requires 0 <= i < Nodes
    requires 0 <= j < Nodes
    decreases i, j
  {
    if i == Nodes - 1 then
      j == 0
    else
      j == i + 1
  }
}

module GenericRefinement_i {

  import opened Native__NativeTypes_s

  import opened Collections__Maps_i

  import opened Collections__Sets_i

  import opened Logic__Option_i
  function uint64_to_int(u: uint64): int
    decreases u
  {
    u as int
  }

  function int_to_int(u: int): int
    decreases u
  {
    u as int
  }

  function nat_to_nat(n: nat): nat
    decreases n
  {
    n
  }

  predicate OptionalIsAbstractable<CT(!new), T>(ov: Option<CT>, refine_func: CT ~> T)
    reads set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in refine_func.reads(_x0)} | _obj in refine_func.reads(_x0) :: _obj
    decreases set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in refine_func.reads(_x0)} | _obj in refine_func.reads(_x0) :: _obj, ov
  {
    match ov
    case Some(v) =>
      refine_func.requires(v)
    case None() =>
      true
  }

  function AbstractifyOptional<CT(!new), T>(ov: Option<CT>, refine_func: CT ~> T): Option<T>
    requires OptionalIsAbstractable(ov, refine_func)
    reads set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in refine_func.reads(_x0)} | _obj in refine_func.reads(_x0) :: _obj
    decreases set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in refine_func.reads(_x0)} | _obj in refine_func.reads(_x0) :: _obj, ov
  {
    match ov {
      case Some(v) =>
        Some(refine_func(v))
      case None() =>
        None()
    }
  }

  function {:opaque} {:fuel 0, 0} MapSeqToSeq<T(!new), U>(s: seq<T>, refine_func: T ~> U): seq<U>
    requires forall i: T {:trigger refine_func.reads(i)} :: refine_func.reads(i) == {}
    requires forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> refine_func.requires(s[i])
    reads set _x0: T, _obj: object? /*{:_reads}*/ {:trigger _obj in refine_func.reads(_x0)} | _obj in refine_func.reads(_x0) :: _obj
    ensures |MapSeqToSeq(s, refine_func)| == |s|
    ensures forall i: int {:trigger MapSeqToSeq(s, refine_func)[i]} {:trigger s[i]} :: 0 <= i < |s| ==> refine_func(s[i]) == MapSeqToSeq(s, refine_func)[i]
    decreases set _x0: T, _obj: object? /*{:_reads}*/ {:trigger _obj in refine_func.reads(_x0)} | _obj in refine_func.reads(_x0) :: _obj, s
  {
    if |s| == 0 then
      []
    else
      [refine_func(s[0])] + MapSeqToSeq(s[1..], refine_func)
  }

  predicate IsInjective<CT(!new), T(!new)>(f: CT ~> T)
    reads set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    decreases set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
  {
    forall i: CT, j: CT {:trigger f(j), f(i)} {:trigger f(j), f.requires(i)} {:trigger f(i), f.requires(j)} {:trigger f.requires(j), f.requires(i)} :: 
      f.requires(i) &&
      f.requires(j) &&
      f(i) == f(j) ==>
        i == j
  }

  predicate SeqIsAbstractable<T(!new), CT(!new)>(s: seq<CT>, RefineValue: CT ~> T)
    reads set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineValue.reads(_x0)} | _obj in RefineValue.reads(_x0) :: _obj
    decreases set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineValue.reads(_x0)} | _obj in RefineValue.reads(_x0) :: _obj, s
  {
    forall i: CT {:trigger RefineValue.requires(i)} {:trigger i in s} :: 
      i in s ==>
        RefineValue.requires(i)
  }

  function NoChange<T(!new)>(v: T): T
  {
    v
  }

  predicate MapIsValid<CKT(!new), CVT(!new)>(m: map<CKT, CVT>, ValidateKey: CKT ~> bool, ValidateValue: CVT ~> bool)
    reads set _x0: CKT, _obj: object? /*{:_reads}*/ {:trigger _obj in ValidateKey.reads(_x0)} | _obj in ValidateKey.reads(_x0) :: _obj, set _x0: CVT, _obj: object? /*{:_reads}*/ {:trigger _obj in ValidateValue.reads(_x0)} | _obj in ValidateValue.reads(_x0) :: _obj
    decreases (set _x0: CKT, _obj: object? /*{:_reads}*/ {:trigger _obj in ValidateKey.reads(_x0)} | _obj in ValidateKey.reads(_x0) :: _obj) + set _x0: CVT, _obj: object? /*{:_reads}*/ {:trigger _obj in ValidateValue.reads(_x0)} | _obj in ValidateValue.reads(_x0) :: _obj, m
  {
    forall k: CKT {:trigger m[k]} {:trigger ValidateKey(k)} {:trigger ValidateKey.requires(k)} {:trigger k in m} :: 
      (k in m ==>
        ValidateKey.requires(k)) &&
      (k in m ==>
        ValidateKey(k)) &&
      (k in m ==>
        ValidateValue.requires(m[k])) &&
      (k in m ==>
        ValidateValue(m[k]))
  }

  predicate SeqIsValid<CT(!new)>(s: seq<CT>, ValidateValue: CT ~> bool)
    reads set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in ValidateValue.reads(_x0)} | _obj in ValidateValue.reads(_x0) :: _obj
    decreases set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in ValidateValue.reads(_x0)} | _obj in ValidateValue.reads(_x0) :: _obj, s
  {
    forall i: CT {:trigger ValidateValue(i)} {:trigger ValidateValue.requires(i)} {:trigger i in s} :: 
      (i in s ==>
        ValidateValue.requires(i)) &&
      (i in s ==>
        ValidateValue(i))
  }

  function AbstractifySeq<T(!new), CT(!new)>(s: seq<CT>, RefineValue: CT ~> T): seq<T>
    requires SeqIsAbstractable(s, RefineValue)
    reads set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineValue.reads(_x0)} | _obj in RefineValue.reads(_x0) :: _obj
    ensures ghost var cs: seq<T> := AbstractifySeq(s, RefineValue); |cs| == |s| && (forall i: int {:trigger s[i]} {:trigger cs[i]} :: 0 <= i < |s| ==> cs[i] == RefineValue(s[i])) && forall i: T {:trigger i in cs} :: i in cs ==> exists x: CT {:trigger RefineValue(x)} {:trigger x in s} :: x in s && i == RefineValue(x)
    decreases set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineValue.reads(_x0)} | _obj in RefineValue.reads(_x0) :: _obj, s
  {
    ghost var cs: seq<T> := if |s| == 0 then [] else [RefineValue(s[0])] + AbstractifySeq(s[1..], RefineValue);
    assert forall i: T {:trigger i in cs} :: i in cs ==> exists x: CT {:trigger RefineValue(x)} {:trigger x in s} :: x in s && i == RefineValue(x);
    cs
  }

  lemma /*{:_induction s1, s2, RefineValue}*/ lemma_seq_concat<T(!new), CT(!new)>(s1: seq<CT>, s2: seq<CT>, RefineValue: CT ~> T)
    requires SeqIsAbstractable(s1, RefineValue)
    requires SeqIsAbstractable(s2, RefineValue)
    ensures AbstractifySeq(s1, RefineValue) + AbstractifySeq(s2, RefineValue) == AbstractifySeq(s1 + s2, RefineValue)
    ensures SeqIsAbstractable(s1 + s2, RefineValue)
    decreases s1, s2
  {
  }

  lemma /*{:_induction s, RefineValue}*/ lemma_seq_sub<T(!new), CT(!new)>(s: seq<CT>, RefineValue: CT ~> T, l: int, r: int)
    requires SeqIsAbstractable(s, RefineValue)
    requires 0 <= l <= r <= |s|
    ensures AbstractifySeq(s[l .. r], RefineValue) == AbstractifySeq(s, RefineValue)[l .. r]
    decreases s, l, r
  {
  }

  predicate SetIsInjective<T(!new), CT(!new)>(s: set<CT>, f: CT ~> T)
    requires SetIsAbstractable(s, f)
    reads set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    decreases set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj, s
  {
    forall i: CT, j: CT {:trigger f(j), f(i)} {:trigger f(j), f.requires(i)} {:trigger f(j), i in s} {:trigger f(i), f.requires(j)} {:trigger f(i), j in s} {:trigger f.requires(j), f.requires(i)} {:trigger f.requires(j), i in s} {:trigger f.requires(i), j in s} {:trigger j in s, i in s} :: 
      i in s &&
      j in s &&
      f.requires(i) &&
      f.requires(j) &&
      f(i) == f(j) ==>
        i == j
  }

  predicate SetIsAbstractable<T(!new), CT(!new)>(s: set<CT>, RefineValue: CT ~> T)
    reads set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineValue.reads(_x0)} | _obj in RefineValue.reads(_x0) :: _obj
    decreases set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineValue.reads(_x0)} | _obj in RefineValue.reads(_x0) :: _obj, s
  {
    forall k: CT {:trigger RefineValue.requires(k)} {:trigger k in s} :: 
      k in s ==>
        RefineValue.requires(k)
  }

  function AbstractifySet<T(!new), CT(!new)>(s: set<CT>, RefineValue: CT ~> T): set<T>
    requires SetIsAbstractable(s, RefineValue)
    requires forall x: CT, y: CT {:trigger RefineValue(y), RefineValue(x)} {:trigger RefineValue(y), x in s} {:trigger RefineValue(x), y in s} {:trigger y in s, x in s} :: x in s && y in s && RefineValue(x) == RefineValue(y) ==> x == y
    reads set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineValue.reads(_x0)} | _obj in RefineValue.reads(_x0) :: _obj
    ensures ghost var ss: set<T> := AbstractifySet(s, RefineValue); (forall k: CT {:trigger RefineValue(k)} {:trigger k in s} :: k in s ==> RefineValue(k) in ss) && |ss| == |s|
    decreases set _x0: CT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineValue.reads(_x0)} | _obj in RefineValue.reads(_x0) :: _obj, s
  {
    ghost var ss: set<T> := set i: CT {:trigger RefineValue(i)} {:trigger i in s} | i in s :: RefineValue(i);
    lemma_AbstractifySet_SizeUnchange(s, ss, RefineValue);
    ss
  }

  lemma lemma_AbstractifySet_SizeUnchange<T(!new), CT(!new)>(s: set<CT>, ss: set<T>, f: CT ~> T)
    requires forall x: CT {:trigger f.requires(x)} {:trigger x in s} :: x in s ==> f.requires(x)
    requires forall x: CT, y: CT {:trigger f(y), f(x)} {:trigger f(y), x in s} {:trigger f(x), y in s} {:trigger y in s, x in s} :: x in s && y in s && f(x) == f(y) ==> x == y
    requires forall x: CT {:trigger f(x)} {:trigger x in s} :: x in s ==> f(x) in ss
    requires forall y: T {:trigger y in ss} :: y in ss <==> exists x: CT {:trigger f(x)} {:trigger x in s} :: x in s && y == f(x)
    ensures |s| == |ss|
    decreases s, ss
  {
  }

  predicate MapIsAbstractable<KT(!new), VT, CKT(!new), CVT(!new)>(m: map<CKT, CVT>, RefineKey: CKT ~> KT, RefineValue: CVT ~> VT, ReverseKey: KT ~> CKT)
    reads set _x0: CKT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineKey.reads(_x0)} | _obj in RefineKey.reads(_x0) :: _obj, set _x0: CVT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineValue.reads(_x0)} | _obj in RefineValue.reads(_x0) :: _obj, set _x0: KT, _obj: object? /*{:_reads}*/ {:trigger _obj in ReverseKey.reads(_x0)} | _obj in ReverseKey.reads(_x0) :: _obj
    decreases (set _x0: CKT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineKey.reads(_x0)} | _obj in RefineKey.reads(_x0) :: _obj) + (set _x0: CVT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineValue.reads(_x0)} | _obj in RefineValue.reads(_x0) :: _obj) + set _x0: KT, _obj: object? /*{:_reads}*/ {:trigger _obj in ReverseKey.reads(_x0)} | _obj in ReverseKey.reads(_x0) :: _obj, m
  {
    (forall ck: CKT {:trigger m[ck]} {:trigger RefineKey.requires(ck)} {:trigger ck in m} :: 
      (ck in m ==>
        RefineKey.requires(ck)) &&
      (ck in m ==>
        RefineValue.requires(m[ck]))) &&
    forall ck: CKT {:trigger RefineKey(ck)} {:trigger ck in m} :: 
      (ck in m ==>
        ReverseKey.requires(RefineKey(ck))) &&
      (ck in m ==>
        ReverseKey(RefineKey(ck)) == ck)
  }

  function {:opaque} {:fuel 0, 0} AbstractifyMap<CKT(!new), CVT(!new), KT(!new), VT>(m: map<CKT, CVT>, RefineKey: CKT ~> KT, RefineValue: CVT ~> VT, ReverseKey: KT ~> CKT): map<KT, VT>
    requires forall ck: CKT {:trigger m[ck]} {:trigger RefineKey.requires(ck)} {:trigger ck in m} :: (ck in m ==> RefineKey.requires(ck)) && (ck in m ==> RefineValue.requires(m[ck]))
    requires forall ck: CKT {:trigger RefineKey(ck)} {:trigger ck in m} :: (ck in m ==> ReverseKey.requires(RefineKey(ck))) && (ck in m ==> ReverseKey(RefineKey(ck)) == ck)
    reads set _x0: CKT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineKey.reads(_x0)} | _obj in RefineKey.reads(_x0) :: _obj, set _x0: CVT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineValue.reads(_x0)} | _obj in RefineValue.reads(_x0) :: _obj, set _x0: KT, _obj: object? /*{:_reads}*/ {:trigger _obj in ReverseKey.reads(_x0)} | _obj in ReverseKey.reads(_x0) :: _obj
    ensures ghost var rm: map<KT, VT> := AbstractifyMap(m, RefineKey, RefineValue, ReverseKey); (forall ck: CKT {:trigger RefineKey(ck)} {:trigger RefineKey.requires(ck)} {:trigger ck in m} :: (ck in m ==> RefineKey.requires(ck)) && (ck in m ==> RefineKey(ck) in rm)) && (forall ck: CKT {:trigger m[ck]} {:trigger RefineKey(ck)} {:trigger ck in m} :: ck in m ==> rm[RefineKey(ck)] == RefineValue(m[ck])) && forall k: KT {:trigger k in rm} :: k in rm ==> exists ck: CKT {:trigger RefineKey(ck)} {:trigger ck in m} :: ck in m && RefineKey(ck) == k
    decreases (set _x0: CKT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineKey.reads(_x0)} | _obj in RefineKey.reads(_x0) :: _obj) + (set _x0: CVT, _obj: object? /*{:_reads}*/ {:trigger _obj in RefineValue.reads(_x0)} | _obj in RefineValue.reads(_x0) :: _obj) + set _x0: KT, _obj: object? /*{:_reads}*/ {:trigger _obj in ReverseKey.reads(_x0)} | _obj in ReverseKey.reads(_x0) :: _obj, m
  {
    map k: KT {:trigger m[ReverseKey(k)]} | k in set ck: CKT {:trigger RefineKey(ck)} {:trigger ck in m} | ck in m :: RefineKey(ck) :: RefineValue(m[ReverseKey(k)])
  }

  lemma Lemma_AbstractifyMap_basic_properties<CKT, CVT, KT, VT>(m: map<CKT, CVT>, RefineKey: CKT ~> KT, RefineValue: CVT ~> VT, ReverseKey: KT ~> CKT)
    requires MapIsAbstractable(m, RefineKey, RefineValue, ReverseKey)
    requires forall ck1: CKT, ck2: CKT {:trigger RefineKey(ck2), RefineKey(ck1)} {:trigger RefineKey(ck2), RefineKey.requires(ck1)} {:trigger RefineKey(ck1), RefineKey.requires(ck2)} {:trigger RefineKey.requires(ck2), RefineKey.requires(ck1)} :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
    ensures m == map[] ==> AbstractifyMap(m, RefineKey, RefineValue, ReverseKey) == map[]
    ensures forall ck: CKT {:trigger m[ck]} {:trigger RefineKey(ck)} {:trigger ck in m} :: ck in m ==> AbstractifyMap(m, RefineKey, RefineValue, ReverseKey)[RefineKey(ck)] == RefineValue(m[ck])
    ensures forall ck: CKT {:trigger RefineKey(ck)} {:trigger RefineKey.requires(ck)} {:trigger ck in m} :: ck in m <==> RefineKey.requires(ck) && RefineKey(ck) in AbstractifyMap(m, RefineKey, RefineValue, ReverseKey)
    ensures forall ck: CKT {:trigger m[ck]} {:trigger RefineKey(ck)} {:trigger ck in m} :: ck in m ==> AbstractifyMap(m, RefineKey, RefineValue, ReverseKey)[RefineKey(ck)] == RefineValue(m[ck])
    decreases m
  {
  }

  lemma Lemma_AbstractifyMap_preimage<KT(!new), VT(!new), CKT(!new), CVT(!new)>(cm: map<CKT, CVT>, RefineKey: CKT ~> KT, RefineValue: CVT ~> VT, ReverseKey: KT ~> CKT)
    requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
    requires forall ck1: CKT, ck2: CKT {:trigger RefineKey(ck2), RefineKey(ck1)} {:trigger RefineKey(ck2), RefineKey.requires(ck1)} {:trigger RefineKey(ck1), RefineKey.requires(ck2)} {:trigger RefineKey.requires(ck2), RefineKey.requires(ck1)} :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
    ensures ghost var rm: map<KT, VT> := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey); forall k: KT {:trigger k in rm} :: k in rm ==> exists ck: CKT {:trigger RefineKey(ck)} {:trigger ck in cm} :: ck in cm && RefineKey(ck) == k
    decreases cm
  {
  }

  lemma Lemma_AbstractifyMap_append<KT(!new), VT(!new), CKT(!new), CVT(!new)>(cm: map<CKT, CVT>, RefineKey: CKT ~> KT, RefineValue: CVT ~> VT, ReverseKey: KT ~> CKT, ck: CKT, cval: CVT)
    requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
    requires forall ck1: CKT, ck2: CKT {:trigger RefineKey(ck2), RefineKey(ck1)} {:trigger RefineKey(ck2), RefineKey.requires(ck1)} {:trigger RefineKey(ck1), RefineKey.requires(ck2)} {:trigger RefineKey.requires(ck2), RefineKey.requires(ck1)} :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
    requires RefineKey.requires(ck)
    requires RefineValue.requires(cval)
    requires ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
    ensures ghost var rm: map<KT, VT> := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey); ghost var rm': map<KT, VT> := AbstractifyMap(cm[ck := cval], RefineKey, RefineValue, ReverseKey); rm' == AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)]
    decreases cm
  {
  }

  lemma Lemma_AbstractifyMap_remove<KT(!new), VT(!new), CKT(!new), CVT(!new)>(cm: map<CKT, CVT>, RefineKey: CKT ~> KT, RefineValue: CVT ~> VT, ReverseKey: KT ~> CKT, ck: CKT)
    requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
    requires forall ck1: CKT, ck2: CKT {:trigger RefineKey(ck2), RefineKey(ck1)} {:trigger RefineKey(ck2), RefineKey.requires(ck1)} {:trigger RefineKey(ck1), RefineKey.requires(ck2)} {:trigger RefineKey.requires(ck2), RefineKey.requires(ck1)} :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
    requires RefineKey.requires(ck)
    requires ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck
    requires ck in cm
    ensures ghost var rm: map<KT, VT> := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey); ghost var rm': map<KT, VT> := AbstractifyMap(RemoveElt(cm, ck), RefineKey, RefineValue, ReverseKey); RefineKey(ck) in rm && rm' == RemoveElt(rm, RefineKey(ck))
    decreases cm
  {
  }

  lemma lemma_AbstractifyMap_properties<CKT(!new), CVT(!new), KT(!new), VT(!new)>(cm: map<CKT, CVT>, RefineKey: CKT ~> KT, RefineValue: CVT ~> VT, ReverseKey: KT ~> CKT)
    requires MapIsAbstractable(cm, RefineKey, RefineValue, ReverseKey)
    requires forall ck1: CKT, ck2: CKT {:trigger RefineKey(ck2), RefineKey(ck1)} {:trigger RefineKey(ck2), RefineKey.requires(ck1)} {:trigger RefineKey(ck1), RefineKey.requires(ck2)} {:trigger RefineKey.requires(ck2), RefineKey.requires(ck1)} :: RefineKey.requires(ck1) && RefineKey.requires(ck2) && RefineKey(ck1) == RefineKey(ck2) ==> ck1 == ck2
    ensures cm == map[] ==> AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey) == map[]
    ensures forall ck: CKT {:trigger RefineKey(ck)} {:trigger RefineKey.requires(ck)} {:trigger ck in cm} :: ck in cm <==> RefineKey.requires(ck) && RefineKey(ck) in AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)
    ensures forall ck: CKT {:trigger cm[ck]} {:trigger RefineKey(ck)} {:trigger ck in cm} :: ck in cm ==> AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck)] == RefineValue(cm[ck])
    ensures forall ck: CKT {:trigger RefineKey(ck)} {:trigger RefineKey.requires(ck)} {:trigger ck in cm} :: ck !in cm && RefineKey.requires(ck) ==> RefineKey(ck) !in AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)
    ensures ghost var rm: map<KT, VT> := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey); forall k: KT {:trigger k in rm} :: k in rm ==> exists ck: CKT {:trigger RefineKey(ck)} {:trigger ck in cm} :: ck in cm && RefineKey(ck) == k
    ensures forall ck: CKT, cval: CVT {:trigger cm[ck := cval]} {:trigger RefineKey(ck), RefineValue(cval)} :: RefineKey.requires(ck) && RefineValue.requires(cval) && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck ==> ghost var rm: map<KT, VT> := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey); ghost var rm': map<KT, VT> := AbstractifyMap(cm[ck := cval], RefineKey, RefineValue, ReverseKey); rm' == AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey)[RefineKey(ck) := RefineValue(cval)]
    ensures forall ck: CKT {:trigger RemoveElt(AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey), RefineKey(ck))} :: RefineKey.requires(ck) && ReverseKey.requires(RefineKey(ck)) && ReverseKey(RefineKey(ck)) == ck && ck in cm ==> ghost var rm: map<KT, VT> := AbstractifyMap(cm, RefineKey, RefineValue, ReverseKey); ghost var rm': map<KT, VT> := AbstractifyMap(RemoveElt(cm, ck), RefineKey, RefineValue, ReverseKey); rm' == RemoveElt(rm, RefineKey(ck))
    decreases cm
  {
  }
}

module Collections__Maps_i {
  predicate eq_map<A(!new), B>(x: map<A, B>, y: map<A, B>)
    ensures eq_map(x, y) ==> x == y
    decreases x, y
  {
    (forall a: A {:trigger a in y} {:trigger a in x} :: 
      a in x <==> a in y) &&
    forall a: A {:trigger y[a]} {:trigger x[a]} {:trigger a in x} :: 
      a in x ==>
        x[a] == y[a]
  }

  function method domain<U(!new), V>(m: map<U, V>): set<U>
    ensures forall i: U {:trigger i in m} {:trigger i in domain(m)} :: i in domain(m) <==> i in m
    decreases m
  {
    set s: U {:trigger s in m} | s in m
  }

  function union<U(!new), V>(m: map<U, V>, m': map<U, V>): map<U, V>
    requires m.Keys !! m'.Keys
    ensures forall i: U {:trigger i in m'} {:trigger i in m} {:trigger i in union(m, m')} :: i in union(m, m') <==> i in m || i in m'
    ensures forall i: U {:trigger m[i]} {:trigger union(m, m')[i]} {:trigger i in m} :: i in m ==> union(m, m')[i] == m[i]
    ensures forall i: U {:trigger m'[i]} {:trigger union(m, m')[i]} {:trigger i in m'} :: i in m' ==> union(m, m')[i] == m'[i]
    decreases m, m'
  {
    map i: U {:auto_trigger} {:trigger m'[i]} {:trigger m[i]} {:trigger i in m} {:trigger i in domain(m) + domain(m')} | i in domain(m) + domain(m') :: if i in m then m[i] else m'[i]
  }

  function method RemoveElt<U(!new), V(!new)>(m: map<U, V>, elt: U): map<U, V>
    requires elt in m
    ensures |RemoveElt(m, elt)| == |m| - 1
    ensures !(elt in RemoveElt(m, elt))
    ensures forall elt': U {:trigger elt' in m} {:trigger elt' in RemoveElt(m, elt)} :: elt' in RemoveElt(m, elt) <==> elt' in m && elt' != elt
    decreases |m|
  {
    var m': map<U, V> := map elt': U {:trigger m[elt']} {:trigger elt' in m} | elt' in m && elt' != elt :: m[elt'];
    lemma_map_remove_one(m, m', elt);
    m'
  }

  lemma lemma_non_empty_map_has_elements<S(!new), T(!new)>(m: map<S, T>)
    requires |m| > 0
    ensures exists x: S {:trigger x in m} :: x in m
    decreases m
  {
  }

  lemma lemma_MapSizeIsDomainSize<S(!new), T(!new)>(dom: set<S>, m: map<S, T>)
    requires dom == domain(m)
    ensures |m| == |dom|
    decreases dom, m
  {
  }

  lemma lemma_maps_decrease<S(!new), T(!new)>(before: map<S, T>, after: map<S, T>, item_removed: S)
    requires item_removed in before
    requires after == map s: S {:trigger before[s]} {:trigger s in before} | s in before && s != item_removed :: before[s]
    ensures |after| < |before|
    decreases before, after
  {
  }

  lemma lemma_map_remove_one<S(!new), T(!new)>(before: map<S, T>, after: map<S, T>, item_removed: S)
    requires item_removed in before
    requires after == map s: S {:trigger before[s]} {:trigger s in before} | s in before && s != item_removed :: before[s]
    ensures |after| + 1 == |before|
    decreases before, after
  {
  }

  lemma Lemma_map2equiv<K1, V>(f: map<K1, V>, g: map<K1, V>)
    requires forall k1: K1 {:trigger k1 in g} {:trigger k1 in f} :: k1 in f <==> k1 in g
    requires forall k1: K1 {:trigger g[k1]} {:trigger f[k1]} {:trigger k1 in f} :: k1 in f ==> f[k1] == g[k1]
    ensures f == g
    decreases f, g
  {
  }
}

module Collections__Sets_i {
  lemma ThingsIKnowAboutSubset<T>(x: set<T>, y: set<T>)
    requires x < y
    ensures |x| < |y|
    decreases x, y
  {
  }

  lemma SubsetCardinality<T>(x: set<T>, y: set<T>)
    ensures x < y ==> |x| < |y|
    ensures x <= y ==> |x| <= |y|
    decreases x, y
  {
  }

  lemma ItIsASingletonSet<T>(foo: set<T>, x: T)
    requires foo == {x}
    ensures |foo| == 1
    decreases foo
  {
  }

  lemma ThingsIKnowAboutASingletonSet<T>(foo: set<T>, x: T, y: T)
    requires |foo| == 1
    requires x in foo
    requires y in foo
    ensures x == y
    decreases foo
  {
  }

  predicate Injective<X(!new), Y>(f: X --> Y)
    requires forall x: X {:trigger f.requires(x)} :: f.requires(x)
    reads set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    decreases set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
  {
    forall x1: X, x2: X {:trigger f(x2), f(x1)} :: 
      f(x1) == f(x2) ==>
        x1 == x2
  }

  predicate InjectiveOver<X(!new), Y>(xs: set<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    reads set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    decreases set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj, xs, ys
  {
    forall x1: X, x2: X {:trigger f(x2), f(x1)} {:trigger f(x2), x1 in xs} {:trigger f(x1), x2 in xs} {:trigger x2 in xs, x1 in xs} :: 
      x1 in xs &&
      x2 in xs &&
      f(x1) in ys &&
      f(x2) in ys &&
      f(x1) == f(x2) ==>
        x1 == x2
  }

  predicate InjectiveOverSeq<X(!new), Y>(xs: seq<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    reads set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    decreases set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj, xs, ys
  {
    forall x1: X, x2: X {:trigger f(x2), f(x1)} {:trigger f(x2), x1 in xs} {:trigger f(x1), x2 in xs} {:trigger x2 in xs, x1 in xs} :: 
      x1 in xs &&
      x2 in xs &&
      f(x1) in ys &&
      f(x2) in ys &&
      f(x1) == f(x2) ==>
        x1 == x2
  }

  lemma lemma_MapSetCardinality<X, Y>(xs: set<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    requires forall x: X {:trigger f(x)} {:trigger x in xs} :: x in xs <==> f(x) in ys
    requires forall y: Y {:trigger y in ys} :: y in ys ==> exists x: X {:trigger f(x)} {:trigger x in xs} :: x in xs && y == f(x)
    ensures |xs| == |ys|
    decreases xs, ys
  {
  }

  lemma lemma_MapSetCardinalityOver<X, Y>(xs: set<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    requires InjectiveOver(xs, ys, f)
    requires forall x: X {:trigger f(x)} {:trigger x in xs} :: x in xs ==> f(x) in ys
    requires forall y: Y {:trigger y in ys} :: y in ys ==> exists x: X {:trigger f(x)} {:trigger x in xs} :: x in xs && y == f(x)
    ensures |xs| == |ys|
    decreases xs, ys
  {
  }

  lemma lemma_MapSubsetCardinalityOver<X, Y>(xs: set<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    requires InjectiveOver(xs, ys, f)
    requires forall x: X {:trigger f(x)} {:trigger x in xs} :: x in xs ==> f(x) in ys
    ensures |xs| <= |ys|
    decreases xs, ys
  {
  }

  lemma lemma_MapSubseqCardinalityOver<X, Y>(xs: seq<X>, ys: set<Y>, f: X --> Y)
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    requires forall i: int, j: int {:trigger xs[j], xs[i]} :: 0 <= i < |xs| && 0 <= j < |xs| && i != j ==> xs[i] != xs[j]
    requires InjectiveOverSeq(xs, ys, f)
    requires forall x: X {:trigger f(x)} {:trigger x in xs} :: x in xs ==> f(x) in ys
    ensures |xs| <= |ys|
    decreases xs, ys
  {
  }

  function MapSetToSet<X(!new), Y>(xs: set<X>, f: X --> Y): set<Y>
    requires forall x: X {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    reads set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    ensures forall x: X {:trigger f(x)} {:trigger x in xs} :: x in xs <==> f(x) in MapSetToSet(xs, f)
    ensures |xs| == |MapSetToSet(xs, f)|
    decreases set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj, xs
  {
    ghost var ys: set<Y> := set x: X {:trigger f(x)} {:trigger x in xs} | x in xs :: f(x);
    lemma_MapSetCardinality(xs, ys, f);
    ys
  }

  function MapSetToSetOver<X(!new), Y>(xs: set<X>, f: X --> Y): set<Y>
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    requires InjectiveOver(xs, set x: X {:trigger f(x)} {:trigger x in xs} | x in xs :: f(x), f)
    reads set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    ensures forall x: X {:trigger f(x)} {:trigger x in xs} :: x in xs ==> f(x) in MapSetToSetOver(xs, f)
    ensures |xs| == |MapSetToSetOver(xs, f)|
    decreases set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj, xs
  {
    ghost var ys: set<Y> := set x: X {:trigger f(x)} {:trigger x in xs} | x in xs :: f(x);
    lemma_MapSetCardinalityOver(xs, ys, f);
    ys
  }

  function MapSeqToSet<X(!new), Y>(xs: seq<X>, f: X --> Y): set<Y>
    requires forall x: X {:trigger f.requires(x)} :: f.requires(x)
    requires Injective(f)
    reads set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    ensures forall x: X {:trigger f(x)} {:trigger x in xs} :: x in xs <==> f(x) in MapSeqToSet(xs, f)
    decreases set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj, xs
  {
    set x: X {:trigger f(x)} {:trigger x in xs} | x in xs :: f(x)
  }

  function SeqToSet<X(!new)>(xs: seq<X>): set<X>
    decreases xs
  {
    set x: X {:trigger x in xs} | x in xs
  }

  lemma lemma_SubsetCardinality<X>(xs: set<X>, ys: set<X>, f: X --> bool)
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    requires forall x: X {:trigger f(x)} {:trigger x in xs} {:trigger x in ys} :: (x in ys ==> x in xs) && (x in ys ==> f(x))
    ensures |ys| <= |xs|
    decreases xs, ys
  {
  }

  function MakeSubset<X(!new)>(xs: set<X>, f: X -> bool): set<X>
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    reads set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    ensures forall x: X {:trigger f(x)} {:trigger x in xs} {:trigger x in MakeSubset(xs, f)} :: x in MakeSubset(xs, f) <==> x in xs && f(x)
    ensures |MakeSubset(xs, f)| <= |xs|
    decreases set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj, xs
  {
    ghost var ys: set<X> := set x: X {:trigger f(x)} {:trigger x in xs} | x in xs && f(x);
    lemma_SubsetCardinality(xs, ys, f);
    ys
  }

  lemma lemma_UnionCardinality<X>(xs: set<X>, ys: set<X>, us: set<X>)
    requires us == xs + ys
    ensures |us| >= |xs|
    decreases ys
  {
  }

  function SetOfNumbersInRightExclusiveRange(a: int, b: int): set<int>
    requires a <= b
    ensures forall opn: int {:trigger opn in SetOfNumbersInRightExclusiveRange(a, b)} :: a <= opn < b ==> opn in SetOfNumbersInRightExclusiveRange(a, b)
    ensures forall opn: int {:trigger opn in SetOfNumbersInRightExclusiveRange(a, b)} :: (opn in SetOfNumbersInRightExclusiveRange(a, b) ==> a <= opn) && (opn in SetOfNumbersInRightExclusiveRange(a, b) ==> opn < b)
    ensures |SetOfNumbersInRightExclusiveRange(a, b)| == b - a
    decreases b - a
  {
    if a == b then
      {}
    else
      {a} + SetOfNumbersInRightExclusiveRange(a + 1, b)
  }

  lemma lemma_CardinalityOfBoundedSet(s: set<int>, a: int, b: int)
    requires forall opn: int {:trigger opn in s} :: (opn in s ==> a <= opn) && (opn in s ==> opn < b)
    requires a <= b
    ensures |s| <= b - a
    decreases s, a, b
  {
  }

  function intsetmax(s: set<int>): int
    requires |s| > 0
    ensures ghost var m: int := intsetmax(s); m in s && forall i: int {:trigger i in s} :: i in s ==> m >= i
    decreases s
  {
    ghost var x: int :| x in s;
    if |s| == 1 then
      assert |s - {x}| == 0;
      x
    else
      ghost var sy: set<int> := s - {x}; ghost var y: int := intsetmax(sy); assert forall i: int {:trigger i in sy} {:trigger i in s} :: i in s ==> i in sy || i == x; if x > y then x else y
  }
}

module Logic__Option_i {
  datatype Option<T> = Some(v: T) | None
}

module CausalMesh_CMessage_i {

  import opened CausalMesh_CTypes_i

  import opened CausalMesh_Message_i

  import opened GenericRefinement_i

  import opened Common__NodeIdentity_i

  import opened Native__Io_s

  import opened Environment_s

  import opened CausalMesh_Types_i
  datatype CMessage = CMessage_Read(opn_read: int, key_read: CKey, deps_read: CDependency) | CMessage_Read_Reply(opn_rreply: int, key_rreply: CKey, vc_rreply: CVectorClock, deps_rreply: CDependency) | CMessage_Write(opn_write: int, key_write: CKey, deps_write: CDependency, local: map<CKey, CMeta>, mvc: CVectorClock) | CMessage_Write_Reply(opn_wreply: int, key_wreply: CKey, vc_wreply: CVectorClock) | CMessage_Propagation(key: CKey, meta: CMeta, start: int, round: int)

  datatype CPacket = CPacket(dst: EndPoint, src: EndPoint, msg: CMessage)

  predicate WriteMessageHasMVCLargerThanAllDepsAndLocals(s: CMessage)
    requires s.CMessage_Write?
    requires CDependencyValid(s.deps_write)
    requires forall i: int {:trigger s.local[i]} {:trigger i in s.local} :: i in s.local ==> CMetaValid(s.local[i])
    requires CVectorClockValid(s.mvc)
    decreases s
  {
    (forall k: int {:trigger s.deps_write[k]} {:trigger k in s.deps_write} :: 
      k in s.deps_write ==>
        CVCEq(s.deps_write[k], s.mvc) || CVCHappendsBefore(s.deps_write[k], s.mvc)) &&
    forall k: int {:trigger s.local[k]} {:trigger k in s.local} :: 
      k in s.local ==>
        CVCEq(s.local[k].vc, s.mvc) || CVCHappendsBefore(s.local[k].vc, s.mvc)
  }

  predicate WriteMessageDepsContainsLocal(s: CMessage)
    requires s.CMessage_Write?
    requires CDependencyValid(s.deps_write)
    requires forall i: int {:trigger s.local[i]} {:trigger i in s.local} :: i in s.local ==> CMetaValid(s.local[i])
    decreases s
  {
    forall k: int {:trigger s.deps_write[k]} {:trigger s.local[k]} {:trigger k in s.deps_write} {:trigger k in s.local} :: 
      (k in s.local ==>
        k in s.deps_write) &&
      (k in s.local ==>
        CVCEq(s.local[k].vc, s.deps_write[k]) || CVCHappendsBefore(s.local[k].vc, s.deps_write[k]))
  }

  predicate CMessageIsValid(s: CMessage)
    decreases s
  {
    match s
    case CMessage_Read(opn_read, key_read, deps_read) =>
      CMessageIsAbstractable(s) &&
      CKeyIsValid(s.key_read) &&
      CDependencyIsValid(s.deps_read)
    case CMessage_Read_Reply(opn_rreply, key_rreply, vc_rreply, deps_rreply) =>
      CMessageIsAbstractable(s) &&
      CKeyIsValid(s.key_rreply) &&
      CVectorClockIsValid(s.vc_rreply) &&
      CDependencyIsValid(s.deps_rreply)
    case CMessage_Write(opn_write, key_write, deps_write, local, mvc) =>
      CMessageIsAbstractable(s) &&
      CKeyIsValid(s.key_write) &&
      CDependencyIsValid(s.deps_write) &&
      CVectorClockIsValid(s.mvc) &&
      forall i: int {:trigger s.local[i]} {:trigger CKeyIsValid(i)} {:trigger i in s.local} :: 
        (i in s.local ==>
          CKeyIsValid(i)) &&
        (i in s.local ==>
          CMetaIsValid(s.local[i]))
    case CMessage_Write_Reply(opn_wreply, key_wreply, vc_wreply) =>
      CMessageIsAbstractable(s) &&
      CKeyIsValid(s.key_wreply) &&
      CVectorClockIsValid(s.vc_wreply)
    case CMessage_Propagation(key, meta, start, round) =>
      CMessageIsAbstractable(s) &&
      CKeyIsValid(s.key) &&
      CMetaIsValid(s.meta)
  }

  predicate CMessageIsAbstractable(s: CMessage)
    decreases s
  {
    match s
    case CMessage_Read(opn_read, key_read, deps_read) =>
      CKeyIsAbstractable(s.key_read) &&
      CDependencyIsAbstractable(s.deps_read)
    case CMessage_Read_Reply(opn_rreply, key_rreply, vc_rreply, deps_rreply) =>
      CKeyIsAbstractable(s.key_rreply) &&
      CVectorClockIsAbstractable(s.vc_rreply) &&
      CDependencyIsAbstractable(s.deps_rreply)
    case CMessage_Write(opn_write, key_write, deps_write, local, mvc) =>
      CKeyIsAbstractable(s.key_write) &&
      CDependencyIsAbstractable(s.deps_write) &&
      CVectorClockIsAbstractable(s.mvc) &&
      forall i: int {:trigger s.local[i]} {:trigger CKeyIsAbstractable(i)} {:trigger i in s.local} :: 
        (i in s.local ==>
          CKeyIsAbstractable(i)) &&
        (i in s.local ==>
          CMetaIsAbstractable(s.local[i]))
    case CMessage_Write_Reply(opn_wreply, key_wreply, vc_wreply) =>
      CKeyIsAbstractable(s.key_wreply) &&
      CVectorClockIsAbstractable(s.vc_wreply)
    case CMessage_Propagation(key, meta, start, round) =>
      CKeyIsAbstractable(s.key) &&
      CMetaIsAbstractable(s.meta)
  }

  function AbstractifyCMessageToMessage(s: CMessage): Message
    requires CMessageIsAbstractable(s)
    decreases s
  {
    match s
    case CMessage_Read(opn_read, key_read, deps_read) =>
      Message_Read(s.opn_read, AbstractifyCKeyToKey(s.key_read), AbstractifyCDependencyToDependency(s.deps_read))
    case CMessage_Read_Reply(opn_rreply, key_rreply, vc_rreply, deps_rreply) =>
      Message_Read_Reply(s.opn_rreply, AbstractifyCKeyToKey(s.key_rreply), AbstractifyCVectorClockToVectorClock(s.vc_rreply), AbstractifyCDependencyToDependency(s.deps_rreply))
    case CMessage_Write(opn_write, key_write, deps_write, local, mvc) =>
      Message_Write(s.opn_write, AbstractifyCKeyToKey(s.key_write), AbstractifyCDependencyToDependency(s.deps_write), AbstractifyMap(s.local, AbstractifyCKeyToKey, AbstractifyCMetaToMeta, AbstractifyCKeyToKey))
    case CMessage_Write_Reply(opn_wreply, key_wreply, vc_wreply) =>
      Message_Write_Reply(s.opn_wreply, AbstractifyCKeyToKey(s.key_wreply), AbstractifyCVectorClockToVectorClock(s.vc_wreply))
    case CMessage_Propagation(key, meta, start, round) =>
      Message_Propagation(AbstractifyCKeyToKey(s.key), AbstractifyCMetaToMeta(s.meta), s.start, s.round)
  }

  predicate CMessageValid(m: CMessage)
    decreases m
  {
    match m
    case CMessage_Read(_, key_read, deps_read) =>
      key_read in Keys_domain &&
      CDependencyValid(deps_read)
    case CMessage_Read_Reply(_, key_rreply, vc_rreply, deps_rreply) =>
      key_rreply in Keys_domain &&
      CVectorClockValid(vc_rreply) &&
      CDependencyValid(deps_rreply)
    case CMessage_Write(_, key_write, deps_write, local, mvc) =>
      key_write in Keys_domain &&
      CDependencyValid(deps_write) &&
      CVectorClockValid(mvc) &&
      (forall k: int {:trigger local[k]} {:trigger k in local} :: 
        (k in local ==>
          CMetaValid(local[k])) &&
        (k in local ==>
          local[k].key == k)) &&
      WriteMessageDepsContainsLocal(m) &&
      WriteMessageHasMVCLargerThanAllDepsAndLocals(m)
    case CMessage_Write_Reply(_, key_wreply, vc_wreply) =>
      key_wreply in Keys_domain &&
      CVectorClockValid(vc_wreply)
    case CMessage_Propagation(key, meta, start, round) =>
      key in Keys_domain &&
      CMetaValid(meta) &&
      meta.key == key &&
      0 <= start < Nodes
  }

  predicate CPacketIsValid(cp: CPacket)
    decreases cp
  {
    CPacketIsAbstractable(cp) &&
    CMessageIsValid(cp.msg) &&
    EndPointIsValid(cp.src) &&
    EndPointIsValid(cp.dst)
  }

  predicate CPacketIsAbstractable(cp: CPacket)
    decreases cp
  {
    CMessageIsAbstractable(cp.msg) &&
    EndPointIsAbstractable(cp.src) &&
    EndPointIsAbstractable(cp.dst)
  }

  function AbstractifyCPacketToPacket(cp: CPacket): Packet
    requires CPacketIsAbstractable(cp)
    decreases cp
  {
    LPacket(AbstractifyEndPointToID(cp.dst), AbstractifyEndPointToID(cp.src), AbstractifyCMessageToMessage(cp.msg))
  }

  function AbstractifyCPacketSeq(s: seq<CPacket>): seq<Packet>
    requires forall i: int {:trigger s[i]} :: 0 <= i < |s| ==> CPacketIsAbstractable(s[i])
    ensures ghost var cs: seq<Packet> := AbstractifyCPacketSeq(s); |cs| == |s| && (forall i: int {:trigger s[i]} {:trigger cs[i]} :: 0 <= i < |s| ==> cs[i] == AbstractifyCPacketToPacket(s[i])) && forall i: LPacket<int, Message> {:trigger i in cs} :: i in cs ==> exists x: CPacket {:trigger AbstractifyCPacketToPacket(x)} {:trigger x in s} :: x in s && i == AbstractifyCPacketToPacket(x)
    decreases s
  {
    ghost var cs: seq<LPacket<int, Message>> := if |s| == 0 then [] else [AbstractifyCPacketToPacket(s[0])] + AbstractifyCPacketSeq(s[1..]);
    cs
  }

  predicate CPacketValid(p: CPacket)
    decreases p
  {
    true &&
    CMessageValid(p.msg)
  }

  function AbstractifyEndPointToID(endpoint: EndPoint): int
    decreases endpoint
  {
    endpoint.port as int
  }
}

module CausalMesh_Message_i {

  import opened CausalMesh_Types_i

  import opened Environment_s
  datatype Message = Message_Read(opn_read: int, key_read: Key, deps_read: Dependency) | Message_Read_Reply(opn_rreply: int, key_rreply: Key, vc_rreply: VectorClock, deps_rreply: Dependency) | Message_Write(opn_write: int, key_write: Key, deps_write: Dependency, local: map<Key, Meta>) | Message_Write_Reply(opn_wreply: int, key_wreply: Key, vc_wreply: VectorClock) | Message_Propagation(key: Key, meta: Meta, start: int, round: int)

  type Packet = LPacket<int, Message>

  predicate MessageValid(m: Message)
    decreases m
  {
    match m
    case Message_Read(_, key_read, deps_read) =>
      key_read in Keys_domain &&
      DependencyValid(deps_read)
    case Message_Read_Reply(_, key_rreply, vc_rreply, deps_rreply) =>
      key_rreply in Keys_domain &&
      VectorClockValid(vc_rreply) &&
      DependencyValid(deps_rreply)
    case Message_Write(_, key_write, deps_write, local) =>
      key_write in Keys_domain &&
      DependencyValid(deps_write) &&
      forall k: int {:trigger local[k]} {:trigger k in local} :: 
        (k in local ==>
          MetaValid(local[k])) &&
        (k in local ==>
          local[k].key == k)
    case Message_Write_Reply(_, key_wreply, vc_wreply) =>
      key_wreply in Keys_domain &&
      VectorClockValid(vc_wreply)
    case Message_Propagation(key, meta, start, round) =>
      key in Keys_domain &&
      MetaValid(meta) &&
      meta.key == key &&
      0 <= start < Nodes
  }

  predicate PacketValid(p: Packet)
    decreases p
  {
    true &&
    MessageValid(p.msg)
  }
}

module Common__NodeIdentity_i {

  import opened Native__NativeTypes_s

  import opened Native__Io_s

  import opened Common__Util_i

  import opened Common__UdpClient_i

  import opened Common__SeqIsUniqueDef_i

  import opened Common__SeqIsUnique_i

  import opened Concrete_NodeIdentity_i

  import opened GenericRefinement_i

  import opened Collections__Sets_i

  import opened Math__power2_s

  import opened Math__power2_i
  function {:opaque} {:fuel 0, 0} AbstractifySeqOfUint64sToSeqOfInts(s: seq<uint64>): seq<int>
    ensures |AbstractifySeqOfUint64sToSeqOfInts(s)| == |s|
    ensures forall i: int {:trigger AbstractifySeqOfUint64sToSeqOfInts(s)[i]} {:trigger s[i]} :: 0 <= i < |s| ==> s[i] as int == AbstractifySeqOfUint64sToSeqOfInts(s)[i]
    decreases s
  {
    MapSeqToSeq(s, uint64_to_int)
  }

  function {:opaque} {:fuel 0, 0} AbstractifySeqOfUint64sToSetOfInts(s: seq<uint64>): set<int>
    requires SeqIsUnique(s)
    ensures forall x: uint64 {:trigger x in s} :: x in s ==> x as int in AbstractifySeqOfUint64sToSetOfInts(s)
    decreases s
  {
    ghost var unique_set: set<uint64> := UniqueSeqToSet(s);
    set i: uint64 {:trigger i in unique_set} | i in unique_set :: i as int
  }

  lemma lemma_AbstractifySeqOfUint64sToSetOfInts_properties(s: seq<uint64>)
    requires SeqIsUnique(s)
    ensures |AbstractifySeqOfUint64sToSetOfInts(s)| == |s|
    ensures forall i: uint64 {:auto_trigger} {:trigger i in s} :: i in s <==> i as int in AbstractifySeqOfUint64sToSetOfInts(s)
    decreases s
  {
  }

  lemma lemma_AbstractifySeqOfUint64sToSetOfInts_append(original_seq: seq<uint64>, new_index: uint64)
    requires SeqIsUnique(original_seq)
    ensures ghost var r_original_set: set<int> := AbstractifySeqOfUint64sToSetOfInts(original_seq); AbstractifySeqOfUint64sToSetOfInts(AppendToUniqueSeqMaybe(original_seq, new_index)) == r_original_set + {new_index as int}
    decreases original_seq, new_index
  {
  }

  predicate EndPointIsValid(endpoint: EndPoint)
    decreases endpoint
  {
    EndPointIsAbstractable(endpoint)
  }

  predicate EndPointIsAbstractable(endpoint: EndPoint)
    decreases endpoint
  {
    EndPointIsValidIPV4(endpoint)
  }

  function AbstractifyEndPointToNodeIdentity(endpoint: EndPoint): NodeIdentity
    decreases endpoint
  {
    endpoint
  }

  predicate Uint64IsAbstractableToNodeIdentity(id: uint64)
    decreases id
  {
    EndPointUint64Representation(id)
  }

  predicate SeqOfEndPointsIsAbstractable(endPoints: seq<EndPoint>)
    decreases endPoints
  {
    forall e: EndPoint {:trigger EndPointIsValidIPV4(e)} {:trigger e in endPoints} :: 
      e in endPoints ==>
        EndPointIsValidIPV4(e)
  }

  predicate SetOfEndPointsIsAbstractable(endPoints: set<EndPoint>)
    decreases endPoints
  {
    forall e: EndPoint {:trigger EndPointIsAbstractable(e)} {:trigger e in endPoints} :: 
      e in endPoints ==>
        EndPointIsAbstractable(e)
  }

  function {:opaque} {:fuel 0, 0} AbstractifyEndPointsToNodeIdentities(endPoints: seq<EndPoint>): seq<NodeIdentity>
    requires forall e: EndPoint {:trigger EndPointIsValidIPV4(e)} {:trigger e in endPoints} :: e in endPoints ==> EndPointIsValidIPV4(e)
    ensures |AbstractifyEndPointsToNodeIdentities(endPoints)| == |endPoints|
    ensures forall i: int {:trigger AbstractifyEndPointsToNodeIdentities(endPoints)[i]} {:trigger endPoints[i]} :: 0 <= i < |endPoints| ==> AbstractifyEndPointToNodeIdentity(endPoints[i]) == AbstractifyEndPointsToNodeIdentities(endPoints)[i]
    decreases endPoints
  {
    if |endPoints| == 0 then
      []
    else
      [AbstractifyEndPointToNodeIdentity(endPoints[0])] + AbstractifyEndPointsToNodeIdentities(endPoints[1..])
  }

  function AbstractifyEndPointsToNodeIdentitiesSet(endPoints: set<EndPoint>): set<NodeIdentity>
    requires forall e: EndPoint {:trigger EndPointIsAbstractable(e)} {:trigger e in endPoints} :: e in endPoints ==> EndPointIsAbstractable(e)
    decreases endPoints
  {
    ghost var ss: set<NodeIdentity> := set s: EndPoint {:trigger AbstractifyEndPointToNodeIdentity(s)} {:trigger s in endPoints} | s in endPoints :: AbstractifyEndPointToNodeIdentity(s);
    ss
  }

  predicate EndPointSeqRepresentation(s: seq<byte>)
    decreases s
  {
    |s| == 8 &&
    s[0] == 0 &&
    s[1] == 0
  }

  predicate EndPointUint64Representation(u: uint64)
    decreases u
  {
    u <= 281474976710655
  }

  lemma EndPointRepresentations()
    ensures forall u: uint64 {:trigger Uint64ToSeqByte(u)} {:trigger EndPointUint64Representation(u)} :: EndPointUint64Representation(u) ==> EndPointSeqRepresentation(Uint64ToSeqByte(u))
  {
  }

  function method {:opaque} {:fuel 0, 0} ConvertEndPointToSeqByte(e: EndPoint): seq<byte>
    requires EndPointIsValidIPV4(e)
    ensures EndPointSeqRepresentation(ConvertEndPointToSeqByte(e))
    decreases e
  {
    [0, 0] + e.addr + Uint16ToSeqByte(e.port)
  }

  function method {:opaque} {:fuel 0, 0} ConvertSeqByteToEndPoint(s: seq<byte>): EndPoint
    requires EndPointSeqRepresentation(s)
    ensures EndPointIsValidIPV4(ConvertSeqByteToEndPoint(s))
    decreases s
  {
    EndPoint(s[2 .. 6], SeqByteToUint16(s[6..]))
  }

  lemma {:timeLimitMultiplier 3} /*{:_timeLimit 30}*/ EndPointSeqRepresentations()
    ensures forall s: seq<byte> {:trigger ConvertSeqByteToEndPoint(s)} {:trigger EndPointSeqRepresentation(s)} :: EndPointSeqRepresentation(s) ==> ConvertEndPointToSeqByte(ConvertSeqByteToEndPoint(s)) == s
    ensures forall e: EndPoint {:trigger ConvertEndPointToSeqByte(e)} {:trigger EndPointIsValidIPV4(e)} :: EndPointIsValidIPV4(e) ==> ConvertSeqByteToEndPoint(ConvertEndPointToSeqByte(e)) == e
  {
  }

  function method {:opaque} {:fuel 0, 0} ConvertEndPointToUint64(e: EndPoint): uint64
    requires EndPointIsValidIPV4(e)
    ensures EndPointUint64Representation(ConvertEndPointToUint64(e))
    decreases e
  {
    SeqByteToUint64(ConvertEndPointToSeqByte(e))
  }

  function method {:opaque} {:fuel 0, 0} ConvertUint64ToEndPoint(u: uint64): EndPoint
    requires EndPointUint64Representation(u)
    ensures EndPointIsValidIPV4(ConvertUint64ToEndPoint(u))
    decreases u
  {
    EndPointRepresentations();
    ConvertSeqByteToEndPoint(Uint64ToSeqByte(u))
  }

  lemma lemma_ConvertUint64ToNodeIdentity_injective_forall()
    ensures forall u1: uint64, u2: uint64 {:trigger AbstractifyUint64ToNodeIdentity(u2), AbstractifyUint64ToNodeIdentity(u1)} {:trigger AbstractifyUint64ToNodeIdentity(u2), EndPointUint64Representation(u1)} {:trigger AbstractifyUint64ToNodeIdentity(u1), EndPointUint64Representation(u2)} {:trigger EndPointUint64Representation(u2), EndPointUint64Representation(u1)} :: EndPointUint64Representation(u1) && EndPointUint64Representation(u2) && AbstractifyUint64ToNodeIdentity(u1) == AbstractifyUint64ToNodeIdentity(u2) ==> u1 == u2
  {
  }

  lemma Uint64EndPointRelationships()
    ensures forall u: uint64 {:trigger ConvertUint64ToEndPoint(u)} {:trigger EndPointUint64Representation(u)} :: (EndPointUint64Representation(u) ==> EndPointIsValidIPV4(ConvertUint64ToEndPoint(u))) && (EndPointUint64Representation(u) ==> ConvertEndPointToUint64(ConvertUint64ToEndPoint(u)) == u)
    ensures forall e: EndPoint {:trigger ConvertEndPointToUint64(e)} {:trigger EndPointIsValidIPV4(e)} :: EndPointIsValidIPV4(e) ==> ConvertUint64ToEndPoint(ConvertEndPointToUint64(e)) == e
  {
  }

  lemma lemma_Uint64EndPointRelationships()
    ensures forall u: uint64 {:trigger ConvertEndPointToUint64(ConvertUint64ToEndPoint(u))} :: (EndPointUint64Representation(u) ==> EndPointIsValidIPV4(ConvertUint64ToEndPoint(u))) && (EndPointUint64Representation(u) ==> ConvertEndPointToUint64(ConvertUint64ToEndPoint(u)) == u)
    ensures forall e: EndPoint {:trigger ConvertUint64ToEndPoint(ConvertEndPointToUint64(e))} :: EndPointIsValidIPV4(e) ==> ConvertUint64ToEndPoint(ConvertEndPointToUint64(e)) == e
  {
  }

  function AbstractifyUint64ToNodeIdentity(u: uint64): NodeIdentity
    requires EndPointUint64Representation(u)
    decreases u
  {
    reveal ConvertUint64ToEndPoint();
    AbstractifyEndPointToNodeIdentity(ConvertUint64ToEndPoint(u))
  }

  lemma lemma_ConvertUint64ToNodeIdentity_injective(u1: uint64, u2: uint64)
    requires EndPointUint64Representation(u1) && EndPointUint64Representation(u2)
    requires AbstractifyUint64ToNodeIdentity(u1) == AbstractifyUint64ToNodeIdentity(u2)
    ensures u1 == u2
    decreases u1, u2
  {
  }

  lemma lemma_AbstractifyEndPointToNodeIdentity_injective(e1: EndPoint, e2: EndPoint)
    requires EndPointIsValidIPV4(e1) && EndPointIsValidIPV4(e2)
    requires AbstractifyEndPointToNodeIdentity(e1) == AbstractifyEndPointToNodeIdentity(e2)
    ensures e1 == e2
    decreases e1, e2
  {
  }

  lemma lemma_AbstractifyEndPointToNodeIdentity_injective_forall()
    ensures forall e1: EndPoint, e2: EndPoint {:trigger AbstractifyEndPointToNodeIdentity(e1), AbstractifyEndPointToNodeIdentity(e2)} :: EndPointIsValidIPV4(e1) && EndPointIsValidIPV4(e2) && AbstractifyEndPointToNodeIdentity(e1) == AbstractifyEndPointToNodeIdentity(e2) ==> e1 == e2
  {
  }

  lemma lemma_seqs_set_cardinality_EndPoint(Q: seq<EndPoint>, S: set<EndPoint>)
    requires SeqIsUnique(Q)
    requires S == set e: EndPoint {:trigger e in Q} | e in Q
    ensures |Q| == |S|
    decreases |Q|
  {
  }

  lemma lemma_sets_cardinality_EndPoint(S: set<EndPoint>, T: set<NodeIdentity>)
    requires forall e: EndPoint {:trigger EndPointIsValidIPV4(e)} {:trigger e in S} :: e in S ==> EndPointIsValidIPV4(e)
    requires T == set e: EndPoint {:trigger AbstractifyEndPointToNodeIdentity(e)} {:trigger e in S} | e in S :: AbstractifyEndPointToNodeIdentity(e)
    ensures |S| == |T|
    decreases |S|
  {
  }

  lemma /*{:_induction endpoints}*/ lemma_AbstractifyEndPointsToNodeIdentities_properties(endpoints: seq<EndPoint>)
    requires SeqIsUnique(endpoints)
    requires SeqOfEndPointsIsAbstractable(endpoints)
    ensures |AbstractifyEndPointsToNodeIdentities(endpoints)| == |endpoints|
    ensures forall e: EndPoint {:trigger AbstractifyEndPointToNodeIdentity(e)} {:trigger e in endpoints} :: e in endpoints ==> AbstractifyEndPointToNodeIdentity(e) in AbstractifyEndPointsToNodeIdentities(endpoints)
    ensures forall e: EndPoint {:trigger AbstractifyEndPointToNodeIdentity(e)} {:trigger e in endpoints} {:trigger EndPointIsValidIPV4(e)} :: EndPointIsValidIPV4(e) ==> (e in endpoints <==> AbstractifyEndPointToNodeIdentity(e) in AbstractifyEndPointsToNodeIdentities(endpoints))
    decreases endpoints
  {
  }

  lemma /*{:_induction s1, s2}*/ lemma_AbstractifyEndPointsToNodeIdentities_injective_elements(s1: seq<EndPoint>, s2: seq<EndPoint>)
    requires forall e: EndPoint {:trigger EndPointIsValidIPV4(e)} {:trigger e in s1} :: e in s1 ==> EndPointIsValidIPV4(e)
    requires forall e: EndPoint {:trigger EndPointIsValidIPV4(e)} {:trigger e in s2} :: e in s2 ==> EndPointIsValidIPV4(e)
    requires AbstractifyEndPointsToNodeIdentities(s1) == AbstractifyEndPointsToNodeIdentities(s2)
    ensures forall e: EndPoint {:trigger e in s2} {:trigger e in s1} :: e in s1 <==> e in s2
    decreases s1, s2
  {
  }

  lemma /*{:_induction s1, s2}*/ lemma_AbstractifyEndPointsToNodeIdentities_injective(s1: seq<EndPoint>, s2: seq<EndPoint>)
    requires forall e: EndPoint {:trigger EndPointIsValidIPV4(e)} {:trigger e in s1} :: e in s1 ==> EndPointIsValidIPV4(e)
    requires forall e: EndPoint {:trigger EndPointIsValidIPV4(e)} {:trigger e in s2} :: e in s2 ==> EndPointIsValidIPV4(e)
    requires AbstractifyEndPointsToNodeIdentities(s1) == AbstractifyEndPointsToNodeIdentities(s2)
    ensures s1 == s2
    decreases s1, s2
  {
  }

  predicate NodeIdentityIsRefinable(id: NodeIdentity)
    decreases id
  {
    exists ep: EndPoint {:trigger AbstractifyEndPointToNodeIdentity(ep)} {:trigger EndPointIsValidIPV4(ep)} :: 
      EndPointIsValidIPV4(ep) &&
      AbstractifyEndPointToNodeIdentity(ep) == id
  }

  function {:opaque} {:fuel 0, 0} AbstractifyNodeIdentityToEndPoint(id: NodeIdentity): EndPoint
    ensures NodeIdentityIsRefinable(id) ==> EndPointIsValidIPV4(AbstractifyNodeIdentityToEndPoint(id))
    ensures NodeIdentityIsRefinable(id) ==> AbstractifyEndPointToNodeIdentity(AbstractifyNodeIdentityToEndPoint(id)) == id
    decreases id
  {
    if NodeIdentityIsRefinable(id) then
      ghost var ep: EndPoint :| EndPointIsValidIPV4(ep) && AbstractifyEndPointToNodeIdentity(ep) == id;
      ep
    else
      ghost var e: EndPoint :| true; e
  }
}

module Common__Util_i {

  import opened Native__Io_s

  import opened Native__NativeTypes_s

  import opened Native__NativeTypes_i

  import opened Math__power2_s

  import opened Math__power2_i

  import opened Math__div_i
  function method ShouldPrintProfilingInfo(): bool
  {
    false
  }

  function method ShouldPrintProgress(): bool
  {
    false
  }

  method seqToArray_slow<A(0)>(s: seq<A>) returns (a: array<A>)
    ensures a[..] == s
    decreases s
  {
    var len := |s|;
    a := new A[len];
    var i := 0;
    while i < len
      invariant 0 <= i <= len
      invariant a[..i] == s[..i]
      decreases len - i
    {
      a[i] := s[i];
      i := i + 1;
    }
  }

  method seqIntoArrayOpt<A>(s: seq<A>, a: array<A>)
    requires |s| == a.Length
    requires |s| < 18446744073709551616
    modifies a
    ensures a[..] == s
    decreases s, a
  {
    var i: uint64 := 0;
    while i < |s| as uint64
      invariant 0 <= i as int <= a.Length
      invariant a[..] == s[0 .. i] + old(a[i..])
      decreases |s| as uint64 as int - i as int
    {
      a[i] := s[i];
      i := i + 1;
    }
  }

  method seqToArrayOpt<A(0)>(s: seq<A>) returns (a: array<A>)
    requires |s| < 18446744073709551616
    ensures a[..] == s
    ensures fresh(a)
    decreases s
  {
    a := new A[|s| as uint64];
    seqIntoArrayOpt(s, a);
  }

  method seqIntoArrayChar(s: seq<char>, a: array<char>)
    requires |s| == a.Length
    requires |s| < 18446744073709551616
    modifies a
    ensures a[..] == s
    decreases s, a
  {
    var i: uint64 := 0;
    while i < |s| as uint64
      invariant 0 <= i as int <= a.Length
      invariant a[..] == s[0 .. i] + old(a[i..])
      decreases |s| as uint64 as int - i as int
    {
      a[i] := s[i];
      i := i + 1;
    }
  }

  method RecordTimingSeq(name: seq<char>, start: uint64, end: uint64)
    requires 0 < |name| < 18446744073709551616
    decreases name, start, end
  {
    if ShouldPrintProfilingInfo() {
      var name_array := new char[|name|];
      seqIntoArrayChar(name, name_array);
      var time: uint64;
      if start <= end {
        time := end - start;
      } else {
        time := 18446744073709551615;
      }
      Time.RecordTiming(name_array, time);
    }
  }

  function BEByteSeqToInt(bytes: seq<byte>): int
    decreases |bytes|
  {
    if bytes == [] then
      0
    else
      BEByteSeqToInt(bytes[..|bytes| - 1]) * 256 + bytes[|bytes| - 1] as int
  }

  lemma /*{:_induction bytes}*/ lemma_BEByteSeqToInt_bound(bytes: seq<byte>)
    ensures 0 <= BEByteSeqToInt(bytes)
    ensures BEByteSeqToInt(bytes) < power2(8 * |bytes|)
    decreases bytes
  {
  }

  lemma /*{:_induction bs}*/ lemma_BEByteSeqToUint64_properties(bs: seq<byte>)
    requires |bs| == Uint64Size() as int
    ensures ghost var ret: uint64 := bs[0] as uint64 * 256 * 256 * 256 * 4294967296 + bs[1] as uint64 * 256 * 256 * 4294967296 + bs[2] as uint64 * 256 * 4294967296 + bs[3] as uint64 * 4294967296 + bs[4] as uint64 * 256 * 256 * 256 + bs[5] as uint64 * 256 * 256 + bs[6] as uint64 * 256 + bs[7] as uint64; ret as int == BEByteSeqToInt(bs)
    decreases bs
  {
  }

  function method SeqByteToUint64(bs: seq<byte>): uint64
    requires |bs| == Uint64Size() as int
    ensures 0 <= BEByteSeqToInt(bs) < 18446744073709551616
    ensures SeqByteToUint64(bs) == BEByteSeqToInt(bs) as uint64
    decreases bs
  {
    lemma_2toX();
    lemma_BEByteSeqToUint64_properties(bs);
    bs[0] as uint64 * 256 * 256 * 256 * 4294967296 + bs[1] as uint64 * 256 * 256 * 4294967296 + bs[2] as uint64 * 256 * 4294967296 + bs[3] as uint64 * 4294967296 + bs[4] as uint64 * 256 * 256 * 256 + bs[5] as uint64 * 256 * 256 + bs[6] as uint64 * 256 + bs[7] as uint64
  }

  function BEUintToSeqByte(v: int, width: int): seq<byte>
    ensures width >= 0 && v >= 0 ==> |BEUintToSeqByte(v, width)| == width
    decreases v, width
  {
    if width > 0 && v >= 0 then
      BEUintToSeqByte(v / 256, width - 1) + [(v % 256) as byte]
    else
      []
  }

  lemma /*{:_induction bytes, val, width}*/ lemma_BEUintToSeqByte_invertability(bytes: seq<byte>, val: int, width: nat)
    requires bytes == BEUintToSeqByte(val, width)
    requires 0 <= val < power2(8 * width)
    requires |bytes| == width
    ensures BEByteSeqToInt(bytes) == val
    decreases bytes, val, width
  {
  }

  lemma /*{:_induction bytes, val, width}*/ lemma_BEByteSeqToInt_invertability(bytes: seq<byte>, val: int, width: nat)
    requires BEByteSeqToInt(bytes) == val
    requires 0 <= val < power2(8 * width)
    requires |bytes| == width
    ensures bytes == BEUintToSeqByte(val, width)
    decreases bytes, val, width
  {
  }

  lemma lemma_BEByteSeqToInt_BEUintToSeqByte_invertability()
    ensures forall bytes: seq<byte>, width: nat {:trigger BEUintToSeqByte(BEByteSeqToInt(bytes), width)} :: |bytes| == width ==> bytes == BEUintToSeqByte(BEByteSeqToInt(bytes), width)
    ensures forall width: nat, val: int {:trigger BEUintToSeqByte(val, width)} :: 0 <= val < power2(8 * width) ==> val == BEByteSeqToInt(BEUintToSeqByte(val, width))
  {
  }

  function method Uint64ToSeqByte(u: uint64): seq<byte>
    ensures Uint64ToSeqByte(u) == BEUintToSeqByte(u as int, 8)
    decreases u
  {
    ghost var pv: int := 256;
    var bs: seq<byte> := [(u / 72057594037927936) as byte, (u / 281474976710656 % 256) as byte, (u / 1099511627776 % 256) as byte, (u / 4294967296 % 256) as byte, (u / 16777216 % 256) as byte, (u / 65536 % 256) as byte, (u / 256 % 256) as byte, (u % 256) as byte];
    lemma_2toX();
    var u_int: int := u as int;
    calc {
      BEUintToSeqByte(u_int, 8);
      BEUintToSeqByte(u_int / 256, 7) + [(u_int % 256) as byte];
      BEUintToSeqByte(u_int / 256 / 256, 6) + [(u_int / 256 % 256) as byte] + [(u_int % 256) as byte];
      {
        lemma_div_denominator(u_int as int, 256, 256);
      }
      BEUintToSeqByte(u_int / 65536, 6) + [(u_int / 256 % 256) as byte] + [(u_int % 256) as byte];
      {
        lemma_div_denominator(u_int as int, 65536, 256);
      }
      BEUintToSeqByte(u_int / 16777216, 5) + [(u_int / 65536 % 256) as byte] + [(u_int / 256 % 256) as byte] + [(u_int % 256) as byte];
      {
        lemma_div_denominator(u_int as int, 16777216, 256);
      }
      BEUintToSeqByte(u_int / 4294967296, 4) + [(u_int / 16777216 % 256) as byte] + [(u_int / 65536 % 256) as byte] + [(u_int / 256 % 256) as byte] + [(u_int % 256) as byte];
      {
        lemma_div_denominator(u_int as int, 4294967296, 256);
      }
      BEUintToSeqByte(u_int / 1099511627776, 3) + [(u_int / 4294967296 % 256) as byte] + [(u_int / 16777216 % 256) as byte] + [(u_int / 65536 % 256) as byte] + [(u_int / 256 % 256) as byte] + [(u_int % 256) as byte];
      {
        lemma_div_denominator(u_int as int, 1099511627776, 256);
      }
      BEUintToSeqByte(u_int / 281474976710656, 2) + [(u_int / 1099511627776 % 256) as byte] + [(u_int / 4294967296 % 256) as byte] + [(u_int / 16777216 % 256) as byte] + [(u_int / 65536 % 256) as byte] + [(u_int / 256 % 256) as byte] + [(u_int % 256) as byte];
      {
        lemma_div_denominator(u_int as int, 281474976710656, 256);
      }
      BEUintToSeqByte(u_int / 72057594037927936, 1) + [(u_int / 281474976710656 % 256) as byte] + [(u_int / 1099511627776 % 256) as byte] + [(u_int / 4294967296 % 256) as byte] + [(u_int / 16777216 % 256) as byte] + [(u_int / 65536 % 256) as byte] + [(u_int / 256 % 256) as byte] + [(u_int % 256) as byte];
      {
        lemma_div_denominator(u_int as int, 72057594037927936, 256);
      }
      BEUintToSeqByte(u_int / 18446744073709551616, 0) + [(u_int / 72057594037927936 % 256) as byte] + [(u_int / 281474976710656 % 256) as byte] + [(u_int / 1099511627776 % 256) as byte] + [(u_int / 4294967296 % 256) as byte] + [(u_int / 16777216 % 256) as byte] + [(u_int / 65536 % 256) as byte] + [(u_int / 256 % 256) as byte] + [(u_int % 256) as byte];
    }
    bs
  }

  function method SeqByteToUint16(bs: seq<byte>): uint16
    requires |bs| == Uint16Size() as int
    ensures 0 <= BEByteSeqToInt(bs) < 18446744073709551616
    ensures BEByteSeqToInt(bs) < 65536
    ensures SeqByteToUint16(bs) == BEByteSeqToInt(bs) as uint16
    decreases bs
  {
    lemma_2toX();
    lemma_BEByteSeqToInt_bound(bs);
    bs[0] as uint16 * 256 + bs[1] as uint16
  }

  function method Uint16ToSeqByte(u: uint16): seq<byte>
    ensures Uint16ToSeqByte(u) == BEUintToSeqByte(u as int, 2)
    decreases u
  {
    ghost var pv: int := 256;
    var s: seq<byte> := [(u / 256 % 256) as byte, (u % 256) as byte];
    lemma_2toX();
    var u_int: int := u as int;
    calc {
      BEUintToSeqByte(u_int, 2);
      BEUintToSeqByte(u_int / 256, 1) + [(u_int % 256) as byte];
      BEUintToSeqByte(u_int / 256 / 256, 0) + [(u_int / 256 % 256) as byte] + [(u_int % 256) as byte];
      {
        lemma_div_denominator(u_int as int, 256, 256);
      }
      BEUintToSeqByte(u_int / 65536, 0) + [(u_int / 256 % 256) as byte] + [(u_int % 256) as byte];
    }
    s
  }
}

module Native__NativeTypes_i {

  import opened Native__NativeTypes_s
  function method Uint64Size(): uint64
  {
    8
  }

  function method Uint32Size(): uint64
  {
    4
  }

  function method Uint16Size(): uint64
  {
    2
  }
}

module Math__power2_i {

  import opened Math__power2_s

  import opened Math__power_s

  import opened Math__power_i

  import opened Math__div_nonlinear_i

  import opened Math__div_i

  import opened Math__mul_auto_i

  import opened Math__mul_i
  lemma lemma_power2_is_power_2_general()
    ensures forall x: nat {:trigger power(2, x)} {:trigger power2(x)} :: power2(x) == power(2, x)
  {
  }

  lemma /*{:_induction x}*/ lemma_power2_is_power_2(x: nat)
    ensures power2(x) == power(2, x)
    decreases x
  {
  }

  lemma lemma_power2_auto()
    ensures power2(0) == 1
    ensures power2(1) == 2
    ensures forall x: nat, y: nat {:trigger power2(x + y)} :: power2(x + y) == power2(x) * power2(y)
    ensures forall x: nat, y: nat {:trigger power2(x - y)} :: x >= y ==> power2(x - y) * power2(y) == power2(x)
    ensures forall x: nat, y: nat {:trigger x * y} :: y == 2 ==> x * y == x + x
  {
  }

  lemma /*{:_induction e1, e2}*/ lemma_power2_strictly_increases(e1: int, e2: int)
    requires 0 <= e1 < e2
    ensures power2(e1) < power2(e2)
    decreases e1, e2
  {
  }

  lemma /*{:_induction e1, e2}*/ lemma_power2_increases(e1: int, e2: int)
    requires 0 <= e1 <= e2
    ensures power2(e1) <= power2(e2)
    decreases e1, e2
  {
  }

  lemma /*{:_induction e1, e2}*/ lemma_power2_strictly_increases_converse(e1: int, e2: int)
    requires 0 <= e1
    requires 0 < e2
    requires power2(e1) < power2(e2)
    ensures e1 < e2
    decreases e1, e2
  {
  }

  lemma /*{:_induction e1, e2}*/ lemma_power2_increases_converse(e1: int, e2: int)
    requires 0 < e1
    requires 0 < e2
    requires power2(e1) <= power2(e2)
    ensures e1 <= e2
    decreases e1, e2
  {
  }

  lemma /*{:_induction e1, e2}*/ lemma_power2_adds(e1: nat, e2: nat)
    ensures power2(e1 + e2) == power2(e1) * power2(e2)
    decreases e2
  {
  }

  lemma /*{:_induction x, y}*/ lemma_power2_div_is_sub(x: int, y: int)
    requires 0 <= x <= y
    ensures power2(y - x) == power2(y) / power2(x) >= 0
    decreases x, y
  {
  }

  lemma lemma_2toX32()
    ensures power2(0) == 1
    ensures power2(1) == 2
    ensures power2(2) == 4
    ensures power2(3) == 8
    ensures power2(4) == 16
    ensures power2(5) == 32
    ensures power2(6) == 64
    ensures power2(7) == 128
    ensures power2(8) == 256
    ensures power2(9) == 512
    ensures power2(10) == 1024
    ensures power2(11) == 2048
    ensures power2(12) == 4096
    ensures power2(13) == 8192
    ensures power2(14) == 16384
    ensures power2(15) == 32768
    ensures power2(16) == 65536
    ensures power2(17) == 131072
    ensures power2(18) == 262144
    ensures power2(19) == 524288
    ensures power2(20) == 1048576
    ensures power2(21) == 2097152
    ensures power2(22) == 4194304
    ensures power2(23) == 8388608
    ensures power2(24) == 16777216
    ensures power2(25) == 33554432
    ensures power2(26) == 67108864
    ensures power2(27) == 134217728
    ensures power2(28) == 268435456
    ensures power2(29) == 536870912
    ensures power2(30) == 1073741824
    ensures power2(31) == 2147483648
    ensures power2(32) == 4294967296
  {
  }

  lemma lemma_2toX()
    ensures power2(64) == 18446744073709551616
    ensures power2(60) == 1152921504606846976
    ensures power2(32) == 4294967296
    ensures power2(24) == 16777216
    ensures power2(19) == 524288
    ensures power2(16) == 65536
    ensures power2(8) == 256
  {
  }

  lemma /*{:_induction n}*/ lemma_power2_add8(n: int)
    requires n >= 0
    ensures power2(n + 1) == 2 * power2(n)
    ensures power2(n + 2) == 4 * power2(n)
    ensures power2(n + 3) == 8 * power2(n)
    ensures power2(n + 4) == 16 * power2(n)
    ensures power2(n + 5) == 32 * power2(n)
    ensures power2(n + 6) == 64 * power2(n)
    ensures power2(n + 7) == 128 * power2(n)
    ensures power2(n + 8) == 256 * power2(n)
    decreases n
  {
  }

  lemma lemma_2to32()
    ensures power2(32) == 4294967296
    ensures power2(24) == 16777216
    ensures power2(19) == 524288
    ensures power2(16) == 65536
    ensures power2(8) == 256
    ensures power2(0) == 1
  {
  }

  lemma lemma_2to64()
    ensures power2(64) == 18446744073709551616
    ensures power2(60) == 1152921504606846976
  {
  }

  lemma lemma_power2_0_is_1()
    ensures power2(0) == 1
  {
  }

  lemma lemma_power2_1_is_2()
    ensures power2(1) == 2
  {
  }

  lemma /*{:_induction a, b}*/ lemma_bit_count_is_unique(x: int, a: int, b: int)
    requires 0 < a
    requires 0 < b
    requires power2(a - 1) <= x < power2(a)
    requires power2(b - 1) <= x < power2(b)
    ensures a == b
    decreases x, a, b
  {
  }

  lemma /*{:_induction x, y, z}*/ lemma_pull_out_powers_of_2(x: nat, y: nat, z: nat)
    ensures 0 <= x * y
    ensures 0 <= y * z
    ensures power(power2(x * y), z) == power(power2(x), y * z)
    decreases x, y, z
  {
  }

  lemma lemma_rebase_powers_of_2()
    ensures forall n: nat, e: nat {:trigger power(power2(n), e)} :: 0 <= n * e && power(power2(n), e) == power2(n * e)
  {
  }

  lemma /*{:_induction c}*/ lemma_mask_div_2(c: nat)
    requires 0 < c
    ensures (power2(c) - 1) / 2 == power2(c - 1) - 1
    decreases c
  {
  }

  lemma /*{:_induction p, s}*/ lemma_power2_division_inequality(x: nat, p: nat, s: nat)
    requires s <= p
    requires x < power2(p)
    ensures x / power2(s) < power2(p - s)
    decreases x, p, s
  {
  }

  lemma /*{:_induction a, b}*/ lemma_power2_unfolding(a: nat, b: nat)
    ensures 0 <= a * b
    ensures power(power2(a), b) == power2(a * b)
    decreases a, b
  {
  }

  function {:opaque} {:fuel 0, 0} NatNumBits(n: nat): nat
    ensures NatNumBits(n) >= 0
    decreases n
  {
    if n == 0 then
      0
    else
      1 + NatNumBits(n / 2)
  }

  lemma /*{:_induction c, n}*/ lemma_Power2BoundIsNatNumBits(c: nat, n: nat)
    ensures (c > 0 ==> power2(c - 1) <= n) && n < power2(c) <==> c == NatNumBits(n)
    decreases c, n
  {
  }
}

module Math__power2_s {
  function {:opaque} {:fuel 0, 0} power2(exp: nat): nat
    ensures power2(exp) > 0
    decreases exp
  {
    if exp == 0 then
      1
    else
      2 * power2(exp - 1)
  }

  lemma lemma_power2_32()
    ensures power2(8) == 256
    ensures power2(16) == 65536
    ensures power2(24) == 16777216
    ensures power2(32) == 4294967296
  {
  }
}

module Math__power_s {
  function {:opaque} {:fuel 0, 0} power(b: int, e: nat): int
    decreases e
  {
    if e == 0 then
      1
    else
      b * power(b, e - 1)
  }
}

module Math__power_i {

  import opened Math__power_s

  import opened Math__mul_i

  import opened Math__mul_auto_i
  lemma /*{:_induction b}*/ lemma_power_0(b: int)
    ensures power(b, 0) == 1
    decreases b
  {
  }

  lemma /*{:_induction b}*/ lemma_power_1(b: int)
    ensures power(b, 1) == b
    decreases b
  {
  }

  lemma /*{:_induction e}*/ lemma_0_power(e: nat)
    requires e > 0
    ensures power(0, e) == 0
    decreases e
  {
  }

  lemma /*{:_induction e}*/ lemma_1_power(e: nat)
    ensures power(1, e) == 1
    decreases e
  {
  }

  lemma /*{:_induction b, e1, e2}*/ lemma_power_adds(b: int, e1: nat, e2: nat)
    ensures power(b, e1) * power(b, e2) == power(b, e1 + e2)
    decreases e1
  {
  }

  lemma /*{:_induction a, b, c}*/ lemma_power_multiplies(a: int, b: nat, c: nat)
    ensures 0 <= b * c
    ensures power(a, b * c) == power(power(a, b), c)
    decreases c
  {
  }

  lemma /*{:_induction a, b, e}*/ lemma_power_distributes(a: int, b: int, e: nat)
    ensures power(a * b, e) == power(a, e) * power(b, e)
    decreases e
  {
  }

  lemma lemma_power_auto()
    ensures forall x: int {:trigger power(x, 0)} :: power(x, 0) == 1
    ensures forall x: int {:trigger power(x, 1)} :: power(x, 1) == x
    ensures forall x: int, y: int {:trigger power(x, y)} :: y == 0 ==> power(x, y) == 1
    ensures forall x: int, y: int {:trigger power(x, y)} :: y == 1 ==> power(x, y) == x
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> x <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 1 < y ==> x < x * y
    ensures forall x: int, y: nat, z: nat {:trigger power(x, y + z)} :: power(x, y + z) == power(x, y) * power(x, z)
    ensures forall x: int, y: nat, z: nat {:trigger power(x, y - z)} :: y >= z ==> power(x, y - z) * power(x, z) == power(x, y)
    ensures forall x: int, y: int, z: nat {:trigger power(x * y, z)} :: power(x * y, z) == power(x, z) * power(y, z)
  {
  }

  lemma /*{:_induction b, e}*/ lemma_power_positive(b: int, e: nat)
    requires 0 < b
    ensures 0 < power(b, e)
    decreases b, e
  {
  }

  lemma /*{:_induction b, e1, e2}*/ lemma_power_increases(b: nat, e1: nat, e2: nat)
    requires 0 < b
    requires e1 <= e2
    ensures power(b, e1) <= power(b, e2)
    decreases b, e1, e2
  {
  }

  lemma /*{:_induction b, e1, e2}*/ lemma_power_strictly_increases(b: nat, e1: nat, e2: nat)
    requires 1 < b
    requires e1 < e2
    ensures power(b, e1) < power(b, e2)
    decreases b, e1, e2
  {
  }

  lemma /*{:_induction x}*/ lemma_square_is_power_2(x: nat)
    ensures power(x, 2) == x * x
    decreases x
  {
  }
}

module Math__div_i {

  import opened Math__power_s

  import opened Math__power_i

  import opened Math__mod_auto_i

  import opened Math__mul_auto_i

  import opened Math__mul_nonlinear_i

  import opened Math__mul_i

  import opened Math__div_def_i

  import opened Math__div_nonlinear_i

  import opened Math__div_auto_i
  lemma lemma_div_by_one_is_identity(x: int)
    decreases x
  {
  }

  lemma lemma_div_basics(x: int)
    ensures x != 0 ==> 0 / x == 0
    ensures x / 1 == x
    ensures x != 0 ==> x / x == 1
    decreases x
  {
  }

  lemma lemma_small_div_converse()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x && 0 < d && x / d == 0 ==> x < d
  {
  }

  lemma lemma_div_is_ordered_by_denominator(x: int, y: int, z: int)
    requires x >= 0
    requires 1 <= y <= z
    ensures x / y >= x / z
    decreases x
  {
  }

  lemma lemma_div_is_strictly_ordered_by_denominator(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d < x
    decreases x
  {
  }

  lemma lemma_dividing_sums(a: int, b: int, d: int, R: int)
    requires 0 < d
    requires R == a % d + b % d - (a + b) % d
    ensures d * (a + b) / d - R == d * a / d + d * b / d
    decreases a, b, d, R
  {
  }

  lemma lemma_div_pos_is_pos(x: int, divisor: int)
    requires 0 <= x
    requires 0 < divisor
    ensures x / divisor >= 0
    decreases x, divisor
  {
  }

  lemma lemma_div_basics_forall()
    ensures forall x: int {:trigger 0 / x} :: x != 0 ==> 0 / x == 0
    ensures forall x: int {:trigger x / 1} :: x / 1 == x
    ensures forall x: int, y: int {:trigger x / y} :: x >= 0 && y > 0 ==> x / y >= 0
    ensures forall x: int, y: int {:trigger x / y} :: x >= 0 && y > 0 ==> x / y <= x
  {
  }

  lemma lemma_div_neg_neg(x: int, d: int)
    requires d > 0
    ensures x / d == -((-x + d - 1) / d)
    decreases x, d
  {
  }

  lemma lemma_mod_2(x: int)
    decreases x
  {
  }

  lemma lemma_mod2_plus(x: int)
    decreases x
  {
  }

  lemma lemma_mod2_plus2(x: int)
    decreases x
  {
  }

  lemma lemma_mod32(x: int)
    decreases x
  {
  }

  lemma lemma_mod_remainder_neg_specific(x: int, m: int)
    decreases x, m
  {
  }

  lemma lemma_mod_remainder_neg()
  {
  }

  lemma lemma_mod_remainder_pos_specific(x: int, m: int)
    decreases x, m
  {
  }

  lemma lemma_mod_remainder_pos()
  {
  }

  lemma lemma_mod_remainder_specific(x: int, m: int)
    decreases x, m
  {
  }

  lemma lemma_mod_remainder()
  {
  }

  lemma lemma_mod_basics()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger x % m % m} :: m > 0 ==> x % m % m == x % m
  {
  }

  lemma lemma_mod_properties()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger x % m % m} :: m > 0 ==> x % m % m == x % m
    ensures forall x: int, m: int {:trigger x % m} :: (m > 0 ==> 0 <= x % m) && (m > 0 ==> x % m < m)
  {
  }

  lemma lemma_mod_decreases(x: nat, d: nat)
    requires 0 < d
    ensures x % d <= x
    decreases x, d
  {
  }

  lemma lemma_mod_add_multiples_vanish(b: int, m: int)
    requires 0 < m
    ensures (m + b) % m == b % m
    decreases b, m
  {
  }

  lemma lemma_mod_sub_multiples_vanish(b: int, m: int)
    requires 0 < m
    ensures (-m + b) % m == b % m
    decreases b, m
  {
  }

  lemma lemma_mod_multiples_vanish(a: int, b: int, m: int)
    requires 0 < m
    ensures (m * a + b) % m == b % m
    decreases if a > 0 then a else -a
  {
  }

  lemma lemma_add_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m + y % m) % m == (x + y) % m
    decreases x, y, m
  {
  }

  lemma lemma_add_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures (x + y % m) % m == (x + y) % m
    decreases x, y, m
  {
  }

  lemma lemma_mod_equivalence(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m == y % m <==> (x - y) % m == 0
    decreases x, y, m
  {
  }

  lemma lemma_sub_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m - y % m) % m == (x - y) % m
    decreases x, y, m
  {
  }

  lemma lemma_sub_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures (x - y % m) % m == (x - y) % m
    decreases x, y, m
  {
  }

  lemma lemma_mod_adds(a: int, b: int, d: int)
    requires 0 < d
    ensures a % d + b % d == (a + b) % d + d * (a % d + b % d) / d
    ensures a % d + b % d < d ==> a % d + b % d == (a + b) % d
    decreases a, b, d
  {
  }

  lemma {:timeLimitMultiplier 2} /*{:_timeLimit 20}*/ lemma_mod_neg_neg(x: int, d: int)
    requires d > 0
    ensures x % d == x * (1 - d) % d
    decreases x, d
  {
  }

  lemma {:timeLimitMultiplier 2} /*{:_timeLimit 20}*/ lemma_fundamental_div_mod_converse(x: int, d: int, q: int, r: int)
    requires d != 0
    requires 0 <= r < d
    requires x == q * d + r
    ensures q == x / d
    ensures r == x % d
    decreases x, d, q, r
  {
  }

  lemma lemma_mod_pos_bound(x: int, m: int)
    requires 0 <= x
    requires 0 < m
    ensures 0 <= x % m < m
    decreases x
  {
  }

  lemma lemma_mul_mod_noop_left(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m * y % m == x * y % m
    decreases x, y, m
  {
  }

  lemma lemma_mul_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures x * y % m % m == x * y % m
    decreases x, y, m
  {
  }

  lemma lemma_mul_mod_noop_general(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m * y % m == x * y % m
    ensures x * y % m % m == x * y % m
    ensures x % m * y % m % m == x * y % m
    decreases x, y, m
  {
  }

  lemma lemma_mul_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m * y % m % m == x * y % m
    decreases x, y, m
  {
  }

  lemma /*{:_induction b, e, m}*/ lemma_power_mod_noop(b: int, e: nat, m: int)
    requires 0 < m
    ensures power(b % m, e) % m == power(b, e) % m
    decreases e
  {
  }

  lemma lemma_mod_subtraction(x: nat, s: nat, d: nat)
    requires 0 < d
    requires 0 <= s <= x % d
    ensures x % d - s % d == (x - s) % d
    decreases x, s, d
  {
  }

  lemma lemma_mod_ordering(x: nat, k: nat, d: nat)
    requires 1 < d
    requires 0 < k
    ensures 0 < d * k
    ensures x % d <= x % (d * k)
    decreases x, k, d
  {
  }

  lemma lemma_mod_multiples_basic(x: int, m: int)
    requires m > 0
    ensures x * m % m == 0
    decreases x, m
  {
  }

  lemma lemma_div_plus_one(x: int, d: int)
    requires d > 0
    ensures 1 + x / d == (d + x) / d
    decreases x, d
  {
  }

  lemma lemma_div_minus_one(x: int, d: int)
    requires d > 0
    ensures -1 + x / d == (-d + x) / d
    decreases x, d
  {
  }

  lemma lemma_mod_mod(x: int, a: int, b: int)
    requires 0 < a
    requires 0 < b
    ensures 0 < a * b
    ensures x % (a * b) % a == x % a
    decreases x, a, b
  {
  }

  lemma lemma_div_is_div_recursive(x: int, d: int)
    requires d > 0
    ensures my_div_recursive(x, d) == x / d
    decreases x, d
  {
  }

  lemma lemma_div_is_div_recursive_forall()
    ensures forall x: int, d: int {:trigger my_div_recursive(x, d)} :: d > 0 ==> my_div_recursive(x, d) == x / d
  {
  }

  lemma /*{:_induction x, m}*/ lemma_mod_is_mod_recursive(x: int, m: int)
    requires m > 0
    ensures my_mod_recursive(x, m) == x % m
    decreases if x < 0 then -x + m else x
  {
  }

  lemma lemma_mod_is_mod_recursive_forall()
    ensures forall x: int, d: int {:trigger my_mod_recursive(x, d)} :: d > 0 ==> my_mod_recursive(x, d) == x % d
  {
  }

  lemma lemma_basic_div(d: int)
    requires d > 0
    ensures forall x: int {:trigger x / d} :: 0 <= x < d ==> x / d == 0
    decreases d
  {
  }

  lemma lemma_div_is_ordered(x: int, y: int, z: int)
    requires x <= y
    requires z > 0
    ensures x / z <= y / z
    decreases x, y, z
  {
  }

  lemma lemma_div_decreases(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d < x
    decreases x, d
  {
  }

  lemma lemma_div_nonincreasing(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x / d <= x
    decreases x, d
  {
  }

  lemma lemma_breakdown(a: int, b: int, c: int)
    requires 0 <= a
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures a % (b * c) == b * a / b % c + a % b
    decreases a, b, c
  {
  }

  lemma lemma_remainder_upper(x: int, divisor: int)
    requires 0 <= x
    requires 0 < divisor
    ensures x - divisor < x / divisor * divisor
    decreases x, divisor
  {
  }

  lemma lemma_remainder_lower(x: int, divisor: int)
    requires 0 <= x
    requires 0 < divisor
    ensures x >= x / divisor * divisor
    decreases x, divisor
  {
  }

  lemma lemma_remainder(x: int, divisor: int)
    requires 0 <= x
    requires 0 < divisor
    ensures 0 <= x - x / divisor * divisor < divisor
    decreases x, divisor
  {
  }

  lemma lemma_div_denominator(x: int, c: nat, d: nat)
    requires 0 <= x
    requires 0 < c
    requires 0 < d
    ensures c * d != 0
    ensures x / c / d == x / (c * d)
    decreases x, c, d
  {
  }

  lemma lemma_mul_hoist_inequality(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < z
    ensures x * y / z <= x * y / z
    decreases x, y, z
  {
  }

  lemma lemma_indistinguishable_quotients(a: int, b: int, d: int)
    requires 0 < d
    requires 0 <= a - a % d <= b < a + d - a % d
    ensures a / d == b / d
    decreases a, b, d
  {
  }

  lemma lemma_truncate_middle(x: int, b: int, c: int)
    requires 0 <= x
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures b * x % (b * c) == b * x % c
    decreases x, b, c
  {
  }

  lemma lemma_div_multiples_vanish_quotient(x: int, a: int, d: int)
    requires 0 < x
    requires 0 <= a
    requires 0 < d
    ensures 0 < x * d
    ensures a / d == x * a / (x * d)
    decreases x, a, d
  {
  }

  lemma lemma_round_down(a: int, r: int, d: int)
    requires 0 < d
    requires a % d == 0
    requires 0 <= r < d
    ensures a == d * (a + r) / d
    decreases a, r, d
  {
  }

  lemma lemma_div_multiples_vanish_fancy(x: int, b: int, d: int)
    requires 0 < d
    requires 0 <= b < d
    ensures (d * x + b) / d == x
    decreases x, b, d
  {
  }

  lemma lemma_div_multiples_vanish(x: int, d: int)
    requires 0 < d
    ensures d * x / d == x
    decreases x, d
  {
  }

  lemma lemma_div_by_multiple(b: int, d: int)
    requires 0 <= b
    requires 0 < d
    ensures b * d / d == b
    decreases b, d
  {
  }

  lemma lemma_div_by_multiple_is_strongly_ordered(x: int, y: int, m: int, z: int)
    requires x < y
    requires y == m * z
    requires z > 0
    ensures x / z < y / z
    decreases x, y, m, z
  {
  }

  lemma lemma_multiply_divide_le(a: int, b: int, c: int)
    requires 0 < b
    requires a <= b * c
    ensures a / b <= c
    decreases a, b, c
  {
  }

  lemma lemma_multiply_divide_lt(a: int, b: int, c: int)
    requires 0 < b
    requires a < b * c
    ensures a / b < c
    decreases a, b, c
  {
  }

  lemma lemma_hoist_over_denominator(x: int, j: int, d: nat)
    requires 0 < d
    ensures x / d + j == (x + j * d) / d
    decreases x, j, d
  {
  }

  lemma lemma_part_bound1(a: int, b: int, c: int)
    requires 0 <= a
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures b * a / b % (b * c) <= b * (c - 1)
    decreases a, b, c
  {
  }

  lemma lemma_part_bound2(a: int, b: int, c: int)
    requires 0 <= a
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures a % b % (b * c) < b
    decreases a, b, c
  {
  }

  lemma lemma_mod_breakdown(a: int, b: int, c: int)
    requires 0 <= a
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures a % (b * c) == b * a / b % c + a % b
    decreases a, b, c
  {
  }

  lemma lemma_div_denominator_forall()
    ensures forall c: nat, d: nat {:trigger c * d} :: 0 < c && 0 < d ==> c * d != 0
    ensures forall x: int, c: nat, d: nat {:trigger x / c / d} :: 0 <= x && 0 < c && 0 < d ==> x / c / d == x / (c * d)
  {
  }
}

module Math__div_def_i {
  function div(x: int, d: int): int
    requires d != 0
    decreases x, d
  {
    x / d
  }

  function mod(x: int, d: int): int
    requires d != 0
    decreases x, d
  {
    x % d
  }

  function div_recursive(x: int, d: int): int
    requires d != 0
    decreases x, d
  {
    INTERNAL_div_recursive(x, d)
  }

  function mod_recursive(x: int, d: int): int
    requires d > 0
    decreases x, d
  {
    INTERNAL_mod_recursive(x, d)
  }

  function mod_boogie(x: int, y: int): int
    requires y != 0
    decreases x, y
  {
    x % y
  }

  function div_boogie(x: int, y: int): int
    requires y != 0
    decreases x, y
  {
    x / y
  }

  function my_div_recursive(x: int, d: int): int
    requires d != 0
    decreases x, d
  {
    if d > 0 then
      my_div_pos(x, d)
    else
      -1 * my_div_pos(x, -1 * d)
  }

  function my_div_pos(x: int, d: int): int
    requires d > 0
    decreases if x < 0 then d - x else x
  {
    if x < 0 then
      -1 + my_div_pos(x + d, d)
    else if x < d then
      0
    else
      1 + my_div_pos(x - d, d)
  }

  function my_mod_recursive(x: int, m: int): int
    requires m > 0
    decreases if x < 0 then m - x else x
  {
    if x < 0 then
      my_mod_recursive(m + x, m)
    else if x < m then
      x
    else
      my_mod_recursive(x - m, m)
  }

  function INTERNAL_mod_recursive(x: int, m: int): int
    requires m > 0
    decreases x, m
  {
    my_mod_recursive(x, m)
  }

  function INTERNAL_div_recursive(x: int, d: int): int
    requires d != 0
    decreases x, d
  {
    my_div_recursive(x, d)
  }
}

module Math__div_auto_i {

  import opened Math__mod_auto_i

  import opened Math__mod_auto_proofs_i

  import opened Math__div_auto_proofs_i
  predicate DivAuto(n: int)
    requires n > 0
    decreases n
  {
    ModAuto(n) &&
    n / n == -(-n / n) == 1 &&
    (forall x: int {:trigger x / n} :: 
      0 <= x < n <==> x / n == 0) &&
    (forall x: int, y: int {:trigger (x + y) / n} :: 
      ghost var z: int := x % n + y % n; (0 <= z < n && (x + y) / n == x / n + y / n) || (n <= z < n + n && (x + y) / n == x / n + y / n + 1)) &&
    forall x: int, y: int {:trigger (x - y) / n} :: 
      ghost var z: int := x % n - y % n; (0 <= z < n && (x - y) / n == x / n - y / n) || (-n <= z < 0 && (x - y) / n == x / n - y / n - 1)
  }

  lemma lemma_div_auto(n: int)
    requires n > 0
    ensures DivAuto(n)
    decreases n
  {
  }

  predicate TDivAutoLe(x: int, y: int)
    decreases x, y
  {
    x <= y
  }

  lemma lemma_div_auto_induction(n: int, x: int, f: int -> bool)
    requires n > 0
    requires DivAuto(n) ==> (forall i: int {:trigger TDivAutoLe(0, i)} :: TDivAutoLe(0, i) && i < n ==> f(i)) && (forall i: int {:trigger TDivAutoLe(0, i)} :: TDivAutoLe(0, i) && f(i) ==> f(i + n)) && forall i: int {:trigger TDivAutoLe(i + 1, n)} :: TDivAutoLe(i + 1, n) && f(i) ==> f(i - n)
    ensures DivAuto(n)
    ensures f(x)
    decreases n, x
  {
  }

  lemma lemma_div_auto_induction_forall(n: int, f: int -> bool)
    requires n > 0
    requires DivAuto(n) ==> (forall i: int {:trigger TDivAutoLe(0, i)} :: TDivAutoLe(0, i) && i < n ==> f(i)) && (forall i: int {:trigger TDivAutoLe(0, i)} :: TDivAutoLe(0, i) && f(i) ==> f(i + n)) && forall i: int {:trigger TDivAutoLe(i + 1, n)} :: TDivAutoLe(i + 1, n) && f(i) ==> f(i - n)
    ensures DivAuto(n)
    ensures forall i: int {:trigger f(i)} :: f(i)
    decreases n
  {
  }
}

module Math__div_auto_proofs_i {

  import opened Math__mod_auto_i

  import opened Math__mod_auto_proofs_i

  import opened Math__div_nonlinear_i
  lemma lemma_div_auto_basics(n: int)
    requires n > 0
    ensures n / n == -(-n / n) == 1
    ensures forall x: int {:trigger x / n} :: 0 <= x < n <==> x / n == 0
    ensures forall x: int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1
    ensures forall x: int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1
    decreases n
  {
  }
}

module Common__SeqIsUnique_i {

  import opened Common__SeqIsUniqueDef_i

  import opened Native__NativeTypes_i
  function UniqueSeqToSet<X>(xs: seq<X>): set<X>
    requires SeqIsUnique(xs)
    ensures forall x: X {:trigger x in UniqueSeqToSet(xs)} {:trigger x in xs} :: x in xs ==> x in UniqueSeqToSet(xs)
    decreases xs
  {
    set x: X {:trigger x in xs} | x in xs
  }

  function {:timeLimitMultiplier 3} {:opaque} {:fuel 0, 0} /*{:_timeLimit 30}*/ SetToUniqueSeq<X(!new)>(s: set<X>): seq<X>
    ensures forall x: X {:trigger x in s} {:trigger x in SetToUniqueSeq(s)} :: x in SetToUniqueSeq(s) <==> x in s
    ensures SeqIsUnique(SetToUniqueSeq(s))
    ensures |SetToUniqueSeq(s)| == |s|
    decreases s
  {
    if s == {} then
      ghost var xs: seq<X> := [];
      calc ==> {
        true;
        {
          reveal SeqIsUnique();
        }
        SeqIsUnique(xs);
      }
      xs
    else
      ghost var x: X :| x in s; ghost var s': set<X> := s - {x}; ghost var xs': seq<X> := SetToUniqueSeq(s'); calc ==> {
    true;
    {
      reveal SeqIsUnique();
    }
    SeqIsUnique(xs' + [x]);
  } xs' + [x]
  }

  function Subsequence<X(!new)>(xs: seq<X>, f: X -> bool): seq<X>
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    reads set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj
    ensures forall x: X {:trigger f(x)} {:trigger x in xs} {:trigger x in Subsequence(xs, f)} :: x in Subsequence(xs, f) <==> x in xs && f(x)
    decreases set _x0: X, _obj: object? /*{:_reads}*/ {:trigger _obj in f.reads(_x0)} | _obj in f.reads(_x0) :: _obj, xs
  {
    ghost var s: set<X> := set x: X {:trigger f(x)} {:trigger x in xs} | x in xs && f(x);
    SetToUniqueSeq(s)
  }

  method SeqToSetConstruct<X>(xs: seq<X>) returns (s: set<X>)
    ensures forall x: X {:trigger x in xs} {:trigger x in s} :: x in s <==> x in xs
    ensures SeqIsUnique(xs) ==> |s| == |xs| && s == UniqueSeqToSet(xs)
    decreases xs
  {
    reveal SeqIsUnique();
    s := {};
    var i := 0;
    while i < |xs|
      invariant 0 <= i <= |xs|
      invariant forall x: X {:trigger x in xs[..i]} {:trigger x in s} :: x in s <==> x in xs[..i]
      invariant SeqIsUnique(xs[..i]) ==> |s| == i
      decreases |xs| - i
    {
      s := s + {xs[i]};
      i := i + 1;
    }
  }

  method {:timeLimitMultiplier 5} /*{:_timeLimit 50}*/ SetToUniqueSeqConstruct<X(0)>(s: set<X>) returns (xs: seq<X>)
    ensures SeqIsUnique(xs)
    ensures UniqueSeqToSet(xs) == s
    ensures forall x: X {:trigger x in s} {:trigger x in xs} :: x in xs <==> x in s
    ensures |xs| == |s|
    decreases s
  {
    var arr := new X[|s|];
    var s1 := s;
    ghost var s2 := {};
    ghost var i := 0;
    forall
      ensures SeqIsUnique(arr[..i])
    {
      reveal SeqIsUnique();
    }
    while |s1| != 0
      invariant 0 <= i <= |s|
      invariant s1 + s2 == s
      invariant s1 !! s2
      invariant |s1| == |s| - i
      invariant |s2| == i
      invariant SeqIsUnique(arr[..i])
      invariant forall x: X {:trigger x in s2} {:trigger x in arr[..i]} :: x in arr[..i] <==> x in s2
      decreases if |s1| <= 0 then 0 - |s1| else |s1| - 0
    {
      reveal SeqIsUnique();
      ghost var old_seq := arr[..i];
      var x :| x in s1;
      assert x !in old_seq;
      assert forall y: X {:trigger y in s2} {:trigger y in old_seq} :: y in s2 + {x} ==> y in old_seq + [x];
      arr[|s| - |s1|] := x;
      s1 := s1 - {x};
      s2 := s2 + {x};
      i := i + 1;
      assert arr[..i] == old_seq + [x];
    }
    xs := arr[..];
    assert xs == arr[..i];
  }

  method SubsequenceConstruct<X(==,0)>(xs: seq<X>, f: X -> bool) returns (xs': seq<X>)
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    ensures forall x: X {:trigger x in xs} {:trigger x in xs'} :: x in xs' <==> x in xs && f(x)
    ensures SeqIsUnique(xs) ==> SeqIsUnique(xs')
    decreases xs
  {
    reveal SeqIsUnique();
    var arr := new X[|xs|];
    var i := 0;
    var j := 0;
    while i < |xs|
      invariant 0 <= i <= |xs|
      invariant 0 <= j <= i
      invariant forall x: X {:trigger x in xs[..i]} {:trigger x in arr[..j]} :: x in arr[..j] <==> x in xs[..i] && f(x)
      invariant SeqIsUnique(xs) ==> SeqIsUnique(arr[..j])
      decreases |xs| - i
    {
      ghost var old_xs := xs[..i];
      ghost var old_xs' := arr[..j];
      if f(xs[i]) {
        if SeqIsUnique(xs) {
          reveal SeqIsUnique();
          assert forall k: int {:trigger xs[k]} :: 0 <= k < i ==> xs[k] != xs[i];
          assert forall k: int {:trigger xs[..i][k]} :: 0 <= k < i ==> xs[..i][k] != xs[i];
          assert xs[i] !in arr[..j];
        }
        arr[j] := xs[i];
        j := j + 1;
        assert arr[..j] == old_xs' + [xs[i]];
      }
      i := i + 1;
      assert xs[..i] == old_xs + [xs[i - 1]];
    }
    xs' := arr[..j];
  }

  method UniqueSubsequenceConstruct<X(==,0)>(xs: seq<X>, f: X -> bool) returns (xs': seq<X>)
    requires forall x: X {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    ensures forall x: X {:trigger x in xs} {:trigger x in xs'} :: x in xs' <==> x in xs && f(x)
    ensures SeqIsUnique(xs')
    decreases xs
  {
    var s := set x: X {:trigger f(x)} {:trigger x in xs} | x in xs && f(x);
    xs' := SetToUniqueSeqConstruct(s);
  }

  lemma EstablishAppendToUniqueSeq<X>(xs: seq<X>, x: X, xs': seq<X>)
    requires SeqIsUnique(xs)
    requires x !in xs
    requires xs' == xs + [x]
    ensures SeqIsUnique(xs')
    ensures x in xs'
    decreases xs, xs'
  {
  }

  function method AppendToUniqueSeq<X>(xs: seq<X>, x: X): seq<X>
    requires SeqIsUnique(xs)
    requires x !in xs
    ensures SeqIsUnique(AppendToUniqueSeq(xs, x))
    ensures x in AppendToUniqueSeq(xs, x)
    decreases xs
  {
    reveal SeqIsUnique();
    var xs': seq<X> := xs + [x];
    EstablishAppendToUniqueSeq(xs, x, xs');
    xs'
  }

  function method AppendToUniqueSeqMaybe<X(==)>(xs: seq<X>, x: X): seq<X>
    requires SeqIsUnique(xs)
    ensures SeqIsUnique(AppendToUniqueSeqMaybe(xs, x))
    ensures x in AppendToUniqueSeqMaybe(xs, x)
    decreases xs
  {
    reveal SeqIsUnique();
    if x in xs then
      xs
    else
      var xs': seq<X> := xs + [x]; EstablishAppendToUniqueSeq(xs, x, xs'); xs'
  }

  lemma lemma_UniqueSeq_SubSeqsUnique<X>(whole: seq<X>, left: seq<X>, right: seq<X>)
    requires SeqIsUnique(whole)
    requires whole == left + right
    ensures SeqIsUnique(left)
    ensures SeqIsUnique(right)
    decreases whole, left, right
  {
  }

  lemma lemma_seqs_set_cardinality<T>(Q: seq<T>, S: set<T>)
    requires SeqIsUnique(Q)
    requires S == UniqueSeqToSet(Q)
    ensures |Q| == |S|
    decreases Q, S
  {
  }

  lemma lemma_seqs_set_membership<T>(Q: seq<T>, S: set<T>)
    requires SeqIsUnique(Q)
    requires S == UniqueSeqToSet(Q)
    ensures forall i: T {:trigger i in S} {:trigger i in Q} :: i in Q <==> i in S
    decreases Q, S
  {
  }
}

module Common__SeqIsUniqueDef_i {
  predicate {:opaque} {:fuel 0, 0} SeqIsUnique<X>(xs: seq<X>)
    decreases xs
  {
    forall i: int, j: int {:trigger xs[j], xs[i]} :: 
      0 <= i < |xs| &&
      0 <= j < |xs| &&
      xs[i] == xs[j] ==>
        i == j
  }
}

module Concrete_NodeIdentity_i refines Common__NodeIdentity_s {

  import opened Native__Io_s

  export Spec
    provides NodeIdentity


  export
    reveals *
    provides Native__Io_s
    reveals NodeIdentity

  type /*{:_provided}*/ NodeIdentity = EndPoint
}

abstract module Common__NodeIdentity_s {
  type NodeIdentity(==)
}

module Common__GenericMarshalling_i {

  import opened Native__Io_s

  import opened Native__NativeTypes_s

  import opened Native__NativeTypes_i

  import opened Collections__Maps_i

  import opened Collections__Seqs_i

  import opened Logic__Option_i

  import opened Common__Util_i

  import opened Common__MarshallInt_i

  import opened Math__power2_i
  datatype G = GUint64 | GArray(elt: G) | GTuple(t: seq<G>) | GByteArray | GTaggedUnion(cases: seq<G>)

  datatype V = VUint64(u: uint64) | VArray(a: seq<V>) | VTuple(t: seq<V>) | VByteArray(b: seq<byte>) | VCase(c: uint64, val: V)

  datatype ContentsTraceStep = ContentsTraceStep(data: seq<byte>, val: Option<V>)

  predicate ValInGrammar(val: V, grammar: G)
    decreases val, grammar
  {
    match val
    case VUint64(_) =>
      grammar.GUint64?
    case VArray(a) =>
      grammar.GArray? &&
      forall v: V {:trigger ValInGrammar(v, grammar.elt)} {:trigger v in a} :: 
        v in a ==>
          ValInGrammar(v, grammar.elt)
    case VTuple(t) =>
      grammar.GTuple? &&
      |t| == |grammar.t| &&
      forall i: int {:trigger grammar.t[i]} {:trigger t[i]} :: 
        0 <= i < |t| ==>
          ValInGrammar(t[i], grammar.t[i])
    case VByteArray(b) =>
      grammar.GByteArray?
    case VCase(c, v) =>
      grammar.GTaggedUnion? &&
      c as int < |grammar.cases| &&
      ValInGrammar(v, grammar.cases[c])
  }

  predicate ValidGrammar(grammar: G)
    decreases grammar
  {
    match grammar
    case GUint64() =>
      true
    case GArray(elt) =>
      ValidGrammar(elt)
    case GTuple(t) =>
      |t| < 18446744073709551616 &&
      forall g: G {:trigger ValidGrammar(g)} {:trigger g in t} :: 
        g in t ==>
          ValidGrammar(g)
    case GByteArray() =>
      true
    case GTaggedUnion(cases) =>
      |cases| < 18446744073709551616 &&
      forall g: G {:trigger ValidGrammar(g)} {:trigger g in cases} :: 
        g in cases ==>
          ValidGrammar(g)
  }

  predicate ValidVal(val: V)
    decreases val
  {
    match val
    case VUint64(_) =>
      true
    case VArray(a) =>
      |a| < 18446744073709551616 &&
      forall v: V {:trigger ValidVal(v)} {:trigger v in a} :: 
        v in a ==>
          ValidVal(v)
    case VTuple(t) =>
      |t| < 18446744073709551616 &&
      forall v: V {:trigger ValidVal(v)} {:trigger v in t} :: 
        v in t ==>
          ValidVal(v)
    case VByteArray(b) =>
      |b| < 18446744073709551616
    case VCase(c, v) =>
      ValidVal(v)
  }

  function {:opaque} {:fuel 0, 0} SeqSum(t: seq<V>): int
    ensures SeqSum(t) >= 0
    decreases t
  {
    if |t| == 0 then
      0
    else
      SizeOfV(t[0]) + SeqSum(t[1..])
  }

  function SizeOfV(val: V): int
    ensures SizeOfV(val) >= 0
    decreases val
  {
    match val
    case VUint64(_) =>
      8
    case VArray(a) =>
      8 + SeqSum(a)
    case VTuple(t) =>
      SeqSum(t)
    case VByteArray(b) =>
      8 + |b|
    case VCase(c, v) =>
      8 + SizeOfV(v)
  }

  predicate Trigger(i: int)
    decreases i
  {
    true
  }

  function method parse_Uint64(data: seq<byte>): (Option<V>, seq<byte>)
    requires |data| < 18446744073709551616
    decreases data
  {
    if |data| as uint64 >= Uint64Size() then
      (Some(VUint64(SeqByteToUint64(data[..Uint64Size()]))), data[Uint64Size()..])
    else
      (None, [])
  }

  method ParseUint64(data: array<byte>, index: uint64)
      returns (success: bool, v: V, rest_index: uint64)
    requires index as int <= data.Length
    requires data.Length < 18446744073709551616
    ensures rest_index as int <= data.Length
    ensures var (v': Option<V>, rest': seq<byte>) := parse_Uint64(data[index..]); var v_opt: Option<V> := if success then Some(v) else None(); v_opt == v' && data[rest_index..] == rest'
    decreases data, index
  {
    lemma_2toX();
    if data.Length as uint64 >= 8 && index <= data.Length as uint64 - 8 {
      var result := data[index as int] as uint64 * 72057594037927936 + data[index as int + 1] as uint64 * 281474976710656 + data[index as int + 2] as uint64 * 1099511627776 + data[index as int + 3] as uint64 * 4294967296 + data[index as int + 4] as uint64 * 16777216 + data[index as int + 5] as uint64 * 65536 + data[index as int + 6] as uint64 * 256 + data[index as int + 7] as uint64;
      success := true;
      v := VUint64(result);
      rest_index := index + Uint64Size();
    } else {
      print ""Parse uint64 fails\n"";
      success := false;
      rest_index := data.Length as uint64;
    }
  }

  function method {:opaque} {:fuel 0, 0} parse_Array_contents(data: seq<byte>, eltType: G, len: uint64): (Option<seq<V>>, seq<byte>)
    requires |data| < 18446744073709551616
    requires ValidGrammar(eltType)
    ensures var (opt_seq: Option<seq<V>>, rest: seq<byte>) := parse_Array_contents(data, eltType, len); |rest| <= |data| && (opt_seq.Some? ==> forall i: int {:trigger opt_seq.v[i]} :: 0 <= i < |opt_seq.v| ==> ValInGrammar(opt_seq.v[i], eltType))
    decreases eltType, 1, len
  {
    if len == 0 then
      (Some([]), data)
    else
      var (val: Option<V>, rest1: seq<byte>) := parse_Val(data, eltType); var (others: Option<seq<V>>, rest2: seq<byte>) := parse_Array_contents(rest1, eltType, len - 1); if !val.None? && !others.None? then (Some([val.v] + others.v), rest2) else (None, [])
  }

  lemma /*{:_induction data, eltType, len}*/ lemma_ArrayContents_helper(data: seq<byte>, eltType: G, len: uint64, v: seq<V>, trace: seq<ContentsTraceStep>)
    requires |data| < 18446744073709551616
    requires ValidGrammar(eltType)
    requires |trace| == len as int + 1
    requires |v| == len as int
    requires forall j: int {:trigger trace[j]} :: 0 <= j < |trace| ==> |trace[j].data| < 18446744073709551616
    requires trace[0].data == data
    requires (forall j: int, _t#0: int {:trigger trace[_t#0], trace[j]} | _t#0 == j - 1 :: 0 < j && j < len as int + 1 ==> trace[j].val == parse_Val(trace[_t#0].data, eltType).0) && forall j: int, _t#0: int {:trigger trace[_t#0], trace[j]} | _t#0 == j - 1 :: 0 < j && j < len as int + 1 ==> trace[j].data == parse_Val(trace[_t#0].data, eltType).1
    requires forall j: int {:trigger trace[j]} :: 0 < j < |trace| ==> trace[j].val.Some?
    requires forall j: int {:trigger trace[j]} :: 0 < j < |trace| ==> v[j - 1] == trace[j].val.v
    ensures var (v': Option<seq<V>>, rest': seq<byte>) := parse_Array_contents(data, eltType, len); ghost var v_opt: Option<seq<V>> := Some(v); v_opt == v' && trace[|trace| - 1].data == rest'
    decreases len
  {
  }

  lemma /*{:_induction data, eltType, len}*/ lemma_ArrayContents_helper_bailout(data: seq<byte>, eltType: G, len: uint64, trace: seq<ContentsTraceStep>)
    requires |data| < 18446744073709551616
    requires ValidGrammar(eltType)
    requires 1 < |trace| <= len as int + 1
    requires forall j: int {:trigger trace[j]} :: 0 <= j < |trace| ==> |trace[j].data| < 18446744073709551616
    requires trace[0].data == data
    requires (forall j: int, _t#0: int {:trigger trace[_t#0], trace[j]} | _t#0 == j - 1 :: 0 < j && j < |trace| ==> trace[j].val == parse_Val(trace[_t#0].data, eltType).0) && forall j: int, _t#0: int {:trigger trace[_t#0], trace[j]} | _t#0 == j - 1 :: 0 < j && j < |trace| ==> trace[j].data == parse_Val(trace[_t#0].data, eltType).1
    requires forall j: int {:trigger trace[j]} :: 0 < j < |trace| - 1 ==> trace[j].val.Some?
    requires trace[|trace| - 1].val.None?
    ensures var (v': Option<seq<V>>, rest': seq<byte>) := parse_Array_contents(data, eltType, len); v'.None? && rest' == []
    decreases len
  {
  }

  method {:timeLimitMultiplier 2} /*{:_timeLimit 20}*/ ParseArrayContents(data: array<byte>, index: uint64, eltType: G, len: uint64)
      returns (success: bool, v: seq<V>, rest_index: uint64)
    requires index as int <= data.Length
    requires data.Length < 18446744073709551616
    requires ValidGrammar(eltType)
    ensures rest_index as int <= data.Length
    ensures var (v': Option<seq<V>>, rest': seq<byte>) := parse_Array_contents(data[index..], eltType, len); var v_opt: Option<seq<V>> := if success then Some(v) else None(); v_opt == v' && data[rest_index..] == rest'
    ensures success ==> ValidVal(VArray(v))
    decreases eltType, 1, len
  {
    reveal parse_Array_contents();
    var vArr := new V[len];
    ghost var g_v := [];
    success := true;
    var i: uint64 := 0;
    var next_val_index: uint64 := index;
    ghost var trace := [ContentsTraceStep(data[index..], None())];
    while i < len
      invariant 0 <= i <= len
      invariant index <= next_val_index <= data.Length as uint64
      invariant |trace| == i as int + 1
      invariant |g_v| == i as int
      invariant vArr[..i] == g_v
      invariant trace[0].data == data[index..]
      invariant forall j: int {:trigger trace[j]} :: 0 <= j < i as int + 1 ==> |trace[j].data| < 18446744073709551616
      invariant trace[i].data == data[next_val_index..]
      invariant forall j: uint64 {:trigger trace[j]} :: 0 < j <= i ==> trace[j].val.Some?
      invariant forall j: uint64 {:trigger trace[j]} :: 0 < j <= i ==> g_v[j - 1] == trace[j].val.v
      invariant (forall j: int, _t#0: int {:trigger trace[_t#0], trace[j]} | _t#0 == j - 1 :: 0 < j && j < i as int + 1 ==> trace[j].val == parse_Val(trace[_t#0].data, eltType).0) && forall j: int, _t#0: int {:trigger trace[_t#0], trace[j]} | _t#0 == j - 1 :: 0 < j && j < i as int + 1 ==> trace[j].data == parse_Val(trace[_t#0].data, eltType).1
      invariant ValidVal(VArray(vArr[..i]))
      decreases len as int - i as int
    {
      var some1, val, rest1 := ParseVal(data, next_val_index, eltType);
      ghost var step := ContentsTraceStep(data[rest1..], if some1 then Some(val) else None());
      ghost var old_trace := trace;
      trace := trace + [step];
      if !some1 {
        success := false;
        rest_index := data.Length as uint64;
        lemma_ArrayContents_helper_bailout(data[index..], eltType, len, trace);
        return;
      }
      g_v := g_v + [val];
      vArr[i] := val;
      next_val_index := rest1;
      i := i + 1;
    }
    success := true;
    rest_index := next_val_index;
    v := vArr[..];
    lemma_ArrayContents_helper(data[index..], eltType, len, v, trace);
  }

  function method parse_Array(data: seq<byte>, eltType: G): (Option<V>, seq<byte>)
    requires ValidGrammar(eltType)
    requires |data| < 18446744073709551616
    ensures var (opt_val: Option<V>, rest: seq<byte>) := parse_Array(data, eltType); |rest| <= |data| && (opt_val.Some? ==> ValInGrammar(opt_val.v, GArray(eltType)))
    decreases eltType
  {
    var (len: Option<V>, rest: seq<byte>) := parse_Uint64(data);
    if !len.None? then
      var (contents: Option<seq<V>>, remainder: seq<byte>) := parse_Array_contents(rest, eltType, len.v.u);
      if !contents.None? then
        (Some(VArray(contents.v)), remainder)
      else
        (None, [])
    else
      (None, [])
  }

  method ParseArray(data: array<byte>, index: uint64, eltType: G)
      returns (success: bool, v: V, rest_index: uint64)
    requires index as int <= data.Length
    requires data.Length < 18446744073709551616
    requires ValidGrammar(eltType)
    ensures rest_index as int <= data.Length
    ensures var (v': Option<V>, rest': seq<byte>) := parse_Array(data[index..], eltType); var v_opt: Option<V> := if success then Some(v) else None(); v_opt == v' && data[rest_index..] == rest'
    ensures success ==> ValidVal(v)
    decreases eltType
  {
    var some1, len, rest := ParseUint64(data, index);
    if some1 {
      var some2, contents, remainder := ParseArrayContents(data, rest, eltType, len.u);
      if some2 {
        success := true;
        v := VArray(contents);
        rest_index := remainder;
      } else {
        print ""Parse array fails\n"";
        success := false;
        rest_index := data.Length as uint64;
      }
    } else {
      print ""Parse array fails\n"";
      success := false;
      rest_index := data.Length as uint64;
    }
  }

  function method {:opaque} {:fuel 0, 0} parse_Tuple_contents(data: seq<byte>, eltTypes: seq<G>): (Option<seq<V>>, seq<byte>)
    requires |data| < 18446744073709551616
    requires |eltTypes| < 18446744073709551616
    requires forall elt: G {:trigger ValidGrammar(elt)} {:trigger elt in eltTypes} :: elt in eltTypes ==> ValidGrammar(elt)
    ensures var (opt_val: Option<seq<V>>, rest: seq<byte>) := parse_Tuple_contents(data, eltTypes); |rest| <= |data| && (opt_val.Some? ==> |opt_val.v| == |eltTypes| && forall i: int {:trigger eltTypes[i]} {:trigger opt_val.v[i]} :: 0 <= i < |opt_val.v| ==> ValInGrammar(opt_val.v[i], eltTypes[i]))
    decreases eltTypes, 0
  {
    if eltTypes == [] then
      (Some([]), data)
    else
      var (val: Option<V>, rest1: seq<byte>) := parse_Val(data, eltTypes[0]); assert |rest1| <= |data|; var (contents: Option<seq<V>>, rest2: seq<byte>) := parse_Tuple_contents(rest1, eltTypes[1..]); if !val.None? && !contents.None? then (Some([val.v] + contents.v), rest2) else (None, [])
  }

  lemma /*{:_induction data, eltTypes}*/ lemma_TupleContents_helper(data: seq<byte>, eltTypes: seq<G>, v: seq<V>, trace: seq<ContentsTraceStep>)
    requires |data| < 18446744073709551616
    requires |eltTypes| < 18446744073709551616
    requires forall elt: G {:trigger ValidGrammar(elt)} {:trigger elt in eltTypes} :: elt in eltTypes ==> ValidGrammar(elt)
    requires |trace| == |eltTypes| + 1
    requires |v| == |eltTypes| as int
    requires forall j: int {:trigger trace[j]} :: 0 <= j < |trace| ==> |trace[j].data| < 18446744073709551616
    requires trace[0].data == data
    requires (forall j: int, _t#0: int {:trigger eltTypes[_t#0], trace[j]} {:trigger trace[_t#0], trace[j]} | _t#0 == j - 1 :: 0 < j && j < |eltTypes| as int + 1 ==> trace[j].val == parse_Val(trace[_t#0].data, eltTypes[_t#0]).0) && forall j: int, _t#0: int {:trigger eltTypes[_t#0], trace[j]} {:trigger trace[_t#0], trace[j]} | _t#0 == j - 1 :: 0 < j && j < |eltTypes| as int + 1 ==> trace[j].data == parse_Val(trace[_t#0].data, eltTypes[_t#0]).1
    requires forall j: int {:trigger trace[j]} :: 0 < j < |trace| ==> trace[j].val.Some?
    requires forall j: int {:trigger trace[j]} :: 0 < j < |trace| ==> v[j - 1] == trace[j].val.v
    ensures var (v': Option<seq<V>>, rest': seq<byte>) := parse_Tuple_contents(data, eltTypes); ghost var v_opt: Option<seq<V>> := Some(v); v_opt == v' && trace[|trace| - 1].data == rest'
    decreases |eltTypes|
  {
  }

  lemma /*{:_induction data, eltTypes}*/ lemma_TupleContents_helper_bailout(data: seq<byte>, eltTypes: seq<G>, trace: seq<ContentsTraceStep>)
    requires |data| < 18446744073709551616
    requires |eltTypes| < 18446744073709551616
    requires forall elt: G {:trigger ValidGrammar(elt)} {:trigger elt in eltTypes} :: elt in eltTypes ==> ValidGrammar(elt)
    requires 1 < |trace| <= |eltTypes| as int + 1
    requires forall j: int {:trigger trace[j]} :: 0 <= j < |trace| ==> |trace[j].data| < 18446744073709551616
    requires trace[0].data == data
    requires (forall j: int, _t#0: int {:trigger eltTypes[_t#0], trace[j]} {:trigger trace[_t#0], trace[j]} | _t#0 == j - 1 :: 0 < j && j < |trace| ==> trace[j].val == parse_Val(trace[_t#0].data, eltTypes[_t#0]).0) && forall j: int, _t#0: int {:trigger eltTypes[_t#0], trace[j]} {:trigger trace[_t#0], trace[j]} | _t#0 == j - 1 :: 0 < j && j < |trace| ==> trace[j].data == parse_Val(trace[_t#0].data, eltTypes[_t#0]).1
    requires forall j: int {:trigger trace[j]} :: 0 < j < |trace| - 1 ==> trace[j].val.Some?
    requires trace[|trace| - 1].val.None?
    ensures var (v': Option<seq<V>>, rest': seq<byte>) := parse_Tuple_contents(data, eltTypes); v'.None? && rest' == []
    decreases |eltTypes|
  {
  }

  method {:timeLimitMultiplier 2} /*{:_timeLimit 20}*/ ParseTupleContents(data: array<byte>, index: uint64, eltTypes: seq<G>)
      returns (success: bool, v: seq<V>, rest_index: uint64)
    requires index as int <= data.Length
    requires data.Length < 18446744073709551616
    requires |eltTypes| < 18446744073709551616
    requires forall elt: G {:trigger ValidGrammar(elt)} {:trigger elt in eltTypes} :: elt in eltTypes ==> ValidGrammar(elt)
    ensures rest_index as int <= data.Length
    ensures var (v': Option<seq<V>>, rest': seq<byte>) := parse_Tuple_contents(data[index..], eltTypes); var v_opt: Option<seq<V>> := if success then Some(v) else None(); v_opt == v' && data[rest_index..] == rest'
    ensures success ==> ValidVal(VTuple(v))
    decreases eltTypes, 0
  {
    reveal parse_Tuple_contents();
    var vArr := new V[|eltTypes|];
    ghost var g_v := [];
    success := true;
    var i: int := 0;
    var next_val_index: uint64 := index;
    ghost var trace := [ContentsTraceStep(data[index..], None())];
    while i < |eltTypes|
      invariant 0 <= i <= |eltTypes|
      invariant index <= next_val_index <= data.Length as uint64
      invariant |trace| == i + 1
      invariant |g_v| == i
      invariant vArr[..i] == g_v
      invariant trace[0].data == data[index..]
      invariant forall j: int {:trigger trace[j]} :: 0 <= j < i + 1 ==> |trace[j].data| < 18446744073709551616
      invariant trace[i].data == data[next_val_index..]
      invariant forall j: int {:trigger trace[j]} :: 0 < j <= i ==> trace[j].val.Some?
      invariant forall j: int {:trigger trace[j]} :: 0 < j <= i ==> g_v[j - 1] == trace[j].val.v
      invariant (forall j: int, _t#0: int {:trigger eltTypes[_t#0], trace[j]} {:trigger trace[_t#0], trace[j]} | _t#0 == j - 1 :: 0 < j && j < i + 1 ==> trace[j].val == parse_Val(trace[_t#0].data, eltTypes[_t#0]).0) && forall j: int, _t#0: int {:trigger eltTypes[_t#0], trace[j]} {:trigger trace[_t#0], trace[j]} | _t#0 == j - 1 :: 0 < j && j < i + 1 ==> trace[j].data == parse_Val(trace[_t#0].data, eltTypes[_t#0]).1
      invariant ValidVal(VTuple(vArr[..i]))
      decreases |eltTypes| - i
    {
      var some1, val, rest1 := ParseVal(data, next_val_index, eltTypes[i]);
      ghost var step := ContentsTraceStep(data[rest1..], if some1 then Some(val) else None());
      ghost var old_trace := trace;
      trace := trace + [step];
      if !some1 {
        success := false;
        rest_index := data.Length as uint64;
        lemma_TupleContents_helper_bailout(data[index..], eltTypes, trace);
        return;
      }
      g_v := g_v + [val];
      vArr[i] := val;
      next_val_index := rest1;
      i := i + 1;
    }
    success := true;
    rest_index := next_val_index;
    v := vArr[..];
    lemma_TupleContents_helper(data[index..], eltTypes, v, trace);
  }

  function method parse_Tuple(data: seq<byte>, eltTypes: seq<G>): (Option<V>, seq<byte>)
    requires |data| < 18446744073709551616
    requires |eltTypes| < 18446744073709551616
    requires forall elt: G {:trigger ValidGrammar(elt)} {:trigger elt in eltTypes} :: elt in eltTypes ==> ValidGrammar(elt)
    ensures var (opt_val: Option<V>, rest: seq<byte>) := parse_Tuple(data, eltTypes); |rest| <= |data| && (opt_val.Some? ==> ValInGrammar(opt_val.v, GTuple(eltTypes)))
    decreases eltTypes, 1
  {
    var (contents: Option<seq<V>>, rest: seq<byte>) := parse_Tuple_contents(data, eltTypes);
    if !contents.None? then
      (Some(VTuple(contents.v)), rest)
    else
      (None, [])
  }

  method ParseTuple(data: array<byte>, index: uint64, eltTypes: seq<G>)
      returns (success: bool, v: V, rest_index: uint64)
    requires index as int <= data.Length
    requires data.Length < 18446744073709551616
    requires |eltTypes| < 18446744073709551616
    requires forall elt: G {:trigger ValidGrammar(elt)} {:trigger elt in eltTypes} :: elt in eltTypes ==> ValidGrammar(elt)
    ensures rest_index as int <= data.Length
    ensures var (v': Option<V>, rest': seq<byte>) := parse_Tuple(data[index..], eltTypes); var v_opt: Option<V> := if success then Some(v) else None(); v_opt == v' && data[rest_index..] == rest'
    ensures success ==> ValidVal(v)
    decreases eltTypes, 1
  {
    var some, contents, rest := ParseTupleContents(data, index, eltTypes);
    if some {
      success := true;
      v := VTuple(contents);
      rest_index := rest;
    } else {
      print ""Parse tuple fails\n"";
      success := false;
      rest_index := data.Length as uint64;
    }
  }

  function method parse_ByteArray(data: seq<byte>): (Option<V>, seq<byte>)
    requires |data| < 18446744073709551616
    decreases data
  {
    var (len: Option<V>, rest: seq<byte>) := parse_Uint64(data);
    if !len.None? && len.v.u <= |rest| as uint64 then
      (Some(VByteArray(rest[0 .. len.v.u])), rest[len.v.u..])
    else
      (None, [])
  }

  method ParseByteArray(data: array<byte>, index: uint64)
      returns (success: bool, v: V, rest_index: uint64)
    requires index as int <= data.Length
    requires data.Length < 18446744073709551616
    ensures rest_index as int <= data.Length
    ensures var (v': Option<V>, rest': seq<byte>) := parse_ByteArray(data[index..]); var v_opt: Option<V> := if success then Some(v) else None(); v_opt == v' && data[rest_index..] == rest'
    decreases data, index
  {
    var some, len, rest := ParseUint64(data, index);
    if some && len.u <= data.Length as uint64 - rest {
      var rest_seq := data[rest..];
      assert len.u <= |rest_seq| as uint64;
      calc {
        rest_seq[0 .. len.u];
        data[rest .. rest + len.u];
      }
      success := true;
      v := VByteArray(data[rest .. rest + len.u]);
      rest_index := rest + len.u;
    } else {
      print ""Parse byte array fails\n"";
      success := false;
      rest_index := data.Length as uint64;
    }
  }

  function method parse_Case(data: seq<byte>, cases: seq<G>): (Option<V>, seq<byte>)
    requires |data| < 18446744073709551616
    requires |cases| < 18446744073709551616
    requires forall elt: G {:trigger ValidGrammar(elt)} {:trigger elt in cases} :: elt in cases ==> ValidGrammar(elt)
    ensures var (opt_val: Option<V>, rest: seq<byte>) := parse_Case(data, cases); |rest| <= |data| && (opt_val.Some? ==> ValInGrammar(opt_val.v, GTaggedUnion(cases)))
    decreases cases
  {
    var (caseID: Option<V>, rest1: seq<byte>) := parse_Uint64(data);
    if !caseID.None? && caseID.v.u < |cases| as uint64 then
      var (val: Option<V>, rest2: seq<byte>) := parse_Val(rest1, cases[caseID.v.u]);
      if !val.None? then
        (Some(VCase(caseID.v.u, val.v)), rest2)
      else
        (None, [])
    else
      (None, [])
  }

  method ParseCase(data: array<byte>, index: uint64, cases: seq<G>)
      returns (success: bool, v: V, rest_index: uint64)
    requires index as int <= data.Length
    requires data.Length < 18446744073709551616
    requires |cases| < 18446744073709551616
    requires forall elt: G {:trigger ValidGrammar(elt)} {:trigger elt in cases} :: elt in cases ==> ValidGrammar(elt)
    ensures rest_index as int <= data.Length
    ensures var (v': Option<V>, rest': seq<byte>) := parse_Case(data[index..], cases); var v_opt: Option<V> := if success then Some(v) else None(); v_opt == v' && data[rest_index..] == rest'
    ensures success ==> ValidVal(v)
    decreases cases
  {
    var some1, caseID, rest1 := ParseUint64(data, index);
    if some1 && caseID.u < |cases| as uint64 {
      var some2, val, rest2 := ParseVal(data, rest1, cases[caseID.u]);
      if some2 {
        success := true;
        v := VCase(caseID.u, val);
        rest_index := rest2;
      } else {
        print ""Parse case fails\n"";
        success := false;
        rest_index := data.Length as uint64;
      }
    } else {
      print ""Parse case fails\n"";
      success := false;
      rest_index := data.Length as uint64;
    }
  }

  function method {:opaque} {:fuel 0, 0} parse_Val(data: seq<byte>, grammar: G): (Option<V>, seq<byte>)
    requires |data| < 18446744073709551616
    requires ValidGrammar(grammar)
    ensures var (val: Option<V>, rest: seq<byte>) := parse_Val(data, grammar); |rest| <= |data| && (!val.None? ==> ValInGrammar(val.v, grammar))
    decreases grammar, 0
  {
    match grammar
    case GUint64() =>
      parse_Uint64(data)
    case GArray(elt) =>
      parse_Array(data, elt)
    case GTuple(t) =>
      parse_Tuple(data, t)
    case GByteArray() =>
      parse_ByteArray(data)
    case GTaggedUnion(cases) =>
      parse_Case(data, cases)
  }

  method ParseVal(data: array<byte>, index: uint64, grammar: G)
      returns (success: bool, v: V, rest_index: uint64)
    requires index as int <= data.Length
    requires data.Length < 18446744073709551616
    requires ValidGrammar(grammar)
    ensures rest_index as int <= data.Length
    ensures var (v': Option<V>, rest': seq<byte>) := parse_Val(data[index..], grammar); var v_opt: Option<V> := if success then Some(v) else None(); v_opt == v' && data[rest_index..] == rest'
    ensures success ==> ValidVal(v)
    decreases grammar, 0
  {
    reveal parse_Val();
    match grammar {
      case {:split false} GUint64() =>
        success, v, rest_index := ParseUint64(data, index);
      case {:split false} GArray(elt) =>
        success, v, rest_index := ParseArray(data, index, elt);
      case {:split false} GTuple(t) =>
        success, v, rest_index := ParseTuple(data, index, t);
      case {:split false} GByteArray() =>
        success, v, rest_index := ParseByteArray(data, index);
      case {:split false} GTaggedUnion(cases) =>
        success, v, rest_index := ParseCase(data, index, cases);
    }
  }

  predicate Demarshallable(data: seq<byte>, grammar: G)
    decreases data, grammar
  {
    |data| < 18446744073709551616 &&
    ValidGrammar(grammar) &&
    !parse_Val(data, grammar).0.None? &&
    ValidVal(parse_Val(data, grammar).0.v) &&
    parse_Val(data, grammar).1 == []
  }

  function DemarshallFunc(data: seq<byte>, grammar: G): V
    requires Demarshallable(data, grammar)
    ensures var (val: Option<V>, rest: seq<byte>) := parse_Val(data, grammar); !val.None? && ValInGrammar(val.v, grammar)
    decreases grammar, 0
  {
    parse_Val(data, grammar).0.v
  }

  method Demarshall(data: array<byte>, grammar: G)
      returns (success: bool, v: V)
    requires data.Length < 18446744073709551616
    requires ValidGrammar(grammar)
    ensures success == Demarshallable(data[..], grammar)
    ensures success ==> v == DemarshallFunc(data[..], grammar)
    decreases data, grammar
  {
    var rest: uint64;
    success, v, rest := ParseVal(data, 0, grammar);
    if success && rest == data.Length as uint64 {
      assert v == parse_Val(data[..], grammar).0.v;
      assert Demarshallable(data[..], grammar);
      assert v == DemarshallFunc(data[..], grammar);
    } else {
      success := false;
      assert !Demarshallable(data[..], grammar);
    }
  }

  lemma /*{:_induction v, grammar}*/ lemma_parse_Val_view_ByteArray(data: seq<byte>, v: V, grammar: G, index: int)
    requires |data| < 18446744073709551616
    requires ValInGrammar(v, grammar)
    requires ValidGrammar(grammar)
    requires grammar.GByteArray?
    requires 0 <= index <= |data|
    requires 0 <= index + SizeOfV(v) <= |data|
    ensures forall bound: int {:trigger data[index .. bound]} {:trigger Trigger(bound)} :: Trigger(bound) ==> index + SizeOfV(v) <= bound <= |data| ==> (parse_ByteArray(data[index .. bound]).0 == Some(v) <==> parse_ByteArray(data[index .. index + SizeOfV(v)]).0 == Some(v))
    ensures forall bound: int {:trigger data[index .. bound]} :: index + SizeOfV(v) <= bound <= |data| ==> parse_ByteArray(data[index .. bound]).0 == Some(v) ==> parse_ByteArray(data[index .. bound]).1 == data[index + SizeOfV(v) .. bound]
    decreases data, v, grammar, index
  {
  }

  lemma /*{:_induction s, v}*/ lemma_SeqSum_prefix(s: seq<V>, v: V)
    ensures SeqSum(s + [v]) == SeqSum(s) + SizeOfV(v)
    decreases s, v
  {
  }

  lemma /*{:_induction s}*/ lemma_SeqSum_bound(s: seq<V>, bound: int)
    requires SeqSum(s) < bound
    ensures forall v: V {:trigger SizeOfV(v)} {:trigger v in s} :: v in s ==> SizeOfV(v) < bound
    decreases s, bound
  {
  }

  lemma /*{:_induction s, prefix}*/ lemma_SeqSum_bound_prefix(s: seq<V>, prefix: seq<V>, index: int)
    requires 0 <= index <= |s|
    requires prefix == s[..index]
    ensures SeqSum(prefix) <= SeqSum(s)
    decreases s, prefix, index
  {
  }

  lemma /*{:_induction data, eltType, len}*/ lemma_parse_Array_contents_len(data: seq<byte>, eltType: G, len: uint64)
    requires |data| < 18446744073709551616
    requires ValidGrammar(eltType)
    requires len >= 0
    requires !parse_Array_contents(data, eltType, len).0.None?
    ensures len as int == |parse_Array_contents(data, eltType, len).0.v|
    decreases len
  {
  }

  lemma /*{:_induction vs, grammar, len}*/ lemma_parse_Val_view_Array_contents(data: seq<byte>, vs: seq<V>, grammar: G, index: int, bound: int, len: uint64)
    requires |data| < 18446744073709551616
    requires forall v: V {:trigger ValInGrammar(v, grammar)} {:trigger v in vs} :: v in vs ==> ValInGrammar(v, grammar)
    requires ValidGrammar(grammar)
    requires len as int == |vs|
    requires 0 <= index <= |data|
    requires 0 <= index + SeqSum(vs) <= |data|
    requires index + SeqSum(vs) <= bound <= |data|
    ensures parse_Array_contents(data[index .. bound], grammar, len).0 == Some(vs) <==> parse_Array_contents(data[index .. index + SeqSum(vs)], grammar, len).0 == Some(vs)
    ensures parse_Array_contents(data[index .. bound], grammar, len).0 == Some(vs) ==> parse_Array_contents(data[index .. bound], grammar, len).1 == data[index + SeqSum(vs) .. bound]
    decreases grammar, 1, len
  {
  }

  lemma /*{:_induction v, grammar}*/ lemma_parse_Val_view_Array(data: seq<byte>, v: V, grammar: G, index: int, bound: int)
    requires |data| < 18446744073709551616
    requires ValInGrammar(v, grammar)
    requires ValidGrammar(grammar)
    requires grammar.GArray?
    requires 0 <= index <= |data|
    requires 0 <= index + SizeOfV(v) <= |data|
    requires index + SizeOfV(v) <= bound <= |data|
    ensures parse_Array(data[index .. bound], grammar.elt).0 == Some(v) <==> parse_Array(data[index .. index + SizeOfV(v)], grammar.elt).0 == Some(v)
    ensures parse_Array(data[index .. bound], grammar.elt).0 == Some(v) ==> parse_Array(data[index .. bound], grammar.elt).1 == data[index + SizeOfV(v) .. bound]
    decreases grammar, -1
  {
  }

  lemma /*{:_induction vs, grammar}*/ lemma_parse_Val_view_Tuple_contents(data: seq<byte>, vs: seq<V>, grammar: seq<G>, index: int, bound: int)
    requires |data| < 18446744073709551616
    requires |vs| == |grammar|
    requires forall i: int {:trigger grammar[i]} {:trigger vs[i]} :: 0 <= i < |vs| ==> ValInGrammar(vs[i], grammar[i])
    requires |grammar| < 18446744073709551616
    requires forall g: G {:trigger ValidGrammar(g)} {:trigger g in grammar} :: g in grammar ==> ValidGrammar(g)
    requires 0 <= index <= |data|
    requires 0 <= index + SeqSum(vs) <= |data|
    requires index + SeqSum(vs) <= bound <= |data|
    ensures parse_Tuple_contents(data[index .. bound], grammar).0 == Some(vs) <==> parse_Tuple_contents(data[index .. index + SeqSum(vs)], grammar).0 == Some(vs)
    ensures parse_Tuple_contents(data[index .. bound], grammar).0 == Some(vs) ==> parse_Tuple_contents(data[index .. bound], grammar).1 == data[index + SeqSum(vs) .. bound]
    decreases grammar, -1, vs
  {
  }

  lemma /*{:_induction v, grammar}*/ lemma_parse_Val_view_Tuple(data: seq<byte>, v: V, grammar: seq<G>, index: int, bound: int)
    requires |data| < 18446744073709551616
    requires v.VTuple?
    requires |v.t| == |grammar|
    requires forall i: int {:trigger grammar[i]} {:trigger v.t[i]} :: 0 <= i < |v.t| ==> ValInGrammar(v.t[i], grammar[i])
    requires |grammar| < 18446744073709551616
    requires forall g: G {:trigger ValidGrammar(g)} {:trigger g in grammar} :: g in grammar ==> ValidGrammar(g)
    requires 0 <= index <= |data|
    requires 0 <= index + SizeOfV(v) <= |data|
    requires index + SizeOfV(v) <= bound <= |data|
    ensures parse_Tuple(data[index .. bound], grammar).0 == Some(v) <==> parse_Tuple(data[index .. index + SizeOfV(v)], grammar).0 == Some(v)
    ensures parse_Tuple(data[index .. bound], grammar).0 == Some(v) ==> parse_Tuple(data[index .. bound], grammar).1 == data[index + SizeOfV(v) .. bound]
    decreases grammar, -1, v
  {
  }

  lemma /*{:_induction v, grammar}*/ lemma_parse_Val_view_Union(data: seq<byte>, v: V, grammar: G, index: int, bound: int)
    requires |data| < 18446744073709551616
    requires ValInGrammar(v, grammar)
    requires ValidGrammar(grammar)
    requires grammar.GTaggedUnion?
    requires 0 <= index <= |data|
    requires 0 <= index + SizeOfV(v) <= |data|
    requires index + SizeOfV(v) <= bound <= |data|
    ensures parse_Case(data[index .. bound], grammar.cases).0 == Some(v) <==> parse_Case(data[index .. index + SizeOfV(v)], grammar.cases).0 == Some(v)
    ensures parse_Case(data[index .. bound], grammar.cases).0 == Some(v) ==> parse_Case(data[index .. bound], grammar.cases).1 == data[index + SizeOfV(v) .. bound]
    decreases grammar, -1
  {
  }

  lemma /*{:_induction v, grammar}*/ lemma_parse_Val_view(data: seq<byte>, v: V, grammar: G, index: int)
    requires |data| < 18446744073709551616
    requires ValInGrammar(v, grammar)
    requires ValidGrammar(grammar)
    requires 0 <= index <= |data|
    requires 0 <= index + SizeOfV(v) <= |data|
    ensures forall bound: int {:trigger data[index .. bound]} :: index + SizeOfV(v) <= bound <= |data| ==> (parse_Val(data[index .. bound], grammar).0 == Some(v) <==> parse_Val(data[index .. index + SizeOfV(v)], grammar).0 == Some(v))
    ensures forall bound: int {:trigger data[index .. bound]} :: index + SizeOfV(v) <= bound <= |data| ==> parse_Val(data[index .. bound], grammar).0 == Some(v) ==> parse_Val(data[index .. bound], grammar).1 == data[index + SizeOfV(v) .. bound]
    decreases grammar, 0
  {
  }

  lemma /*{:_induction v, grammar}*/ lemma_parse_Val_view_specific(data: seq<byte>, v: V, grammar: G, index: int, bound: int)
    requires |data| < 18446744073709551616
    requires ValInGrammar(v, grammar)
    requires ValidGrammar(grammar)
    requires 0 <= index <= |data|
    requires 0 <= index + SizeOfV(v) <= |data|
    requires index + SizeOfV(v) <= bound <= |data|
    requires parse_Val(data[index .. index + SizeOfV(v)], grammar).0 == Some(v)
    ensures parse_Val(data[index .. bound], grammar).0 == Some(v)
    ensures parse_Val(data[index .. bound], grammar).1 == data[index + SizeOfV(v) .. bound]
    decreases grammar, 0
  {
  }

  lemma /*{:_induction v, grammar}*/ lemma_parse_Val_view_specific_size(data: seq<byte>, v: V, grammar: G, index: int, bound: int)
    requires |data| < 18446744073709551616
    requires ValInGrammar(v, grammar)
    requires ValidGrammar(grammar)
    requires 0 <= index <= |data|
    requires 0 <= index + SizeOfV(v) <= |data|
    requires index + SizeOfV(v) <= bound <= |data|
    requires parse_Val(data[index .. bound], grammar).0 == Some(v)
    ensures parse_Val(data[index .. index + SizeOfV(v)], grammar).0 == Some(v)
    ensures parse_Val(data[index .. bound], grammar).1 == data[index + SizeOfV(v) .. bound]
    decreases grammar, 0
  {
  }

  method ComputeSeqSum(s: seq<V>) returns (size: uint64)
    requires |s| < 18446744073709551616
    requires 0 <= SeqSum(s) < 18446744073709551616
    requires forall v: V {:trigger ValidVal(v)} {:trigger v in s} :: v in s ==> ValidVal(v)
    ensures size as int == SeqSum(s)
    decreases s
  {
    reveal SeqSum();
    if |s| as uint64 == 0 {
      size := 0;
    } else {
      var v_size := ComputeSizeOf(s[0]);
      var rest_size := ComputeSeqSum(s[1..]);
      size := v_size + rest_size;
    }
  }

  method ComputeSizeOf(val: V) returns (size: uint64)
    requires 0 <= SizeOfV(val) < 18446744073709551616
    requires ValidVal(val)
    ensures size as int == SizeOfV(val)
    decreases val
  {
    match val
    case {:split false} VUint64(_) =>
      size := 8;
    case {:split false} VArray(a) =>
      var v := ComputeSeqSum(a);
      if v == 0 {
        size := 8;
      } else {
        size := 8 + v;
      }
    case {:split false} VTuple(t) =>
      size := ComputeSeqSum(t);
    case {:split false} VByteArray(b) =>
      size := 8 + |b| as uint64;
    case {:split false} VCase(c, v) =>
      var vs := ComputeSizeOf(v);
      size := 8 + vs;
  }

  method MarshallUint64(n: uint64, data: array<byte>, index: uint64)
    requires index as int + Uint64Size() as int <= data.Length
    requires 0 <= index as int + Uint64Size() as int < 18446744073709551616
    requires data.Length < 18446744073709551616
    modifies data
    ensures SeqByteToUint64(data[index .. index + Uint64Size()]) == n
    ensures !parse_Uint64(data[index .. index + Uint64Size()]).0.None?
    ensures !parse_Uint64(data[index..]).0.None?
    ensures var tuple: (Option<V>, seq<byte>) := parse_Uint64(data[index .. index + Uint64Size()]); tuple.0.v.u == n && tuple.1 == []
    ensures var tuple: (Option<V>, seq<byte>) := parse_Uint64(data[index..]); tuple.0.v.u == n && tuple.1 == data[index + Uint64Size()..]
    ensures data[0 .. index] == old(data[0 .. index])
    ensures data[index + Uint64Size()..] == old(data[index + Uint64Size()..])
    ensures forall i: uint64 {:trigger old(data[i])} {:trigger data[i]} :: 0 <= i < index ==> data[i] == old(data[i])
    ensures forall i: int {:trigger old(data[i])} {:trigger data[i]} :: index as int + Uint64Size() as int <= i < data.Length ==> data[i] == old(data[i])
    decreases n, data, index
  {
    MarshallUint64_guts(n, data, index);
    var tuple := parse_Uint64(data[index..]);
  }

  lemma /*{:_induction contents, eltType, marshalled_bytes, trace}*/ lemma_marshall_array_contents(contents: seq<V>, eltType: G, marshalled_bytes: seq<byte>, trace: seq<seq<byte>>)
    requires forall v: V {:trigger ValInGrammar(v, eltType)} {:trigger v in contents} :: v in contents ==> ValInGrammar(v, eltType)
    requires forall v: V {:trigger ValidVal(v)} {:trigger v in contents} :: v in contents ==> ValidVal(v)
    requires ValidGrammar(eltType)
    requires |marshalled_bytes| < 18446744073709551616
    requires |contents| < 18446744073709551616
    requires |contents| == |trace|
    requires |marshalled_bytes| == SeqSum(contents)
    requires marshalled_bytes == SeqCatRev(trace)
    requires forall j: int {:trigger trace[j]} {:trigger contents[j]} :: (0 <= j < |trace| ==> SizeOfV(contents[j]) == |trace[j]|) && (0 <= j < |trace| ==> |trace[j]| < 18446744073709551616)
    requires forall j: int {:trigger contents[j]} {:trigger trace[j]} :: 0 <= j < |trace| ==> var (val: Option<V>, rest: seq<byte>) := parse_Val(trace[j], eltType); val.Some? && val.v == contents[j]
    ensures parse_Array_contents(marshalled_bytes, eltType, |contents| as uint64).0.Some?
    ensures parse_Array_contents(marshalled_bytes, eltType, |contents| as uint64).0.v == contents
    decreases contents, eltType, marshalled_bytes, trace
  {
  }

  method {:timeLimitMultiplier 4} /*{:_timeLimit 40}*/ MarshallArrayContents(contents: seq<V>, eltType: G, data: array<byte>, index: uint64)
      returns (size: uint64)
    requires forall v: V {:trigger ValInGrammar(v, eltType)} {:trigger v in contents} :: v in contents ==> ValInGrammar(v, eltType)
    requires forall v: V {:trigger ValidVal(v)} {:trigger v in contents} :: v in contents ==> ValidVal(v)
    requires ValidGrammar(eltType)
    requires index as int + SeqSum(contents) <= data.Length
    requires 0 <= index as int + SeqSum(contents) < 18446744073709551616
    requires data.Length < 18446744073709551616
    requires |contents| < 18446744073709551616
    modifies data
    ensures parse_Array_contents(data[index .. index as int + SeqSum(contents)], eltType, |contents| as uint64).0.Some?
    ensures parse_Array_contents(data[index .. index as int + SeqSum(contents)], eltType, |contents| as uint64).0.v == contents
    ensures forall i: uint64 {:trigger old(data[i])} {:trigger data[i]} :: 0 <= i < index ==> data[i] == old(data[i])
    ensures forall i: int {:trigger old(data[i])} {:trigger data[i]} :: index as int + SeqSum(contents) <= i < data.Length ==> data[i] == old(data[i])
    ensures size as int == SeqSum(contents)
    decreases eltType, 1, |contents|
  {
    var i: int := 0;
    var cur_index := index;
    reveal SeqSum();
    reveal parse_Array_contents();
    ghost var trace := [];
    ghost var marshalled_bytes := [];
    while i < |contents|
      invariant 0 <= i <= |contents|
      invariant 0 <= index as int <= index as int + SeqSum(contents[..i]) <= data.Length
      invariant cur_index as int == index as int + SeqSum(contents[..i])
      invariant forall j: uint64 {:trigger old(data[j])} {:trigger data[j]} :: 0 <= j < index ==> data[j] == old(data[j])
      invariant forall j: int {:trigger old(data[j])} {:trigger data[j]} :: index as int + SeqSum(contents) <= j < data.Length ==> data[j] == old(data[j])
      invariant marshalled_bytes == data[index .. cur_index]
      invariant marshalled_bytes == SeqCatRev(trace)
      invariant |trace| == i
      invariant forall j: int {:trigger trace[j]} {:trigger contents[j]} :: (0 <= j < |trace| ==> SizeOfV(contents[j]) == |trace[j]|) && (0 <= j < |trace| ==> |trace[j]| < 18446744073709551616)
      invariant forall j: int {:trigger contents[j]} {:trigger trace[j]} :: 0 <= j < |trace| ==> var (val: Option<V>, rest: seq<byte>) := parse_Val(trace[j], eltType); val.Some? && val.v == contents[j]
      decreases |contents| - i
    {
      lemma_SeqSum_bound(contents, 18446744073709551616);
      calc <= {
        cur_index as int + SizeOfV(contents[i]);
        index as int + SeqSum(contents[..i]) + SizeOfV(contents[i]);
        {
          lemma_SeqSum_prefix(contents[..i], contents[i]);
          assert contents[..i] + [contents[i]] == contents[..i + 1];
        }
        index as int + SeqSum(contents[..i + 1]);
        {
          lemma_SeqSum_bound_prefix(contents, contents[..i + 1], i + 1);
        }
        index as int + SeqSum(contents);
      }
      var item_size := MarshallVal(contents[i], eltType, data, cur_index);
      ghost var fresh_bytes := data[cur_index .. cur_index + item_size];
      marshalled_bytes := marshalled_bytes + fresh_bytes;
      forall
        ensures var (val: Option<V>, rest: seq<byte>) := parse_Val(fresh_bytes, eltType); val.Some? && val.v == contents[i]
      {
        assert SizeOfV(contents[i]) <= |fresh_bytes|;
        lemma_parse_Val_view(fresh_bytes, contents[i], eltType, 0);
      }
      ghost var old_trace := trace;
      trace := trace + [fresh_bytes];
      ghost var old_cur_index := cur_index;
      cur_index := cur_index + item_size;
      i := i + 1;
      calc <= {
        index as int + SeqSum(contents[..i]);
        calc {
          SeqSum(contents[..i]);
        <=
          {
            lemma_SeqSum_bound_prefix(contents, contents[..i], i);
          }
          SeqSum(contents);
        }
        index as int + SeqSum(contents);
        data.Length;
      }
      assert {:split_here} true;
      assert marshalled_bytes == data[index .. cur_index];
      calc {
        cur_index as int;
        old_cur_index as int + SizeOfV(contents[i - 1]);
        index as int + SeqSum(contents[..i - 1]) + SizeOfV(contents[i - 1]);
        {
          lemma_SeqSum_prefix(contents[..i - 1], contents[i - 1]);
          assert contents[..i - 1] + [contents[i - 1]] == contents[..i];
        }
        index as int + SeqSum(contents[..i]);
      }
      assert cur_index as int == index as int + SeqSum(contents[..i]);
      assert marshalled_bytes == data[index .. cur_index];
    }
    assert contents[..i] == contents;
    assert cur_index as int == index as int + SeqSum(contents);
    assert marshalled_bytes == data[index .. index as int + SeqSum(contents)];
    lemma_marshall_array_contents(contents, eltType, marshalled_bytes, trace);
    size := cur_index - index;
  }

  method MarshallArray(val: V, grammar: G, data: array<byte>, index: uint64)
      returns (size: uint64)
    requires val.VArray?
    requires ValInGrammar(val, grammar)
    requires ValidGrammar(grammar)
    requires ValidVal(val)
    requires index as int + SizeOfV(val) <= data.Length
    requires 0 <= index as int + SizeOfV(val) < 18446744073709551616
    requires data.Length < 18446744073709551616
    modifies data
    ensures parse_Val(data[index .. index as int + SizeOfV(val)], grammar).0.Some? && parse_Val(data[index .. index as int + SizeOfV(val)], grammar).0.v == val
    ensures forall i: uint64 {:trigger old(data[i])} {:trigger data[i]} :: 0 <= i < index ==> data[i] == old(data[i])
    ensures forall i: int {:trigger old(data[i])} {:trigger data[i]} :: index as int + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i])
    ensures size as int == SizeOfV(val)
    decreases grammar, -1
  {
    reveal parse_Val();
    MarshallUint64(|val.a| as uint64, data, index);
    ghost var tuple := parse_Uint64(data[index .. index as int + SizeOfV(val)]);
    ghost var len := tuple.0;
    ghost var rest := tuple.1;
    assert !len.None?;
    var contents_size := MarshallArrayContents(val.a, grammar.elt, data, index + Uint64Size());
    tuple := parse_Uint64(data[index .. index as int + SizeOfV(val)]);
    assert {:split_here} true;
    len := tuple.0;
    rest := tuple.1;
    assert !len.None?;
    ghost var contents_tuple := parse_Array_contents(rest, grammar.elt, len.v.u);
    ghost var contents := contents_tuple.0;
    ghost var remainder := contents_tuple.1;
    assert !contents.None?;
    size := 8 + contents_size;
  }

  lemma /*{:_induction contents, eltTypes, marshalled_bytes, trace}*/ lemma_marshall_tuple_contents(contents: seq<V>, eltTypes: seq<G>, marshalled_bytes: seq<byte>, trace: seq<seq<byte>>)
    requires |contents| == |eltTypes|
    requires forall i: int {:trigger eltTypes[i]} {:trigger contents[i]} :: 0 <= i < |contents| ==> ValInGrammar(contents[i], eltTypes[i])
    requires forall g: G {:trigger ValidGrammar(g)} {:trigger g in eltTypes} :: g in eltTypes ==> ValidGrammar(g)
    requires |eltTypes| < 18446744073709551616
    requires forall i: int {:trigger contents[i]} :: 0 <= i < |contents| ==> ValidVal(contents[i])
    requires |marshalled_bytes| < 18446744073709551616
    requires |contents| < 18446744073709551616
    requires |contents| == |trace|
    requires |marshalled_bytes| == SeqSum(contents)
    requires marshalled_bytes == SeqCatRev(trace)
    requires forall j: int {:trigger trace[j]} {:trigger contents[j]} :: (0 <= j < |trace| ==> SizeOfV(contents[j]) == |trace[j]|) && (0 <= j < |trace| ==> |trace[j]| < 18446744073709551616)
    requires forall j: int {:trigger contents[j]} {:trigger eltTypes[j]} {:trigger trace[j]} :: 0 <= j < |trace| ==> var (val: Option<V>, rest: seq<byte>) := parse_Val(trace[j], eltTypes[j]); val.Some? && val.v == contents[j]
    ensures parse_Tuple_contents(marshalled_bytes, eltTypes).0.Some?
    ensures parse_Tuple_contents(marshalled_bytes, eltTypes).0.v == contents
    decreases contents, eltTypes, marshalled_bytes, trace
  {
  }

  method {:timeLimitMultiplier 2} /*{:_timeLimit 20}*/ MarshallTupleContents(contents: seq<V>, eltTypes: seq<G>, data: array<byte>, index: uint64)
      returns (size: uint64)
    requires |contents| == |eltTypes|
    requires forall i: int {:trigger eltTypes[i]} {:trigger contents[i]} :: 0 <= i < |contents| ==> ValInGrammar(contents[i], eltTypes[i])
    requires forall g: G {:trigger ValidGrammar(g)} {:trigger g in eltTypes} :: g in eltTypes ==> ValidGrammar(g)
    requires |eltTypes| < 18446744073709551616
    requires forall i: int {:trigger contents[i]} :: 0 <= i < |contents| ==> ValidVal(contents[i])
    requires index as int + SeqSum(contents) <= data.Length
    requires 0 <= index as int + SeqSum(contents) < 18446744073709551616
    requires data.Length < 18446744073709551616
    requires |contents| < 18446744073709551616
    modifies data
    ensures parse_Tuple_contents(data[index .. index as int + SeqSum(contents)], eltTypes).0.Some?
    ensures parse_Tuple_contents(data[index .. index as int + SeqSum(contents)], eltTypes).0.v == contents
    ensures forall i: uint64 {:trigger old(data[i])} {:trigger data[i]} :: 0 <= i < index ==> data[i] == old(data[i])
    ensures forall i: int {:trigger old(data[i])} {:trigger data[i]} :: index as int + SeqSum(contents) <= i < data.Length ==> data[i] == old(data[i])
    ensures size as int == SeqSum(contents)
    decreases eltTypes, 1, |contents|
  {
    var i: int := 0;
    var cur_index := index;
    reveal SeqSum();
    reveal parse_Tuple_contents();
    ghost var trace := [];
    ghost var marshalled_bytes := [];
    while i < |contents|
      invariant 0 <= i <= |contents|
      invariant 0 <= index as int <= index as int + SeqSum(contents[..i]) <= data.Length
      invariant cur_index as int == index as int + SeqSum(contents[..i])
      invariant forall j: uint64 {:trigger old(data[j])} {:trigger data[j]} :: 0 <= j < index ==> data[j] == old(data[j])
      invariant forall j: int {:trigger old(data[j])} {:trigger data[j]} :: index as int + SeqSum(contents) <= j < data.Length ==> data[j] == old(data[j])
      invariant marshalled_bytes == data[index .. cur_index]
      invariant marshalled_bytes == SeqCatRev(trace)
      invariant |trace| == i
      invariant forall j: int {:trigger trace[j]} {:trigger contents[j]} :: (0 <= j < |trace| ==> SizeOfV(contents[j]) == |trace[j]|) && (0 <= j < |trace| ==> |trace[j]| < 18446744073709551616)
      invariant forall j: int {:trigger contents[j]} {:trigger eltTypes[j]} {:trigger trace[j]} :: 0 <= j < |trace| ==> var (val: Option<V>, rest: seq<byte>) := parse_Val(trace[j], eltTypes[j]); val.Some? && val.v == contents[j]
      decreases |contents| - i
    {
      lemma_SeqSum_bound(contents, 18446744073709551616);
      ghost var old_marshalled_bytes := marshalled_bytes;
      ghost var old_data := data[index .. cur_index];
      assert old_marshalled_bytes == old_data;
      calc <= {
        cur_index as int + SizeOfV(contents[i]);
        index as int + SeqSum(contents[..i]) + SizeOfV(contents[i]);
        {
          lemma_SeqSum_prefix(contents[..i], contents[i]);
          assert contents[..i] + [contents[i]] == contents[..i + 1];
        }
        index as int + SeqSum(contents[..i + 1]);
        {
          lemma_SeqSum_bound_prefix(contents, contents[..i + 1], i + 1);
        }
        index as int + SeqSum(contents);
      }
      var item_size := MarshallVal(contents[i], eltTypes[i], data, cur_index);
      ghost var fresh_bytes := data[cur_index .. cur_index + item_size];
      marshalled_bytes := marshalled_bytes + fresh_bytes;
      forall
        ensures var (val: Option<V>, rest: seq<byte>) := parse_Val(fresh_bytes, eltTypes[i]); val.Some? && val.v == contents[i]
      {
        assert SizeOfV(contents[i]) <= |fresh_bytes|;
        lemma_parse_Val_view(fresh_bytes, contents[i], eltTypes[i], 0);
      }
      ghost var old_trace := trace;
      trace := trace + [fresh_bytes];
      ghost var old_cur_index := cur_index;
      cur_index := cur_index + item_size;
      i := i + 1;
      assert {:split_here} true;
      calc {
        marshalled_bytes;
        old_marshalled_bytes + fresh_bytes;
        old_data + fresh_bytes;
        data[index .. old_cur_index] + fresh_bytes;
        data[index .. old_cur_index] + data[old_cur_index .. cur_index];
        data[index .. cur_index];
      }
      calc <= {
        index as int + SeqSum(contents[..i]);
        calc {
          SeqSum(contents[..i]);
        <=
          {
            lemma_SeqSum_bound_prefix(contents, contents[..i], i);
          }
          SeqSum(contents);
        }
        index as int + SeqSum(contents);
        data.Length;
      }
      calc {
        cur_index as int;
        old_cur_index as int + SizeOfV(contents[i - 1]);
        index as int + SeqSum(contents[..i - 1]) + SizeOfV(contents[i - 1]);
        {
          lemma_SeqSum_prefix(contents[..i - 1], contents[i - 1]);
          assert contents[..i - 1] + [contents[i - 1]] == contents[..i];
        }
        index as int + SeqSum(contents[..i]);
      }
      assert cur_index as int == index as int + SeqSum(contents[..i]);
    }
    assert contents[..i] == contents;
    assert cur_index as int == index as int + SeqSum(contents);
    assert marshalled_bytes == data[index .. index as int + SeqSum(contents)];
    lemma_marshall_tuple_contents(contents, eltTypes, marshalled_bytes, trace);
    size := cur_index - index;
  }

  method MarshallTuple(val: V, grammar: G, data: array<byte>, index: uint64)
      returns (size: uint64)
    requires val.VTuple?
    requires ValidVal(val)
    requires ValidGrammar(grammar)
    requires ValInGrammar(val, grammar)
    requires index as int + SizeOfV(val) <= data.Length
    requires 0 <= index as int + SizeOfV(val) < 18446744073709551616
    requires data.Length < 18446744073709551616
    modifies data
    ensures parse_Val(data[index .. index as int + SizeOfV(val)], grammar).0.Some? && parse_Val(data[index .. index as int + SizeOfV(val)], grammar).0.v == val
    ensures forall i: uint64 {:trigger old(data[i])} {:trigger data[i]} :: 0 <= i < index ==> data[i] == old(data[i])
    ensures forall i: int {:trigger old(data[i])} {:trigger data[i]} :: index as int + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i])
    ensures size as int == SizeOfV(val)
    decreases grammar, -1
  {
    size := MarshallTupleContents(val.t, grammar.t, data, index);
    calc {
      parse_Val(data[index .. index as int + SizeOfV(val)], grammar);
      {
        reveal parse_Val();
      }
      parse_Tuple(data[index .. index as int + SizeOfV(val)], grammar.t);
    }
  }

  method MarshallBytes(bytes: seq<byte>, data: array<byte>, index: uint64)
    requires index as int + |bytes| <= data.Length
    requires 0 <= index as int + |bytes| < 18446744073709551616
    requires data.Length < 18446744073709551616
    modifies data
    ensures forall i: uint64 {:trigger old(data[i])} {:trigger data[i]} :: 0 <= i < index ==> data[i] == old(data[i])
    ensures forall i: int {:trigger data[i]} :: index as int <= i < index as int + |bytes| ==> data[i] == bytes[i - index as int]
    ensures forall i: int {:trigger old(data[i])} {:trigger data[i]} :: index as int + |bytes| <= i < data.Length ==> data[i] == old(data[i])
    decreases bytes, data, index
  {
    Arrays.CopySeqIntoArray(bytes, 0, data, index, |bytes| as uint64);
  }

  method MarshallByteArray(val: V, grammar: G, data: array<byte>, index: uint64)
      returns (size: uint64)
    requires val.VByteArray?
    requires ValidGrammar(grammar)
    requires ValInGrammar(val, grammar)
    requires ValidVal(val)
    requires index as int + SizeOfV(val) <= data.Length
    requires 0 <= index as int + SizeOfV(val) < 18446744073709551616
    requires data.Length < 18446744073709551616
    modifies data
    ensures parse_Val(data[index .. index as int + SizeOfV(val)], grammar).0.Some? && parse_Val(data[index .. index as int + SizeOfV(val)], grammar).0.v == val
    ensures forall i: uint64 {:trigger old(data[i])} {:trigger data[i]} :: 0 <= i < index ==> data[i] == old(data[i])
    ensures forall i: int {:trigger old(data[i])} {:trigger data[i]} :: index as int + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i])
    ensures size as int == SizeOfV(val)
    decreases grammar
  {
    MarshallUint64(|val.b| as uint64, data, index);
    assert SeqByteToUint64(data[index .. index + Uint64Size()]) == |val.b| as uint64;
    MarshallBytes(val.b, data, index + 8);
    calc {
      parse_Val(data[index .. index as int + SizeOfV(val)], grammar);
      {
        reveal parse_Val();
      }
      parse_ByteArray(data[index .. index as int + SizeOfV(val)]);
    }
    ghost var data_seq := data[index .. index as int + SizeOfV(val)];
    ghost var tuple := parse_Uint64(data_seq);
    ghost var len := tuple.0;
    ghost var rest := tuple.1;
    assert {:split_here} true;
    assert rest == data[index + 8 .. index as int + SizeOfV(val)] == val.b;
    assert !len.None? && len.v.u as int <= |rest|;
    assert rest[0 .. len.v.u] == val.b;
    size := 8 + |val.b| as uint64;
  }

  method MarshallCase(val: V, grammar: G, data: array<byte>, index: uint64)
      returns (size: uint64)
    requires val.VCase?
    requires ValidGrammar(grammar)
    requires ValInGrammar(val, grammar)
    requires ValidVal(val)
    requires index as int + SizeOfV(val) <= data.Length
    requires 0 <= index as int + SizeOfV(val) < 18446744073709551616
    requires data.Length < 18446744073709551616
    modifies data
    ensures parse_Val(data[index .. index as int + SizeOfV(val)], grammar).0.Some? && parse_Val(data[index .. index as int + SizeOfV(val)], grammar).0.v == val
    ensures forall i: uint64 {:trigger old(data[i])} {:trigger data[i]} :: 0 <= i < index ==> data[i] == old(data[i])
    ensures forall i: int {:trigger old(data[i])} {:trigger data[i]} :: index as int + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i])
    ensures size as int == SizeOfV(val)
    decreases grammar, -1
  {
    MarshallUint64(val.c, data, index);
    ghost var int_bytes := data[index .. index + Uint64Size()];
    ghost var tuple0 := parse_Uint64(int_bytes);
    ghost var caseID0 := tuple0.0;
    ghost var rest10 := tuple0.1;
    assert !caseID0.None?;
    assert caseID0.v.u == val.c;
    var val_size := MarshallVal(val.val, grammar.cases[val.c], data, index + 8);
    ghost var new_int_bytes := data[index .. index + Uint64Size()];
    assert forall i: uint64 {:auto_trigger} {:trigger new_int_bytes[i]} {:trigger int_bytes[i]} :: 0 <= i < Uint64Size() ==> int_bytes[i] == new_int_bytes[i];
    assert int_bytes == new_int_bytes;
    assert val.VCase?;
    assert grammar.GTaggedUnion?;
    assert val.c as int < |grammar.cases|;
    ghost var bytes := data[index .. index as int + SizeOfV(val)];
    assert bytes[..8] == new_int_bytes;
    calc {
      parse_Val(bytes, grammar);
      {
        reveal parse_Val();
      }
      parse_Case(bytes, grammar.cases);
    }
    assert {:split_here} true;
    ghost var tuple1 := parse_Uint64(bytes);
    ghost var caseID := tuple1.0;
    ghost var rest1 := tuple1.1;
    assert !caseID.None?;
    assert caseID.v.u == val.c;
    assert caseID.v.u as int < |grammar.cases|;
    ghost var tuple2 := parse_Val(rest1, grammar.cases[caseID.v.u]);
    ghost var v := tuple2.0;
    ghost var rest2 := tuple2.1;
    assert !v.None?;
    size := 8 + val_size;
  }

  method MarshallVUint64(val: V, grammar: G, data: array<byte>, index: uint64)
      returns (size: uint64)
    requires val.VUint64?
    requires ValidGrammar(grammar)
    requires ValInGrammar(val, grammar)
    requires index as int + SizeOfV(val) <= data.Length
    requires 0 <= index as int + SizeOfV(val) < 18446744073709551616
    requires data.Length < 18446744073709551616
    modifies data
    ensures parse_Val(data[index .. index as int + SizeOfV(val)], grammar).0.Some? && parse_Val(data[index .. index as int + SizeOfV(val)], grammar).0.v == val
    ensures forall i: uint64 {:trigger old(data[i])} {:trigger data[i]} :: 0 <= i < index ==> data[i] == old(data[i])
    ensures forall i: int {:trigger old(data[i])} {:trigger data[i]} :: index as int + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i])
    ensures size as int == SizeOfV(val)
    decreases grammar
  {
    MarshallUint64(val.u, data, index);
    calc {
      parse_Val(data[index .. index as int + SizeOfV(val)], grammar);
      {
        reveal parse_Val();
      }
      parse_Uint64(data[index .. index as int + SizeOfV(val)]);
    }
    return 8;
  }

  method MarshallVal(val: V, grammar: G, data: array<byte>, index: uint64)
      returns (size: uint64)
    requires ValidGrammar(grammar)
    requires ValInGrammar(val, grammar)
    requires ValidVal(val)
    requires 0 <= SizeOfV(val) < 18446744073709551616
    requires index as int + SizeOfV(val) <= data.Length
    requires data.Length < 18446744073709551616
    modifies data
    ensures parse_Val(data[index .. index as int + SizeOfV(val)], grammar).0.Some? && parse_Val(data[index .. index as int + SizeOfV(val)], grammar).0.v == val
    ensures forall i: uint64 {:trigger old(data[i])} {:trigger data[i]} :: 0 <= i < index ==> data[i] == old(data[i])
    ensures forall i: int {:trigger old(data[i])} {:trigger data[i]} :: index as int + SizeOfV(val) <= i < data.Length ==> data[i] == old(data[i])
    ensures size as int == SizeOfV(val)
    decreases grammar, 0
  {
    match val
    case {:split false} VUint64(_) =>
      size := MarshallVUint64(val, grammar, data, index);
    case {:split false} VArray(_) =>
      size := MarshallArray(val, grammar, data, index);
    case {:split false} VTuple(_) =>
      size := MarshallTuple(val, grammar, data, index);
    case {:split false} VByteArray(_) =>
      size := MarshallByteArray(val, grammar, data, index);
    case {:split false} VCase(_, _) =>
      size := MarshallCase(val, grammar, data, index);
  }

  method Marshall(val: V, grammar: G) returns (data: array<byte>)
    requires ValidGrammar(grammar)
    requires ValInGrammar(val, grammar)
    requires ValidVal(val)
    requires 0 <= SizeOfV(val) < 18446744073709551616
    ensures fresh(data)
    ensures Demarshallable(data[..], grammar)
    ensures parse_Val(data[..], grammar).0.Some? && parse_Val(data[..], grammar).0.v == val
    ensures parse_Val(data[..], grammar).1 == []
    ensures |data[..]| == SizeOfV(val)
    decreases val, grammar
  {
    var size := ComputeSizeOf(val);
    data := new byte[size];
    var computed_size := MarshallVal(val, grammar, data, 0);
    assert data[0 .. 0 + SizeOfV(val)] == data[0 .. 0 + size] == data[..];
    lemma_parse_Val_view_specific(data[..], val, grammar, 0, size as int);
  }
}

module Common__MarshallInt_i {

  import opened Native__NativeTypes_s

  import opened Native__NativeTypes_i

  import opened Common__Util_i

  import opened Math__power2_i
  method MarshallUint64_guts(n: uint64, data: array<byte>, index: uint64)
    requires index as int + Uint64Size() as int <= data.Length
    requires 0 <= index as int + Uint64Size() as int < 18446744073709551616
    requires data.Length < 18446744073709551616
    modifies data
    ensures SeqByteToUint64(data[index .. index + Uint64Size() as uint64]) == n
    ensures data[0 .. index] == old(data[0 .. index])
    ensures data[index + Uint64Size() as uint64..] == old(data[index + Uint64Size() as uint64..])
    decreases n, data, index
  {
    data[index] := (n / 72057594037927936) as byte;
    data[index + 1] := (n / 281474976710656 % 256) as byte;
    data[index + 2] := (n / 1099511627776 % 256) as byte;
    data[index + 3] := (n / 4294967296 % 256) as byte;
    data[index + 4] := (n / 16777216 % 256) as byte;
    data[index + 5] := (n / 65536 % 256) as byte;
    data[index + 6] := (n / 256 % 256) as byte;
    data[index + 7] := (n % 256) as byte;
    lemma_2toX();
    assert data[index .. index + Uint64Size() as uint64] == Uint64ToSeqByte(n);
    lemma_BEUintToSeqByte_invertability(data[index .. index + Uint64Size() as uint64], n as int, 8);
  }
}

module CausalMesh_ServerImpl_i {

  import opened Native__Io_s

  import opened Native__NativeTypes_s

  import opened Collections__Seqs_i

  import opened Math__mod_auto_i

  import opened Common__GenericMarshalling_i

  import opened Common__UdpClient_i

  import opened Common__Util_i

  import opened CausalMesh_CCache_i

  import opened CausalMesh_PacketParsing_i

  import opened CausalMesh_CTypes_i

  import opened CausalMesh_CMessage_i

  import opened CausalMesh_Types_i
  class ServerImpl {
    var server: CServer
    var netClient: UdpClient?
    var localAddr: EndPoint
    var msg_grammar: G
    ghost var Repr: set<object>

    constructor ()
    {
      netClient := null;
    }

    predicate Valid()
      reads this, if netClient != null then UdpClientIsValid.reads(netClient) else {}
      decreases (if netClient != null then UdpClientIsValid.reads(netClient) else {}) + {this}
    {
      CServerIsValid(server) &&
      CServerValid(server) &&
      netClient != null &&
      UdpClientIsValid(netClient) &&
      netClient.LocalEndPoint() == localAddr &&
      netClient.LocalEndPoint() == server.endpoint &&
      Repr == {this} + UdpClientRepr(netClient) &&
      msg_grammar == CMessage_grammar()
    }

    method ConstructUdpClient(ep: EndPoint, ghost env_: HostEnvironment)
        returns (ok: bool, client: UdpClient?)
      requires env_.Valid() && env_.ok.ok()
      requires EndPointIsValidIPV4(ep)
      modifies env_.ok
      ensures ok ==> client != null && UdpClientIsValid(client) && client.LocalEndPoint() == ep && client.env == env_
      decreases ep, env_
    {
      var my_ep := ep;
      var ip_byte_array := new byte[|my_ep.addr|];
      assert EndPointIsValidIPV4(my_ep);
      seqIntoArrayOpt(my_ep.addr, ip_byte_array);
      var ip_endpoint;
      ok, ip_endpoint := IPEndPoint.Construct(ip_byte_array, my_ep.port, env_);
      if !ok {
        return;
      }
      ok, client := UdpClient.Construct(ip_endpoint, env_);
      if ok {
        calc {
          client.LocalEndPoint();
          ip_endpoint.EP();
          my_ep;
        }
      }
    }

    method Server_Init(id: int, eps: seq<EndPoint>, ghost env_: HostEnvironment)
        returns (ok: bool)
      requires env_.Valid() && env_.ok.ok()
      requires 0 <= id < |eps|
      requires |eps| == Nodes
      requires forall ep: EndPoint {:trigger EndPointIsValidIPV4(ep)} {:trigger ep in eps} :: ep in eps ==> EndPointIsValidIPV4(ep)
      modifies this, netClient, env_.ok
      ensures ok ==> 0 <= this.server.next < Nodes && this.server.endpoint == eps[id] && this.server.next_endpoint == eps[this.server.next]
      decreases id, eps, env_
    {
      ok, netClient := ConstructUdpClient(eps[id], env_);
      if ok {
        server := CServerInit(id, eps);
        localAddr := eps[id];
        this.msg_grammar := CMessage_grammar();
      }
    }
  }
}

module CausalMesh_CCache_i {

  import opened CausalMesh_CTypes_i

  import opened CausalMesh_CMessage_i

  import opened CausalMesh_Message_i

  import opened CausalMesh_CPullDeps_i

  import opened CausalMesh_PullDeps_i

  import opened CausalMesh_Cache_i

  import opened GenericRefinement_i

  import opened Native__Io_s

  import opened Common__NodeIdentity_i

  import opened Environment_s

  import opened CausalMesh_Types_i

  import opened Collections__Maps_i
  datatype CServer = CServer(id: int, endpoint: EndPoint, gvc: CVectorClock, next: int, next_endpoint: EndPoint, icache: CICache, ccache: CCCache)

  method CReceiveRead(s: CServer, p: CPacket)
      returns (s': CServer, sp: seq<CPacket>)
    requires CServerIsValid(s)
    requires CPacketIsValid(p)
    requires p.msg.CMessage_Read?
    requires CServerValid(s)
    requires CPacketValid(p)
    ensures CServerIsValid(s')
    ensures forall i: int {:trigger sp[i]} :: 0 <= i < |sp| ==> CPacketIsAbstractable(sp[i])
    ensures ReceiveRead(AbstractifyCServerToServer(s), AbstractifyCServerToServer(s'), AbstractifyCPacketToPacket(p), AbstractifyCPacketSeq(sp))
    decreases s, p
  {
    ghost var gs := AbstractifyCServerToServer(s);
    ghost var gp := AbstractifyCPacketToPacket(p);
    var new_icache, new_ccache := CPullDeps3(s.icache, s.ccache, p.msg.deps_read);
    ghost var (gnew_icache, gnew_ccache) := PullDeps3(gs.icache, gs.ccache, gp.msg.deps_read);
    assert AbstractifyCICacheToICache(new_icache) == gnew_icache;
    assert AbstractifyCCCacheToCCache(new_ccache) == gnew_ccache;
    if p.msg.key_read !in new_ccache {
      new_ccache := new_ccache[p.msg.key_read := CEmptyMeta(p.msg.key_read)];
    } else {
      new_ccache := new_ccache;
    }
    var t1 := s.(icache := new_icache, ccache := new_ccache);
    var rep := CPacket(p.src, s.endpoint, CMessage_Read_Reply(p.msg.opn_read, p.msg.key_read, new_ccache[p.msg.key_read].vc, map[]));
    assert CDependencyIsValid(map[]);
    lemma_AbstractifyEndpointToID(rep.src, gs.id);
    lemma_AbstractifyEndpointToID(rep.dst, gp.src);
    lemma_AbstractifyEmptyDependency(map[]);
    assert AbstractifyCPacketToPacket(rep) == LPacket(gp.src, gs.id, Message_Read_Reply(gp.msg.opn_read, gp.msg.key_read, gnew_ccache[gp.msg.key_read].vc, map[]));
    s' := t1;
    sp := [rep];
    lemma_PacketSeqIsAbstractable(sp, LPacket(gp.src, gs.id, Message_Read_Reply(gp.msg.opn_read, gp.msg.key_read, gnew_ccache[gp.msg.key_read].vc, map[])));
  }

  lemma lemma_AbstractifyEmptyDependency(dep: CDependency)
    requires dep == map[]
    ensures AbstractifyCDependencyToDependency(dep) == map[]
    decreases dep
  {
  }

  lemma /*{:_induction sp}*/ lemma_PacketSeqIsAbstractable(sp: seq<CPacket>, p: Packet)
    requires |sp| == 1
    requires CPacketIsAbstractable(sp[0])
    requires AbstractifyCPacketToPacket(sp[0]) == p
    ensures forall i: int {:trigger sp[i]} :: 0 <= i < |sp| ==> CPacketIsAbstractable(sp[i])
    ensures AbstractifyCPacketSeq(sp) == [p]
    decreases sp, p
  {
  }

  method FilterSatisfiedDependency2(dep: CDependency, ccache: CCCache) returns (res: CDependency)
    requires CCCacheIsValid(ccache) && CCCacheValid(ccache)
    requires CDependencyValid(dep) && CDependencyIsValid(dep)
    ensures CDependencyValid(res) && CDependencyIsValid(res)
    ensures forall k: int {:trigger res[k]} {:trigger dep[k]} {:trigger k in dep} {:trigger k in res} :: (k in res ==> k in dep) && (k in res ==> dep[k] == res[k]) && (k in res ==> CVCEq(dep[k], res[k]))
    ensures forall k: int {:trigger ccache[k]} {:trigger dep[k]} {:trigger k in ccache} {:trigger k in res} :: k in res ==> k !in ccache || (!CVCEq(dep[k], ccache[k].vc) && !CVCHappendsBefore(dep[k], ccache[k].vc))
    ensures forall k: int {:trigger ccache[k]} {:trigger dep[k]} {:trigger k in ccache} {:trigger k in res} {:trigger k in dep} :: (k in dep && k !in res ==> k in ccache) && (k in dep && k !in res ==> CVCEq(dep[k], ccache[k].vc) || CVCHappendsBefore(dep[k], ccache[k].vc))
    decreases dep, ccache
  {
    res := map k: int {:trigger ccache[k]} {:trigger dep[k]} {:trigger k in ccache} {:trigger k in dep} | k in dep && (k !in ccache || (!CVCEq(dep[k], ccache[k].vc) && !CVCHappendsBefore(dep[k], ccache[k].vc))) :: dep[k];
  }

  lemma lemma_VCSSatisfiedInCacheMustSatisfiedInNewCache(deps: CDependency, deps2: CDependency, ccache: CCCache, ccache': CCCache)
    requires CDependencyValid(deps) && CDependencyValid(deps2) && CCCacheValid(ccache) && CCCacheValid(ccache')
    requires forall k: int {:trigger deps2[k]} {:trigger deps[k]} {:trigger k in deps} {:trigger k in deps2} :: (k in deps2 ==> k in deps) && (k in deps2 ==> CVCEq(deps[k], deps2[k]))
    requires forall k: int {:trigger ccache[k]} {:trigger deps[k]} {:trigger k in ccache} {:trigger k in deps2} {:trigger k in deps} :: (k in deps && k !in deps2 ==> k in ccache) && (k in deps && k !in deps2 ==> CVCEq(deps[k], ccache[k].vc) || CVCHappendsBefore(deps[k], ccache[k].vc))
    requires forall k: int {:trigger ccache'[k]} {:trigger ccache[k]} {:trigger k in ccache'} {:trigger k in ccache} :: (k in ccache ==> k in ccache') && (k in ccache ==> CVCEq(ccache[k].vc, ccache'[k].vc) || CVCHappendsBefore(ccache[k].vc, ccache'[k].vc))
    requires forall k: int {:trigger ccache'[k]} {:trigger deps2[k]} {:trigger k in ccache'} {:trigger k in deps2} :: (k in deps2 ==> k in ccache') && (k in deps2 ==> CVCEq(deps2[k], ccache'[k].vc) || CVCHappendsBefore(deps2[k], ccache'[k].vc))
    ensures forall k: int {:trigger ccache'[k]} {:trigger deps[k]} {:trigger k in ccache'} {:trigger k in deps2} {:trigger k in deps} :: (k in deps && k !in deps2 ==> k in ccache') && (k in deps && k !in deps2 ==> CVCEq(deps[k], ccache'[k].vc) || CVCHappendsBefore(deps[k], ccache'[k].vc))
    ensures forall k: int {:trigger ccache'[k]} {:trigger deps[k]} {:trigger k in ccache'} {:trigger k in deps2} {:trigger k in deps} :: (k in deps && k in deps2 ==> k in ccache') && (k in deps && k in deps2 ==> CVCEq(deps[k], ccache'[k].vc) || CVCHappendsBefore(deps[k], ccache'[k].vc))
    ensures forall k: int {:trigger ccache'[k]} {:trigger deps[k]} {:trigger k in ccache'} {:trigger k in deps} :: (k in deps ==> k in ccache') && (k in deps ==> CVCEq(deps[k], ccache'[k].vc) || CVCHappendsBefore(deps[k], ccache'[k].vc))
    decreases deps, deps2, ccache, ccache'
  {
  }

  method CReceiveRead_I1(s: CServer, p: CPacket)
      returns (s': CServer, sp: seq<CPacket>)
    requires CServerIsValid(s)
    requires CPacketIsValid(p)
    requires p.msg.CMessage_Read?
    requires CServerValid(s)
    requires CPacketValid(p)
    ensures CServerIsValid(s')
    ensures forall i: int {:trigger sp[i]} :: 0 <= i < |sp| ==> CPacketIsAbstractable(sp[i])
    decreases s, p
  {
    ghost var gs := AbstractifyCServerToServer(s);
    ghost var gp := AbstractifyCPacketToPacket(p);
    var new_dep := FilterSatisfiedDependency2(p.msg.deps_read, s.ccache);
    assert forall k: int {:trigger p.msg.deps_read[k]} {:trigger new_dep[k]} {:trigger k in p.msg.deps_read} {:trigger k in new_dep} :: (k in new_dep ==> k in p.msg.deps_read) && (k in new_dep ==> CVCEq(new_dep[k], p.msg.deps_read[k]));
    assert forall k: int {:trigger s.ccache[k]} {:trigger p.msg.deps_read[k]} {:trigger k in s.ccache} {:trigger k in new_dep} :: k in new_dep ==> k in s.ccache ==> !CVCEq(p.msg.deps_read[k], s.ccache[k].vc) && !CVCHappendsBefore(p.msg.deps_read[k], s.ccache[k].vc);
    assert forall k: int {:trigger s.ccache[k]} {:trigger p.msg.deps_read[k]} {:trigger k in s.ccache} {:trigger k in new_dep} {:trigger k in p.msg.deps_read} :: (k in p.msg.deps_read && k !in new_dep ==> k in s.ccache) && (k in p.msg.deps_read && k !in new_dep ==> CVCEq(p.msg.deps_read[k], s.ccache[k].vc) || CVCHappendsBefore(p.msg.deps_read[k], s.ccache[k].vc));
    var new_icache, new_ccache := CPullDeps3(s.icache, s.ccache, new_dep);
    assert forall k: int {:trigger new_ccache[k]} {:trigger new_dep[k]} {:trigger k in new_ccache} {:trigger k in new_dep} :: (k in new_dep ==> k in new_ccache) && (k in new_dep ==> CVCEq(new_dep[k], new_ccache[k].vc) || CVCHappendsBefore(new_dep[k], new_ccache[k].vc));
    assert forall k: int {:trigger new_ccache[k]} {:trigger s.ccache[k]} {:trigger k in new_ccache} {:trigger k in s.ccache} :: (k in s.ccache ==> k in new_ccache) && (k in s.ccache ==> CVCEq(s.ccache[k].vc, new_ccache[k].vc) || CVCHappendsBefore(s.ccache[k].vc, new_ccache[k].vc));
    lemma_VCSSatisfiedInCacheMustSatisfiedInNewCache(p.msg.deps_read, new_dep, s.ccache, new_ccache);
    assert forall k: int {:trigger new_ccache[k]} {:trigger p.msg.deps_read[k]} {:trigger k in new_ccache} {:trigger k in p.msg.deps_read} :: (k in p.msg.deps_read ==> k in new_ccache) && (k in p.msg.deps_read ==> CVCEq(p.msg.deps_read[k], new_ccache[k].vc) || CVCHappendsBefore(p.msg.deps_read[k], new_ccache[k].vc));
    ghost var (gnew_icache, gnew_ccache) := PullDeps3(gs.icache, gs.ccache, gp.msg.deps_read);
    assert AbstractifyCICacheToICache(new_icache) == gnew_icache;
    lemma_ReceiveRead_I1(new_ccache, gnew_ccache);
    assert AbstractifyCCCacheToCCache(new_ccache) == gnew_ccache;
    if p.msg.key_read !in new_ccache {
      new_ccache := new_ccache[p.msg.key_read := CEmptyMeta(p.msg.key_read)];
    }
    var t1 := s.(icache := new_icache, ccache := new_ccache);
    ghost var gnew_ccache' := if gp.msg.key_read !in gnew_ccache then gnew_ccache[gp.msg.key_read := EmptyMeta(gp.msg.key_read)] else gnew_ccache;
    ghost var gs' := gs.(icache := gnew_icache, ccache := gnew_ccache');
    assert AbstractifyCServerToServer(t1) == gs';
    var rep := CPacket(p.src, s.endpoint, CMessage_Read_Reply(p.msg.opn_read, p.msg.key_read, new_ccache[p.msg.key_read].vc, map[]));
    assert CDependencyIsValid(map[]);
    assert CMessageIsValid(CMessage_Read_Reply(p.msg.opn_read, p.msg.key_read, new_ccache[p.msg.key_read].vc, map[]));
    assert CPacketIsAbstractable(rep);
    assert CMessageIsValid(rep.msg);
    lemma_AbstractifyEndpointToID(rep.src, gs.id);
    lemma_AbstractifyEndpointToID(rep.dst, gp.src);
    lemma_AbstractifyEmptyDependency(map[]);
    assert AbstractifyCPacketToPacket(rep) == LPacket(gp.src, gs.id, Message_Read_Reply(gp.msg.opn_read, gp.msg.key_read, gnew_ccache[gp.msg.key_read].vc, map[]));
    s' := t1;
    sp := [rep];
    assert CPacketIsAbstractable(sp[0]);
    assert |sp| == 1;
    lemma_PacketSeqIsAbstractable(sp, LPacket(gp.src, gs.id, Message_Read_Reply(gp.msg.opn_read, gp.msg.key_read, gnew_ccache[gp.msg.key_read].vc, map[])));
  }

  lemma {:axiom} lemma_ReceiveRead_I1(ccache: CCCache, gccache: CCache)
    requires CCCacheIsValid(ccache)
    ensures AbstractifyCCCacheToCCache(ccache) == gccache
    decreases ccache, gccache

  method CReceivePropagate(s: CServer, p: CPacket)
      returns (s': CServer, sp: seq<CPacket>)
    requires CServerIsValid(s)
    requires CPacketIsValid(p)
    requires p.msg.CMessage_Propagation?
    requires CServerValid(s)
    requires CPacketValid(p)
    ensures CServerIsValid(s')
    ensures forall i: int {:trigger sp[i]} :: 0 <= i < |sp| ==> CPacketIsValid(sp[i])
    ensures ReceivePropagate(AbstractifyCServerToServer(s), AbstractifyCServerToServer(s'), AbstractifyCPacketToPacket(p), AbstractifyCPacketSeq(sp))
    decreases s, p
  {
    ghost var gs := AbstractifyCServerToServer(s);
    ghost var gp := AbstractifyCPacketToPacket(p);
    if s.next == p.msg.start {
      if p.msg.round == 2 {
        assert gs.next == gp.msg.start;
        assert gp.msg.round == 2;
        var vcs := p.msg.meta.vc;
        var new_gvc := CVCMerge(s.gvc, vcs);
        var new_deps := p.msg.meta.deps;
        var new_icache, new_ccache := CPullDeps3(s.icache, s.ccache, new_deps);
        ghost var (gnew_icache, gnew_ccache) := PullDeps3(gs.icache, gs.ccache, gp.msg.meta.deps);
        assert AbstractifyCICacheToICache(new_icache) == gnew_icache;
        assert AbstractifyCCCacheToCCache(new_ccache) == gnew_ccache;
        var new_ccache' := CInsertIntoCCache(new_ccache, p.msg.meta);
        ghost var gnew_ccache' := InsertIntoCCache(gnew_ccache, gp.msg.meta);
        assert AbstractifyCCCacheToCCache(new_ccache') == gnew_ccache';
        var new_icache' := CAddMetaToICache(new_icache, p.msg.meta);
        ghost var gnew_icache' := AddMetaToICache(gnew_icache, gp.msg.meta);
        assert AbstractifyCICacheToICache(new_icache') == gnew_icache';
        s' := s.(gvc := new_gvc, icache := new_icache', ccache := new_ccache');
        assert AbstractifyCServerToServer(s') == gs.(gvc := AbstractifyCVectorClockToVectorClock(new_gvc), icache := AbstractifyCICacheToICache(new_icache'), ccache := AbstractifyCCCacheToCCache(new_ccache'));
        sp := [];
        assert AbstractifyCPacketSeq(sp) == [];
        assert ReceivePropagate(gs, AbstractifyCServerToServer(s'), gp, AbstractifyCPacketSeq(sp));
      } else {
        assert gs.next == gp.msg.start;
        assert gp.msg.round != 2;
        var new_icache := CAddMetaToICache(s.icache, p.msg.meta);
        s' := s.(icache := new_icache);
        ghost var gs' := AbstractifyCServerToServer(s');
        assert gs' == gs.(icache := AbstractifyCICacheToICache(new_icache));
        var propagate := CPacket(s.next_endpoint, s.endpoint, p.msg.(round := 2));
        lemma_AbstractifyEndpointToID(propagate.src, gs.id);
        lemma_AbstractifyEndpointToID(propagate.dst, gs.next);
        assert AbstractifyEndPointToID(propagate.src) == gs.id;
        assert AbstractifyEndPointToID(propagate.dst) == gs.next;
        assert AbstractifyCMessageToMessage(propagate.msg) == gp.msg.(round := 2);
        assert AbstractifyCPacketToPacket(propagate) == LPacket(gs.next, gs.id, gp.msg.(round := 2));
        sp := [propagate];
        assert AbstractifyCPacketSeq(sp) == [LPacket(gs.next, gs.id, gp.msg.(round := 2))];
        assert ReceivePropagate(gs, AbstractifyCServerToServer(s'), gp, AbstractifyCPacketSeq(sp));
      }
    } else {
      var new_icache := CAddMetaToICache(s.icache, p.msg.meta);
      s' := s.(icache := new_icache);
      var propagate := CPacket(s.next_endpoint, s.endpoint, p.msg);
      lemma_AbstractifyEndpointToID(propagate.src, gs.id);
      lemma_AbstractifyEndpointToID(propagate.dst, gs.next);
      assert AbstractifyEndPointToID(propagate.src) == gs.id;
      assert AbstractifyEndPointToID(propagate.dst) == gs.next;
      sp := [propagate];
      assert AbstractifyCPacketSeq(sp) == [LPacket(gs.next, gs.id, gp.msg)];
      assert ReceivePropagate(gs, AbstractifyCServerToServer(s'), gp, AbstractifyCPacketSeq(sp));
      assert ReceivePropagate(gs, AbstractifyCServerToServer(s'), gp, AbstractifyCPacketSeq(sp));
    }
  }

  lemma {:axiom} lemma_CReceiveWrite(s: CServer, p: CPacket, s': CServer, sp: seq<CPacket>)
    requires CServerIsValid(s)
    requires CPacketIsValid(p)
    requires p.msg.CMessage_Write?
    requires CServerValid(s)
    requires CPacketValid(p)
    requires CServerIsValid(s')
    requires forall i: int {:trigger sp[i]} :: 0 <= i < |sp| ==> CPacketIsValid(sp[i])
    ensures ReceiveWrite(AbstractifyCServerToServer(s), AbstractifyCServerToServer(s'), AbstractifyCPacketToPacket(p), AbstractifyCPacketSeq(sp))
    decreases s, p, s', sp

  method CReceiveWrite(s: CServer, p: CPacket)
      returns (s': CServer, sp: seq<CPacket>)
    requires CServerIsValid(s)
    requires CPacketIsValid(p)
    requires p.msg.CMessage_Write?
    requires CServerValid(s)
    requires CPacketValid(p)
    ensures CServerIsValid(s')
    ensures forall i: int {:trigger sp[i]} :: 0 <= i < |sp| ==> CPacketIsValid(sp[i])
    ensures ReceiveWrite(AbstractifyCServerToServer(s), AbstractifyCServerToServer(s'), AbstractifyCPacketToPacket(p), AbstractifyCPacketSeq(sp))
    decreases s, p
  {
    ghost var gs := AbstractifyCServerToServer(s);
    ghost var gp := AbstractifyCPacketToPacket(p);
    assert forall k: int {:trigger p.msg.local[k]} {:trigger k in p.msg.local} :: (k in p.msg.local ==> CMetaValid(p.msg.local[k])) && (k in p.msg.local ==> CMetaIsValid(p.msg.local[k]));
    var local_metas := set m: CMeta {:trigger m in p.msg.local.Values} | m in p.msg.local.Values;
    assert forall m: CMeta {:trigger CMetaIsValid(m)} {:trigger CMetaValid(m)} {:trigger m in local_metas} :: (m in local_metas ==> CMetaValid(m)) && (m in local_metas ==> CMetaIsValid(m));
    ghost var glocal_metas := set m: Meta {:trigger m in gp.msg.local.Values} | m in gp.msg.local.Values;
    lemma_AbstractifyCMetaToMeta_Is_Injective(local_metas);
    var vcs_local := set m: CMeta {:trigger m.vc} {:trigger m in local_metas} | m in local_metas :: m.vc;
    assert forall vc: CVectorClock {:trigger CVectorClockValid(vc)} {:trigger vc in vcs_local} :: vc in vcs_local ==> CVectorClockValid(vc);
    ghost var gvcs_local := set m: CMeta {:trigger m.vc} {:trigger m in local_metas} | m in local_metas :: m.vc;
    var vcs_deps := set k: int {:trigger p.msg.deps_write[k]} {:trigger k in p.msg.deps_write} | k in p.msg.deps_write :: p.msg.deps_write[k];
    ghost var gvcs_deps := set k: int {:trigger gp.msg.deps_write[k]} {:trigger k in gp.msg.deps_write} | k in gp.msg.deps_write :: gp.msg.deps_write[k];
    var merged_vc := CFoldVC(s.gvc, vcs_local);
    var merged_vc2 := CFoldVC(merged_vc, vcs_deps);
    var new_vc := CAdvanceVC(merged_vc2, s.id);
    var merged_deps := CFoldDependencyFromMetaSet(p.msg.deps_write, local_metas);
    var meta := CMeta(p.msg.key_write, new_vc, merged_deps);
    assert CMetaIsValid(meta) && CMetaValid(meta);
    assert forall m: CMeta {:trigger CMetaValid(m)} {:trigger CMetaIsValid(m)} {:trigger m in local_metas} :: (m in local_metas ==> CMetaIsValid(m)) && (m in local_metas ==> CMetaValid(m));
    lemma_AddNewMeta(local_metas, meta);
    var new_icache := CAddMetaToICache(s.icache, meta);
    var wreply := CPacket(p.src, s.endpoint, CMessage_Write_Reply(p.msg.opn_write, p.msg.key_write, new_vc));
    assert CPacketIsValid(wreply);
    lemma_AbstractifyEndpointToID(wreply.src, gs.id);
    lemma_AbstractifyEndpointToID(wreply.dst, gp.src);
    assert AbstractifyEndPointToID(wreply.src) == gs.id;
    assert AbstractifyEndPointToID(wreply.dst) == gp.src;
    assert AbstractifyCPacketToPacket(wreply) == LPacket(gp.src, gs.id, Message_Write_Reply(gp.msg.opn_write, gp.msg.key_write, AbstractifyCVectorClockToVectorClock(new_vc)));
    var propagate := CPacket(s.next_endpoint, s.endpoint, CMessage_Propagation(p.msg.key_write, meta, s.id, 1));
    assert CPacketIsValid(propagate);
    lemma_AbstractifyEndpointToID(propagate.src, gs.id);
    lemma_AbstractifyEndpointToID(propagate.dst, gs.next);
    assert AbstractifyEndPointToID(propagate.src) == gs.id;
    assert AbstractifyEndPointToID(propagate.dst) == gs.next;
    assert AbstractifyCPacketToPacket(propagate) == LPacket(gs.next, gs.id, Message_Propagation(gp.msg.key_write, AbstractifyCMetaToMeta(meta), gs.id, 1));
    s' := s.(gvc := new_vc, icache := new_icache);
    ghost var gs' := AbstractifyCServerToServer(s');
    assert gs' == gs.(gvc := AbstractifyCVectorClockToVectorClock(new_vc), icache := AbstractifyCICacheToICache(new_icache));
    sp := [wreply] + [propagate];
    lemma_PacketSeqIsValid(wreply, propagate, LPacket(gp.src, gs.id, Message_Write_Reply(gp.msg.opn_write, gp.msg.key_write, AbstractifyCVectorClockToVectorClock(new_vc))), LPacket(gs.next, gs.id, Message_Propagation(gp.msg.key_write, AbstractifyCMetaToMeta(meta), gs.id, 1)));
    assert forall i: int {:trigger sp[i]} :: 0 <= i < |sp| ==> CPacketIsValid(sp[i]);
    assert AbstractifyCPacketSeq(sp) == [LPacket(gp.src, gs.id, Message_Write_Reply(gp.msg.opn_write, gp.msg.key_write, AbstractifyCVectorClockToVectorClock(new_vc)))] + [LPacket(gs.next, gs.id, Message_Propagation(gp.msg.key_write, AbstractifyCMetaToMeta(meta), gs.id, 1))];
    lemma_CReceiveWrite(s, p, s', sp);
  }

  lemma lemma_VCTransitive(m: CMessage, vc: CVectorClock)
    requires m.CMessage_Write?
    requires CMessageValid(m)
    requires CVectorClockValid(vc)
    requires CVCEq(m.mvc, vc) || CVCHappendsBefore(m.mvc, vc)
    ensures forall k: int {:trigger m.deps_write[k]} {:trigger k in m.deps_write} :: k in m.deps_write ==> CVCEq(m.deps_write[k], vc) || CVCHappendsBefore(m.deps_write[k], vc)
    ensures forall k: int {:trigger m.local[k]} {:trigger k in m.local} :: k in m.local ==> CVCEq(m.local[k].vc, vc) || CVCHappendsBefore(m.local[k].vc, vc)
    decreases m, vc
  {
  }

  method CReceiveWrite_I1(s: CServer, p: CPacket)
      returns (s': CServer, sp: seq<CPacket>)
    requires CServerIsValid(s)
    requires CPacketIsValid(p)
    requires p.msg.CMessage_Write?
    requires CServerValid(s)
    requires CPacketValid(p)
    ensures CServerIsValid(s')
    ensures forall i: int {:trigger sp[i]} :: 0 <= i < |sp| ==> CPacketIsValid(sp[i])
    decreases s, p
  {
    ghost var gs := AbstractifyCServerToServer(s);
    ghost var gp := AbstractifyCPacketToPacket(p);
    assert forall k: int {:trigger p.msg.local[k]} {:trigger k in p.msg.local} :: (k in p.msg.local ==> CMetaValid(p.msg.local[k])) && (k in p.msg.local ==> CMetaIsValid(p.msg.local[k]));
    var vcs_deps := set k: int {:trigger p.msg.deps_write[k]} {:trigger k in p.msg.deps_write} | k in p.msg.deps_write :: p.msg.deps_write[k];
    assert forall k: int {:trigger p.msg.deps_write[k]} {:trigger k in p.msg.deps_write} :: k in p.msg.deps_write ==> CVCEq(p.msg.deps_write[k], p.msg.mvc) || CVCHappendsBefore(p.msg.deps_write[k], p.msg.mvc);
    assert forall k: int {:trigger p.msg.local[k]} {:trigger k in p.msg.local} :: k in p.msg.local ==> CVCEq(p.msg.local[k].vc, p.msg.mvc) || CVCHappendsBefore(p.msg.local[k].vc, p.msg.mvc);
    var merged_vc := CVCMerge(s.gvc, p.msg.mvc);
    assert CVCEq(p.msg.mvc, merged_vc) || CVCHappendsBefore(p.msg.mvc, merged_vc);
    lemma_VCTransitive(p.msg, merged_vc);
    assert forall k: int {:trigger p.msg.deps_write[k]} {:trigger k in p.msg.deps_write} :: k in p.msg.deps_write ==> CVCEq(p.msg.deps_write[k], merged_vc) || CVCHappendsBefore(p.msg.deps_write[k], merged_vc);
    assert forall k: int {:trigger p.msg.local[k]} {:trigger k in p.msg.local} :: k in p.msg.local ==> CVCEq(p.msg.local[k].vc, merged_vc) || CVCHappendsBefore(p.msg.local[k].vc, merged_vc);
    var new_vc := CAdvanceVC(merged_vc, s.id);
    var meta := CMeta(p.msg.key_write, new_vc, p.msg.deps_write);
    assert forall k: int {:trigger p.msg.deps_write[k]} {:trigger p.msg.local[k]} {:trigger k in p.msg.deps_write} {:trigger k in p.msg.local} :: (k in p.msg.local ==> k in p.msg.deps_write) && (k in p.msg.local ==> CVCEq(p.msg.local[k].vc, p.msg.deps_write[k]) || CVCHappendsBefore(p.msg.local[k].vc, p.msg.deps_write[k]));
    assert CMetaIsValid(meta) && CMetaValid(meta);
    var new_icache := CAddMetaToICache(s.icache, meta);
    var wreply := CPacket(p.src, s.endpoint, CMessage_Write_Reply(p.msg.opn_write, p.msg.key_write, new_vc));
    assert CPacketIsValid(wreply);
    lemma_AbstractifyEndpointToID(wreply.src, gs.id);
    lemma_AbstractifyEndpointToID(wreply.dst, gp.src);
    assert AbstractifyEndPointToID(wreply.src) == gs.id;
    assert AbstractifyEndPointToID(wreply.dst) == gp.src;
    assert AbstractifyCPacketToPacket(wreply) == LPacket(gp.src, gs.id, Message_Write_Reply(gp.msg.opn_write, gp.msg.key_write, AbstractifyCVectorClockToVectorClock(new_vc)));
    var propagate := CPacket(s.next_endpoint, s.endpoint, CMessage_Propagation(p.msg.key_write, meta, s.id, 1));
    assert CPacketIsValid(propagate);
    lemma_AbstractifyEndpointToID(propagate.src, gs.id);
    lemma_AbstractifyEndpointToID(propagate.dst, gs.next);
    assert AbstractifyEndPointToID(propagate.src) == gs.id;
    assert AbstractifyEndPointToID(propagate.dst) == gs.next;
    assert AbstractifyCPacketToPacket(propagate) == LPacket(gs.next, gs.id, Message_Propagation(gp.msg.key_write, AbstractifyCMetaToMeta(meta), gs.id, 1));
    s' := s.(gvc := new_vc, icache := new_icache);
    ghost var gs' := AbstractifyCServerToServer(s');
    sp := [wreply] + [propagate];
    lemma_PacketSeqIsValid(wreply, propagate, LPacket(gp.src, gs.id, Message_Write_Reply(gp.msg.opn_write, gp.msg.key_write, AbstractifyCVectorClockToVectorClock(new_vc))), LPacket(gs.next, gs.id, Message_Propagation(gp.msg.key_write, AbstractifyCMetaToMeta(meta), gs.id, 1)));
    assert forall i: int {:trigger sp[i]} :: 0 <= i < |sp| ==> CPacketIsValid(sp[i]);
    assert AbstractifyCPacketSeq(sp) == [LPacket(gp.src, gs.id, Message_Write_Reply(gp.msg.opn_write, gp.msg.key_write, AbstractifyCVectorClockToVectorClock(new_vc)))] + [LPacket(gs.next, gs.id, Message_Propagation(gp.msg.key_write, AbstractifyCMetaToMeta(meta), gs.id, 1))];
  }

  lemma lemma_PacketSeqIsValid(p1: CPacket, p2: CPacket, lp1: Packet, lp2: Packet)
    requires CPacketIsValid(p1)
    requires CPacketIsValid(p2)
    requires AbstractifyCPacketToPacket(p1) == lp1
    requires AbstractifyCPacketToPacket(p2) == lp2
    ensures ghost var sp: seq<CPacket> := [p1] + [p2]; forall i: int {:trigger sp[i]} :: 0 <= i < |sp| ==> CPacketIsValid(sp[i])
    ensures ghost var sp: seq<CPacket> := [p1] + [p2]; AbstractifyCPacketSeq(sp) == [lp1] + [lp2]
    decreases p1, p2, lp1, lp2
  {
  }

  lemma lemma_AddNewMeta(s: set<CMeta>, m: CMeta)
    requires CMetaValid(m) && CMetaIsValid(m)
    requires forall m: CMeta {:trigger CMetaIsValid(m)} {:trigger CMetaValid(m)} {:trigger m in s} :: (m in s ==> CMetaValid(m)) && (m in s ==> CMetaIsValid(m))
    ensures forall x: CMeta {:trigger CMetaIsValid(x)} {:trigger CMetaValid(x)} {:trigger x in s + {m}} :: (x in s + {m} ==> CMetaValid(x)) && (x in s + {m} ==> CMetaIsValid(x))
    decreases s, m
  {
  }

  function method CCircle(id: int, nodes: int): int
    requires 0 <= id && id < nodes
    ensures var i: int := CCircle(id, nodes); 0 <= i && i < nodes
    ensures var lr: int := Circle(id, nodes); var cr: int := CCircle(id, nodes); cr == lr
    decreases id, nodes
  {
    if nodes == 1 then
      id
    else if id == nodes - 1 then
      0
    else
      id + 1
  }

  function method CInsertIntoCCache(c: CCCache, m: CMeta): CCCache
    requires CCCacheIsValid(c)
    requires CMetaIsValid(m)
    requires CCCacheValid(c)
    requires CMetaValid(m)
    ensures var lr: CCache := InsertIntoCCache(AbstractifyCCCacheToCCache(c), AbstractifyCMetaToMeta(m)); var cr: CCCache := CInsertIntoCCache(c, m); CCCacheIsValid(cr) && AbstractifyCCCacheToCCache(cr) == lr
    decreases c, m
  {
    if m.key in c then
      c[m.key := CMetaMerge(c[m.key], m)]
    else
      c[m.key := m]
  }

  method CAddMetasToICache(c: CICache, metas: set<CMeta>) returns (res: CICache)
    requires CICacheIsValid(c)
    requires forall i: CMeta {:trigger CMetaIsValid(i)} {:trigger i in metas} :: i in metas ==> CMetaIsValid(i)
    requires CICacheValid(c)
    requires forall m: CMeta {:trigger m.deps} {:trigger CMetaValid(m)} {:trigger m in metas} :: (m in metas ==> CMetaValid(m)) && (m in metas ==> forall k: int {:trigger k in c} {:trigger k in m.deps} :: k in m.deps ==> k in c)
    ensures CICacheValid(res)
    ensures CICacheIsValid(res)
    ensures SetIsInjective(metas, AbstractifyCMetaToMeta)
    ensures var lr: ICache := AddMetasToICache(AbstractifyCICacheToICache(c), AbstractifySet(metas, AbstractifyCMetaToMeta)); AbstractifyCICacheToICache(res) == lr
    decreases |metas|
  {
    if |metas| == 0 {
      res := c;
      assert AbstractifyCICacheToICache(res) == AddMetasToICache(AbstractifyCICacheToICache(c), AbstractifySet(metas, AbstractifyCMetaToMeta));
    } else {
      var m :| m in metas;
      var new_metas := metas - {m};
      res := CAddMetasToICache(CAddMetaToICache(c, m), new_metas);
      ghost var gacc := AbstractifyCICacheToICache(c);
      lemma_AbstractifyCMetaToMeta_Is_Injective(metas);
      ghost var gmetas := AbstractifySet(metas, AbstractifyCMetaToMeta);
      ghost var gnmetas := AbstractifySet(metas - {m}, AbstractifyCMetaToMeta);
      ghost var gx := AbstractifyCMetaToMeta(m);
      assert gnmetas == gmetas - {gx};
      lemma_CAddMetasToICache(gacc, gmetas, gx);
      assert AddMetasToICache(gacc, gmetas) == AddMetasToICache(AddMetaToICache(gacc, gx), gmetas - {gx});
      assert AbstractifyCICacheToICache(res) == AddMetasToICache(gacc, gmetas);
    }
  }

  lemma {:axiom} lemma_CAddMetasToICache(c: ICache, metas: set<Meta>, x: Meta)
    requires ICacheValid(c)
    requires forall i: Meta {:trigger i.deps} {:trigger MetaValid(i)} {:trigger i in metas} :: (i in metas ==> MetaValid(i)) && (i in metas ==> forall k: int {:trigger k in c} {:trigger k in i.deps} :: k in i.deps ==> k in c)
    requires MetaValid(x) && forall k: int {:trigger k in c} {:trigger k in x.deps} :: k in x.deps ==> k in c
    ensures AddMetasToICache(c, metas) == AddMetasToICache(AddMetaToICache(c, x), metas - {x})
    decreases c, metas, x

  function method CAddMetaToICache(c: CICache, m: CMeta): CICache
    requires CICacheIsValid(c)
    requires CMetaIsValid(m)
    requires CICacheValid(c)
    requires CMetaValid(m)
    requires forall k: int {:trigger k in c} {:trigger k in m.deps} :: k in m.deps ==> k in c
    ensures var lr: ICache := AddMetaToICache(AbstractifyCICacheToICache(c), AbstractifyCMetaToMeta(m)); var cr: CICache := CAddMetaToICache(c, m); CICacheIsValid(cr) && AbstractifyCICacheToICache(cr) == lr
    decreases c, m
  {
    ghost var gm: Meta := AbstractifyCMetaToMeta(m);
    ghost var gc: ICache := AbstractifyCICacheToICache(c);
    assert m.key == gm.key;
    if m.key in c then
      assert gm.key in gc;
      var r: map<CKey, set<CMeta>> := c[m.key := c[m.key] + {m}];
      ghost var ms: set<CMeta> := {m};
      ghost var gms: set<Meta> := {gm};
      assert (set i: CMeta {:trigger AbstractifyCMetaToMeta(i)} {:trigger i in ms} | i in ms :: AbstractifyCMetaToMeta(i)) == gms;
      ghost var ms2: set<CMeta> := c[m.key] + {m};
      ghost var gms2: set<Meta> := gc[gm.key] + {gm};
      assert (set i: CMeta {:trigger AbstractifyCMetaToMeta(i)} {:trigger i in ms2} | i in ms2 :: AbstractifyCMetaToMeta(i)) == gms2;
      r
    else
      var r: map<CKey, set<CMeta>> := c[m.key := {m}]; ghost var ms: set<CMeta> := {m}; ghost var gms: set<Meta> := {gm}; assert (set i: CMeta {:trigger AbstractifyCMetaToMeta(i)} {:trigger i in ms} | i in ms :: AbstractifyCMetaToMeta(i)) == gms; r
  }

  lemma {:axiom} lemma_CAddMetaToICache(c: CICache, m: CMeta, res: CICache)
    requires CICacheIsValid(c)
    requires CMetaIsValid(m)
    requires CICacheValid(c)
    requires CMetaValid(m)
    requires forall k: int {:trigger k in c} {:trigger k in m.deps} :: k in m.deps ==> k in c
    requires CICacheIsValid(res)
    ensures AbstractifyCICacheToICache(res) == AddMetaToICache(AbstractifyCICacheToICache(c), AbstractifyCMetaToMeta(m))
    decreases c, m, res

  method CPullDeps3(icache: CICache, ccache: CCCache, deps: CDependency)
      returns (icache': CICache, ccache': CCCache)
    requires CICacheIsValid(icache)
    requires CCCacheIsValid(ccache)
    requires CDependencyIsValid(deps)
    requires CICacheValid(icache)
    requires CCCacheValid(ccache)
    requires forall k: int {:trigger k in ccache} {:trigger k in icache} {:trigger k in Keys_domain} :: (k in Keys_domain ==> k in icache) && (k in Keys_domain ==> k in ccache)
    requires forall k: int {:trigger k in icache} {:trigger k in ccache} :: k in ccache ==> k in icache
    requires CDependencyValid(deps)
    ensures CICacheValid(icache')
    ensures var (lr0: ICache, lr1: CCache) := PullDeps3(AbstractifyCICacheToICache(icache), AbstractifyCCCacheToCCache(ccache), AbstractifyCDependencyToDependency(deps)); CICacheIsValid(icache') && CCCacheIsValid(ccache') && (AbstractifyCICacheToICache(icache'), AbstractifyCCCacheToCCache(ccache')) == (lr0, lr1)
    ensures forall k: int {:trigger ccache'[k]} {:trigger deps[k]} {:trigger k in ccache'} {:trigger k in deps} :: (k in deps ==> k in ccache') && (k in deps ==> CVCEq(deps[k], ccache'[k].vc) || CVCHappendsBefore(deps[k], ccache'[k].vc))
    ensures forall k: int {:trigger ccache'[k]} {:trigger ccache[k]} {:trigger k in ccache'} {:trigger k in ccache} :: (k in ccache ==> k in ccache') && (k in ccache ==> CVCEq(ccache[k].vc, ccache'[k].vc) || CVCHappendsBefore(ccache[k].vc, ccache'[k].vc))
    decreases icache, ccache, deps
  {
    ghost var gicache := AbstractifyCICacheToICache(icache);
    ghost var gccache := AbstractifyCCCacheToCCache(ccache);
    ghost var gdeps := AbstractifyCDependencyToDependency(deps);
    ghost var (gicache', gccache') := PullDeps3(gicache, gccache, gdeps);
    ghost var domain := icache.Keys + deps.Keys;
    ghost var gdomain := gicache.Keys + gdeps.Keys;
    assert gdomain == domain;
    var new_icache, todos := CGetMetasOfAllDeps3(icache, deps, map[], domain);
    ghost var gtodos := GetMetasOfAllDeps(gicache, gdeps, map[], gdomain);
    lemma_CGetMetasOfAllDeps(icache, deps, map[], domain, todos);
    assert forall k: int {:trigger todos[k]} {:trigger deps[k]} {:trigger k in todos} {:trigger k in deps} :: (k in deps ==> k in todos) && (k in deps ==> CVCEq(deps[k], todos[k]));
    assert AbstractifyMap(todos, AbstractifyCKeyToKey, AbstractifyCVectorClockToVectorClock, AbstractifyCKeyToKey) == gtodos;
    var new_cache := CMergeVCIntoCCache(ccache, todos);
    lemma_CMergeVCIntoCCache(ccache, todos);
    assert forall k: int {:trigger new_cache[k]} {:trigger todos[k]} {:trigger k in new_cache} {:trigger k in todos} :: (k in todos ==> k in new_cache) && (k in todos ==> CVCEq(todos[k], new_cache[k].vc) || CVCHappendsBefore(todos[k], new_cache[k].vc));
    assert forall k: int {:trigger new_cache[k]} {:trigger deps[k]} {:trigger k in new_cache} {:trigger k in deps} :: (k in deps ==> k in new_cache) && (k in deps ==> CVCEq(deps[k], new_cache[k].vc) || CVCHappendsBefore(deps[k], new_cache[k].vc));
    assert forall k: int {:trigger new_cache[k]} {:trigger ccache[k]} {:trigger k in new_cache} {:trigger k in ccache} :: (k in ccache ==> k in new_cache) && (k in ccache ==> CVCEq(ccache[k].vc, new_cache[k].vc) || CVCHappendsBefore(ccache[k].vc, new_cache[k].vc));
    gccache' := MergeVCIntoCCache(gccache, gtodos);
    assert CCCacheValid(new_cache);
    icache' := new_icache;
    ccache' := new_cache;
    assert CCCacheValid(ccache');
    assert CICacheIsValid(icache');
    assert CCCacheIsValid(ccache');
    lemma_CPullDeps3(icache, new_icache, ccache', gccache');
    assert AbstractifyCICacheToICache(icache') == gicache';
    assert AbstractifyCCCacheToCCache(ccache') == gccache';
  }

  lemma {:axiom} lemma_CPullDeps3(icache: CICache, icache': CICache, ccache: CCCache, ccache': CCache)
    ensures icache == icache'
    ensures AbstractifyCCCacheToCCache(ccache) == ccache'
    decreases icache, icache', ccache, ccache'

  lemma {:axiom} lemma_CGetMetasOfAllDeps(icache: CICache, deps: CDependency, todos: map<CKey, CVectorClock>, domain: set<CKey>, res: map<CKey, CVectorClock>)
    requires CICacheIsValid(icache)
    requires CDependencyIsValid(deps)
    requires forall i: int {:trigger todos[i]} {:trigger i in todos} :: i in todos ==> CVectorClockIsValid(todos[i])
    requires forall k: int {:trigger icache[k]} {:trigger k in Keys_domain} {:trigger k in icache} :: (k in icache ==> k in Keys_domain) && (k in icache ==> forall m: CMeta {:trigger m.deps} {:trigger m.key} {:trigger CMetaValid(m)} {:trigger m in icache[k]} :: (m in icache[k] ==> CMetaValid(m)) && (m in icache[k] ==> m.key == k) && (m in icache[k] ==> forall kk: int {:trigger kk in Keys_domain} {:trigger kk in domain} {:trigger kk in m.deps} :: (kk in m.deps ==> kk in domain) && (kk in m.deps ==> kk in Keys_domain)))
    requires CDependencyValid(deps)
    requires forall k: int {:trigger k in Keys_domain} {:trigger todos[k]} {:trigger k in todos} :: (k in todos ==> CVectorClockValid(todos[k])) && (k in todos ==> k in Keys_domain)
    requires forall k: int {:trigger k in icache} {:trigger k in Keys_domain} :: k in Keys_domain ==> k in icache
    requires forall k: int {:trigger k in domain} {:trigger k in deps} :: k in deps ==> k in domain
    requires forall k: int {:trigger res[k]} {:trigger k in Keys_domain} {:trigger k in res} :: (k in res ==> k in Keys_domain) && (k in res ==> CVectorClockValid(res[k]))
    requires forall i: int {:trigger res[i]} {:trigger i in res} :: i in res ==> CVectorClockIsValid(res[i])
    ensures CICacheValid(icache)
    ensures forall k: int {:trigger todos[k]} {:trigger deps[k]} {:trigger k in todos} {:trigger k in deps} :: (k in deps ==> k in todos) && (k in deps ==> CVCEq(deps[k], todos[k]))
    ensures AbstractifyMap(res, AbstractifyCKeyToKey, AbstractifyCVectorClockToVectorClock, AbstractifyCKeyToKey) == GetMetasOfAllDeps(AbstractifyCICacheToICache(icache), AbstractifyCDependencyToDependency(deps), map[], AbstractifyCICacheToICache(icache).Keys + AbstractifyCDependencyToDependency(deps).Keys)
    decreases icache, deps, todos, domain, res

  function method CAdvanceVC(vc: CVectorClock, i: int): CVectorClock
    requires CVectorClockIsValid(vc)
    requires CVectorClockValid(vc)
    requires 0 <= i && i < Nodes
    ensures var res: CVectorClock := CAdvanceVC(vc, i); CVectorClockValid(res)
    ensures var lr: VectorClock := AdvanceVC(AbstractifyCVectorClockToVectorClock(vc), i); var cr: CVectorClock := CAdvanceVC(vc, i); CVectorClockIsValid(cr) && AbstractifyCVectorClockToVectorClock(cr) == lr
    decreases vc, i
  {
    vc[i := vc[i] + 1]
  }

  predicate CServerIsValid(s: CServer)
    decreases s
  {
    CServerIsAbstractable(s) &&
    CVectorClockIsValid(s.gvc) &&
    CICacheIsValid(s.icache) &&
    CCCacheIsValid(s.ccache) &&
    EndPointIsValid(s.endpoint) &&
    EndPointIsValid(s.next_endpoint)
  }

  predicate CServerIsAbstractable(s: CServer)
    decreases s
  {
    CVectorClockIsAbstractable(s.gvc) &&
    CCCacheIsAbstractable(s.ccache)
  }

  function AbstractifyCServerToServer(s: CServer): Server
    decreases s
  {
    Server(s.id, AbstractifyCVectorClockToVectorClock(s.gvc), s.next, AbstractifyCICacheToICache(s.icache), AbstractifyCCCacheToCCache(s.ccache))
  }

  function CServerValid(s: CServer): bool
    requires CServerIsValid(s)
    ensures ghost var lr: bool := ServerValid(AbstractifyCServerToServer(s)); ghost var cr: bool := CServerValid(s); cr == lr
    decreases s
  {
    0 <= s.id &&
    s.id < Nodes &&
    0 <= s.next &&
    s.next < Nodes &&
    s.next == CCircle(s.id, Nodes) &&
    CVectorClockValid(s.gvc) &&
    CICacheValid(s.icache) &&
    CCCacheValid(s.ccache) &&
    (forall k: int {:trigger k in s.ccache} {:trigger k in s.icache} {:trigger k in Keys_domain} :: 
      (k in Keys_domain ==>
        k in s.icache) &&
      (k in Keys_domain ==>
        k in s.ccache)) &&
    forall k: int {:trigger k in s.icache} {:trigger k in s.ccache} :: 
      k in s.ccache ==>
        k in s.icache
  }

  function method CInitICache(): CICache
    ensures var lr: ICache := InitICache(); var cr: CICache := CInitICache(); CICacheIsValid(cr) && AbstractifyCICacheToICache(cr) == lr
  {
    map[]
  }

  function method CInitCCache(): CCCache
    ensures var lr: CCache := InitCCache(); var cr: CCCache := CInitCCache(); CCCacheIsValid(cr) && AbstractifyCCCacheToCCache(cr) == lr
  {
    map[]
  }

  function method CServerInit(id: int, endpoints: seq<EndPoint>): CServer
    requires 0 <= id && id < Nodes
    requires |endpoints| == Nodes
    requires forall e: EndPoint {:trigger EndPointIsValid(e)} {:trigger e in endpoints} :: e in endpoints ==> EndPointIsValid(e)
    ensures var s: CServer := CServerInit(id, endpoints); CServerIsValid(s) && ServerInit(AbstractifyCServerToServer(s), id)
    decreases id, endpoints
  {
    var t1: int := id;
    var t2: int := CCircle(id, Nodes);
    var t3: CVectorClock := CEmptyVC();
    var t4: CICache := CInitICache();
    var t5: CCCache := CInitCCache();
    var end: EndPoint := endpoints[id];
    var next_end: EndPoint := endpoints[t2];
    CServer(t1, end, t3, t2, next_end, t4, t5)
  }

  lemma {:axiom} lemma_AbstractifyEndpointToID(e: EndPoint, id: int)
    ensures AbstractifyEndPointToID(e) == id
    decreases e, id
}

module CausalMesh_CPullDeps_i {

  import opened CausalMesh_CTypes_i

  import opened CausalMesh_PullDeps_i

  import opened GenericRefinement_i

  import opened Collections__Maps2_i

  import opened Collections__Maps_i

  import opened CausalMesh_Types_i
  function method CAddMetaToMetaMap(todos: map<CKey, CVectorClock>, m: CMeta): map<CKey, CVectorClock>
    requires forall i: int {:trigger todos[i]} {:trigger i in todos} :: i in todos ==> CVectorClockIsValid(todos[i])
    requires CMetaIsValid(m)
    requires forall k: int {:trigger todos[k]} {:trigger k in todos} :: k in todos ==> CVectorClockValid(todos[k])
    requires CMetaValid(m)
    ensures var res: map<CKey, CVectorClock> := CAddMetaToMetaMap(todos, m); m.key in res && forall k: int {:trigger res[k]} {:trigger k in res} :: k in res ==> CVectorClockValid(res[k])
    ensures var lr: map<Key, VectorClock> := AddMetaToMetaMap(map k: int {:trigger todos[k]} | k in set ck: int {:trigger ck in todos} | ck in todos :: AbstractifyCVectorClockToVectorClock(todos[k]), AbstractifyCMetaToMeta(m)); var cr: map<CKey, CVectorClock> := CAddMetaToMetaMap(todos, m); (forall i: int {:trigger cr[i]} {:trigger i in cr} :: i in cr ==> CVectorClockValid(cr[i])) && (map k: int {:trigger cr[k]} | k in set ck: int {:trigger ck in cr} | ck in cr :: AbstractifyCVectorClockToVectorClock(cr[k])) == lr
    decreases todos, m
  {
    if m.key in todos then
      todos[m.key := CVCMerge(todos[m.key], m.vc)]
    else
      todos[m.key := m.vc]
  }

  method CGetMetasOfAllDeps3(icache: CICache, deps: CDependency, todos: map<CKey, CVectorClock>, ghost domain: set<CKey>)
      returns (icache': CICache, res: map<CKey, CVectorClock>)
    requires CDependencyIsValid(deps)
    requires forall i: int {:trigger todos[i]} {:trigger i in todos} :: i in todos ==> CVectorClockIsValid(todos[i])
    requires forall k: int {:trigger icache[k]} {:trigger k in Keys_domain} {:trigger k in icache} :: (k in icache ==> k in Keys_domain) && (k in icache ==> forall m: CMeta {:trigger m.deps} {:trigger m.key} {:trigger CMetaValid(m)} {:trigger m in icache[k]} :: (m in icache[k] ==> CMetaValid(m)) && (m in icache[k] ==> m.key == k) && (m in icache[k] ==> forall kk: int {:trigger kk in Keys_domain} {:trigger kk in domain} {:trigger kk in m.deps} :: (kk in m.deps ==> kk in domain) && (kk in m.deps ==> kk in Keys_domain)))
    requires CDependencyValid(deps)
    requires forall k: int {:trigger k in Keys_domain} {:trigger todos[k]} {:trigger k in todos} :: (k in todos ==> CVectorClockValid(todos[k])) && (k in todos ==> k in Keys_domain)
    requires forall k: int {:trigger k in domain} {:trigger k in deps} :: k in deps ==> k in domain
    ensures forall k: int {:trigger res[k]} {:trigger k in Keys_domain} {:trigger k in res} :: (k in res ==> k in Keys_domain) && (k in res ==> CVectorClockValid(res[k]))
    ensures forall i: int {:trigger res[i]} {:trigger i in res} :: i in res ==> CVectorClockIsValid(res[i])
    ensures forall k: int {:trigger icache'[k]} {:trigger k in Keys_domain} {:trigger k in icache'} :: (k in icache' ==> k in Keys_domain) && (k in icache' ==> forall m: CMeta {:trigger m.deps} {:trigger m.key} {:trigger CMetaValid(m)} {:trigger m in icache'[k]} :: (m in icache'[k] ==> CMetaValid(m)) && (m in icache'[k] ==> m.key == k) && (m in icache'[k] ==> forall kk: int {:trigger kk in Keys_domain} {:trigger kk in domain} {:trigger kk in m.deps} :: (kk in m.deps ==> kk in domain) && (kk in m.deps ==> kk in Keys_domain)))
    ensures |icache'.Values| <= |icache.Values|
    decreases |icache.Values|, |deps|
  {
    if |deps| == 0 {
      icache' := icache;
      res := todos;
      assert forall k: int {:trigger res[k]} {:trigger k in Keys_domain} {:trigger k in res} :: (k in res ==> k in Keys_domain) && (k in res ==> CVectorClockValid(res[k]));
    } else {
      var k :| k in deps;
      var new_deps := RemoveElt(deps, k);
      if k in todos && (CVCHappendsBefore(deps[k], todos[k]) || CVCEq(deps[k], todos[k])) {
        icache', res := CGetMetasOfAllDeps3(icache, new_deps, todos, domain);
      } else if k in icache {
        assert forall k: int {:trigger icache[k]} {:trigger k in Keys_domain} {:trigger k in icache} :: (k in icache ==> k in Keys_domain) && (k in icache ==> forall m: CMeta {:trigger m.deps} {:trigger m.key} {:trigger CMetaValid(m)} {:trigger m in icache[k]} :: (m in icache[k] ==> CMetaValid(m)) && (m in icache[k] ==> m.key == k) && (m in icache[k] ==> forall kk: int {:trigger kk in Keys_domain} {:trigger kk in domain} {:trigger kk in m.deps} :: (kk in m.deps ==> kk in domain) && (kk in m.deps ==> kk in Keys_domain)));
        var metas := set m: CMeta {:trigger m.vc} {:trigger m in icache[k]} | m in icache[k] && (CVCHappendsBefore(m.vc, deps[k]) || CVCEq(m.vc, deps[k]));
        if |metas| > 0 {
          res := todos;
          var initial := CEmptyMeta(k);
          assert forall m: CMeta {:trigger CMetaValid(m)} {:trigger m in metas} :: m in metas ==> CMetaValid(m);
          var merged := CFoldMetaSet(initial, metas, domain);
          var meta := merged.(vc := deps[k]);
          var new_cache := icache[k := icache[k] - metas];
          assert icache[k] >= metas;
          lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas);
          assert |new_cache.Values| < |icache.Values|;
          assert forall k: int {:trigger k in domain} {:trigger k in merged.deps} :: k in merged.deps ==> k in domain;
          var new_icache', res' := CGetMetasOfAllDeps3(new_cache, merged.deps, todos, domain);
          assert forall k: int {:trigger res'[k]} {:trigger k in Keys_domain} {:trigger k in res'} :: (k in res' ==> k in Keys_domain) && (k in res' ==> CVectorClockValid(res'[k]));
          var todos' := CAddMetaToMetaMap(res', meta);
          assert |new_icache'.Values| <= |new_cache.Values|;
          icache', res := CGetMetasOfAllDeps3(new_icache', new_deps, todos', domain);
        } else {
          var initial := CEmptyMeta(k);
          var meta := initial.(vc := deps[k]);
          var todos' := CAddMetaToMetaMap(todos, meta);
          icache', res := CGetMetasOfAllDeps3(icache, new_deps, todos', domain);
          assert forall k: int {:trigger res[k]} {:trigger k in res} :: k in res ==> CVectorClockValid(res[k]);
        }
      } else {
        var initial := CEmptyMeta(k);
        var meta := initial.(vc := deps[k]);
        var todos' := CAddMetaToMetaMap(todos, meta);
        icache', res := CGetMetasOfAllDeps3(icache, new_deps, todos', domain);
        assert forall k: int {:trigger res[k]} {:trigger k in res} :: k in res ==> CVectorClockValid(res[k]);
      }
    }
  }
}

module CausalMesh_PullDeps_i {

  import opened Collections__Maps_i

  import opened CausalMesh_Types_i

  import opened CausalMesh_Message_i

  import opened Collections__Maps2_i
  function AddMetaToMetaMap(todos: map<Key, VectorClock>, m: Meta): (res: map<Key, VectorClock>)
    requires forall k: int {:trigger todos[k]} {:trigger k in todos} :: k in todos ==> VectorClockValid(todos[k])
    requires MetaValid(m)
    ensures m.key in res
    ensures forall k: int {:trigger res[k]} {:trigger k in res} :: k in res ==> VectorClockValid(res[k])
    decreases todos, m
  {
    if m.key in todos then
      todos[m.key := VCMerge(todos[m.key], m.vc)]
    else
      todos[m.key := m.vc]
  }

  function GetMetasOfAllDeps(icache: ICache, deps: Dependency, todos: map<Key, VectorClock>, domain: set<Key>): map<Key, VectorClock>
    requires forall k: int {:trigger icache[k]} {:trigger k in Keys_domain} {:trigger k in icache} :: (k in icache ==> k in Keys_domain) && (k in icache ==> forall m: Meta {:trigger m.deps} {:trigger m.key} {:trigger MetaValid(m)} {:trigger m in icache[k]} :: (m in icache[k] ==> MetaValid(m)) && (m in icache[k] ==> m.key == k) && (m in icache[k] ==> forall kk: int {:trigger kk in Keys_domain} {:trigger kk in domain} {:trigger kk in m.deps} :: (kk in m.deps ==> kk in domain) && (kk in m.deps ==> kk in Keys_domain)))
    requires DependencyValid(deps)
    requires forall k: int {:trigger k in Keys_domain} {:trigger todos[k]} {:trigger k in todos} :: (k in todos ==> VectorClockValid(todos[k])) && (k in todos ==> k in Keys_domain)
    requires forall k: int {:trigger k in icache} {:trigger k in Keys_domain} :: k in Keys_domain ==> k in icache
    requires forall k: int {:trigger k in domain} {:trigger k in deps} :: k in deps ==> k in domain
    ensures ghost var res: map<Key, VectorClock> := GetMetasOfAllDeps(icache, deps, todos, domain); forall k: int {:trigger k in Keys_domain} {:trigger res[k]} {:trigger k in res} :: (k in res ==> VectorClockValid(res[k])) && (k in res ==> k in Keys_domain)
    decreases |icache.Values|, |deps|
  {
    if |deps| == 0 then
      todos
    else
      ghost var k: int :| k in deps; ghost var new_deps: map<int, VectorClock> := RemoveElt(deps, k); if k in todos && (VCHappendsBefore(deps[k], todos[k]) || VCEq(deps[k], todos[k])) then ghost var res: map<Key, VectorClock> := GetMetasOfAllDeps(icache, new_deps, todos, domain); res else ghost var metas: set<Meta> := set m: Meta {:trigger m.vc} {:trigger m in icache[k]} | m in icache[k] && (VCHappendsBefore(m.vc, deps[k]) || VCEq(m.vc, deps[k])); if |metas| > 0 then ghost var initial: Meta := EmptyMeta(k); ghost var merged: Meta := FoldMetaSet(initial, metas, domain); ghost var meta: Meta := merged.(vc := deps[k]); ghost var new_cache: map<Key, set<Meta>> := icache[k := icache[k] - metas]; assert icache[k] >= metas; lemma_MapRemoveSubsetOfTheValOfKey(icache, k, metas); assert |new_cache.Values| < |icache.Values|; assert forall k: int {:trigger k in domain} {:trigger k in merged.deps} :: k in merged.deps ==> k in domain; ghost var res: map<Key, VectorClock> := GetMetasOfAllDeps(new_cache, merged.deps, todos, domain); ghost var todos': map<Key, VectorClock> := AddMetaToMetaMap(res, meta); ghost var res': map<Key, VectorClock> := GetMetasOfAllDeps(icache, new_deps, todos', domain); res' else ghost var initial: Meta := EmptyMeta(k); ghost var meta: Meta := initial.(vc := deps[k]); ghost var todos': map<Key, VectorClock> := AddMetaToMetaMap(todos, meta); ghost var res: map<Key, VectorClock> := GetMetasOfAllDeps(icache, new_deps, todos', domain); res
  }

  lemma {:axiom} lemma_MapRemoveSubsetOfTheValOfKey<K, V>(m: map<K, set<V>>, k: K, s: set<V>)
    requires k in m && m[k] >= s
    ensures |m.Values| > |m[k := m[k] - s].Values|
    decreases m, s
}

module Collections__Maps2_i {

  import opened Collections__Maps2_s
  type imap2<!K1, !K2, V> = imap<K1, imap<K2, V>>

  function maprange<KT, VT>(m: map<KT, VT>): set<VT>
    decreases m
  {
    set k: KT {:trigger m[k]} {:trigger k in m} | k in m :: m[k]
  }

  predicate imap2total<K1(!new), K2(!new), V>(m: imap2<K1, K2, V>)
  {
    imaptotal(m) &&
    forall k1: K1 {:trigger m[k1]} :: 
      imaptotal(m[k1])
  }

  predicate imaptotal_(f: imap<int, int>)
  {
    imaptotal(f)
  }

  predicate monotonic(f: imap<int, int>)
  {
    forall i1: int, i2: int {:trigger f[i2], f[i1]} {:trigger f[i2], i1 in f} {:trigger f[i1], i2 in f} {:trigger i2 in f, i1 in f} :: 
      i1 in f &&
      i2 in f &&
      i1 <= i2 ==>
        f[i1] <= f[i2]
  }

  predicate monotonic_from(start: int, f: imap<int, int>)
    decreases start
  {
    forall i1: int, i2: int {:trigger f[i2], f[i1]} {:trigger f[i2], i1 in f} {:trigger f[i1], i2 in f} {:trigger i2 in f, i1 in f} :: 
      i1 in f &&
      i2 in f &&
      start <= i1 <= i2 ==>
        f[i1] <= f[i2]
  }

  predicate behaviorMonotonic<S>(b: imap<int, S>, f: imap<S, int>)
    requires imaptotal(b)
    requires imaptotal(f)
  {
    forall i1: int, i2: int {:trigger b[i2], b[i1]} :: 
      i1 <= i2 ==>
        f[b[i1]] <= f[b[i2]]
  }

  lemma Lemma_EqualityConditionForMapsWithSameDomain<S, T>(m1: map<S, T>, m2: map<S, T>)
    requires mapdomain(m1) == mapdomain(m2)
    requires forall s: S {:trigger m2[s]} {:trigger m1[s]} {:trigger s in m2} {:trigger s in m1} :: s in m1 && s in m2 ==> m1[s] == m2[s]
    ensures m1 == m2
    decreases m1, m2
  {
  }

  lemma Lemma_imap2equiv<K1, K2, V>(f: imap2<K1, K2, V>, g: imap2<K1, K2, V>)
    requires forall k1: K1 {:trigger k1 in g} {:trigger k1 in f} :: k1 in f <==> k1 in g
    requires forall k1: K1 {:trigger g[k1]} {:trigger f[k1]} {:trigger k1 in f} :: k1 in f ==> f[k1] == g[k1]
    ensures f == g
  {
  }

  predicate TLe(i: int, j: int)
    decreases i, j
  {
    i <= j
  }

  lemma Lemma_imapInductionRange(start: int, end: int, f: imap<int, bool>)
    requires TLe(start, end)
    requires forall i: int {:trigger i in f} {:trigger TLe(i, end)} {:trigger TLe(start, i)} :: TLe(start, i) && TLe(i, end) ==> i in f
    requires forall i: int, _t#0: int {:trigger f[_t#0], f[i]} {:trigger f[_t#0], TLe(start, i)} {:trigger f[i], TLe(_t#0, end)} {:trigger TLe(_t#0, end), TLe(start, i)} | _t#0 == i + 1 :: TLe(start, i) && TLe(_t#0, end) && f[i] ==> f[_t#0]
    requires f[start]
    ensures f[end]
    decreases end - start
  {
  }
}

module CausalMesh_Cache_i {

  import opened Collections__Maps_i

  import opened CausalMesh_Types_i

  import opened CausalMesh_Message_i

  import opened CausalMesh_Properties_i

  import opened CausalMesh_PullDeps_i

  import opened Environment_s
  datatype Server = Server(id: int, gvc: VectorClock, next: int, icache: ICache, ccache: CCache)

  datatype Client = Client(id: int, opn: int, local: map<Key, Meta>, deps: Dependency)

  function Circle(id: int, nodes: int): (i: int)
    requires 0 <= id < nodes
    ensures 0 <= i < nodes
    decreases id, nodes
  {
    if nodes == 1 then
      id
    else if id == nodes - 1 then
      0
    else
      id + 1
  }

  function InsertIntoCCache(c: CCache, m: Meta): CCache
    requires CCacheValid(c)
    requires MetaValid(m)
    decreases c, m
  {
    if m.key in c then
      c[m.key := MetaMerge(c[m.key], m)]
    else
      c[m.key := m]
  }

  function AddMetaToICache(c: ICache, m: Meta): ICache
    requires ICacheValid(c)
    requires MetaValid(m)
    requires forall k: int {:trigger k in c} {:trigger k in m.deps} :: k in m.deps ==> k in c
    decreases c, m
  {
    if m.key in c then
      c[m.key := c[m.key] + {m}]
    else
      c[m.key := {m}]
  }

  function AddMetasToICache(c: ICache, metas: set<Meta>): ICache
    requires ICacheValid(c)
    requires forall m: Meta {:trigger m.deps} {:trigger MetaValid(m)} {:trigger m in metas} :: (m in metas ==> MetaValid(m)) && (m in metas ==> forall k: int {:trigger k in c} {:trigger k in m.deps} :: k in m.deps ==> k in c)
    decreases |metas|
  {
    if |metas| == 0 then
      c
    else
      ghost var m: Meta :| m in metas; ghost var new_metas: set<Meta> := metas - {m}; AddMetasToICache(AddMetaToICache(c, m), new_metas)
  }

  function PullDeps3(icache: ICache, ccache: CCache, deps: Dependency): (c: (ICache, CCache))
    requires ICacheValid(icache)
    requires CCacheValid(ccache)
    requires forall k: int {:trigger k in ccache} {:trigger k in icache} {:trigger k in Keys_domain} :: (k in Keys_domain ==> k in icache) && (k in Keys_domain ==> k in ccache)
    requires forall k: int {:trigger k in icache} {:trigger k in ccache} :: k in ccache ==> k in icache
    requires DependencyValid(deps)
    requires forall k: int {:trigger k in icache} {:trigger k in deps} :: k in deps ==> k in icache
    ensures ICacheValid(c.0)
    ensures CCacheValid(c.1)
    ensures forall k: int {:trigger k in c.0} {:trigger k in icache} :: k in icache ==> k in c.0
    ensures forall k: int {:trigger k in c.1} {:trigger k in ccache} :: k in ccache ==> k in c.1
    decreases icache, ccache, deps
  {
    ghost var domain: set<Key> := icache.Keys + deps.Keys;
    ghost var todos: map<Key, VectorClock> := GetMetasOfAllDeps(icache, deps, map[], domain);
    ghost var new_cache: CCache := MergeVCIntoCCache(ccache, todos);
    (icache, new_cache)
  }

  function AdvanceVC(vc: VectorClock, i: int): (res: VectorClock)
    requires VectorClockValid(vc)
    requires 0 <= i < Nodes
    ensures VectorClockValid(res)
    decreases vc, i
  {
    vc[i := vc[i] + 1]
  }

  predicate ServerValid(s: Server)
    decreases s
  {
    0 <= s.id < Nodes &&
    0 <= s.next < Nodes &&
    s.next == Circle(s.id, Nodes) &&
    VectorClockValid(s.gvc) &&
    ICacheValid(s.icache) &&
    CCacheValid(s.ccache) &&
    (forall k: int {:trigger k in s.ccache} {:trigger k in s.icache} {:trigger k in Keys_domain} :: 
      (k in Keys_domain ==>
        k in s.icache) &&
      (k in Keys_domain ==>
        k in s.ccache)) &&
    forall k: int {:trigger k in s.icache} {:trigger k in s.ccache} :: 
      k in s.ccache ==>
        k in s.icache
  }

  function InitICache(): ICache
  {
    map[]
  }

  function InitCCache(): CCache
  {
    map[]
  }

  predicate ServerInit(s: Server, id: int)
    requires 0 <= id < Nodes
    decreases s, id
  {
    s.id == id &&
    s.next == Circle(id, Nodes) &&
    s.gvc == EmptyVC() &&
    s.icache == InitICache() &&
    s.ccache == InitCCache()
  }

  predicate ReceiveRead(s: Server, s': Server, p: Packet, sp: seq<Packet>)
    requires p.msg.Message_Read?
    requires ServerValid(s)
    requires PacketValid(p)
    decreases s, s', p, sp
  {
    var (new_icache: ICache, new_ccache: CCache) := PullDeps3(s.icache, s.ccache, p.msg.deps_read);
    ghost var new_ccache': map<Key, Meta> := if p.msg.key_read !in new_ccache then new_ccache[p.msg.key_read := EmptyMeta(p.msg.key_read)] else new_ccache;
    s' == s.(icache := new_icache, ccache := new_ccache) &&
    sp == [LPacket(p.src, s.id, Message_Read_Reply(p.msg.opn_read, p.msg.key_read, new_ccache[p.msg.key_read].vc, map[]))]
  }

  predicate ReceiveWrite(s: Server, s': Server, p: Packet, sp: seq<Packet>)
    requires p.msg.Message_Write?
    requires ServerValid(s)
    requires PacketValid(p)
    decreases s, s', p, sp
  {
    assert forall k: int {:trigger p.msg.local[k]} {:trigger k in p.msg.local} :: k in p.msg.local ==> MetaValid(p.msg.local[k]);
    ghost var local_metas: set<Meta> := set m: Meta {:trigger m in p.msg.local.Values} | m in p.msg.local.Values;
    assert forall m: Meta {:trigger MetaValid(m)} {:trigger m in local_metas} :: m in local_metas ==> MetaValid(m);
    ghost var vcs_local: set<VectorClock> := set m: Meta {:trigger m.vc} {:trigger m in local_metas} | m in local_metas :: m.vc;
    assert forall vc: VectorClock {:trigger VectorClockValid(vc)} {:trigger vc in vcs_local} :: vc in vcs_local ==> VectorClockValid(vc);
    ghost var vcs_deps: set<seq<int>> := set k: int {:trigger p.msg.deps_write[k]} {:trigger k in p.msg.deps_write} | k in p.msg.deps_write :: p.msg.deps_write[k];
    ghost var merged_vc: VectorClock := FoldVC(s.gvc, vcs_local);
    ghost var merged_vc2: VectorClock := FoldVC(merged_vc, vcs_deps);
    ghost var new_vc: VectorClock := AdvanceVC(merged_vc2, s.id);
    ghost var merged_deps: Dependency := FoldDependencyFromMetaSet(p.msg.deps_write, local_metas);
    ghost var meta: Meta := Meta(p.msg.key_write, new_vc, merged_deps);
    ghost var new_local_metas: set<Meta> := local_metas + {meta};
    ghost var new_icache: ICache := AddMetasToICache(s.icache, new_local_metas);
    ghost var wreply: LPacket<int, Message> := LPacket(p.src, s.id, Message_Write_Reply(p.msg.opn_write, p.msg.key_write, new_vc));
    ghost var propagate: LPacket<int, Message> := LPacket(s.next, s.id, Message_Propagation(p.msg.key_write, meta, s.id, 1));
    s' == s.(gvc := new_vc, icache := new_icache) &&
    sp == [wreply] + [propagate]
  }

  predicate ReceivePropagate(s: Server, s': Server, p: Packet, sp: seq<Packet>)
    requires p.msg.Message_Propagation?
    requires ServerValid(s)
    requires PacketValid(p)
    decreases s, s', p, sp
  {
    if s.next == p.msg.start then
      if p.msg.round == 2 then
        ghost var vcs: VectorClock := p.msg.meta.vc;
        ghost var new_gvc: VectorClock := VCMerge(s.gvc, vcs);
        ghost var new_deps: Dependency := p.msg.meta.deps;
        var (new_icache: ICache, new_ccache: CCache) := PullDeps3(s.icache, s.ccache, new_deps);
        ghost var new_ccache': CCache := InsertIntoCCache(new_ccache, p.msg.meta);
        ghost var new_icache': ICache := AddMetaToICache(new_icache, p.msg.meta);
        s' == s.(gvc := new_gvc, icache := new_icache', ccache := new_ccache') &&
        sp == []
      else
        ghost var new_icache: ICache := AddMetaToICache(s.icache, p.msg.meta); s' == s.(icache := new_icache) && sp == [LPacket(s.next, s.id, p.msg.(round := 2))]
    else
      ghost var new_icache: ICache := AddMetaToICache(s.icache, p.msg.meta); s' == s.(icache := new_icache) && sp == [LPacket(s.next, s.id, p.msg)]
  }

  predicate ClientValid(c: Client)
    decreases c
  {
    Nodes <= c.id < Nodes + Clients &&
    (forall k: int {:trigger c.local[k]} {:trigger k in Keys_domain} {:trigger k in c.local} :: 
      (k in c.local ==>
        k in Keys_domain) &&
      (k in c.local ==>
        MetaValid(c.local[k])) &&
      (k in c.local ==>
        c.local[k].key == k)) &&
    DependencyValid(c.deps)
  }

  predicate ClientInit(c: Client, id: int)
    requires Nodes <= id < Nodes + Clients
    decreases c, id
  {
    c.opn == 0 &&
    c.id == id &&
    c.local == map[] &&
    c.deps == map[]
  }

  predicate SendRead(c: Client, c': Client, sp: seq<Packet>)
    requires ClientValid(c)
    decreases c, c', sp
  {
    ghost var k: int :| 0 <= k < MaxKeys as int;
    if k in c.local then
      c' == c.(opn := c.opn + 1) &&
      sp == []
    else
      ghost var server: int :| 0 <= server < Nodes as int; c' == c.(opn := c.opn + 1) && sp == [LPacket(c.id, server, Message_Read(c.opn, k, c.deps))]
  }

  predicate ReceiveReadReply(c: Client, c': Client, p: Packet, sp: seq<Packet>)
    requires ClientValid(c)
    requires p.msg.Message_Read_Reply?
    requires PacketValid(p)
    decreases c, c', p, sp
  {
    ghost var m: Meta := Meta(p.msg.key_rreply, p.msg.vc_rreply, p.msg.deps_rreply);
    c' == c.(deps := DependencyInsertOrMerge(c.deps, p.msg.key_rreply, p.msg.vc_rreply)) &&
    sp == []
  }

  predicate SendWrite(c: Client, c': Client, sp: seq<Packet>)
    decreases c, c', sp
  {
    ghost var k: int :| 0 <= k < MaxKeys as int;
    ghost var server: int :| 0 <= server < Nodes as int;
    c' == c.(opn := c.opn + 1) &&
    sp == [LPacket(c.id, server, Message_Write(c.opn + 1, k, c.deps, c.local))]
  }

  predicate ReceiveWriteReply(c: Client, c': Client, p: Packet, sp: seq<Packet>)
    requires ClientValid(c)
    requires p.msg.Message_Write_Reply?
    requires PacketValid(p)
    decreases c, c', p, sp
  {
    ghost var k: Key := p.msg.key_wreply;
    ghost var vc: VectorClock := p.msg.vc_wreply;
    ghost var m: Meta := Meta(k, vc, c.deps);
    c' == c.(local := c.local[k := m]) &&
    sp == []
  }
}

module CausalMesh_Properties_i {

  import opened Collections__Maps_i

  import opened CausalMesh_Types_i

  import opened CausalMesh_Message_i
  predicate CausalCut(ccache: CCache)
    requires forall k: int {:trigger ccache[k]} {:trigger k in ccache} :: k in ccache ==> MetaValid(ccache[k])
    decreases ccache
  {
    forall k: int {:trigger ccache[k]} {:trigger k in ccache} :: 
      k in ccache ==>
        forall kk: int {:trigger ccache[kk]} {:trigger ccache[k].deps[kk]} {:trigger kk in ccache} {:trigger kk in ccache[k].deps} :: 
          (kk in ccache[k].deps ==>
            kk in ccache) &&
          (kk in ccache[k].deps ==>
            VCHappendsBefore(ccache[k].deps[kk], ccache[kk].vc) || VCEq(ccache[k].deps[kk], ccache[kk].vc))
  }

  predicate ReadsDepsAreMet2(icache: ICache, ccache: CCache, deps: Dependency)
    requires ICacheValid(icache)
    requires CCacheValid(ccache)
    requires forall k: int {:trigger k in ccache} {:trigger k in icache} {:trigger k in Keys_domain} :: (k in Keys_domain ==> k in icache) && (k in Keys_domain ==> k in ccache)
    requires DependencyValid(deps)
    decreases icache, ccache, deps
  {
    forall k: int {:trigger icache[k]} {:trigger ccache[k]} {:trigger deps[k]} {:trigger k in deps} :: 
      k in deps ==>
        ghost var m: Meta := FoldMetaSet(ccache[k], icache[k], icache.Keys); VCEq(deps[k], m.vc) || VCHappendsBefore(deps[k], m.vc)
  }

  predicate ReadsDepsAreMet(icache: ICache, ccache: CCache, deps: Dependency)
    requires ICacheValid(icache)
    requires CCacheValid(ccache)
    requires forall k: int {:trigger k in ccache} {:trigger k in icache} {:trigger k in Keys_domain} :: (k in Keys_domain ==> k in icache) && (k in Keys_domain ==> k in ccache)
    requires DependencyValid(deps)
    decreases icache, ccache, deps
  {
    forall k: int {:trigger icache[k]} {:trigger ccache[k]} {:trigger deps[k]} {:trigger k in deps} :: 
      k in deps ==>
        VCEq(deps[k], ccache[k].vc) || VCHappendsBefore(deps[k], ccache[k].vc) || exists m: Meta {:trigger m.vc} {:trigger m in icache[k]} :: m in icache[k] && m.vc == deps[k]
  }

  predicate ReadsDepsAreMet1(icache: ICache, ccache: CCache, deps: map<Key, Meta>)
    requires ICacheValid(icache)
    requires CCacheValid(ccache)
    requires forall k: int {:trigger k in ccache} {:trigger k in icache} {:trigger k in Keys_domain} :: (k in Keys_domain ==> k in icache) && (k in Keys_domain ==> k in ccache)
    requires forall k: int {:trigger deps[k]} {:trigger k in Keys_domain} {:trigger k in deps} :: (k in deps ==> k in Keys_domain) && (k in deps ==> MetaValid(deps[k]))
    decreases icache, ccache, deps
  {
    forall k: int {:trigger icache[k]} {:trigger ccache[k]} {:trigger deps[k]} {:trigger k in deps} :: 
      k in deps ==>
        VCEq(deps[k].vc, ccache[k].vc) || VCHappendsBefore(deps[k].vc, ccache[k].vc) || exists m: Meta {:trigger m.vc} {:trigger m in icache[k]} :: m in icache[k] && m.vc == deps[k].vc
  }

  predicate UponReadsDepsAreMet(ccache: CCache, deps: Dependency)
    requires CCacheValid(ccache)
    requires forall k: int {:trigger k in ccache} {:trigger k in deps} :: k in deps ==> k in ccache
    requires DependencyValid(deps)
    decreases ccache, deps
  {
    forall k: int {:trigger ccache[k]} {:trigger deps[k]} {:trigger k in deps} :: 
      k in deps ==>
        VCEq(deps[k], ccache[k].vc) || VCHappendsBefore(deps[k], ccache[k].vc)
  }

  predicate DepsAreMetInICache(icache: ICache, deps: Dependency)
    requires forall k: int {:trigger k in icache} {:trigger k in Keys_domain} :: k in Keys_domain ==> k in icache
    requires DependencyValid(deps)
    decreases icache, deps
  {
    forall k: int {:trigger deps[k]} {:trigger icache[k]} {:trigger k in deps} :: 
      k in deps ==>
        exists m: Meta {:trigger m.vc} {:trigger m in icache[k]} :: 
          m in icache[k] &&
          m.vc == deps[k]
  }

  predicate AllVersionsInCCacheAreMetInICache(icache: ICache, ccache: CCache)
    requires forall k: int {:trigger k in icache} {:trigger k in Keys_domain} :: k in Keys_domain ==> k in icache
    requires ICacheValid(icache)
    requires CCacheValid(ccache)
    decreases icache, ccache
  {
    (forall k: int {:trigger ccache[k]} {:trigger icache[k]} {:trigger k in ccache} :: 
      k in ccache ==>
        exists m: Meta {:trigger m.vc} {:trigger m in icache[k]} :: 
          m in icache[k] &&
          ccache[k].vc == m.vc) &&
    forall k: int {:trigger icache[k]} {:trigger ccache[k]} {:trigger k in ccache} :: 
      k in ccache ==>
        forall kk: int {:trigger ccache[k].deps[kk]} {:trigger kk in ccache[k].deps} :: 
          kk in ccache[k].deps ==>
            exists m: Meta {:trigger m.vc} {:trigger m in icache[k]} :: 
              m in icache[k] &&
              ccache[k].deps[kk] == m.vc
  }
}

module CausalMesh_CmdParser_i {

  import opened Native__Io_s

  import opened Native__NativeTypes_s

  import opened CmdLineParser_i

  import opened Common__UdpClient_i

  import opened Common__SeqIsUniqueDef_i

  import opened Common__NodeIdentity_i

  import opened Collections__Seqs_i

  import opened CausalMesh_CTypes_i

  import opened CausalMesh_Types_i
  function causalmesh_config_parsing(args: seq<seq<uint16>>): seq<EndPoint>
    decreases args
  {
    if args != [] && |args[1..]| % 2 == 0 then
      var (ok: bool, endpoints: seq<EndPoint>) := parse_end_points(args[1..]);
      endpoints
    else
      []
  }

  method parse_cmd_line(ghost env: HostEnvironment)
      returns (ok: bool, config: seq<EndPoint>, my_index: int)
    requires HostEnvironmentIsValid(env)
    ensures ok ==> 0 <= my_index as int < |config|
    ensures ok ==> |config| == Nodes
    ensures ok ==> forall ep: EndPoint {:trigger EndPointIsValidIPV4(ep)} {:trigger ep in config} :: ep in config ==> EndPointIsValidIPV4(ep)
    decreases env
  {
    ok := false;
    var num_args := HostConstants.NumCommandLineArgs(env);
    if num_args < 4 || num_args % 2 != 1 {
      print ""Incorrect number of command line arguments.\n"";
      print ""Expected: ./Main.exe [IP port]+ [IP port]\n"";
      print ""  where the final argument is one of the IP-port pairs provided earlier \n"";
      return;
    }
    var args := collect_cmd_line_args(env);
    assert args == env.constants.CommandLineArgs();
    var tuple1 := parse_end_points(args[1 .. |args| - 2]);
    ok := tuple1.0;
    var endpoints := tuple1.1;
    if !ok || |endpoints| >= 18446744073709551615 {
      ok := false;
      return;
    }
    var tuple2 := parse_end_point(args[|args| - 2], args[|args| - 1]);
    ok := tuple2.0;
    if !ok {
      return;
    }
    var unique := test_unique'(endpoints);
    if !unique {
      ok := false;
      return;
    }
    config := endpoints;
    my_index := FindIndexInSeq(config, tuple2.1);
    lemma_ConfigValid(config, my_index);
    ok := true;
    assert 0 <= my_index as int < |config|;
    assert |config| == Nodes;
  }

  lemma {:axiom} lemma_ConfigValid(config: seq<EndPoint>, my_index: int)
    ensures |config| == Nodes
    ensures 0 <= my_index as int < |config|
    decreases config, my_index
}

module CmdLineParser_i {

  import opened Native__Io_s

  import opened Native__NativeTypes_s

  import opened Math__power_s

  import opened Common__SeqIsUniqueDef_i

  import opened Common__UdpClient_i
  function method ascii_to_int(short: uint16): (bool, byte)
    ensures var tuple: (bool, byte) := ascii_to_int(short); tuple.0 ==> 0 <= tuple.1 <= 9
    decreases short
  {
    if 48 <= short <= 57 then
      (true, (short - 48) as byte)
    else
      (false, 0)
  }

  method power10(e: nat) returns (val: int)
    ensures val == power(10, e)
    decreases e
  {
    reveal power();
    if e == 0 {
      return 1;
    } else {
      var tmp := power10(e - 1);
      return 10 * tmp;
    }
  }

  function method shorts_to_bytes(shorts: seq<uint16>): (bool, seq<byte>)
    decreases shorts
  {
    if |shorts| == 0 then
      (true, [])
    else
      var tuple: (bool, seq<byte>) := shorts_to_bytes(shorts[1..]); var ok: bool, rest: seq<byte> := tuple.0, tuple.1; var tuple': (bool, byte) := ascii_to_int(shorts[0]); var ok': bool, a_byte: byte := tuple'.0, tuple'.1; if ok && ok' then (true, [a_byte] + rest) else (false, [])
  }

  function method bytes_to_decimal(bytes: seq<byte>): nat
    decreases bytes
  {
    if |bytes| == 0 then
      0
    else
      bytes[|bytes| - 1] as int + 10 * bytes_to_decimal(bytes[0 .. |bytes| - 1])
  }

  function method shorts_to_nat(shorts: seq<uint16>): (bool, int)
    decreases shorts
  {
    if |shorts| == 0 then
      (false, 0)
    else
      var tuple: (bool, seq<byte>) := shorts_to_bytes(shorts); var ok: bool, bytes: seq<byte> := tuple.0, tuple.1; if !ok then (false, 0) else (true, bytes_to_decimal(bytes))
  }

  function method shorts_to_byte(shorts: seq<uint16>): (bool, byte)
    decreases shorts
  {
    var tuple: (bool, int) := shorts_to_nat(shorts);
    var ok: bool, val: int := tuple.0, tuple.1;
    if 0 <= val < 256 then
      (true, val as byte)
    else
      (false, 0)
  }

  function method shorts_to_uint16(shorts: seq<uint16>): (bool, uint16)
    decreases shorts
  {
    var tuple: (bool, int) := shorts_to_nat(shorts);
    var ok: bool, val: int := tuple.0, tuple.1;
    if 0 <= val < 65536 then
      (true, val as uint16)
    else
      (false, 0)
  }

  function method shorts_to_uint32(shorts: seq<uint16>): (bool, uint32)
    decreases shorts
  {
    var tuple: (bool, int) := shorts_to_nat(shorts);
    var ok: bool, val: int := tuple.0, tuple.1;
    if 0 <= val < 4294967296 then
      (true, val as uint32)
    else
      (false, 0)
  }

  function method is_ascii_period(short: uint16): bool
    decreases short
  {
    short == 46
  }

  function method parse_ip_addr_helper(ip_shorts: seq<uint16>, current_octet_shorts: seq<uint16>): (bool, seq<byte>)
    decreases ip_shorts, current_octet_shorts
  {
    if |ip_shorts| == 0 then
      var tuple: (bool, byte) := shorts_to_byte(current_octet_shorts);
      var okay: bool, b: byte := tuple.0, tuple.1;
      if !okay then
        (false, [])
      else
        (true, [b])
    else if is_ascii_period(ip_shorts[0]) then
      var tuple: (bool, byte) := shorts_to_byte(current_octet_shorts);
      var okay: bool, b: byte := tuple.0, tuple.1;
      if !okay then
        (false, [])
      else
        var tuple': (bool, seq<byte>) := parse_ip_addr_helper(ip_shorts[1..], []); var ok: bool, ip_bytes: seq<byte> := tuple'.0, tuple'.1; if !ok then (false, []) else (true, [b] + ip_bytes)
    else
      parse_ip_addr_helper(ip_shorts[1..], current_octet_shorts + [ip_shorts[0]])
  }

  function method parse_ip_addr(ip_shorts: seq<uint16>): (bool, seq<byte>)
    decreases ip_shorts
  {
    var tuple: (bool, seq<byte>) := parse_ip_addr_helper(ip_shorts, []);
    var ok: bool, ip_bytes: seq<byte> := tuple.0, tuple.1;
    if ok && |ip_bytes| == 4 then
      (true, ip_bytes)
    else
      (false, [])
  }

  function method {:opaque} {:fuel 0, 0} parse_end_point(ip_shorts: seq<uint16>, port_shorts: seq<uint16>): (bool, EndPoint)
    ensures var tuple: (bool, EndPoint) := parse_end_point(ip_shorts, port_shorts); var ok: bool, ep: EndPoint := tuple.0, tuple.1; ok ==> EndPointIsValidIPV4(ep)
    decreases ip_shorts, port_shorts
  {
    var tuple: (bool, seq<byte>) := parse_ip_addr(ip_shorts);
    var okay: bool, ip_bytes: seq<byte> := tuple.0, tuple.1;
    if !okay then
      (false, EndPoint([0, 0, 0, 0], 0))
    else
      var tuple': (bool, uint16) := shorts_to_uint16(port_shorts); var okay': bool, port: uint16 := tuple'.0, tuple'.1; if !okay' then (false, EndPoint([0, 0, 0, 0], 0)) else (true, EndPoint(ip_bytes, port))
  }

  method test_unique'(endpoints: seq<EndPoint>) returns (unique: bool)
    ensures unique <==> SeqIsUnique(endpoints)
    decreases endpoints
  {
    unique := true;
    var i := 0;
    while i < |endpoints|
      invariant 0 <= i <= |endpoints|
      invariant forall j: int, k: int {:trigger endpoints[k], endpoints[j]} :: 0 <= j < |endpoints| && 0 <= k < i && j != k ==> endpoints[j] != endpoints[k]
      decreases |endpoints| - i
    {
      var j := 0;
      while j < |endpoints|
        invariant 0 <= j <= |endpoints|
        invariant forall k: int {:trigger endpoints[k]} :: 0 <= k < j && k != i ==> endpoints[i] != endpoints[k]
        decreases |endpoints| - j
      {
        if i != j && endpoints[i] == endpoints[j] {
          unique := false;
          reveal_SeqIsUnique();
          return;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    reveal SeqIsUnique();
  }

  function method parse_end_points(args: seq<seq<uint16>>): (bool, seq<EndPoint>)
    requires |args| % 2 == 0
    ensures var (ok: bool, endpoints: seq<EndPoint>) := parse_end_points(args); ok ==> forall e: EndPoint {:trigger EndPointIsValidIPV4(e)} {:trigger e in endpoints} :: e in endpoints ==> EndPointIsValidIPV4(e)
    decreases args
  {
    if |args| == 0 then
      (true, [])
    else
      var (ok1: bool, ep: EndPoint) := parse_end_point(args[0], args[1]); var (ok2: bool, rest: seq<EndPoint>) := parse_end_points(args[2..]); if !(ok1 && ok2) then (false, []) else (true, [ep] + rest)
  }

  method collect_cmd_line_args(ghost env: HostEnvironment) returns (args: seq<seq<uint16>>)
    requires HostEnvironmentIsValid(env)
    ensures |env.constants.CommandLineArgs()| == |args|
    ensures forall i: int {:trigger env.constants.CommandLineArgs()[i]} {:trigger args[i]} :: 0 <= i < |env.constants.CommandLineArgs()| ==> args[i] == env.constants.CommandLineArgs()[i]
    decreases env
  {
    var num_args := HostConstants.NumCommandLineArgs(env);
    var i := 0;
    args := [];
    while i < num_args
      invariant 0 <= i <= num_args
      invariant |env.constants.CommandLineArgs()[0 .. i]| == |args|
      invariant forall j: uint32 {:trigger env.constants.CommandLineArgs()[j]} {:trigger args[j]} :: 0 <= j < i ==> args[j] == env.constants.CommandLineArgs()[j]
      decreases num_args as int - i as int
    {
      var arg := HostConstants.GetCommandLineArg(i as uint64, env);
      args := args + [arg[..]];
      i := i + 1;
    }
  }
}

module CM_DistributedSystem_i refines DistributedSystem_s {

  import H_s = Host_i
  predicate ValidPhysicalAddress(endPoint: EndPoint)
    decreases endPoint
  {
    |endPoint.addr| == 4 &&
    0 <= endPoint.port <= 65535
  }

  predicate ValidPhysicalPacket(p: LPacket<EndPoint, seq<byte>>)
    decreases p
  {
    ValidPhysicalAddress(p.src) &&
    ValidPhysicalAddress(p.dst) &&
    |p.msg| < 18446744073709551616
  }

  predicate ValidPhysicalIo(io: LIoOp<EndPoint, seq<byte>>)
    decreases io
  {
    (io.LIoOpReceive? ==>
      ValidPhysicalPacket(io.r)) &&
    (io.LIoOpSend? ==>
      ValidPhysicalPacket(io.s))
  }

  predicate ValidPhysicalEnvironmentStep(step: LEnvStep<EndPoint, seq<byte>>)
    decreases step
  {
    step.LEnvStepHostIos? ==>
      forall io: LIoOp<EndPoint, seq<byte>> {:trigger io in step.ios} {:trigger ValidPhysicalIo(io)} :: 
        io in step.ios ==>
          ValidPhysicalIo(io)
  }

  predicate DS_Init(s: DS_State, config: H_s.ConcreteConfiguration)
    reads *
    decreases {}, s, config
  {
    s.config == config &&
    H_s.ConcreteConfigInit(s.config, mapdomain(s.servers), s.clients) &&
    LEnvironment_Init(s.environment) &&
    forall id: EndPoint {:trigger s.servers[id]} {:trigger id in s.servers} :: 
      id in s.servers ==>
        _default.HostInit(s.servers[id], config, id)
  }

  predicate DS_NextOneServer(s: DS_State, s': DS_State, id: EndPoint, ios: seq<LIoOp<EndPoint, seq<byte>>>)
    requires id in s.servers
    reads *
    decreases {}, s, s', id, ios
  {
    id in s'.servers &&
    H_s.HostNext(s.servers[id], s'.servers[id], ios) &&
    s'.servers == s.servers[id := s'.servers[id]]
  }

  predicate DS_Next(s: DS_State, s': DS_State)
    reads *
    decreases {}, s, s'
  {
    s'.config == s.config &&
    s'.clients == s.clients &&
    LEnvironment_Next(s.environment, s'.environment) &&
    ValidPhysicalEnvironmentStep(s.environment.nextStep) &&
    if s.environment.nextStep.LEnvStepHostIos? && s.environment.nextStep.actor in s.servers then DS_NextOneServer(s, s', s.environment.nextStep.actor, s.environment.nextStep.ios) else s'.servers == s.servers
  }

  import opened Collections__Maps2_s

  import opened Native__Io_s

  import opened Environment_s

  import opened Native__NativeTypes_s

  datatype DS_State = DS_State(config: H_s.ConcreteConfiguration, environment: LEnvironment<EndPoint, seq<byte>>, servers: map<EndPoint, H_s.HostState>, clients: set<EndPoint>)
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
using System.Collections;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  // Similar to System.Text.Rune, which would be perfect to use
  // except that it isn't available in the platforms we support
  // (.NET Standard 2.0 and .NET Framework 4.5.2)
  public readonly struct Rune : IComparable, IComparable<Rune>, IEquatable<Rune> {

    private readonly uint _value;

    public Rune(int value)
      : this((uint)value) {
    }

    public Rune(uint value) {
      if (!(value < 0xD800 || (0xE000 <= value && value < 0x11_0000))) {
        throw new ArgumentException();
      }

      _value = value;
    }

    public int Value => (int)_value;

    public bool Equals(Rune other) => this == other;

    public override bool Equals(object obj) => (obj is Rune other) && Equals(other);

    public override int GetHashCode() => Value;

    // Values are always between 0 and 0x11_0000, so overflow isn't possible
    public int CompareTo(Rune other) => this.Value - other.Value;

    int IComparable.CompareTo(object obj) {
      switch (obj) {
        case null:
          return 1; // non-null ("this") always sorts after null
        case Rune other:
          return CompareTo(other);
        default:
          throw new ArgumentException();
      }
    }

    public static bool operator ==(Rune left, Rune right) => left._value == right._value;

    public static bool operator !=(Rune left, Rune right) => left._value != right._value;

    public static bool operator <(Rune left, Rune right) => left._value < right._value;

    public static bool operator <=(Rune left, Rune right) => left._value <= right._value;

    public static bool operator >(Rune left, Rune right) => left._value > right._value;

    public static bool operator >=(Rune left, Rune right) => left._value >= right._value;

    public static explicit operator Rune(int value) => new Rune(value);
    public static explicit operator Rune(BigInteger value) => new Rune((uint)value);

    // Defined this way to be consistent with System.Text.Rune,
    // but note that Dafny will use Helpers.ToString(rune),
    // which will print in the style of a character literal instead.
    public override string ToString() {
      return char.ConvertFromUtf32(Value);
    }

    // Replacement for String.EnumerateRunes() from newer platforms
    public static IEnumerable<Rune> Enumerate(string s) {
      var sLength = s.Length;
      for (var i = 0; i < sLength; i++) {
        if (char.IsHighSurrogate(s[i])) {
          if (char.IsLowSurrogate(s[i + 1])) {
            yield return (Rune)char.ConvertToUtf32(s[i], s[i + 1]);
            i++;
          } else {
            throw new ArgumentException();
          }
        } else if (char.IsLowSurrogate(s[i])) {
          throw new ArgumentException();
        } else {
          yield return (Rune)s[i];
        }
      }
    }
  }

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || Count != other.Count) {
        return false;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (var t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }
      BigInteger m;
      if (t is T && dict.TryGetValue((T)(object)t, out m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }

      if (other == null || LongCount != other.LongCount) {
        return false;
      }

      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }

      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (ReferenceEquals(this, other)) {
        return true;
      }
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> : IEnumerable<T> {
    long LongCount { get; }
    int Count { get; }
    [Obsolete("Use CloneAsArray() instead of Elements (both perform a copy).")]
    T[] Elements { get; }
    T[] CloneAsArray();
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
    string ToVerbatimString(bool asLiteral);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var builder = ImmutableArray.CreateBuilder<T>(len);
      for (int i = 0; i < len; i++) {
        builder.Add(init(new BigInteger(i)));
      }
      return new ArraySequence<T>(builder.MoveToImmutable());
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public static ISequence<Rune> UnicodeFromString(string s) {
      var runes = new List<Rune>();

      foreach (var rune in Rune.Enumerate(s)) {
        runes.Add(rune);
      }
      return new ArraySequence<Rune>(runes.ToArray());
    }

    public static ISequence<ISequence<char>> FromMainArguments(string[] args) {
      Dafny.ISequence<char>[] dafnyArgs = new Dafny.ISequence<char>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<char>.FromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<char>.FromString(args[i]);
      }

      return Sequence<ISequence<char>>.FromArray(dafnyArgs);
    }
    public static ISequence<ISequence<Rune>> UnicodeFromMainArguments(string[] args) {
      Dafny.ISequence<Rune>[] dafnyArgs = new Dafny.ISequence<Rune>[args.Length + 1];
      dafnyArgs[0] = Dafny.Sequence<Rune>.UnicodeFromString("dotnet");
      for (var i = 0; i < args.Length; i++) {
        dafnyArgs[i + 1] = Dafny.Sequence<Rune>.UnicodeFromString(args[i]);
      }

      return Sequence<ISequence<Rune>>.FromArray(dafnyArgs);
    }

    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = sequence.CloneAsArray();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      for (int i = 0; i < n; i++) {
        if (!Equals(left.Select(i), right.Select(i))) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n <= right.Count && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Count;
      return n < right.Count && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    internal abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements { get { return CloneAsArray(); } }

    public T[] CloneAsArray() {
      return ImmutableElements.ToArray();
    }

    public IEnumerable<T> UniqueElements {
      get {
        return Set<T>.FromCollection(ImmutableElements).Elements;
      }
    }

    public IEnumerator<T> GetEnumerator() {
      foreach (var el in ImmutableElements) {
        yield return el;
      }
    }

    IEnumerator IEnumerable.GetEnumerator() {
      return GetEnumerator();
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      return ReferenceEquals(this, other) || (Count == other.Count && EqualUntil(this, other, Count));
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      if (typeof(T) == typeof(char)) {
        return string.Concat(this);
      } else {
        return "[" + string.Join(", ", ImmutableElements.Select(Dafny.Helpers.ToString)) + "]";
      }
    }

    public string ToVerbatimString(bool asLiteral) {
      var builder = new System.Text.StringBuilder();
      if (asLiteral) {
        builder.Append('"');
      }
      foreach (var c in this) {
        var rune = (Rune)(object)c;
        if (asLiteral) {
          builder.Append(Helpers.EscapeCharacter(rune));
        } else {
          builder.Append(char.ConvertFromUtf32(rune.Value));
        }
      }
      if (asLiteral) {
        builder.Append('"');
      }
      return builder.ToString();
    }

    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      return Subsequence(0, m);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      return Subsequence(m, Count);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == Count) {
        return this;
      }
      int startingIndex = checked((int)lo);
      var length = checked((int)hi) - startingIndex;
      return new ArraySequence<T>(ImmutableArray.Create<T>(ImmutableElements, startingIndex, length));
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }

    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private volatile ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    internal override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>(count);
      var toVisit = new Stack<ISequence<T>>();
      var leftBuffer = left;
      var rightBuffer = right;
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          leftBuffer = cs.left;
          rightBuffer = cs.right;
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          if (seq is Sequence<T> sq) {
            ansBuilder.AddRange(sq.ImmutableElements); // Optimized path for ImmutableArray
          } else {
            ansBuilder.AddRange(seq); // Slower path using IEnumerable
          }
        }
      }
      return ansBuilder.MoveToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else if (g is Rune) {
        return "'" + EscapeCharacter((Rune)(object)g) + "'";
      } else {
        return g.ToString();
      }
    }

    public static string EscapeCharacter(Rune r) {
      switch (r.Value) {
        case '\n': return "\\n";
        case '\r': return "\\r";
        case '\t': return "\\t";
        case '\0': return "\\0";
        case '\'': return "\\'";
        case '\"': return "\\\"";
        case '\\': return "\\\\";
        default: return r.ToString();
      };
    }

    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<Rune> RUNE = new TypeDescriptor<Rune>(new Rune('D'));  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x1_0000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<Rune> AllUnicodeChars() {
      for (int i = 0; i < 0xD800; i++) {
        yield return new Rune(i);
      }
      for (int i = 0xE000; i < 0x11_0000; i++) {
        yield return new Rune(i);
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>(array);
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
        // This is unfriendly given that Dafny's C# compiler will
        // invoke the compiled main method directly,
        // so we might be exiting the whole Dafny process here.
        // That's the best we can do until Dafny main methods support
        // a return value though (https://github.com/dafny-lang/dafny/issues/2699).
        // If we just set Environment.ExitCode here, the Dafny CLI
        // will just override that with 0.
        Environment.Exit(1);
      }
    }

    public static Rune AddRunes(Rune left, Rune right) {
      return (Rune)(left.Value + right.Value);
    }

    public static Rune SubtractRunes(Rune left, Rune right) {
      return (Rune)(left.Value - right.Value);
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    public readonly BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)

    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(uint n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(long n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(ulong n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    /// <summary>
    /// Construct an exact rational representation of a double value.
    /// Throw an exception on NaN or infinite values. Does not support
    /// subnormal values, though it would be possible to extend it to.
    /// </summary>
    public BigRational(double n) {
      if (Double.IsNaN(n)) {
        throw new ArgumentException("Can't convert NaN to a rational.");
      }
      if (Double.IsInfinity(n)) {
        throw new ArgumentException(
          "Can't convert +/- infinity to a rational.");
      }

      // Double-specific values
      const int exptBias = 1023;
      const ulong signMask = 0x8000000000000000;
      const ulong exptMask = 0x7FF0000000000000;
      const ulong mantMask = 0x000FFFFFFFFFFFFF;
      const int mantBits = 52;
      ulong bits = BitConverter.ToUInt64(BitConverter.GetBytes(n), 0);

      // Generic conversion
      bool isNeg = (bits & signMask) != 0;
      int expt = ((int)((bits & exptMask) >> mantBits)) - exptBias;
      var mant = (bits & mantMask);

      if (expt == -exptBias && mant != 0) {
        throw new ArgumentException(
          "Can't convert a subnormal value to a rational (yet).");
      }

      var one = BigInteger.One;
      var negFactor = isNeg ? BigInteger.Negate(one) : one;
      var two = new BigInteger(2);
      var exptBI = BigInteger.Pow(two, Math.Abs(expt));
      var twoToMantBits = BigInteger.Pow(two, mantBits);
      var mantNum = negFactor * (twoToMantBits + new BigInteger(mant));
      if (expt == -exptBias && mant == 0) {
        num = den = 0;
      } else if (expt < 0) {
        num = mantNum;
        den = twoToMantBits * exptBI;
      } else {
        num = exptBI * mantNum;
        den = twoToMantBits;
      }
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}

namespace @_System {

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += ")";
      return s;
    }
    private static readonly _ITuple0 theDefault = create();
    public static _ITuple0 Default() {
      return theDefault;
    }
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
  }

  public interface _ITuple1<out T1> {
    T1 dtor__0 { get; }
    _ITuple1<__T1> DowncastClone<__T1>(Func<T1, __T1> converter0);
  }
  public class Tuple1<T1> : _ITuple1<T1> {
    public readonly T1 _0;
    public Tuple1(T1 _0) {
      this._0 = _0;
    }
    public _ITuple1<__T1> DowncastClone<__T1>(Func<T1, __T1> converter0) {
      if (this is _ITuple1<__T1> dt) { return dt; }
      return new Tuple1<__T1>(converter0(_0));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple1<T1>;
      return oth != null && object.Equals(this._0, oth._0);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ")";
      return s;
    }
    public static _ITuple1<T1> Default(T1 _default_T1) {
      return create(_default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple1<T1>> _TypeDescriptor(Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple1<T1>>(_System.Tuple1<T1>.Default(_td_T1.Default()));
    }
    public static _ITuple1<T1> create(T1 _0) {
      return new Tuple1<T1>(_0);
    }
    public T1 dtor__0 {
      get {
        return this._0;
      }
    }
  }

  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
  }

  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static _ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

  public interface _ITuple3<out T0, out T1, out T2> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2);
  }
  public class Tuple3<T0, T1, T2> : _ITuple3<T0, T1, T2> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public Tuple3(T0 _0, T1 _1, T2 _2) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
    }
    public _ITuple3<__T0, __T1, __T2> DowncastClone<__T0, __T1, __T2>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2) {
      if (this is _ITuple3<__T0, __T1, __T2> dt) { return dt; }
      return new Tuple3<__T0, __T1, __T2>(converter0(_0), converter1(_1), converter2(_2));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3<T0, T1, T2>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ")";
      return s;
    }
    public static _ITuple3<T0, T1, T2> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2) {
      return create(_default_T0, _default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3<T0, T1, T2>>(_System.Tuple3<T0, T1, T2>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3<T0, T1, T2> create(T0 _0, T1 _1, T2 _2) {
      return new Tuple3<T0, T1, T2>(_0, _1, _2);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
  }

  public interface _ITuple4<out T0, out T1, out T2, out T3> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3);
  }
  public class Tuple4<T0, T1, T2, T3> : _ITuple4<T0, T1, T2, T3> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public Tuple4(T0 _0, T1 _1, T2 _2, T3 _3) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
    }
    public _ITuple4<__T0, __T1, __T2, __T3> DowncastClone<__T0, __T1, __T2, __T3>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3) {
      if (this is _ITuple4<__T0, __T1, __T2, __T3> dt) { return dt; }
      return new Tuple4<__T0, __T1, __T2, __T3>(converter0(_0), converter1(_1), converter2(_2), converter3(_3));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple4<T0, T1, T2, T3>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ")";
      return s;
    }
    public static _ITuple4<T0, T1, T2, T3> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3);
    }
    public static Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3) {
      return new Dafny.TypeDescriptor<_System._ITuple4<T0, T1, T2, T3>>(_System.Tuple4<T0, T1, T2, T3>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default()));
    }
    public static _ITuple4<T0, T1, T2, T3> create(T0 _0, T1 _1, T2 _2, T3 _3) {
      return new Tuple4<T0, T1, T2, T3>(_0, _1, _2, _3);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
  }

  public interface _ITuple5<out T0, out T1, out T2, out T3, out T4> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4);
  }
  public class Tuple5<T0, T1, T2, T3, T4> : _ITuple5<T0, T1, T2, T3, T4> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public Tuple5(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
    }
    public _ITuple5<__T0, __T1, __T2, __T3, __T4> DowncastClone<__T0, __T1, __T2, __T3, __T4>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4) {
      if (this is _ITuple5<__T0, __T1, __T2, __T3, __T4> dt) { return dt; }
      return new Tuple5<__T0, __T1, __T2, __T3, __T4>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple5<T0, T1, T2, T3, T4>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ")";
      return s;
    }
    public static _ITuple5<T0, T1, T2, T3, T4> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4);
    }
    public static Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4) {
      return new Dafny.TypeDescriptor<_System._ITuple5<T0, T1, T2, T3, T4>>(_System.Tuple5<T0, T1, T2, T3, T4>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default()));
    }
    public static _ITuple5<T0, T1, T2, T3, T4> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4) {
      return new Tuple5<T0, T1, T2, T3, T4>(_0, _1, _2, _3, _4);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
  }

  public interface _ITuple6<out T0, out T1, out T2, out T3, out T4, out T5> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5);
  }
  public class Tuple6<T0, T1, T2, T3, T4, T5> : _ITuple6<T0, T1, T2, T3, T4, T5> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public Tuple6(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
    }
    public _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5) {
      if (this is _ITuple6<__T0, __T1, __T2, __T3, __T4, __T5> dt) { return dt; }
      return new Tuple6<__T0, __T1, __T2, __T3, __T4, __T5>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple6<T0, T1, T2, T3, T4, T5>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ")";
      return s;
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5);
    }
    public static Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5) {
      return new Dafny.TypeDescriptor<_System._ITuple6<T0, T1, T2, T3, T4, T5>>(_System.Tuple6<T0, T1, T2, T3, T4, T5>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default()));
    }
    public static _ITuple6<T0, T1, T2, T3, T4, T5> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5) {
      return new Tuple6<T0, T1, T2, T3, T4, T5>(_0, _1, _2, _3, _4, _5);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
  }

  public interface _ITuple7<out T0, out T1, out T2, out T3, out T4, out T5, out T6> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6);
  }
  public class Tuple7<T0, T1, T2, T3, T4, T5, T6> : _ITuple7<T0, T1, T2, T3, T4, T5, T6> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public Tuple7(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
    }
    public _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6) {
      if (this is _ITuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6> dt) { return dt; }
      return new Tuple7<__T0, __T1, __T2, __T3, __T4, __T5, __T6>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple7<T0, T1, T2, T3, T4, T5, T6>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ")";
      return s;
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6);
    }
    public static Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6) {
      return new Dafny.TypeDescriptor<_System._ITuple7<T0, T1, T2, T3, T4, T5, T6>>(_System.Tuple7<T0, T1, T2, T3, T4, T5, T6>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default()));
    }
    public static _ITuple7<T0, T1, T2, T3, T4, T5, T6> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6) {
      return new Tuple7<T0, T1, T2, T3, T4, T5, T6>(_0, _1, _2, _3, _4, _5, _6);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
  }

  public interface _ITuple8<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7);
  }
  public class Tuple8<T0, T1, T2, T3, T4, T5, T6, T7> : _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public Tuple8(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
    }
    public _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7) {
      if (this is _ITuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7> dt) { return dt; }
      return new Tuple8<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ")";
      return s;
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7);
    }
    public static Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7) {
      return new Dafny.TypeDescriptor<_System._ITuple8<T0, T1, T2, T3, T4, T5, T6, T7>>(_System.Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default()));
    }
    public static _ITuple8<T0, T1, T2, T3, T4, T5, T6, T7> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7) {
      return new Tuple8<T0, T1, T2, T3, T4, T5, T6, T7>(_0, _1, _2, _3, _4, _5, _6, _7);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
  }

  public interface _ITuple9<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8);
  }
  public class Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> : _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public Tuple9(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
    }
    public _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8) {
      if (this is _ITuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8> dt) { return dt; }
      return new Tuple9<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ")";
      return s;
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8);
    }
    public static Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8) {
      return new Dafny.TypeDescriptor<_System._ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>>(_System.Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default()));
    }
    public static _ITuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8) {
      return new Tuple9<T0, T1, T2, T3, T4, T5, T6, T7, T8>(_0, _1, _2, _3, _4, _5, _6, _7, _8);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
  }

  public interface _ITuple10<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9);
  }
  public class Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> : _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public Tuple10(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
    }
    public _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9) {
      if (this is _ITuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9> dt) { return dt; }
      return new Tuple10<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ")";
      return s;
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9);
    }
    public static Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9) {
      return new Dafny.TypeDescriptor<_System._ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>>(_System.Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default()));
    }
    public static _ITuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9) {
      return new Tuple10<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
  }

  public interface _ITuple11<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10);
  }
  public class Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> : _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public Tuple11(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
    }
    public _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10) {
      if (this is _ITuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10> dt) { return dt; }
      return new Tuple11<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ")";
      return s;
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10);
    }
    public static Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10) {
      return new Dafny.TypeDescriptor<_System._ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>>(_System.Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default()));
    }
    public static _ITuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10) {
      return new Tuple11<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
  }

  public interface _ITuple12<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11);
  }
  public class Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> : _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public Tuple12(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
    }
    public _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11) {
      if (this is _ITuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11> dt) { return dt; }
      return new Tuple12<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ")";
      return s;
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11);
    }
    public static Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11) {
      return new Dafny.TypeDescriptor<_System._ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>>(_System.Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default()));
    }
    public static _ITuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11) {
      return new Tuple12<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
  }

  public interface _ITuple13<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12);
  }
  public class Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> : _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public Tuple13(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
    }
    public _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12) {
      if (this is _ITuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12> dt) { return dt; }
      return new Tuple13<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ")";
      return s;
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12);
    }
    public static Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12) {
      return new Dafny.TypeDescriptor<_System._ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>>(_System.Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default()));
    }
    public static _ITuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12) {
      return new Tuple13<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
  }

  public interface _ITuple14<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13);
  }
  public class Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> : _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public Tuple14(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
    }
    public _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13) {
      if (this is _ITuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13> dt) { return dt; }
      return new Tuple14<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ")";
      return s;
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13);
    }
    public static Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13) {
      return new Dafny.TypeDescriptor<_System._ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>>(_System.Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default()));
    }
    public static _ITuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13) {
      return new Tuple14<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
  }

  public interface _ITuple15<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14);
  }
  public class Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> : _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public Tuple15(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
    }
    public _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14) {
      if (this is _ITuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14> dt) { return dt; }
      return new Tuple15<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ")";
      return s;
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14);
    }
    public static Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14) {
      return new Dafny.TypeDescriptor<_System._ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>>(_System.Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default()));
    }
    public static _ITuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14) {
      return new Tuple15<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
  }

  public interface _ITuple16<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15);
  }
  public class Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> : _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public Tuple16(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
    }
    public _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15) {
      if (this is _ITuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15> dt) { return dt; }
      return new Tuple16<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ")";
      return s;
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15);
    }
    public static Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15) {
      return new Dafny.TypeDescriptor<_System._ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>>(_System.Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default()));
    }
    public static _ITuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15) {
      return new Tuple16<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
  }

  public interface _ITuple17<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16);
  }
  public class Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> : _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public Tuple17(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
    }
    public _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16) {
      if (this is _ITuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16> dt) { return dt; }
      return new Tuple17<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ")";
      return s;
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16);
    }
    public static Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16) {
      return new Dafny.TypeDescriptor<_System._ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>>(_System.Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default()));
    }
    public static _ITuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16) {
      return new Tuple17<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
  }

  public interface _ITuple18<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17);
  }
  public class Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> : _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public readonly T17 _17;
    public Tuple18(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
      this._17 = _17;
    }
    public _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17) {
      if (this is _ITuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17> dt) { return dt; }
      return new Tuple18<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16), converter17(_17));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16) && object.Equals(this._17, oth._17);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._17));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ", ";
      s += Dafny.Helpers.ToString(this._17);
      s += ")";
      return s;
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17);
    }
    public static Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17) {
      return new Dafny.TypeDescriptor<_System._ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>>(_System.Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default()));
    }
    public static _ITuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17) {
      return new Tuple18<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
    public T17 dtor__17 {
      get {
        return this._17;
      }
    }
  }

  public interface _ITuple19<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18);
  }
  public class Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> : _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public readonly T17 _17;
    public readonly T18 _18;
    public Tuple19(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
      this._17 = _17;
      this._18 = _18;
    }
    public _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18) {
      if (this is _ITuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18> dt) { return dt; }
      return new Tuple19<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16), converter17(_17), converter18(_18));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16) && object.Equals(this._17, oth._17) && object.Equals(this._18, oth._18);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._18));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ", ";
      s += Dafny.Helpers.ToString(this._17);
      s += ", ";
      s += Dafny.Helpers.ToString(this._18);
      s += ")";
      return s;
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18);
    }
    public static Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18) {
      return new Dafny.TypeDescriptor<_System._ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>>(_System.Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default()));
    }
    public static _ITuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18) {
      return new Tuple19<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
    public T17 dtor__17 {
      get {
        return this._17;
      }
    }
    public T18 dtor__18 {
      get {
        return this._18;
      }
    }
  }

  public interface _ITuple20<out T0, out T1, out T2, out T3, out T4, out T5, out T6, out T7, out T8, out T9, out T10, out T11, out T12, out T13, out T14, out T15, out T16, out T17, out T18, out T19> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
    T2 dtor__2 { get; }
    T3 dtor__3 { get; }
    T4 dtor__4 { get; }
    T5 dtor__5 { get; }
    T6 dtor__6 { get; }
    T7 dtor__7 { get; }
    T8 dtor__8 { get; }
    T9 dtor__9 { get; }
    T10 dtor__10 { get; }
    T11 dtor__11 { get; }
    T12 dtor__12 { get; }
    T13 dtor__13 { get; }
    T14 dtor__14 { get; }
    T15 dtor__15 { get; }
    T16 dtor__16 { get; }
    T17 dtor__17 { get; }
    T18 dtor__18 { get; }
    T19 dtor__19 { get; }
    _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19);
  }
  public class Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> : _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> {
    public readonly T0 _0;
    public readonly T1 _1;
    public readonly T2 _2;
    public readonly T3 _3;
    public readonly T4 _4;
    public readonly T5 _5;
    public readonly T6 _6;
    public readonly T7 _7;
    public readonly T8 _8;
    public readonly T9 _9;
    public readonly T10 _10;
    public readonly T11 _11;
    public readonly T12 _12;
    public readonly T13 _13;
    public readonly T14 _14;
    public readonly T15 _15;
    public readonly T16 _16;
    public readonly T17 _17;
    public readonly T18 _18;
    public readonly T19 _19;
    public Tuple20(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      this._0 = _0;
      this._1 = _1;
      this._2 = _2;
      this._3 = _3;
      this._4 = _4;
      this._5 = _5;
      this._6 = _6;
      this._7 = _7;
      this._8 = _8;
      this._9 = _9;
      this._10 = _10;
      this._11 = _11;
      this._12 = _12;
      this._13 = _13;
      this._14 = _14;
      this._15 = _15;
      this._16 = _16;
      this._17 = _17;
      this._18 = _18;
      this._19 = _19;
    }
    public _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> DowncastClone<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(Func<T0, __T0> converter0, Func<T1, __T1> converter1, Func<T2, __T2> converter2, Func<T3, __T3> converter3, Func<T4, __T4> converter4, Func<T5, __T5> converter5, Func<T6, __T6> converter6, Func<T7, __T7> converter7, Func<T8, __T8> converter8, Func<T9, __T9> converter9, Func<T10, __T10> converter10, Func<T11, __T11> converter11, Func<T12, __T12> converter12, Func<T13, __T13> converter13, Func<T14, __T14> converter14, Func<T15, __T15> converter15, Func<T16, __T16> converter16, Func<T17, __T17> converter17, Func<T18, __T18> converter18, Func<T19, __T19> converter19) {
      if (this is _ITuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19> dt) { return dt; }
      return new Tuple20<__T0, __T1, __T2, __T3, __T4, __T5, __T6, __T7, __T8, __T9, __T10, __T11, __T12, __T13, __T14, __T15, __T16, __T17, __T18, __T19>(converter0(_0), converter1(_1), converter2(_2), converter3(_3), converter4(_4), converter5(_5), converter6(_6), converter7(_7), converter8(_8), converter9(_9), converter10(_10), converter11(_11), converter12(_12), converter13(_13), converter14(_14), converter15(_15), converter16(_16), converter17(_17), converter18(_18), converter19(_19));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1) && object.Equals(this._2, oth._2) && object.Equals(this._3, oth._3) && object.Equals(this._4, oth._4) && object.Equals(this._5, oth._5) && object.Equals(this._6, oth._6) && object.Equals(this._7, oth._7) && object.Equals(this._8, oth._8) && object.Equals(this._9, oth._9) && object.Equals(this._10, oth._10) && object.Equals(this._11, oth._11) && object.Equals(this._12, oth._12) && object.Equals(this._13, oth._13) && object.Equals(this._14, oth._14) && object.Equals(this._15, oth._15) && object.Equals(this._16, oth._16) && object.Equals(this._17, oth._17) && object.Equals(this._18, oth._18) && object.Equals(this._19, oth._19);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._2));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._3));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._4));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._5));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._6));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._7));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._8));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._9));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._10));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._11));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._12));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._13));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._14));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._15));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._16));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._17));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._18));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._19));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ", ";
      s += Dafny.Helpers.ToString(this._2);
      s += ", ";
      s += Dafny.Helpers.ToString(this._3);
      s += ", ";
      s += Dafny.Helpers.ToString(this._4);
      s += ", ";
      s += Dafny.Helpers.ToString(this._5);
      s += ", ";
      s += Dafny.Helpers.ToString(this._6);
      s += ", ";
      s += Dafny.Helpers.ToString(this._7);
      s += ", ";
      s += Dafny.Helpers.ToString(this._8);
      s += ", ";
      s += Dafny.Helpers.ToString(this._9);
      s += ", ";
      s += Dafny.Helpers.ToString(this._10);
      s += ", ";
      s += Dafny.Helpers.ToString(this._11);
      s += ", ";
      s += Dafny.Helpers.ToString(this._12);
      s += ", ";
      s += Dafny.Helpers.ToString(this._13);
      s += ", ";
      s += Dafny.Helpers.ToString(this._14);
      s += ", ";
      s += Dafny.Helpers.ToString(this._15);
      s += ", ";
      s += Dafny.Helpers.ToString(this._16);
      s += ", ";
      s += Dafny.Helpers.ToString(this._17);
      s += ", ";
      s += Dafny.Helpers.ToString(this._18);
      s += ", ";
      s += Dafny.Helpers.ToString(this._19);
      s += ")";
      return s;
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> Default(T0 _default_T0, T1 _default_T1, T2 _default_T2, T3 _default_T3, T4 _default_T4, T5 _default_T5, T6 _default_T6, T7 _default_T7, T8 _default_T8, T9 _default_T9, T10 _default_T10, T11 _default_T11, T12 _default_T12, T13 _default_T13, T14 _default_T14, T15 _default_T15, T16 _default_T16, T17 _default_T17, T18 _default_T18, T19 _default_T19) {
      return create(_default_T0, _default_T1, _default_T2, _default_T3, _default_T4, _default_T5, _default_T6, _default_T7, _default_T8, _default_T9, _default_T10, _default_T11, _default_T12, _default_T13, _default_T14, _default_T15, _default_T16, _default_T17, _default_T18, _default_T19);
    }
    public static Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2, Dafny.TypeDescriptor<T3> _td_T3, Dafny.TypeDescriptor<T4> _td_T4, Dafny.TypeDescriptor<T5> _td_T5, Dafny.TypeDescriptor<T6> _td_T6, Dafny.TypeDescriptor<T7> _td_T7, Dafny.TypeDescriptor<T8> _td_T8, Dafny.TypeDescriptor<T9> _td_T9, Dafny.TypeDescriptor<T10> _td_T10, Dafny.TypeDescriptor<T11> _td_T11, Dafny.TypeDescriptor<T12> _td_T12, Dafny.TypeDescriptor<T13> _td_T13, Dafny.TypeDescriptor<T14> _td_T14, Dafny.TypeDescriptor<T15> _td_T15, Dafny.TypeDescriptor<T16> _td_T16, Dafny.TypeDescriptor<T17> _td_T17, Dafny.TypeDescriptor<T18> _td_T18, Dafny.TypeDescriptor<T19> _td_T19) {
      return new Dafny.TypeDescriptor<_System._ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>>(_System.Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>.Default(_td_T0.Default(), _td_T1.Default(), _td_T2.Default(), _td_T3.Default(), _td_T4.Default(), _td_T5.Default(), _td_T6.Default(), _td_T7.Default(), _td_T8.Default(), _td_T9.Default(), _td_T10.Default(), _td_T11.Default(), _td_T12.Default(), _td_T13.Default(), _td_T14.Default(), _td_T15.Default(), _td_T16.Default(), _td_T17.Default(), _td_T18.Default(), _td_T19.Default()));
    }
    public static _ITuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19> create(T0 _0, T1 _1, T2 _2, T3 _3, T4 _4, T5 _5, T6 _6, T7 _7, T8 _8, T9 _9, T10 _10, T11 _11, T12 _12, T13 _13, T14 _14, T15 _15, T16 _16, T17 _17, T18 _18, T19 _19) {
      return new Tuple20<T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19>(_0, _1, _2, _3, _4, _5, _6, _7, _8, _9, _10, _11, _12, _13, _14, _15, _16, _17, _18, _19);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
    public T2 dtor__2 {
      get {
        return this._2;
      }
    }
    public T3 dtor__3 {
      get {
        return this._3;
      }
    }
    public T4 dtor__4 {
      get {
        return this._4;
      }
    }
    public T5 dtor__5 {
      get {
        return this._5;
      }
    }
    public T6 dtor__6 {
      get {
        return this._6;
      }
    }
    public T7 dtor__7 {
      get {
        return this._7;
      }
    }
    public T8 dtor__8 {
      get {
        return this._8;
      }
    }
    public T9 dtor__9 {
      get {
        return this._9;
      }
    }
    public T10 dtor__10 {
      get {
        return this._10;
      }
    }
    public T11 dtor__11 {
      get {
        return this._11;
      }
    }
    public T12 dtor__12 {
      get {
        return this._12;
      }
    }
    public T13 dtor__13 {
      get {
        return this._13;
      }
    }
    public T14 dtor__14 {
      get {
        return this._14;
      }
    }
    public T15 dtor__15 {
      get {
        return this._15;
      }
    }
    public T16 dtor__16 {
      get {
        return this._16;
      }
    }
    public T17 dtor__17 {
      get {
        return this._17;
      }
    }
    public T18 dtor__18 {
      get {
        return this._18;
      }
    }
    public T19 dtor__19 {
      get {
        return this._19;
      }
    }
  }
} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace _System
namespace Native____NativeTypes__s_Compile {

  public partial class @sbyte {
    public static System.Collections.Generic.IEnumerable<sbyte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (sbyte)j; }
    }
    private static readonly Dafny.TypeDescriptor<sbyte> _TYPE = new Dafny.TypeDescriptor<sbyte>(0);
    public static Dafny.TypeDescriptor<sbyte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class @byte {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int16 {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int64 {
    public static System.Collections.Generic.IEnumerable<long> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (long)j; }
    }
    private static readonly Dafny.TypeDescriptor<long> _TYPE = new Dafny.TypeDescriptor<long>(0);
    public static Dafny.TypeDescriptor<long> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat8 {
    public static System.Collections.Generic.IEnumerable<sbyte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (sbyte)j; }
    }
    private static readonly Dafny.TypeDescriptor<sbyte> _TYPE = new Dafny.TypeDescriptor<sbyte>(0);
    public static Dafny.TypeDescriptor<sbyte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat16 {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat64 {
    public static System.Collections.Generic.IEnumerable<long> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (long)j; }
    }
    private static readonly Dafny.TypeDescriptor<long> _TYPE = new Dafny.TypeDescriptor<long>(0);
    public static Dafny.TypeDescriptor<long> _TypeDescriptor() {
      return _TYPE;
    }
  }

} // end of namespace Native____NativeTypes__s_Compile
namespace Collections____Maps2__s_Compile {

  public partial class __default {
    public static Dafny.ISet<__KT> mapdomain<__KT, __VT>(Dafny.IMap<__KT,__VT> m) {
      return Dafny.Helpers.Id<Func<Dafny.IMap<__KT,__VT>, Dafny.ISet<__KT>>>((_0_m) => ((System.Func<Dafny.ISet<__KT>>)(() => {
        var _coll0 = new System.Collections.Generic.List<__KT>();
        foreach (__KT _compr_0 in (_0_m).Keys.Elements) {
          __KT _1_k = (__KT)_compr_0;
          if ((_0_m).Contains((_1_k))) {
            _coll0.Add(_1_k);
          }
        }
        return Dafny.Set<__KT>.FromCollection(_coll0);
      }))())(m);
    }
    public static Dafny.IMap<__KT,__VT> mapremove<__KT, __VT>(Dafny.IMap<__KT,__VT> m, __KT k)
    {
      return Dafny.Helpers.Id<Func<Dafny.IMap<__KT,__VT>, __KT, Dafny.IMap<__KT,__VT>>>((_2_m, _3_k) => ((System.Func<Dafny.IMap<__KT,__VT>>)(() => {
        var _coll1 = new System.Collections.Generic.List<Dafny.Pair<__KT,__VT>>();
        foreach (__KT _compr_1 in (_2_m).Keys.Elements) {
          __KT _4_ki = (__KT)_compr_1;
          if (((_2_m).Contains((_4_ki))) && (!object.Equals(_4_ki, _3_k))) {
            _coll1.Add(new Dafny.Pair<__KT,__VT>(_4_ki, Dafny.Map<__KT, __VT>.Select(_2_m,_4_ki)));
          }
        }
        return Dafny.Map<__KT,__VT>.FromCollection(_coll1);
      }))())(m, k);
    }
  }
} // end of namespace Collections____Maps2__s_Compile
namespace Temporal____Temporal__s_Compile {

} // end of namespace Temporal____Temporal__s_Compile
namespace Environment__s_Compile {

  public interface _ILPacket<IdType, MessageType> {
    bool is_LPacket { get; }
    IdType dtor_dst { get; }
    IdType dtor_src { get; }
    MessageType dtor_msg { get; }
    _ILPacket<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1);
  }
  public class LPacket<IdType, MessageType> : _ILPacket<IdType, MessageType> {
    public readonly IdType _dst;
    public readonly IdType _src;
    public readonly MessageType _msg;
    public LPacket(IdType dst, IdType src, MessageType msg) {
      this._dst = dst;
      this._src = src;
      this._msg = msg;
    }
    public _ILPacket<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILPacket<__IdType, __MessageType> dt) { return dt; }
      return new LPacket<__IdType, __MessageType>(converter0(_dst), converter0(_src), converter1(_msg));
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LPacket<IdType, MessageType>;
      return oth != null && object.Equals(this._dst, oth._dst) && object.Equals(this._src, oth._src) && object.Equals(this._msg, oth._msg);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dst));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._src));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._msg));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LPacket.LPacket";
      s += "(";
      s += Dafny.Helpers.ToString(this._dst);
      s += ", ";
      s += Dafny.Helpers.ToString(this._src);
      s += ", ";
      s += Dafny.Helpers.ToString(this._msg);
      s += ")";
      return s;
    }
    public static Environment__s_Compile._ILPacket<IdType, MessageType> Default(IdType _default_IdType, MessageType _default_MessageType) {
      return create(_default_IdType, _default_IdType, _default_MessageType);
    }
    public static Dafny.TypeDescriptor<Environment__s_Compile._ILPacket<IdType, MessageType>> _TypeDescriptor(Dafny.TypeDescriptor<IdType> _td_IdType, Dafny.TypeDescriptor<MessageType> _td_MessageType) {
      return new Dafny.TypeDescriptor<Environment__s_Compile._ILPacket<IdType, MessageType>>(Environment__s_Compile.LPacket<IdType, MessageType>.Default(_td_IdType.Default(), _td_MessageType.Default()));
    }
    public static _ILPacket<IdType, MessageType> create(IdType dst, IdType src, MessageType msg) {
      return new LPacket<IdType, MessageType>(dst, src, msg);
    }
    public static _ILPacket<IdType, MessageType> create_LPacket(IdType dst, IdType src, MessageType msg) {
      return create(dst, src, msg);
    }
    public bool is_LPacket { get { return true; } }
    public IdType dtor_dst {
      get {
        return this._dst;
      }
    }
    public IdType dtor_src {
      get {
        return this._src;
      }
    }
    public MessageType dtor_msg {
      get {
        return this._msg;
      }
    }
  }

  public interface _ILIoOp<IdType, MessageType> {
    bool is_LIoOpSend { get; }
    bool is_LIoOpReceive { get; }
    bool is_LIoOpTimeoutReceive { get; }
    bool is_LIoOpReadClock { get; }
    Environment__s_Compile._ILPacket<IdType, MessageType> dtor_s { get; }
    Environment__s_Compile._ILPacket<IdType, MessageType> dtor_r { get; }
    BigInteger dtor_t { get; }
    _ILIoOp<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1);
  }
  public abstract class LIoOp<IdType, MessageType> : _ILIoOp<IdType, MessageType> {
    public LIoOp() { }
    public static Environment__s_Compile._ILIoOp<IdType, MessageType> Default() {
      return create_LIoOpTimeoutReceive();
    }
    public static Dafny.TypeDescriptor<Environment__s_Compile._ILIoOp<IdType, MessageType>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Environment__s_Compile._ILIoOp<IdType, MessageType>>(Environment__s_Compile.LIoOp<IdType, MessageType>.Default());
    }
    public static _ILIoOp<IdType, MessageType> create_LIoOpSend(Environment__s_Compile._ILPacket<IdType, MessageType> s) {
      return new LIoOp_LIoOpSend<IdType, MessageType>(s);
    }
    public static _ILIoOp<IdType, MessageType> create_LIoOpReceive(Environment__s_Compile._ILPacket<IdType, MessageType> r) {
      return new LIoOp_LIoOpReceive<IdType, MessageType>(r);
    }
    public static _ILIoOp<IdType, MessageType> create_LIoOpTimeoutReceive() {
      return new LIoOp_LIoOpTimeoutReceive<IdType, MessageType>();
    }
    public static _ILIoOp<IdType, MessageType> create_LIoOpReadClock(BigInteger t) {
      return new LIoOp_LIoOpReadClock<IdType, MessageType>(t);
    }
    public bool is_LIoOpSend { get { return this is LIoOp_LIoOpSend<IdType, MessageType>; } }
    public bool is_LIoOpReceive { get { return this is LIoOp_LIoOpReceive<IdType, MessageType>; } }
    public bool is_LIoOpTimeoutReceive { get { return this is LIoOp_LIoOpTimeoutReceive<IdType, MessageType>; } }
    public bool is_LIoOpReadClock { get { return this is LIoOp_LIoOpReadClock<IdType, MessageType>; } }
    public Environment__s_Compile._ILPacket<IdType, MessageType> dtor_s {
      get {
        var d = this;
        return ((LIoOp_LIoOpSend<IdType, MessageType>)d)._s;
      }
    }
    public Environment__s_Compile._ILPacket<IdType, MessageType> dtor_r {
      get {
        var d = this;
        return ((LIoOp_LIoOpReceive<IdType, MessageType>)d)._r;
      }
    }
    public BigInteger dtor_t {
      get {
        var d = this;
        return ((LIoOp_LIoOpReadClock<IdType, MessageType>)d)._t;
      }
    }
    public abstract _ILIoOp<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1);
  }
  public class LIoOp_LIoOpSend<IdType, MessageType> : LIoOp<IdType, MessageType> {
    public readonly Environment__s_Compile._ILPacket<IdType, MessageType> _s;
    public LIoOp_LIoOpSend(Environment__s_Compile._ILPacket<IdType, MessageType> s) {
      this._s = s;
    }
    public override _ILIoOp<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILIoOp<__IdType, __MessageType> dt) { return dt; }
      return new LIoOp_LIoOpSend<__IdType, __MessageType>((_s).DowncastClone<__IdType, __MessageType>(Dafny.Helpers.CastConverter<IdType, __IdType>, Dafny.Helpers.CastConverter<MessageType, __MessageType>));
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LIoOp_LIoOpSend<IdType, MessageType>;
      return oth != null && object.Equals(this._s, oth._s);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._s));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "Environment__s_Compile.LIoOp.LIoOpSend";
      ss += "(";
      ss += Dafny.Helpers.ToString(this._s);
      ss += ")";
      return ss;
    }
  }
  public class LIoOp_LIoOpReceive<IdType, MessageType> : LIoOp<IdType, MessageType> {
    public readonly Environment__s_Compile._ILPacket<IdType, MessageType> _r;
    public LIoOp_LIoOpReceive(Environment__s_Compile._ILPacket<IdType, MessageType> r) {
      this._r = r;
    }
    public override _ILIoOp<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILIoOp<__IdType, __MessageType> dt) { return dt; }
      return new LIoOp_LIoOpReceive<__IdType, __MessageType>((_r).DowncastClone<__IdType, __MessageType>(Dafny.Helpers.CastConverter<IdType, __IdType>, Dafny.Helpers.CastConverter<MessageType, __MessageType>));
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LIoOp_LIoOpReceive<IdType, MessageType>;
      return oth != null && object.Equals(this._r, oth._r);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._r));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LIoOp.LIoOpReceive";
      s += "(";
      s += Dafny.Helpers.ToString(this._r);
      s += ")";
      return s;
    }
  }
  public class LIoOp_LIoOpTimeoutReceive<IdType, MessageType> : LIoOp<IdType, MessageType> {
    public LIoOp_LIoOpTimeoutReceive() {
    }
    public override _ILIoOp<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILIoOp<__IdType, __MessageType> dt) { return dt; }
      return new LIoOp_LIoOpTimeoutReceive<__IdType, __MessageType>();
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LIoOp_LIoOpTimeoutReceive<IdType, MessageType>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LIoOp.LIoOpTimeoutReceive";
      return s;
    }
  }
  public class LIoOp_LIoOpReadClock<IdType, MessageType> : LIoOp<IdType, MessageType> {
    public readonly BigInteger _t;
    public LIoOp_LIoOpReadClock(BigInteger t) {
      this._t = t;
    }
    public override _ILIoOp<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILIoOp<__IdType, __MessageType> dt) { return dt; }
      return new LIoOp_LIoOpReadClock<__IdType, __MessageType>(_t);
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LIoOp_LIoOpReadClock<IdType, MessageType>;
      return oth != null && this._t == oth._t;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LIoOp.LIoOpReadClock";
      s += "(";
      s += Dafny.Helpers.ToString(this._t);
      s += ")";
      return s;
    }
  }

  public interface _ILEnvStep<IdType, MessageType> {
    bool is_LEnvStepHostIos { get; }
    bool is_LEnvStepDeliverPacket { get; }
    bool is_LEnvStepAdvanceTime { get; }
    bool is_LEnvStepStutter { get; }
    IdType dtor_actor { get; }
    Dafny.ISequence<Environment__s_Compile._ILIoOp<IdType, MessageType>> dtor_ios { get; }
    Environment__s_Compile._ILPacket<IdType, MessageType> dtor_p { get; }
    _ILEnvStep<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1);
  }
  public abstract class LEnvStep<IdType, MessageType> : _ILEnvStep<IdType, MessageType> {
    public LEnvStep() { }
    public static Environment__s_Compile._ILEnvStep<IdType, MessageType> Default() {
      return create_LEnvStepAdvanceTime();
    }
    public static Dafny.TypeDescriptor<Environment__s_Compile._ILEnvStep<IdType, MessageType>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Environment__s_Compile._ILEnvStep<IdType, MessageType>>(Environment__s_Compile.LEnvStep<IdType, MessageType>.Default());
    }
    public static _ILEnvStep<IdType, MessageType> create_LEnvStepHostIos(IdType actor, Dafny.ISequence<Environment__s_Compile._ILIoOp<IdType, MessageType>> ios) {
      return new LEnvStep_LEnvStepHostIos<IdType, MessageType>(actor, ios);
    }
    public static _ILEnvStep<IdType, MessageType> create_LEnvStepDeliverPacket(Environment__s_Compile._ILPacket<IdType, MessageType> p) {
      return new LEnvStep_LEnvStepDeliverPacket<IdType, MessageType>(p);
    }
    public static _ILEnvStep<IdType, MessageType> create_LEnvStepAdvanceTime() {
      return new LEnvStep_LEnvStepAdvanceTime<IdType, MessageType>();
    }
    public static _ILEnvStep<IdType, MessageType> create_LEnvStepStutter() {
      return new LEnvStep_LEnvStepStutter<IdType, MessageType>();
    }
    public bool is_LEnvStepHostIos { get { return this is LEnvStep_LEnvStepHostIos<IdType, MessageType>; } }
    public bool is_LEnvStepDeliverPacket { get { return this is LEnvStep_LEnvStepDeliverPacket<IdType, MessageType>; } }
    public bool is_LEnvStepAdvanceTime { get { return this is LEnvStep_LEnvStepAdvanceTime<IdType, MessageType>; } }
    public bool is_LEnvStepStutter { get { return this is LEnvStep_LEnvStepStutter<IdType, MessageType>; } }
    public IdType dtor_actor {
      get {
        var d = this;
        return ((LEnvStep_LEnvStepHostIos<IdType, MessageType>)d)._actor;
      }
    }
    public Dafny.ISequence<Environment__s_Compile._ILIoOp<IdType, MessageType>> dtor_ios {
      get {
        var d = this;
        return ((LEnvStep_LEnvStepHostIos<IdType, MessageType>)d)._ios;
      }
    }
    public Environment__s_Compile._ILPacket<IdType, MessageType> dtor_p {
      get {
        var d = this;
        return ((LEnvStep_LEnvStepDeliverPacket<IdType, MessageType>)d)._p;
      }
    }
    public abstract _ILEnvStep<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1);
  }
  public class LEnvStep_LEnvStepHostIos<IdType, MessageType> : LEnvStep<IdType, MessageType> {
    public readonly IdType _actor;
    public readonly Dafny.ISequence<Environment__s_Compile._ILIoOp<IdType, MessageType>> _ios;
    public LEnvStep_LEnvStepHostIos(IdType actor, Dafny.ISequence<Environment__s_Compile._ILIoOp<IdType, MessageType>> ios) {
      this._actor = actor;
      this._ios = ios;
    }
    public override _ILEnvStep<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILEnvStep<__IdType, __MessageType> dt) { return dt; }
      return new LEnvStep_LEnvStepHostIos<__IdType, __MessageType>(converter0(_actor), (_ios).DowncastClone<Environment__s_Compile._ILIoOp<__IdType, __MessageType>>(Dafny.Helpers.CastConverter<Environment__s_Compile._ILIoOp<IdType, MessageType>, Environment__s_Compile._ILIoOp<__IdType, __MessageType>>));
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LEnvStep_LEnvStepHostIos<IdType, MessageType>;
      return oth != null && object.Equals(this._actor, oth._actor) && object.Equals(this._ios, oth._ios);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._actor));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ios));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LEnvStep.LEnvStepHostIos";
      s += "(";
      s += Dafny.Helpers.ToString(this._actor);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ios);
      s += ")";
      return s;
    }
  }
  public class LEnvStep_LEnvStepDeliverPacket<IdType, MessageType> : LEnvStep<IdType, MessageType> {
    public readonly Environment__s_Compile._ILPacket<IdType, MessageType> _p;
    public LEnvStep_LEnvStepDeliverPacket(Environment__s_Compile._ILPacket<IdType, MessageType> p) {
      this._p = p;
    }
    public override _ILEnvStep<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILEnvStep<__IdType, __MessageType> dt) { return dt; }
      return new LEnvStep_LEnvStepDeliverPacket<__IdType, __MessageType>((_p).DowncastClone<__IdType, __MessageType>(Dafny.Helpers.CastConverter<IdType, __IdType>, Dafny.Helpers.CastConverter<MessageType, __MessageType>));
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LEnvStep_LEnvStepDeliverPacket<IdType, MessageType>;
      return oth != null && object.Equals(this._p, oth._p);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._p));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LEnvStep.LEnvStepDeliverPacket";
      s += "(";
      s += Dafny.Helpers.ToString(this._p);
      s += ")";
      return s;
    }
  }
  public class LEnvStep_LEnvStepAdvanceTime<IdType, MessageType> : LEnvStep<IdType, MessageType> {
    public LEnvStep_LEnvStepAdvanceTime() {
    }
    public override _ILEnvStep<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILEnvStep<__IdType, __MessageType> dt) { return dt; }
      return new LEnvStep_LEnvStepAdvanceTime<__IdType, __MessageType>();
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LEnvStep_LEnvStepAdvanceTime<IdType, MessageType>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LEnvStep.LEnvStepAdvanceTime";
      return s;
    }
  }
  public class LEnvStep_LEnvStepStutter<IdType, MessageType> : LEnvStep<IdType, MessageType> {
    public LEnvStep_LEnvStepStutter() {
    }
    public override _ILEnvStep<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILEnvStep<__IdType, __MessageType> dt) { return dt; }
      return new LEnvStep_LEnvStepStutter<__IdType, __MessageType>();
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LEnvStep_LEnvStepStutter<IdType, MessageType>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LEnvStep.LEnvStepStutter";
      return s;
    }
  }

  public interface _ILHostInfo<IdType, MessageType> {
    bool is_LHostInfo { get; }
    Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>> dtor_queue { get; }
  }
  public class LHostInfo<IdType, MessageType> : _ILHostInfo<IdType, MessageType> {
    public readonly Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>> _queue;
    public LHostInfo(Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>> queue) {
      this._queue = queue;
    }
    public static Dafny.ISequence<Environment__s_Compile._ILPacket<__IdType, __MessageType>> DowncastClone<__IdType, __MessageType>(Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>> _this, Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      return (_this).DowncastClone<Environment__s_Compile._ILPacket<__IdType, __MessageType>>(Dafny.Helpers.CastConverter<Environment__s_Compile._ILPacket<IdType, MessageType>, Environment__s_Compile._ILPacket<__IdType, __MessageType>>);
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LHostInfo<IdType, MessageType>;
      return oth != null && object.Equals(this._queue, oth._queue);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._queue));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LHostInfo.LHostInfo";
      s += "(";
      s += Dafny.Helpers.ToString(this._queue);
      s += ")";
      return s;
    }
    public static Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>> Default() {
      return Dafny.Sequence<Environment__s_Compile._ILPacket<IdType, MessageType>>.Empty;
    }
    public static Dafny.TypeDescriptor<Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>>>(Dafny.Sequence<Environment__s_Compile._ILPacket<IdType, MessageType>>.Empty);
    }
    public static _ILHostInfo<IdType, MessageType> create(Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>> queue) {
      return new LHostInfo<IdType, MessageType>(queue);
    }
    public static _ILHostInfo<IdType, MessageType> create_LHostInfo(Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>> queue) {
      return create(queue);
    }
    public bool is_LHostInfo { get { return true; } }
    public Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>> dtor_queue {
      get {
        return this._queue;
      }
    }
  }

  public interface _ILEnvironment<IdType, MessageType> {
    bool is_LEnvironment { get; }
    BigInteger dtor_time { get; }
    Dafny.ISet<Environment__s_Compile._ILPacket<IdType, MessageType>> dtor_sentPackets { get; }
    Dafny.IMap<IdType,Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>>> dtor_hostInfo { get; }
    Environment__s_Compile._ILEnvStep<IdType, MessageType> dtor_nextStep { get; }
    _ILEnvironment<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1);
  }
  public class LEnvironment<IdType, MessageType> : _ILEnvironment<IdType, MessageType> {
    public readonly BigInteger _time;
    public readonly Dafny.ISet<Environment__s_Compile._ILPacket<IdType, MessageType>> _sentPackets;
    public readonly Dafny.IMap<IdType,Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>>> _hostInfo;
    public readonly Environment__s_Compile._ILEnvStep<IdType, MessageType> _nextStep;
    public LEnvironment(BigInteger time, Dafny.ISet<Environment__s_Compile._ILPacket<IdType, MessageType>> sentPackets, Dafny.IMap<IdType,Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>>> hostInfo, Environment__s_Compile._ILEnvStep<IdType, MessageType> nextStep) {
      this._time = time;
      this._sentPackets = sentPackets;
      this._hostInfo = hostInfo;
      this._nextStep = nextStep;
    }
    public _ILEnvironment<__IdType, __MessageType> DowncastClone<__IdType, __MessageType>(Func<IdType, __IdType> converter0, Func<MessageType, __MessageType> converter1) {
      if (this is _ILEnvironment<__IdType, __MessageType> dt) { return dt; }
      return new LEnvironment<__IdType, __MessageType>(_time, (_sentPackets).DowncastClone<Environment__s_Compile._ILPacket<__IdType, __MessageType>>(Dafny.Helpers.CastConverter<Environment__s_Compile._ILPacket<IdType, MessageType>, Environment__s_Compile._ILPacket<__IdType, __MessageType>>), (_hostInfo).DowncastClone<__IdType, Dafny.ISequence<Environment__s_Compile._ILPacket<__IdType, __MessageType>>>(Dafny.Helpers.CastConverter<IdType, __IdType>, Dafny.Helpers.CastConverter<Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>>, Dafny.ISequence<Environment__s_Compile._ILPacket<__IdType, __MessageType>>>), (_nextStep).DowncastClone<__IdType, __MessageType>(Dafny.Helpers.CastConverter<IdType, __IdType>, Dafny.Helpers.CastConverter<MessageType, __MessageType>));
    }
    public override bool Equals(object other) {
      var oth = other as Environment__s_Compile.LEnvironment<IdType, MessageType>;
      return oth != null && this._time == oth._time && object.Equals(this._sentPackets, oth._sentPackets) && object.Equals(this._hostInfo, oth._hostInfo) && object.Equals(this._nextStep, oth._nextStep);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._time));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._sentPackets));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._hostInfo));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._nextStep));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Environment__s_Compile.LEnvironment.LEnvironment";
      s += "(";
      s += Dafny.Helpers.ToString(this._time);
      s += ", ";
      s += Dafny.Helpers.ToString(this._sentPackets);
      s += ", ";
      s += Dafny.Helpers.ToString(this._hostInfo);
      s += ", ";
      s += Dafny.Helpers.ToString(this._nextStep);
      s += ")";
      return s;
    }
    public static Environment__s_Compile._ILEnvironment<IdType, MessageType> Default() {
      return create(BigInteger.Zero, Dafny.Set<Environment__s_Compile._ILPacket<IdType, MessageType>>.Empty, Dafny.Map<IdType, Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>>>.Empty, Environment__s_Compile.LEnvStep<IdType, MessageType>.Default());
    }
    public static Dafny.TypeDescriptor<Environment__s_Compile._ILEnvironment<IdType, MessageType>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Environment__s_Compile._ILEnvironment<IdType, MessageType>>(Environment__s_Compile.LEnvironment<IdType, MessageType>.Default());
    }
    public static _ILEnvironment<IdType, MessageType> create(BigInteger time, Dafny.ISet<Environment__s_Compile._ILPacket<IdType, MessageType>> sentPackets, Dafny.IMap<IdType,Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>>> hostInfo, Environment__s_Compile._ILEnvStep<IdType, MessageType> nextStep) {
      return new LEnvironment<IdType, MessageType>(time, sentPackets, hostInfo, nextStep);
    }
    public static _ILEnvironment<IdType, MessageType> create_LEnvironment(BigInteger time, Dafny.ISet<Environment__s_Compile._ILPacket<IdType, MessageType>> sentPackets, Dafny.IMap<IdType,Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>>> hostInfo, Environment__s_Compile._ILEnvStep<IdType, MessageType> nextStep) {
      return create(time, sentPackets, hostInfo, nextStep);
    }
    public bool is_LEnvironment { get { return true; } }
    public BigInteger dtor_time {
      get {
        return this._time;
      }
    }
    public Dafny.ISet<Environment__s_Compile._ILPacket<IdType, MessageType>> dtor_sentPackets {
      get {
        return this._sentPackets;
      }
    }
    public Dafny.IMap<IdType,Dafny.ISequence<Environment__s_Compile._ILPacket<IdType, MessageType>>> dtor_hostInfo {
      get {
        return this._hostInfo;
      }
    }
    public Environment__s_Compile._ILEnvStep<IdType, MessageType> dtor_nextStep {
      get {
        return this._nextStep;
      }
    }
  }

} // end of namespace Environment__s_Compile
namespace Native____Io__s_Compile {

  public partial class HostEnvironment {
    public HostEnvironment() {
    }
  }

  public partial class HostConstants {
    public HostConstants() {
    }
  }

  public partial class OkState {
    public OkState() {
    }
  }

  public partial class NowState {
    public NowState() {
    }
  }

  public partial class Time {
    public Time() {
    }
  }

  public interface _IEndPoint {
    bool is_EndPoint { get; }
    Dafny.ISequence<byte> dtor_addr { get; }
    ushort dtor_port { get; }
    _IEndPoint DowncastClone();
  }
  public class EndPoint : _IEndPoint {
    public readonly Dafny.ISequence<byte> _addr;
    public readonly ushort _port;
    public EndPoint(Dafny.ISequence<byte> addr, ushort port) {
      this._addr = addr;
      this._port = port;
    }
    public _IEndPoint DowncastClone() {
      if (this is _IEndPoint dt) { return dt; }
      return new EndPoint(_addr, _port);
    }
    public override bool Equals(object other) {
      var oth = other as Native____Io__s_Compile.EndPoint;
      return oth != null && object.Equals(this._addr, oth._addr) && this._port == oth._port;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._addr));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._port));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Native____Io__s_Compile.EndPoint.EndPoint";
      s += "(";
      s += Dafny.Helpers.ToString(this._addr);
      s += ", ";
      s += Dafny.Helpers.ToString(this._port);
      s += ")";
      return s;
    }
    private static readonly Native____Io__s_Compile._IEndPoint theDefault = create(Dafny.Sequence<byte>.Empty, 0);
    public static Native____Io__s_Compile._IEndPoint Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Native____Io__s_Compile._IEndPoint> _TYPE = new Dafny.TypeDescriptor<Native____Io__s_Compile._IEndPoint>(Native____Io__s_Compile.EndPoint.Default());
    public static Dafny.TypeDescriptor<Native____Io__s_Compile._IEndPoint> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IEndPoint create(Dafny.ISequence<byte> addr, ushort port) {
      return new EndPoint(addr, port);
    }
    public static _IEndPoint create_EndPoint(Dafny.ISequence<byte> addr, ushort port) {
      return create(addr, port);
    }
    public bool is_EndPoint { get { return true; } }
    public Dafny.ISequence<byte> dtor_addr {
      get {
        return this._addr;
      }
    }
    public ushort dtor_port {
      get {
        return this._port;
      }
    }
  }

  public partial class UdpState {
    public UdpState() {
    }
  }

  public partial class IPEndPoint {
    public IPEndPoint() {
    }
  }

  public partial class UdpClient {
    public UdpClient() {
    }
  }

  public partial class FileSystemState {
    public FileSystemState() {
    }
  }

  public partial class MutableSet<T> {
    private Dafny.TypeDescriptor<T> _td_T;
    public MutableSet(Dafny.TypeDescriptor<T> _td_T) {
      this._td_T = _td_T;
    }
  }

  public partial class MutableMap<K, V> {
    public MutableMap() {
    }
  }

  public partial class Arrays {
    public Arrays() {
    }
  }

} // end of namespace Native____Io__s_Compile
namespace Collections____Seqs__s_Compile {

} // end of namespace Collections____Seqs__s_Compile
namespace Math____power__s_Compile {

} // end of namespace Math____power__s_Compile
namespace Common____SeqIsUniqueDef__i_Compile {

} // end of namespace Common____SeqIsUniqueDef__i_Compile
namespace Common____UdpClient__i_Compile {

  public partial class __default {
    public static bool EndPointIsValidIPV4(Native____Io__s_Compile._IEndPoint endPoint) {
      return ((new BigInteger(((endPoint).dtor_addr).Count)) == (new BigInteger(4))) && ((((ushort)(0)) <= ((endPoint).dtor_port)) && (((endPoint).dtor_port) <= ((ushort)(65535))));
    }
  }
} // end of namespace Common____UdpClient__i_Compile
namespace CmdLineParser__i_Compile {

  public partial class __default {
    public static _System._ITuple2<bool, byte> ascii__to__int(ushort @short) {
      if ((((ushort)(48)) <= (@short)) && ((@short) <= ((ushort)(57)))) {
        return _System.Tuple2<bool, byte>.create(true, (byte)((ushort)((@short) - ((ushort)(48)))));
      } else {
        return _System.Tuple2<bool, byte>.create(false, (byte)(0));
      }
    }
    public static BigInteger power10(BigInteger e)
    {
      BigInteger val = BigInteger.Zero;
      if ((e).Sign == 0) {
        val = BigInteger.One;
        return val;
      } else {
        BigInteger _5_tmp;
        BigInteger _out0;
        _out0 = CmdLineParser__i_Compile.__default.power10((e) - (BigInteger.One));
        _5_tmp = _out0;
        val = (new BigInteger(10)) * (_5_tmp);
        return val;
      }
      return val;
    }
    public static _System._ITuple2<bool, Dafny.ISequence<byte>> shorts__to__bytes(Dafny.ISequence<ushort> shorts) {
      if ((new BigInteger((shorts).Count)).Sign == 0) {
        return _System.Tuple2<bool, Dafny.ISequence<byte>>.create(true, Dafny.Sequence<byte>.FromElements());
      } else {
        _System._ITuple2<bool, Dafny.ISequence<byte>> _6_tuple = CmdLineParser__i_Compile.__default.shorts__to__bytes((shorts).Drop(BigInteger.One));
        bool _7_ok = (_6_tuple).dtor__0;
        Dafny.ISequence<byte> _8_rest = (_6_tuple).dtor__1;
        _System._ITuple2<bool, byte> _9_tuple_k = CmdLineParser__i_Compile.__default.ascii__to__int((shorts).Select(BigInteger.Zero));
        bool _10_ok_k = (_9_tuple_k).dtor__0;
        byte _11_a__byte = (_9_tuple_k).dtor__1;
        if ((_7_ok) && (_10_ok_k)) {
          return _System.Tuple2<bool, Dafny.ISequence<byte>>.create(true, Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements(_11_a__byte), _8_rest));
        } else {
          return _System.Tuple2<bool, Dafny.ISequence<byte>>.create(false, Dafny.Sequence<byte>.FromElements());
        }
      }
    }
    public static BigInteger bytes__to__decimal(Dafny.ISequence<byte> bytes) {
      if ((new BigInteger((bytes).Count)).Sign == 0) {
        return BigInteger.Zero;
      } else {
        return (new BigInteger((bytes).Select((new BigInteger((bytes).Count)) - (BigInteger.One)))) + ((new BigInteger(10)) * (CmdLineParser__i_Compile.__default.bytes__to__decimal((bytes).Subsequence(BigInteger.Zero, (new BigInteger((bytes).Count)) - (BigInteger.One)))));
      }
    }
    public static _System._ITuple2<bool, BigInteger> shorts__to__nat(Dafny.ISequence<ushort> shorts) {
      if ((new BigInteger((shorts).Count)).Sign == 0) {
        return _System.Tuple2<bool, BigInteger>.create(false, BigInteger.Zero);
      } else {
        _System._ITuple2<bool, Dafny.ISequence<byte>> _12_tuple = CmdLineParser__i_Compile.__default.shorts__to__bytes(shorts);
        bool _13_ok = (_12_tuple).dtor__0;
        Dafny.ISequence<byte> _14_bytes = (_12_tuple).dtor__1;
        if (!(_13_ok)) {
          return _System.Tuple2<bool, BigInteger>.create(false, BigInteger.Zero);
        } else {
          return _System.Tuple2<bool, BigInteger>.create(true, CmdLineParser__i_Compile.__default.bytes__to__decimal(_14_bytes));
        }
      }
    }
    public static _System._ITuple2<bool, byte> shorts__to__byte(Dafny.ISequence<ushort> shorts) {
      _System._ITuple2<bool, BigInteger> _15_tuple = CmdLineParser__i_Compile.__default.shorts__to__nat(shorts);
      bool _16_ok = (_15_tuple).dtor__0;
      BigInteger _17_val = (_15_tuple).dtor__1;
      if (((_17_val).Sign != -1) && ((_17_val) < (new BigInteger(256)))) {
        return _System.Tuple2<bool, byte>.create(true, (byte)(_17_val));
      } else {
        return _System.Tuple2<bool, byte>.create(false, (byte)(0));
      }
    }
    public static _System._ITuple2<bool, ushort> shorts__to__uint16(Dafny.ISequence<ushort> shorts) {
      _System._ITuple2<bool, BigInteger> _18_tuple = CmdLineParser__i_Compile.__default.shorts__to__nat(shorts);
      bool _19_ok = (_18_tuple).dtor__0;
      BigInteger _20_val = (_18_tuple).dtor__1;
      if (((_20_val).Sign != -1) && ((_20_val) < (new BigInteger(65536)))) {
        return _System.Tuple2<bool, ushort>.create(true, (ushort)(_20_val));
      } else {
        return _System.Tuple2<bool, ushort>.create(false, (ushort)(0));
      }
    }
    public static _System._ITuple2<bool, uint> shorts__to__uint32(Dafny.ISequence<ushort> shorts) {
      _System._ITuple2<bool, BigInteger> _21_tuple = CmdLineParser__i_Compile.__default.shorts__to__nat(shorts);
      bool _22_ok = (_21_tuple).dtor__0;
      BigInteger _23_val = (_21_tuple).dtor__1;
      if (((_23_val).Sign != -1) && ((_23_val) < (new BigInteger(4294967296L)))) {
        return _System.Tuple2<bool, uint>.create(true, (uint)(_23_val));
      } else {
        return _System.Tuple2<bool, uint>.create(false, 0U);
      }
    }
    public static bool is__ascii__period(ushort @short) {
      return (@short) == ((ushort)(46));
    }
    public static _System._ITuple2<bool, Dafny.ISequence<byte>> parse__ip__addr__helper(Dafny.ISequence<ushort> ip__shorts, Dafny.ISequence<ushort> current__octet__shorts)
    {
      if ((new BigInteger((ip__shorts).Count)).Sign == 0) {
        _System._ITuple2<bool, byte> _24_tuple = CmdLineParser__i_Compile.__default.shorts__to__byte(current__octet__shorts);
        bool _25_okay = (_24_tuple).dtor__0;
        byte _26_b = (_24_tuple).dtor__1;
        if (!(_25_okay)) {
          return _System.Tuple2<bool, Dafny.ISequence<byte>>.create(false, Dafny.Sequence<byte>.FromElements());
        } else {
          return _System.Tuple2<bool, Dafny.ISequence<byte>>.create(true, Dafny.Sequence<byte>.FromElements(_26_b));
        }
      } else if (CmdLineParser__i_Compile.__default.is__ascii__period((ip__shorts).Select(BigInteger.Zero))) {
        _System._ITuple2<bool, byte> _27_tuple = CmdLineParser__i_Compile.__default.shorts__to__byte(current__octet__shorts);
        bool _28_okay = (_27_tuple).dtor__0;
        byte _29_b = (_27_tuple).dtor__1;
        if (!(_28_okay)) {
          return _System.Tuple2<bool, Dafny.ISequence<byte>>.create(false, Dafny.Sequence<byte>.FromElements());
        } else {
          _System._ITuple2<bool, Dafny.ISequence<byte>> _30_tuple_k = CmdLineParser__i_Compile.__default.parse__ip__addr__helper((ip__shorts).Drop(BigInteger.One), Dafny.Sequence<ushort>.FromElements());
          bool _31_ok = (_30_tuple_k).dtor__0;
          Dafny.ISequence<byte> _32_ip__bytes = (_30_tuple_k).dtor__1;
          if (!(_31_ok)) {
            return _System.Tuple2<bool, Dafny.ISequence<byte>>.create(false, Dafny.Sequence<byte>.FromElements());
          } else {
            return _System.Tuple2<bool, Dafny.ISequence<byte>>.create(true, Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements(_29_b), _32_ip__bytes));
          }
        }
      } else {
        return CmdLineParser__i_Compile.__default.parse__ip__addr__helper((ip__shorts).Drop(BigInteger.One), Dafny.Sequence<ushort>.Concat(current__octet__shorts, Dafny.Sequence<ushort>.FromElements((ip__shorts).Select(BigInteger.Zero))));
      }
    }
    public static _System._ITuple2<bool, Dafny.ISequence<byte>> parse__ip__addr(Dafny.ISequence<ushort> ip__shorts) {
      _System._ITuple2<bool, Dafny.ISequence<byte>> _33_tuple = CmdLineParser__i_Compile.__default.parse__ip__addr__helper(ip__shorts, Dafny.Sequence<ushort>.FromElements());
      bool _34_ok = (_33_tuple).dtor__0;
      Dafny.ISequence<byte> _35_ip__bytes = (_33_tuple).dtor__1;
      if ((_34_ok) && ((new BigInteger((_35_ip__bytes).Count)) == (new BigInteger(4)))) {
        return _System.Tuple2<bool, Dafny.ISequence<byte>>.create(true, _35_ip__bytes);
      } else {
        return _System.Tuple2<bool, Dafny.ISequence<byte>>.create(false, Dafny.Sequence<byte>.FromElements());
      }
    }
    public static _System._ITuple2<bool, Native____Io__s_Compile._IEndPoint> parse__end__point(Dafny.ISequence<ushort> ip__shorts, Dafny.ISequence<ushort> port__shorts)
    {
      _System._ITuple2<bool, Dafny.ISequence<byte>> _36_tuple = CmdLineParser__i_Compile.__default.parse__ip__addr(ip__shorts);
      bool _37_okay = (_36_tuple).dtor__0;
      Dafny.ISequence<byte> _38_ip__bytes = (_36_tuple).dtor__1;
      if (!(_37_okay)) {
        return _System.Tuple2<bool, Native____Io__s_Compile._IEndPoint>.create(false, Native____Io__s_Compile.EndPoint.create(Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(0), (byte)(0), (byte)(0)), (ushort)(0)));
      } else {
        _System._ITuple2<bool, ushort> _39_tuple_k = CmdLineParser__i_Compile.__default.shorts__to__uint16(port__shorts);
        bool _40_okay_k = (_39_tuple_k).dtor__0;
        ushort _41_port = (_39_tuple_k).dtor__1;
        if (!(_40_okay_k)) {
          return _System.Tuple2<bool, Native____Io__s_Compile._IEndPoint>.create(false, Native____Io__s_Compile.EndPoint.create(Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(0), (byte)(0), (byte)(0)), (ushort)(0)));
        } else {
          return _System.Tuple2<bool, Native____Io__s_Compile._IEndPoint>.create(true, Native____Io__s_Compile.EndPoint.create(_38_ip__bytes, _41_port));
        }
      }
    }
    public static bool test__unique_k(Dafny.ISequence<Native____Io__s_Compile._IEndPoint> endpoints)
    {
      bool unique = false;
      unique = true;
      BigInteger _42_i;
      _42_i = BigInteger.Zero;
      while ((_42_i) < (new BigInteger((endpoints).Count))) {
        BigInteger _43_j;
        _43_j = BigInteger.Zero;
        while ((_43_j) < (new BigInteger((endpoints).Count))) {
          if (((_42_i) != (_43_j)) && (object.Equals((endpoints).Select(_42_i), (endpoints).Select(_43_j)))) {
            unique = false;
            return unique;
          }
          _43_j = (_43_j) + (BigInteger.One);
        }
        _42_i = (_42_i) + (BigInteger.One);
      }
      return unique;
    }
    public static _System._ITuple2<bool, Dafny.ISequence<Native____Io__s_Compile._IEndPoint>> parse__end__points(Dafny.ISequence<Dafny.ISequence<ushort>> args) {
      if ((new BigInteger((args).Count)).Sign == 0) {
        return _System.Tuple2<bool, Dafny.ISequence<Native____Io__s_Compile._IEndPoint>>.create(true, Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.FromElements());
      } else {
        _System._ITuple2<bool, Native____Io__s_Compile._IEndPoint> _let_tmp_rhs0 = CmdLineParser__i_Compile.__default.parse__end__point((args).Select(BigInteger.Zero), (args).Select(BigInteger.One));
        bool _44_ok1 = _let_tmp_rhs0.dtor__0;
        Native____Io__s_Compile._IEndPoint _45_ep = _let_tmp_rhs0.dtor__1;
        _System._ITuple2<bool, Dafny.ISequence<Native____Io__s_Compile._IEndPoint>> _let_tmp_rhs1 = CmdLineParser__i_Compile.__default.parse__end__points((args).Drop(new BigInteger(2)));
        bool _46_ok2 = _let_tmp_rhs1.dtor__0;
        Dafny.ISequence<Native____Io__s_Compile._IEndPoint> _47_rest = _let_tmp_rhs1.dtor__1;
        if (!((_44_ok1) && (_46_ok2))) {
          return _System.Tuple2<bool, Dafny.ISequence<Native____Io__s_Compile._IEndPoint>>.create(false, Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.FromElements());
        } else {
          return _System.Tuple2<bool, Dafny.ISequence<Native____Io__s_Compile._IEndPoint>>.create(true, Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.Concat(Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.FromElements(_45_ep), _47_rest));
        }
      }
    }
    public static Dafny.ISequence<Dafny.ISequence<ushort>> collect__cmd__line__args()
    {
      Dafny.ISequence<Dafny.ISequence<ushort>> args = Dafny.Sequence<Dafny.ISequence<ushort>>.Empty;
      uint _48_num__args;
      uint _out1;
      _out1 = Native____Io__s_Compile.HostConstants.NumCommandLineArgs();
      _48_num__args = _out1;
      uint _49_i;
      _49_i = 0U;
      args = Dafny.Sequence<Dafny.ISequence<ushort>>.FromElements();
      while ((_49_i) < (_48_num__args)) {
        ushort[] _50_arg;
        ushort[] _out2;
        _out2 = Native____Io__s_Compile.HostConstants.GetCommandLineArg((ulong)(_49_i));
        _50_arg = _out2;
        args = Dafny.Sequence<Dafny.ISequence<ushort>>.Concat(args, Dafny.Sequence<Dafny.ISequence<ushort>>.FromElements(Dafny.Helpers.SeqFromArray(_50_arg)));
        _49_i = (_49_i) + (1U);
      }
      return args;
    }
  }
} // end of namespace CmdLineParser__i_Compile
namespace Native____NativeTypes__i_Compile {

  public partial class __default {
    public static ulong Uint64Size() {
      return 8UL;
    }
    public static ulong Uint32Size() {
      return 4UL;
    }
    public static ulong Uint16Size() {
      return 2UL;
    }
  }
} // end of namespace Native____NativeTypes__i_Compile
namespace Math____power2__s_Compile {

} // end of namespace Math____power2__s_Compile
namespace Math____mul__nonlinear__i_Compile {

} // end of namespace Math____mul__nonlinear__i_Compile
namespace Math____mul__auto__proofs__i_Compile {

} // end of namespace Math____mul__auto__proofs__i_Compile
namespace Math____mul__auto__i_Compile {

} // end of namespace Math____mul__auto__i_Compile
namespace Math____mul__i_Compile {

} // end of namespace Math____mul__i_Compile
namespace Math____power__i_Compile {

} // end of namespace Math____power__i_Compile
namespace Math____div__nonlinear__i_Compile {

} // end of namespace Math____div__nonlinear__i_Compile
namespace Math____mod__auto__proofs__i_Compile {

} // end of namespace Math____mod__auto__proofs__i_Compile
namespace Math____mod__auto__i_Compile {

} // end of namespace Math____mod__auto__i_Compile
namespace Math____div__def__i_Compile {

} // end of namespace Math____div__def__i_Compile
namespace Math____div__auto__proofs__i_Compile {

} // end of namespace Math____div__auto__proofs__i_Compile
namespace Math____div__auto__i_Compile {

} // end of namespace Math____div__auto__i_Compile
namespace Math____div__i_Compile {

} // end of namespace Math____div__i_Compile
namespace Math____power2__i_Compile {

} // end of namespace Math____power2__i_Compile
namespace Common____Util__i_Compile {

  public partial class __default {
    public static bool ShouldPrintProfilingInfo() {
      return false;
    }
    public static bool ShouldPrintProgress() {
      return false;
    }
    public static __A[] seqToArray__slow<__A>(Dafny.TypeDescriptor<__A> _td___A, Dafny.ISequence<__A> s)
    {
      __A[] a = new __A[0];
      BigInteger _51_len;
      _51_len = new BigInteger((s).Count);
      __A[] _nw0 = Dafny.ArrayHelpers.InitNewArray1<__A>(_td___A.Default(), Dafny.Helpers.ToIntChecked(_51_len, "array size exceeds memory limit"));
      a = _nw0;
      BigInteger _52_i;
      _52_i = BigInteger.Zero;
      while ((_52_i) < (_51_len)) {
        (a)[(int)((_52_i))] = (s).Select(_52_i);
        _52_i = (_52_i) + (BigInteger.One);
      }
      return a;
    }
    public static void seqIntoArrayOpt<__A>(Dafny.ISequence<__A> s, __A[] a)
    {
      ulong _53_i;
      _53_i = 0UL;
      while ((_53_i) < ((ulong)(s).LongCount)) {
        (a)[(int)((_53_i))] = (s).Select(_53_i);
        _53_i = (_53_i) + (1UL);
      }
    }
    public static __A[] seqToArrayOpt<__A>(Dafny.TypeDescriptor<__A> _td___A, Dafny.ISequence<__A> s)
    {
      __A[] a = new __A[0];
      __A[] _nw1 = Dafny.ArrayHelpers.InitNewArray1<__A>(_td___A.Default(), Dafny.Helpers.ToIntChecked((ulong)(s).LongCount, "array size exceeds memory limit"));
      a = _nw1;
      Common____Util__i_Compile.__default.seqIntoArrayOpt<__A>(s, a);
      return a;
    }
    public static void seqIntoArrayChar(Dafny.ISequence<char> s, char[] a)
    {
      ulong _54_i;
      _54_i = 0UL;
      while ((_54_i) < ((ulong)(s).LongCount)) {
        (a)[(int)((_54_i))] = (s).Select(_54_i);
        _54_i = (_54_i) + (1UL);
      }
    }
    public static void RecordTimingSeq(Dafny.ISequence<char> name, ulong start, ulong end)
    {
      if (Common____Util__i_Compile.__default.ShouldPrintProfilingInfo()) {
        char[] _55_name__array;
        char[] _nw2 = Dafny.ArrayHelpers.InitNewArray1<char>('D', Dafny.Helpers.ToIntChecked(new BigInteger((name).Count), "array size exceeds memory limit"));
        _55_name__array = _nw2;
        Common____Util__i_Compile.__default.seqIntoArrayChar(name, _55_name__array);
        ulong _56_time = 0;
        if ((start) <= (end)) {
          _56_time = (end) - (start);
        } else {
          _56_time = 18446744073709551615UL;
        }
        Native____Io__s_Compile.Time.RecordTiming(_55_name__array, _56_time);
      }
    }
    public static ulong SeqByteToUint64(Dafny.ISequence<byte> bs) {
      return ((((((((((((ulong)((bs).Select(BigInteger.Zero))) * (256UL)) * (256UL)) * (256UL)) * (4294967296UL)) + (((((ulong)((bs).Select(BigInteger.One))) * (256UL)) * (256UL)) * (4294967296UL))) + ((((ulong)((bs).Select(new BigInteger(2)))) * (256UL)) * (4294967296UL))) + (((ulong)((bs).Select(new BigInteger(3)))) * (4294967296UL))) + (((((ulong)((bs).Select(new BigInteger(4)))) * (256UL)) * (256UL)) * (256UL))) + ((((ulong)((bs).Select(new BigInteger(5)))) * (256UL)) * (256UL))) + (((ulong)((bs).Select(new BigInteger(6)))) * (256UL))) + ((ulong)((bs).Select(new BigInteger(7))));
    }
    public static Dafny.ISequence<byte> Uint64ToSeqByte(ulong u) {
      Dafny.ISequence<byte> _57_bs = Dafny.Sequence<byte>.FromElements((byte)((u) / (72057594037927936UL)), (byte)(((u) / (281474976710656UL)) % (256UL)), (byte)(((u) / (1099511627776UL)) % (256UL)), (byte)(((u) / (4294967296UL)) % (256UL)), (byte)(((u) / (16777216UL)) % (256UL)), (byte)(((u) / (65536UL)) % (256UL)), (byte)(((u) / (256UL)) % (256UL)), (byte)((u) % (256UL)));
      BigInteger _58_u__int = new BigInteger(u);
      return _57_bs;
    }
    public static ushort SeqByteToUint16(Dafny.ISequence<byte> bs) {
      return (ushort)(((ushort)(((ushort)((bs).Select(BigInteger.Zero))) * ((ushort)(256)))) + ((ushort)((bs).Select(BigInteger.One))));
    }
    public static Dafny.ISequence<byte> Uint16ToSeqByte(ushort u) {
      Dafny.ISequence<byte> _59_s = Dafny.Sequence<byte>.FromElements((byte)((ushort)(((ushort)((u) / ((ushort)(256)))) % ((ushort)(256)))), (byte)((ushort)((u) % ((ushort)(256)))));
      BigInteger _60_u__int = new BigInteger(u);
      return _59_s;
    }
  }
} // end of namespace Common____Util__i_Compile
namespace Common____SeqIsUnique__i_Compile {

  public partial class __default {
    public static Dafny.ISet<__X> SeqToSetConstruct<__X>(Dafny.ISequence<__X> xs)
    {
      Dafny.ISet<__X> s = Dafny.Set<__X>.Empty;
      s = Dafny.Set<__X>.FromElements();
      BigInteger _61_i;
      _61_i = BigInteger.Zero;
      while ((_61_i) < (new BigInteger((xs).Count))) {
        s = Dafny.Set<__X>.Union(s, Dafny.Set<__X>.FromElements((xs).Select(_61_i)));
        _61_i = (_61_i) + (BigInteger.One);
      }
      return s;
    }
    public static Dafny.ISequence<__X> SetToUniqueSeqConstruct<__X>(Dafny.TypeDescriptor<__X> _td___X, Dafny.ISet<__X> s)
    {
      Dafny.ISequence<__X> xs = Dafny.Sequence<__X>.Empty;
      __X[] _62_arr;
      __X[] _nw3 = Dafny.ArrayHelpers.InitNewArray1<__X>(_td___X.Default(), Dafny.Helpers.ToIntChecked(new BigInteger((s).Count), "array size exceeds memory limit"));
      _62_arr = _nw3;
      Dafny.ISet<__X> _63_s1;
      _63_s1 = s;
      while ((new BigInteger((_63_s1).Count)).Sign != 0) {
        __X _64_x;
        foreach (__X _assign_such_that_0 in (_63_s1).Elements) {
          _64_x = (__X)_assign_such_that_0;
          if ((_63_s1).Contains((_64_x))) {
            goto after__ASSIGN_SUCH_THAT_0;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 85)");
      after__ASSIGN_SUCH_THAT_0: ;
        var _index0 = (new BigInteger((s).Count)) - (new BigInteger((_63_s1).Count));
        (_62_arr)[(int)(_index0)] = _64_x;
        _63_s1 = Dafny.Set<__X>.Difference(_63_s1, Dafny.Set<__X>.FromElements(_64_x));
      }
      xs = Dafny.Helpers.SeqFromArray(_62_arr);
      return xs;
    }
    public static Dafny.ISequence<__X> SubsequenceConstruct<__X>(Dafny.TypeDescriptor<__X> _td___X, Dafny.ISequence<__X> xs, Func<__X, bool> f)
    {
      Dafny.ISequence<__X> xs_k = Dafny.Sequence<__X>.Empty;
      __X[] _65_arr;
      __X[] _nw4 = Dafny.ArrayHelpers.InitNewArray1<__X>(_td___X.Default(), Dafny.Helpers.ToIntChecked(new BigInteger((xs).Count), "array size exceeds memory limit"));
      _65_arr = _nw4;
      BigInteger _66_i;
      _66_i = BigInteger.Zero;
      BigInteger _67_j;
      _67_j = BigInteger.Zero;
      while ((_66_i) < (new BigInteger((xs).Count))) {
        if (Dafny.Helpers.Id<Func<__X, bool>>(f)((xs).Select(_66_i))) {
          (_65_arr)[(int)((_67_j))] = (xs).Select(_66_i);
          _67_j = (_67_j) + (BigInteger.One);
        }
        _66_i = (_66_i) + (BigInteger.One);
      }
      xs_k = Dafny.Helpers.SeqFromArray(_65_arr).Take(_67_j);
      return xs_k;
    }
    public static Dafny.ISequence<__X> UniqueSubsequenceConstruct<__X>(Dafny.TypeDescriptor<__X> _td___X, Dafny.ISequence<__X> xs, Func<__X, bool> f)
    {
      Dafny.ISequence<__X> xs_k = Dafny.Sequence<__X>.Empty;
      Dafny.ISet<__X> _68_s;
      _68_s = Dafny.Helpers.Id<Func<Dafny.ISequence<__X>, Func<__X, bool>, Dafny.ISet<__X>>>((_69_xs, _70_f) => ((System.Func<Dafny.ISet<__X>>)(() => {
        var _coll2 = new System.Collections.Generic.List<__X>();
        foreach (__X _compr_2 in (_69_xs).Elements) {
          __X _71_x = (__X)_compr_2;
          if (((_69_xs).Contains((_71_x))) && (Dafny.Helpers.Id<Func<__X, bool>>(_70_f)(_71_x))) {
            _coll2.Add(_71_x);
          }
        }
        return Dafny.Set<__X>.FromCollection(_coll2);
      }))())(xs, f);
      Dafny.ISequence<__X> _out3;
      _out3 = Common____SeqIsUnique__i_Compile.__default.SetToUniqueSeqConstruct<__X>(_td___X, _68_s);
      xs_k = _out3;
      return xs_k;
    }
    public static Dafny.ISequence<__X> AppendToUniqueSeq<__X>(Dafny.ISequence<__X> xs, __X x)
    {
      Dafny.ISequence<__X> _72_xs_k = Dafny.Sequence<__X>.Concat(xs, Dafny.Sequence<__X>.FromElements(x));
      return _72_xs_k;
    }
    public static Dafny.ISequence<__X> AppendToUniqueSeqMaybe<__X>(Dafny.ISequence<__X> xs, __X x)
    {
      if ((xs).Contains((x))) {
        return xs;
      } else {
        Dafny.ISequence<__X> _73_xs_k = Dafny.Sequence<__X>.Concat(xs, Dafny.Sequence<__X>.FromElements(x));
        return _73_xs_k;
      }
    }
  }
} // end of namespace Common____SeqIsUnique__i_Compile
namespace Concrete__NodeIdentity__i_Compile {

} // end of namespace Concrete__NodeIdentity__i_Compile
namespace Collections____Maps__i_Compile {

  public partial class __default {
    public static Dafny.ISet<__U> domain<__U, __V>(Dafny.IMap<__U,__V> m) {
      return Dafny.Helpers.Id<Func<Dafny.IMap<__U,__V>, Dafny.ISet<__U>>>((_74_m) => ((System.Func<Dafny.ISet<__U>>)(() => {
        var _coll3 = new System.Collections.Generic.List<__U>();
        foreach (__U _compr_3 in (_74_m).Keys.Elements) {
          __U _75_s = (__U)_compr_3;
          if ((_74_m).Contains((_75_s))) {
            _coll3.Add(_75_s);
          }
        }
        return Dafny.Set<__U>.FromCollection(_coll3);
      }))())(m);
    }
    public static Dafny.IMap<__U,__V> RemoveElt<__U, __V>(Dafny.IMap<__U,__V> m, __U elt)
    {
      Dafny.IMap<__U,__V> _76_m_k = Dafny.Helpers.Id<Func<Dafny.IMap<__U,__V>, __U, Dafny.IMap<__U,__V>>>((_77_m, _78_elt) => ((System.Func<Dafny.IMap<__U,__V>>)(() => {
        var _coll4 = new System.Collections.Generic.List<Dafny.Pair<__U,__V>>();
        foreach (__U _compr_4 in (_77_m).Keys.Elements) {
          __U _79_elt_k = (__U)_compr_4;
          if (((_77_m).Contains((_79_elt_k))) && (!object.Equals(_79_elt_k, _78_elt))) {
            _coll4.Add(new Dafny.Pair<__U,__V>(_79_elt_k, Dafny.Map<__U, __V>.Select(_77_m,_79_elt_k)));
          }
        }
        return Dafny.Map<__U,__V>.FromCollection(_coll4);
      }))())(m, elt);
      return _76_m_k;
    }
  }
} // end of namespace Collections____Maps__i_Compile
namespace Collections____Sets__i_Compile {

} // end of namespace Collections____Sets__i_Compile
namespace Logic____Option__i_Compile {

  public interface _IOption<T> {
    bool is_Some { get; }
    bool is_None { get; }
    T dtor_v { get; }
    _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public abstract class Option<T> : _IOption<T> {
    public Option() { }
    public static Logic____Option__i_Compile._IOption<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<Logic____Option__i_Compile._IOption<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Logic____Option__i_Compile._IOption<T>>(Logic____Option__i_Compile.Option<T>.Default());
    }
    public static _IOption<T> create_Some(T v) {
      return new Option_Some<T>(v);
    }
    public static _IOption<T> create_None() {
      return new Option_None<T>();
    }
    public bool is_Some { get { return this is Option_Some<T>; } }
    public bool is_None { get { return this is Option_None<T>; } }
    public T dtor_v {
      get {
        var d = this;
        return ((Option_Some<T>)d)._v;
      }
    }
    public abstract _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Option_Some<T> : Option<T> {
    public readonly T _v;
    public Option_Some(T v) {
      this._v = v;
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_Some<__T>(converter0(_v));
    }
    public override bool Equals(object other) {
      var oth = other as Logic____Option__i_Compile.Option_Some<T>;
      return oth != null && object.Equals(this._v, oth._v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Logic____Option__i_Compile.Option.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this._v);
      s += ")";
      return s;
    }
  }
  public class Option_None<T> : Option<T> {
    public Option_None() {
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_None<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Logic____Option__i_Compile.Option_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Logic____Option__i_Compile.Option.None";
      return s;
    }
  }

} // end of namespace Logic____Option__i_Compile
namespace GenericRefinement__i_Compile {

} // end of namespace GenericRefinement__i_Compile
namespace Common____NodeIdentity__i_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> ConvertEndPointToSeqByte(Native____Io__s_Compile._IEndPoint e) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(0)), (e).dtor_addr), Common____Util__i_Compile.__default.Uint16ToSeqByte((e).dtor_port));
    }
    public static Native____Io__s_Compile._IEndPoint ConvertSeqByteToEndPoint(Dafny.ISequence<byte> s) {
      return Native____Io__s_Compile.EndPoint.create((s).Subsequence(new BigInteger(2), new BigInteger(6)), Common____Util__i_Compile.__default.SeqByteToUint16((s).Drop(new BigInteger(6))));
    }
    public static ulong ConvertEndPointToUint64(Native____Io__s_Compile._IEndPoint e) {
      return Common____Util__i_Compile.__default.SeqByteToUint64(Common____NodeIdentity__i_Compile.__default.ConvertEndPointToSeqByte(e));
    }
    public static Native____Io__s_Compile._IEndPoint ConvertUint64ToEndPoint(ulong u) {
      return Common____NodeIdentity__i_Compile.__default.ConvertSeqByteToEndPoint(Common____Util__i_Compile.__default.Uint64ToSeqByte(u));
    }
  }
} // end of namespace Common____NodeIdentity__i_Compile
namespace Collections____Multisets__s_Compile {

} // end of namespace Collections____Multisets__s_Compile
namespace Collections____Seqs__i_Compile {

  public partial class __default {
    public static bool CItemAtPositionInSeq<__T>(Dafny.ISequence<__T> s, __T v, BigInteger idx)
    {
      return (((idx).Sign != -1) && ((idx) < (new BigInteger((s).Count)))) && (object.Equals((s).Select(idx), v));
    }
    public static BigInteger FindIndexInSeq<__T>(Dafny.ISequence<__T> s, __T v)
    {
      if ((new BigInteger((s).Count)).Sign == 0) {
        return new BigInteger(-1);
      } else if (object.Equals((s).Select(BigInteger.Zero), v)) {
        return BigInteger.Zero;
      } else {
        BigInteger _80_r = Collections____Seqs__i_Compile.__default.FindIndexInSeq<__T>((s).Drop(BigInteger.One), v);
        if ((_80_r) == (new BigInteger(-1))) {
          return new BigInteger(-1);
        } else {
          return (_80_r) + (BigInteger.One);
        }
      }
    }
    public static Dafny.ISequence<BigInteger> InsertSort(Dafny.ISequence<BigInteger> a)
    {
      Dafny.ISequence<BigInteger> sorted = Dafny.Sequence<BigInteger>.Empty;
      if ((new BigInteger((a).Count)) <= (BigInteger.One)) {
        sorted = a;
      } else {
        BigInteger _81_last;
        _81_last = (a).Select((new BigInteger((a).Count)) - (BigInteger.One));
        Dafny.ISequence<BigInteger> _82_rest;
        _82_rest = (a).Take((new BigInteger((a).Count)) - (BigInteger.One));
        Dafny.ISequence<BigInteger> _83_sortedRest;
        Dafny.ISequence<BigInteger> _out4;
        _out4 = Collections____Seqs__i_Compile.__default.InsertSort(_82_rest);
        _83_sortedRest = _out4;
        Dafny.ISequence<BigInteger> _out5;
        _out5 = Collections____Seqs__i_Compile.__default.Insert(_83_sortedRest, _81_last);
        sorted = _out5;
      }
      return sorted;
    }
    public static Dafny.ISequence<BigInteger> Insert(Dafny.ISequence<BigInteger> sortedSeq, BigInteger @value)
    {
      Dafny.ISequence<BigInteger> newSeq = Dafny.Sequence<BigInteger>.Empty;
      if ((new BigInteger((sortedSeq).Count)).Sign == 0) {
        newSeq = Dafny.Sequence<BigInteger>.FromElements(@value);
      } else {
        if ((@value) <= ((sortedSeq).Select(BigInteger.Zero))) {
          newSeq = Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements(@value), sortedSeq);
        } else {
          Dafny.ISequence<BigInteger> _84_res;
          Dafny.ISequence<BigInteger> _out6;
          _out6 = Collections____Seqs__i_Compile.__default.Insert((sortedSeq).Drop(BigInteger.One), @value);
          _84_res = _out6;
          newSeq = Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements((sortedSeq).Select(BigInteger.Zero)), _84_res);
        }
      }
      return newSeq;
    }
  }
} // end of namespace Collections____Seqs__i_Compile
namespace CausalMesh__Types__i_Compile {

  public interface _IMeta {
    bool is_Meta { get; }
    BigInteger dtor_key { get; }
    Dafny.ISequence<BigInteger> dtor_vc { get; }
    Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps { get; }
    _IMeta DowncastClone();
  }
  public class Meta : _IMeta {
    public readonly BigInteger _key;
    public readonly Dafny.ISequence<BigInteger> _vc;
    public readonly Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _deps;
    public Meta(BigInteger key, Dafny.ISequence<BigInteger> vc, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps) {
      this._key = key;
      this._vc = vc;
      this._deps = deps;
    }
    public _IMeta DowncastClone() {
      if (this is _IMeta dt) { return dt; }
      return new Meta(_key, _vc, _deps);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__Types__i_Compile.Meta;
      return oth != null && this._key == oth._key && object.Equals(this._vc, oth._vc) && object.Equals(this._deps, oth._deps);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._vc));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._deps));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__Types__i_Compile.Meta.Meta";
      s += "(";
      s += Dafny.Helpers.ToString(this._key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._vc);
      s += ", ";
      s += Dafny.Helpers.ToString(this._deps);
      s += ")";
      return s;
    }
    private static readonly CausalMesh__Types__i_Compile._IMeta theDefault = create(BigInteger.Zero, Dafny.Sequence<BigInteger>.Empty, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty);
    public static CausalMesh__Types__i_Compile._IMeta Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<CausalMesh__Types__i_Compile._IMeta> _TYPE = new Dafny.TypeDescriptor<CausalMesh__Types__i_Compile._IMeta>(CausalMesh__Types__i_Compile.Meta.Default());
    public static Dafny.TypeDescriptor<CausalMesh__Types__i_Compile._IMeta> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMeta create(BigInteger key, Dafny.ISequence<BigInteger> vc, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps) {
      return new Meta(key, vc, deps);
    }
    public static _IMeta create_Meta(BigInteger key, Dafny.ISequence<BigInteger> vc, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps) {
      return create(key, vc, deps);
    }
    public bool is_Meta { get { return true; } }
    public BigInteger dtor_key {
      get {
        return this._key;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_vc {
      get {
        return this._vc;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps {
      get {
        return this._deps;
      }
    }
  }

  public partial class __default {
    public static BigInteger Nodes { get {
      return new BigInteger(3);
    } }
    public static Dafny.ISet<BigInteger> Keys__domain { get {
      return ((System.Func<Dafny.ISet<BigInteger>>)(() => {
        var _coll5 = new System.Collections.Generic.List<BigInteger>();
        foreach (BigInteger _compr_5 in Dafny.Helpers.IntegerRange(BigInteger.Zero, (new BigInteger(1000)) + (BigInteger.One))) {
          BigInteger _85_i = (BigInteger)_compr_5;
          if (((_85_i).Sign != -1) && ((_85_i) <= (new BigInteger(1000)))) {
            _coll5.Add(_85_i);
          }
        }
        return Dafny.Set<BigInteger>.FromCollection(_coll5);
      }))();
    } }
    public static BigInteger Clients { get {
      return new BigInteger(5);
    } }
    public static BigInteger MaxKeys { get {
      return new BigInteger(1000);
    } }
  }
} // end of namespace CausalMesh__Types__i_Compile
namespace CausalMesh__CTypes__i_Compile {

  public interface _ICMeta {
    bool is_CMeta { get; }
    BigInteger dtor_key { get; }
    Dafny.ISequence<BigInteger> dtor_vc { get; }
    Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps { get; }
    _ICMeta DowncastClone();
  }
  public class CMeta : _ICMeta {
    public readonly BigInteger _key;
    public readonly Dafny.ISequence<BigInteger> _vc;
    public readonly Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _deps;
    public CMeta(BigInteger key, Dafny.ISequence<BigInteger> vc, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps) {
      this._key = key;
      this._vc = vc;
      this._deps = deps;
    }
    public _ICMeta DowncastClone() {
      if (this is _ICMeta dt) { return dt; }
      return new CMeta(_key, _vc, _deps);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__CTypes__i_Compile.CMeta;
      return oth != null && this._key == oth._key && object.Equals(this._vc, oth._vc) && object.Equals(this._deps, oth._deps);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._vc));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._deps));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__CTypes__i_Compile.CMeta.CMeta";
      s += "(";
      s += Dafny.Helpers.ToString(this._key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._vc);
      s += ", ";
      s += Dafny.Helpers.ToString(this._deps);
      s += ")";
      return s;
    }
    private static readonly CausalMesh__CTypes__i_Compile._ICMeta theDefault = create(BigInteger.Zero, Dafny.Sequence<BigInteger>.Empty, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty);
    public static CausalMesh__CTypes__i_Compile._ICMeta Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<CausalMesh__CTypes__i_Compile._ICMeta> _TYPE = new Dafny.TypeDescriptor<CausalMesh__CTypes__i_Compile._ICMeta>(CausalMesh__CTypes__i_Compile.CMeta.Default());
    public static Dafny.TypeDescriptor<CausalMesh__CTypes__i_Compile._ICMeta> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICMeta create(BigInteger key, Dafny.ISequence<BigInteger> vc, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps) {
      return new CMeta(key, vc, deps);
    }
    public static _ICMeta create_CMeta(BigInteger key, Dafny.ISequence<BigInteger> vc, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps) {
      return create(key, vc, deps);
    }
    public bool is_CMeta { get { return true; } }
    public BigInteger dtor_key {
      get {
        return this._key;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_vc {
      get {
        return this._vc;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps {
      get {
        return this._deps;
      }
    }
  }

  public partial class __default {
    public static Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> CMergeVCIntoCCache(Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> c1, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> c2)
    {
      return Dafny.Helpers.Id<Func<Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>, Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>>>((_86_c1, _87_c2) => ((System.Func<Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>>)(() => {
        var _coll6 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>>();
        foreach (BigInteger _compr_6 in (Dafny.Set<BigInteger>.Union((_86_c1).Keys, (_87_c2).Keys)).Elements) {
          BigInteger _88_k = (BigInteger)_compr_6;
          if ((Dafny.Set<BigInteger>.Union((_86_c1).Keys, (_87_c2).Keys)).Contains((_88_k))) {
            _coll6.Add(new Dafny.Pair<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>(_88_k, ((((_86_c1).Contains((_88_k))) && ((_87_c2).Contains((_88_k)))) ? (Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Select(_86_c1,_88_k), _pat_let0_0 => Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(_pat_let0_0, _89_m => Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(_89_m, _pat_let2_0 => Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(_pat_let2_0, _90_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CTypes__i_Compile._ICMeta>(CausalMesh__CTypes__i_Compile.__default.CVCMerge((_89_m).dtor_vc, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_87_c2,_88_k)), _pat_let3_0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CTypes__i_Compile._ICMeta>(_pat_let3_0, _91_dt__update_hvc_h0 => CausalMesh__CTypes__i_Compile.CMeta.create((_90_dt__update__tmp_h0).dtor_key, _91_dt__update_hvc_h0, (_90_dt__update__tmp_h0).dtor_deps))))), _pat_let1_0 => Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(_pat_let1_0, _92_new__m => _92_new__m))))) : ((((_86_c1).Contains((_88_k))) ? (Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Select(_86_c1,_88_k)) : (Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(CausalMesh__CTypes__i_Compile.__default.CEmptyMeta(_88_k), _pat_let4_0 => Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(_pat_let4_0, _93_m => Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(_93_m, _pat_let5_0 => Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(_pat_let5_0, _94_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CTypes__i_Compile._ICMeta>(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_87_c2,_88_k), _pat_let6_0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CTypes__i_Compile._ICMeta>(_pat_let6_0, _95_dt__update_hvc_h1 => CausalMesh__CTypes__i_Compile.CMeta.create((_94_dt__update__tmp_h1).dtor_key, _95_dt__update_hvc_h1, (_94_dt__update__tmp_h1).dtor_deps)))))))))))));
          }
        }
        return Dafny.Map<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>.FromCollection(_coll6);
      }))())(c1, c2);
    }
    public static bool CVectorClockValid(Dafny.ISequence<BigInteger> vc) {
      return ((new BigInteger((vc).Count)) == (CausalMesh__Types__i_Compile.__default.Nodes)) && (Dafny.Helpers.Id<Func<Dafny.ISequence<BigInteger>, bool>>((_96_vc) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_96_vc).Count)), true, (((_forall_var_0) => {
        BigInteger _97_i = (BigInteger)_forall_var_0;
        return !(((_97_i).Sign != -1) && ((_97_i) < (new BigInteger((_96_vc).Count)))) || (((_96_vc).Select(_97_i)).Sign != -1);
      }))))(vc));
    }
    public static Dafny.ISequence<BigInteger> CEmptyVC() {
      return ((System.Func<Dafny.ISequence<BigInteger>>) (() => {
        BigInteger dim0 = CausalMesh__Types__i_Compile.__default.Nodes;
        var arr0 = new BigInteger[Dafny.Helpers.ToIntChecked(dim0, "array size exceeds memory limit")];
        for (int i0 = 0; i0 < dim0; i0++) {
          var _98_idx = (BigInteger) i0;
          arr0[(int)(_98_idx)] = BigInteger.Zero;
        }
        return Dafny.Sequence<BigInteger>.FromArray(arr0);
      }))();
    }
    public static bool CVCEq(Dafny.ISequence<BigInteger> vc1, Dafny.ISequence<BigInteger> vc2)
    {
      return Dafny.Helpers.Id<Func<Dafny.ISequence<BigInteger>, Dafny.ISequence<BigInteger>, bool>>((_99_vc1, _100_vc2) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_99_vc1).Count)), true, (((_forall_var_1) => {
        BigInteger _101_i = (BigInteger)_forall_var_1;
        return !(((_101_i).Sign != -1) && ((_101_i) < (new BigInteger((_99_vc1).Count)))) || (((_99_vc1).Select(_101_i)) == ((_100_vc2).Select(_101_i)));
      }))))(vc1, vc2);
    }
    public static bool CVCHappendsBefore(Dafny.ISequence<BigInteger> vc1, Dafny.ISequence<BigInteger> vc2)
    {
      return (!(CausalMesh__CTypes__i_Compile.__default.CVCEq(vc1, vc2))) && (Dafny.Helpers.Id<Func<Dafny.ISequence<BigInteger>, Dafny.ISequence<BigInteger>, bool>>((_102_vc1, _103_vc2) => Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger((_102_vc1).Count)), true, (((_forall_var_2) => {
        BigInteger _104_i = (BigInteger)_forall_var_2;
        return !(((_104_i).Sign != -1) && ((_104_i) < (new BigInteger((_102_vc1).Count)))) || (((_102_vc1).Select(_104_i)) <= ((_103_vc2).Select(_104_i)));
      }))))(vc1, vc2));
    }
    public static Dafny.ISequence<BigInteger> CMergeSeqs(Dafny.ISequence<BigInteger> s1, Dafny.ISequence<BigInteger> s2)
    {
      Dafny.ISequence<BigInteger> _105___accumulator = Dafny.Sequence<BigInteger>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((s1).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.Concat(_105___accumulator, Dafny.Sequence<BigInteger>.FromElements());
      } else if (((s1).Select(BigInteger.Zero)) > ((s2).Select(BigInteger.Zero))) {
        _105___accumulator = Dafny.Sequence<BigInteger>.Concat(_105___accumulator, Dafny.Sequence<BigInteger>.FromElements((s1).Select(BigInteger.Zero)));
        Dafny.ISequence<BigInteger> _in0 = (s1).Drop(BigInteger.One);
        Dafny.ISequence<BigInteger> _in1 = (s2).Drop(BigInteger.One);
        s1 = _in0;
        s2 = _in1;
        goto TAIL_CALL_START;
      } else {
        _105___accumulator = Dafny.Sequence<BigInteger>.Concat(_105___accumulator, Dafny.Sequence<BigInteger>.FromElements((s2).Select(BigInteger.Zero)));
        Dafny.ISequence<BigInteger> _in2 = (s1).Drop(BigInteger.One);
        Dafny.ISequence<BigInteger> _in3 = (s2).Drop(BigInteger.One);
        s1 = _in2;
        s2 = _in3;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<BigInteger> CVCMerge(Dafny.ISequence<BigInteger> vc1, Dafny.ISequence<BigInteger> vc2)
    {
      return CausalMesh__CTypes__i_Compile.__default.CMergeSeqs(vc1, vc2);
    }
    public static bool CDependencyValid(Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dep) {
      return Dafny.Helpers.Id<Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>, bool>>((_106_dep) => Dafny.Helpers.Quantifier<BigInteger>((_106_dep).Keys.Elements, true, (((_forall_var_3) => {
        BigInteger _107_k = (BigInteger)_forall_var_3;
        return !((_106_dep).Contains((_107_k))) || (((CausalMesh__Types__i_Compile.__default.Keys__domain).Contains((_107_k))) && (CausalMesh__CTypes__i_Compile.__default.CVectorClockValid(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_106_dep,_107_k))));
      }))))(dep);
    }
    public static bool CDependencyEq(Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dep1, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dep2)
    {
      return Dafny.Helpers.Id<Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>, bool>>((_108_dep1, _109_dep2) => Dafny.Helpers.Quantifier<BigInteger>((_108_dep1).Keys.Elements, true, (((_forall_var_4) => {
        BigInteger _110_k = (BigInteger)_forall_var_4;
        return !((_108_dep1).Contains((_110_k))) || (((_109_dep2).Contains((_110_k))) && (CausalMesh__CTypes__i_Compile.__default.CVCEq(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_108_dep1,_110_k), Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_109_dep2,_110_k))));
      }))))(dep1, dep2);
    }
    public static Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> CDependencyMerge(Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dep1, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dep2)
    {
      return Dafny.Helpers.Id<Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>>((_111_dep1, _112_dep2) => ((System.Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>)(() => {
        var _coll7 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>>();
        foreach (BigInteger _compr_7 in (Dafny.Set<BigInteger>.Union((_111_dep1).Keys, (_112_dep2).Keys)).Elements) {
          BigInteger _113_k = (BigInteger)_compr_7;
          if ((Dafny.Set<BigInteger>.Union((_111_dep1).Keys, (_112_dep2).Keys)).Contains((_113_k))) {
            _coll7.Add(new Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>(_113_k, ((((_111_dep1).Contains((_113_k))) && ((_112_dep2).Contains((_113_k)))) ? (CausalMesh__CTypes__i_Compile.__default.CVCMerge(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_111_dep1,_113_k), Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_112_dep2,_113_k))) : ((((_111_dep1).Contains((_113_k))) ? (Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_111_dep1,_113_k)) : (Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_112_dep2,_113_k)))))));
          }
        }
        return Dafny.Map<BigInteger,Dafny.ISequence<BigInteger>>.FromCollection(_coll7);
      }))())(dep1, dep2);
    }
    public static Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> CDependencyInsertOrMerge(Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dep, BigInteger k, Dafny.ISequence<BigInteger> vc)
    {
      if ((dep).Contains((k))) {
        Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _114_d = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update(dep, k, CausalMesh__CTypes__i_Compile.__default.CVCMerge(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(dep,k), vc));
        return _114_d;
      } else {
        return Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update(dep, k, vc);
      }
    }
    public static CausalMesh__CTypes__i_Compile._ICMeta CEmptyMeta(BigInteger k) {
      return CausalMesh__CTypes__i_Compile.CMeta.create(k, ((System.Func<Dafny.ISequence<BigInteger>>) (() => {
  BigInteger dim1 = CausalMesh__Types__i_Compile.__default.Nodes;
  var arr1 = new BigInteger[Dafny.Helpers.ToIntChecked(dim1, "array size exceeds memory limit")];
  for (int i1 = 0; i1 < dim1; i1++) {
    var _115_idx = (BigInteger) i1;
    arr1[(int)(_115_idx)] = BigInteger.Zero;
  }
  return Dafny.Sequence<BigInteger>.FromArray(arr1);
}))(), Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements());
    }
    public static bool CMetaValid(CausalMesh__CTypes__i_Compile._ICMeta m) {
      return (((CausalMesh__Types__i_Compile.__default.Keys__domain).Contains(((m).dtor_key))) && (CausalMesh__CTypes__i_Compile.__default.CVectorClockValid((m).dtor_vc))) && (CausalMesh__CTypes__i_Compile.__default.CDependencyValid((m).dtor_deps));
    }
    public static bool CMetaEq(CausalMesh__CTypes__i_Compile._ICMeta m1, CausalMesh__CTypes__i_Compile._ICMeta m2)
    {
      return ((((m1).dtor_key) == ((m2).dtor_key)) && (CausalMesh__CTypes__i_Compile.__default.CVCEq((m1).dtor_vc, (m2).dtor_vc))) && (CausalMesh__CTypes__i_Compile.__default.CDependencyEq((m1).dtor_deps, (m2).dtor_deps));
    }
    public static bool CMetaHappensBefore(CausalMesh__CTypes__i_Compile._ICMeta m1, CausalMesh__CTypes__i_Compile._ICMeta m2)
    {
      return CausalMesh__CTypes__i_Compile.__default.CVCHappendsBefore((m1).dtor_vc, (m2).dtor_vc);
    }
    public static CausalMesh__CTypes__i_Compile._ICMeta CMetaMerge(CausalMesh__CTypes__i_Compile._ICMeta m1, CausalMesh__CTypes__i_Compile._ICMeta m2)
    {
      CausalMesh__CTypes__i_Compile._ICMeta _116_dt__update__tmp_h0 = m1;
      Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _117_dt__update_hdeps_h0 = CausalMesh__CTypes__i_Compile.__default.CDependencyMerge((m1).dtor_deps, (m2).dtor_deps);
      Dafny.ISequence<BigInteger> _118_dt__update_hvc_h0 = CausalMesh__CTypes__i_Compile.__default.CVCMerge((m1).dtor_vc, (m2).dtor_vc);
      return CausalMesh__CTypes__i_Compile.CMeta.create((_116_dt__update__tmp_h0).dtor_key, _118_dt__update_hvc_h0, _117_dt__update_hdeps_h0);
    }
    public static CausalMesh__CTypes__i_Compile._ICMeta CFoldMetaSet(CausalMesh__CTypes__i_Compile._ICMeta acc, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta> metas)
    {
    TAIL_CALL_START: ;
      CausalMesh__CTypes__i_Compile._ICMeta res = CausalMesh__CTypes__i_Compile.CMeta.Default();
      if ((new BigInteger((metas).Count)).Sign == 0) {
        res = acc;
      } else {
        CausalMesh__CTypes__i_Compile._ICMeta _119_x;
        foreach (CausalMesh__CTypes__i_Compile._ICMeta _assign_such_that_1 in (metas).Elements) {
          _119_x = (CausalMesh__CTypes__i_Compile._ICMeta)_assign_such_that_1;
          if ((metas).Contains((_119_x))) {
            goto after__ASSIGN_SUCH_THAT_1;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 352)");
      after__ASSIGN_SUCH_THAT_1: ;
        CausalMesh__CTypes__i_Compile._ICMeta _in4 = CausalMesh__CTypes__i_Compile.__default.CMetaMerge(acc, _119_x);
        Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta> _in5 = Dafny.Set<CausalMesh__CTypes__i_Compile._ICMeta>.Difference(metas, Dafny.Set<CausalMesh__CTypes__i_Compile._ICMeta>.FromElements(_119_x));
        acc = _in4;
        metas = _in5;
        goto TAIL_CALL_START;
      }
      return res;
    }
    public static Dafny.ISequence<BigInteger> CFoldVC(Dafny.ISequence<BigInteger> acc, Dafny.ISet<Dafny.ISequence<BigInteger>> vcs)
    {
      Dafny.ISequence<BigInteger> res = Dafny.Sequence<BigInteger>.Empty;
      if ((new BigInteger((vcs).Count)).Sign == 0) {
        res = acc;
      } else {
        Dafny.ISequence<BigInteger> _120_x;
        foreach (Dafny.ISequence<BigInteger> _assign_such_that_2 in (vcs).Elements) {
          _120_x = (Dafny.ISequence<BigInteger>)_assign_such_that_2;
          if ((vcs).Contains((_120_x))) {
            goto after__ASSIGN_SUCH_THAT_2;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 395)");
      after__ASSIGN_SUCH_THAT_2: ;
        Dafny.ISet<Dafny.ISequence<BigInteger>> _121_nvcs;
        _121_nvcs = Dafny.Set<Dafny.ISequence<BigInteger>>.Difference(vcs, Dafny.Set<Dafny.ISequence<BigInteger>>.FromElements(_120_x));
        Dafny.ISequence<BigInteger> _122_r;
        Dafny.ISequence<BigInteger> _out7;
        _out7 = CausalMesh__CTypes__i_Compile.__default.CFoldVC(CausalMesh__CTypes__i_Compile.__default.CVCMerge(acc, _120_x), _121_nvcs);
        _122_r = _out7;
        res = _122_r;
      }
      return res;
    }
    public static Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> CFoldDependencyFromMetaSet(Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> acc, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta> metas)
    {
    TAIL_CALL_START: ;
      Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> res = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty;
      if ((new BigInteger((metas).Count)).Sign == 0) {
        res = acc;
      } else {
        CausalMesh__CTypes__i_Compile._ICMeta _123_x;
        foreach (CausalMesh__CTypes__i_Compile._ICMeta _assign_such_that_3 in (metas).Elements) {
          _123_x = (CausalMesh__CTypes__i_Compile._ICMeta)_assign_such_that_3;
          if ((metas).Contains((_123_x))) {
            goto after__ASSIGN_SUCH_THAT_3;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 471)");
      after__ASSIGN_SUCH_THAT_3: ;
        Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _in6 = CausalMesh__CTypes__i_Compile.__default.CDependencyMerge(acc, (_123_x).dtor_deps);
        Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta> _in7 = Dafny.Set<CausalMesh__CTypes__i_Compile._ICMeta>.Difference(metas, Dafny.Set<CausalMesh__CTypes__i_Compile._ICMeta>.FromElements(_123_x));
        acc = _in6;
        metas = _in7;
        goto TAIL_CALL_START;
      }
      return res;
    }
    public static bool CNodesAreNext(BigInteger i, BigInteger j)
    {
      if ((i) == ((CausalMesh__Types__i_Compile.__default.Nodes) - (BigInteger.One))) {
        return (j).Sign == 0;
      } else {
        return (j) == ((i) + (BigInteger.One));
      }
    }
  }
} // end of namespace CausalMesh__CTypes__i_Compile
namespace CausalMesh__CmdParser__i_Compile {

  public partial class __default {
    public static void parse__cmd__line(out bool ok, out Dafny.ISequence<Native____Io__s_Compile._IEndPoint> config, out BigInteger my__index)
    {
      ok = false;
      config = Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.Empty;
      my__index = BigInteger.Zero;
      ok = false;
      uint _124_num__args;
      uint _out8;
      _out8 = Native____Io__s_Compile.HostConstants.NumCommandLineArgs();
      _124_num__args = _out8;
      if (((_124_num__args) < (4U)) || (((_124_num__args) % (2U)) != (1U))) {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Incorrect number of command line arguments.\n")));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Expected: ./Main.exe [IP port]+ [IP port]\n")));
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("  where the final argument is one of the IP-port pairs provided earlier \n")));
        return ;
      }
      Dafny.ISequence<Dafny.ISequence<ushort>> _125_args;
      Dafny.ISequence<Dafny.ISequence<ushort>> _out9;
      _out9 = CmdLineParser__i_Compile.__default.collect__cmd__line__args();
      _125_args = _out9;
      _System._ITuple2<bool, Dafny.ISequence<Native____Io__s_Compile._IEndPoint>> _126_tuple1;
      _126_tuple1 = CmdLineParser__i_Compile.__default.parse__end__points((_125_args).Subsequence(BigInteger.One, (new BigInteger((_125_args).Count)) - (new BigInteger(2))));
      ok = (_126_tuple1).dtor__0;
      Dafny.ISequence<Native____Io__s_Compile._IEndPoint> _127_endpoints;
      _127_endpoints = (_126_tuple1).dtor__1;
      if ((!(ok)) || ((new BigInteger((_127_endpoints).Count)) >= (new BigInteger(18446744073709551615UL)))) {
        ok = false;
        return ;
      }
      _System._ITuple2<bool, Native____Io__s_Compile._IEndPoint> _128_tuple2;
      _128_tuple2 = CmdLineParser__i_Compile.__default.parse__end__point((_125_args).Select((new BigInteger((_125_args).Count)) - (new BigInteger(2))), (_125_args).Select((new BigInteger((_125_args).Count)) - (BigInteger.One)));
      ok = (_128_tuple2).dtor__0;
      if (!(ok)) {
        return ;
      }
      bool _129_unique;
      bool _out10;
      _out10 = CmdLineParser__i_Compile.__default.test__unique_k(_127_endpoints);
      _129_unique = _out10;
      if (!(_129_unique)) {
        ok = false;
        return ;
      }
      config = _127_endpoints;
      my__index = Collections____Seqs__i_Compile.__default.FindIndexInSeq<Native____Io__s_Compile._IEndPoint>(config, (_128_tuple2).dtor__1);
      ok = true;
    }
  }
} // end of namespace CausalMesh__CmdParser__i_Compile
namespace Common____MarshallInt__i_Compile {

  public partial class __default {
    public static void MarshallUint64__guts(ulong n, byte[] data, ulong index)
    {
      (data)[(int)((index))] = (byte)((n) / (72057594037927936UL));
      var _index1 = (index) + (1UL);
      (data)[(int)(_index1)] = (byte)(((n) / (281474976710656UL)) % (256UL));
      var _index2 = (index) + (2UL);
      (data)[(int)(_index2)] = (byte)(((n) / (1099511627776UL)) % (256UL));
      var _index3 = (index) + (3UL);
      (data)[(int)(_index3)] = (byte)(((n) / (4294967296UL)) % (256UL));
      var _index4 = (index) + (4UL);
      (data)[(int)(_index4)] = (byte)(((n) / (16777216UL)) % (256UL));
      var _index5 = (index) + (5UL);
      (data)[(int)(_index5)] = (byte)(((n) / (65536UL)) % (256UL));
      var _index6 = (index) + (6UL);
      (data)[(int)(_index6)] = (byte)(((n) / (256UL)) % (256UL));
      var _index7 = (index) + (7UL);
      (data)[(int)(_index7)] = (byte)((n) % (256UL));
    }
  }
} // end of namespace Common____MarshallInt__i_Compile
namespace Common____GenericMarshalling__i_Compile {

  public interface _IG {
    bool is_GUint64 { get; }
    bool is_GArray { get; }
    bool is_GTuple { get; }
    bool is_GByteArray { get; }
    bool is_GTaggedUnion { get; }
    Common____GenericMarshalling__i_Compile._IG dtor_elt { get; }
    Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> dtor_t { get; }
    Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> dtor_cases { get; }
    _IG DowncastClone();
  }
  public abstract class G : _IG {
    public G() { }
    private static readonly Common____GenericMarshalling__i_Compile._IG theDefault = create_GUint64();
    public static Common____GenericMarshalling__i_Compile._IG Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Common____GenericMarshalling__i_Compile._IG> _TYPE = new Dafny.TypeDescriptor<Common____GenericMarshalling__i_Compile._IG>(Common____GenericMarshalling__i_Compile.G.Default());
    public static Dafny.TypeDescriptor<Common____GenericMarshalling__i_Compile._IG> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IG create_GUint64() {
      return new G_GUint64();
    }
    public static _IG create_GArray(Common____GenericMarshalling__i_Compile._IG elt) {
      return new G_GArray(elt);
    }
    public static _IG create_GTuple(Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> t) {
      return new G_GTuple(t);
    }
    public static _IG create_GByteArray() {
      return new G_GByteArray();
    }
    public static _IG create_GTaggedUnion(Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> cases) {
      return new G_GTaggedUnion(cases);
    }
    public bool is_GUint64 { get { return this is G_GUint64; } }
    public bool is_GArray { get { return this is G_GArray; } }
    public bool is_GTuple { get { return this is G_GTuple; } }
    public bool is_GByteArray { get { return this is G_GByteArray; } }
    public bool is_GTaggedUnion { get { return this is G_GTaggedUnion; } }
    public Common____GenericMarshalling__i_Compile._IG dtor_elt {
      get {
        var d = this;
        return ((G_GArray)d)._elt;
      }
    }
    public Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> dtor_t {
      get {
        var d = this;
        return ((G_GTuple)d)._t;
      }
    }
    public Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> dtor_cases {
      get {
        var d = this;
        return ((G_GTaggedUnion)d)._cases;
      }
    }
    public abstract _IG DowncastClone();
  }
  public class G_GUint64 : G {
    public G_GUint64() {
    }
    public override _IG DowncastClone() {
      if (this is _IG dt) { return dt; }
      return new G_GUint64();
    }
    public override bool Equals(object other) {
      var oth = other as Common____GenericMarshalling__i_Compile.G_GUint64;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Common____GenericMarshalling__i_Compile.G.GUint64";
      return s;
    }
  }
  public class G_GArray : G {
    public readonly Common____GenericMarshalling__i_Compile._IG _elt;
    public G_GArray(Common____GenericMarshalling__i_Compile._IG elt) {
      this._elt = elt;
    }
    public override _IG DowncastClone() {
      if (this is _IG dt) { return dt; }
      return new G_GArray(_elt);
    }
    public override bool Equals(object other) {
      var oth = other as Common____GenericMarshalling__i_Compile.G_GArray;
      return oth != null && object.Equals(this._elt, oth._elt);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._elt));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Common____GenericMarshalling__i_Compile.G.GArray";
      s += "(";
      s += Dafny.Helpers.ToString(this._elt);
      s += ")";
      return s;
    }
  }
  public class G_GTuple : G {
    public readonly Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> _t;
    public G_GTuple(Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> t) {
      this._t = t;
    }
    public override _IG DowncastClone() {
      if (this is _IG dt) { return dt; }
      return new G_GTuple(_t);
    }
    public override bool Equals(object other) {
      var oth = other as Common____GenericMarshalling__i_Compile.G_GTuple;
      return oth != null && object.Equals(this._t, oth._t);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Common____GenericMarshalling__i_Compile.G.GTuple";
      s += "(";
      s += Dafny.Helpers.ToString(this._t);
      s += ")";
      return s;
    }
  }
  public class G_GByteArray : G {
    public G_GByteArray() {
    }
    public override _IG DowncastClone() {
      if (this is _IG dt) { return dt; }
      return new G_GByteArray();
    }
    public override bool Equals(object other) {
      var oth = other as Common____GenericMarshalling__i_Compile.G_GByteArray;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Common____GenericMarshalling__i_Compile.G.GByteArray";
      return s;
    }
  }
  public class G_GTaggedUnion : G {
    public readonly Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> _cases;
    public G_GTaggedUnion(Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> cases) {
      this._cases = cases;
    }
    public override _IG DowncastClone() {
      if (this is _IG dt) { return dt; }
      return new G_GTaggedUnion(_cases);
    }
    public override bool Equals(object other) {
      var oth = other as Common____GenericMarshalling__i_Compile.G_GTaggedUnion;
      return oth != null && object.Equals(this._cases, oth._cases);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cases));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Common____GenericMarshalling__i_Compile.G.GTaggedUnion";
      s += "(";
      s += Dafny.Helpers.ToString(this._cases);
      s += ")";
      return s;
    }
  }

  public interface _IV {
    bool is_VUint64 { get; }
    bool is_VArray { get; }
    bool is_VTuple { get; }
    bool is_VByteArray { get; }
    bool is_VCase { get; }
    ulong dtor_u { get; }
    Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> dtor_a { get; }
    Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> dtor_t { get; }
    Dafny.ISequence<byte> dtor_b { get; }
    ulong dtor_c { get; }
    Common____GenericMarshalling__i_Compile._IV dtor_val { get; }
    _IV DowncastClone();
  }
  public abstract class V : _IV {
    public V() { }
    private static readonly Common____GenericMarshalling__i_Compile._IV theDefault = create_VUint64(0);
    public static Common____GenericMarshalling__i_Compile._IV Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Common____GenericMarshalling__i_Compile._IV> _TYPE = new Dafny.TypeDescriptor<Common____GenericMarshalling__i_Compile._IV>(Common____GenericMarshalling__i_Compile.V.Default());
    public static Dafny.TypeDescriptor<Common____GenericMarshalling__i_Compile._IV> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IV create_VUint64(ulong u) {
      return new V_VUint64(u);
    }
    public static _IV create_VArray(Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> a) {
      return new V_VArray(a);
    }
    public static _IV create_VTuple(Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> t) {
      return new V_VTuple(t);
    }
    public static _IV create_VByteArray(Dafny.ISequence<byte> b) {
      return new V_VByteArray(b);
    }
    public static _IV create_VCase(ulong c, Common____GenericMarshalling__i_Compile._IV val) {
      return new V_VCase(c, val);
    }
    public bool is_VUint64 { get { return this is V_VUint64; } }
    public bool is_VArray { get { return this is V_VArray; } }
    public bool is_VTuple { get { return this is V_VTuple; } }
    public bool is_VByteArray { get { return this is V_VByteArray; } }
    public bool is_VCase { get { return this is V_VCase; } }
    public ulong dtor_u {
      get {
        var d = this;
        return ((V_VUint64)d)._u;
      }
    }
    public Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> dtor_a {
      get {
        var d = this;
        return ((V_VArray)d)._a;
      }
    }
    public Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> dtor_t {
      get {
        var d = this;
        return ((V_VTuple)d)._t;
      }
    }
    public Dafny.ISequence<byte> dtor_b {
      get {
        var d = this;
        return ((V_VByteArray)d)._b;
      }
    }
    public ulong dtor_c {
      get {
        var d = this;
        return ((V_VCase)d)._c;
      }
    }
    public Common____GenericMarshalling__i_Compile._IV dtor_val {
      get {
        var d = this;
        return ((V_VCase)d)._val;
      }
    }
    public abstract _IV DowncastClone();
  }
  public class V_VUint64 : V {
    public readonly ulong _u;
    public V_VUint64(ulong u) {
      this._u = u;
    }
    public override _IV DowncastClone() {
      if (this is _IV dt) { return dt; }
      return new V_VUint64(_u);
    }
    public override bool Equals(object other) {
      var oth = other as Common____GenericMarshalling__i_Compile.V_VUint64;
      return oth != null && this._u == oth._u;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._u));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Common____GenericMarshalling__i_Compile.V.VUint64";
      s += "(";
      s += Dafny.Helpers.ToString(this._u);
      s += ")";
      return s;
    }
  }
  public class V_VArray : V {
    public readonly Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> _a;
    public V_VArray(Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> a) {
      this._a = a;
    }
    public override _IV DowncastClone() {
      if (this is _IV dt) { return dt; }
      return new V_VArray(_a);
    }
    public override bool Equals(object other) {
      var oth = other as Common____GenericMarshalling__i_Compile.V_VArray;
      return oth != null && object.Equals(this._a, oth._a);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._a));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Common____GenericMarshalling__i_Compile.V.VArray";
      s += "(";
      s += Dafny.Helpers.ToString(this._a);
      s += ")";
      return s;
    }
  }
  public class V_VTuple : V {
    public readonly Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> _t;
    public V_VTuple(Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> t) {
      this._t = t;
    }
    public override _IV DowncastClone() {
      if (this is _IV dt) { return dt; }
      return new V_VTuple(_t);
    }
    public override bool Equals(object other) {
      var oth = other as Common____GenericMarshalling__i_Compile.V_VTuple;
      return oth != null && object.Equals(this._t, oth._t);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._t));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Common____GenericMarshalling__i_Compile.V.VTuple";
      s += "(";
      s += Dafny.Helpers.ToString(this._t);
      s += ")";
      return s;
    }
  }
  public class V_VByteArray : V {
    public readonly Dafny.ISequence<byte> _b;
    public V_VByteArray(Dafny.ISequence<byte> b) {
      this._b = b;
    }
    public override _IV DowncastClone() {
      if (this is _IV dt) { return dt; }
      return new V_VByteArray(_b);
    }
    public override bool Equals(object other) {
      var oth = other as Common____GenericMarshalling__i_Compile.V_VByteArray;
      return oth != null && object.Equals(this._b, oth._b);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Common____GenericMarshalling__i_Compile.V.VByteArray";
      s += "(";
      s += Dafny.Helpers.ToString(this._b);
      s += ")";
      return s;
    }
  }
  public class V_VCase : V {
    public readonly ulong _c;
    public readonly Common____GenericMarshalling__i_Compile._IV _val;
    public V_VCase(ulong c, Common____GenericMarshalling__i_Compile._IV val) {
      this._c = c;
      this._val = val;
    }
    public override _IV DowncastClone() {
      if (this is _IV dt) { return dt; }
      return new V_VCase(_c, _val);
    }
    public override bool Equals(object other) {
      var oth = other as Common____GenericMarshalling__i_Compile.V_VCase;
      return oth != null && this._c == oth._c && object.Equals(this._val, oth._val);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._c));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._val));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Common____GenericMarshalling__i_Compile.V.VCase";
      s += "(";
      s += Dafny.Helpers.ToString(this._c);
      s += ", ";
      s += Dafny.Helpers.ToString(this._val);
      s += ")";
      return s;
    }
  }

  public interface _IContentsTraceStep {
    bool is_ContentsTraceStep { get; }
    Dafny.ISequence<byte> dtor_data { get; }
    Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV> dtor_val { get; }
    _IContentsTraceStep DowncastClone();
  }
  public class ContentsTraceStep : _IContentsTraceStep {
    public readonly Dafny.ISequence<byte> _data;
    public readonly Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV> _val;
    public ContentsTraceStep(Dafny.ISequence<byte> data, Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV> val) {
      this._data = data;
      this._val = val;
    }
    public _IContentsTraceStep DowncastClone() {
      if (this is _IContentsTraceStep dt) { return dt; }
      return new ContentsTraceStep(_data, _val);
    }
    public override bool Equals(object other) {
      var oth = other as Common____GenericMarshalling__i_Compile.ContentsTraceStep;
      return oth != null && object.Equals(this._data, oth._data) && object.Equals(this._val, oth._val);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._data));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._val));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Common____GenericMarshalling__i_Compile.ContentsTraceStep.ContentsTraceStep";
      s += "(";
      s += Dafny.Helpers.ToString(this._data);
      s += ", ";
      s += Dafny.Helpers.ToString(this._val);
      s += ")";
      return s;
    }
    private static readonly Common____GenericMarshalling__i_Compile._IContentsTraceStep theDefault = create(Dafny.Sequence<byte>.Empty, Logic____Option__i_Compile.Option<Common____GenericMarshalling__i_Compile._IV>.Default());
    public static Common____GenericMarshalling__i_Compile._IContentsTraceStep Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Common____GenericMarshalling__i_Compile._IContentsTraceStep> _TYPE = new Dafny.TypeDescriptor<Common____GenericMarshalling__i_Compile._IContentsTraceStep>(Common____GenericMarshalling__i_Compile.ContentsTraceStep.Default());
    public static Dafny.TypeDescriptor<Common____GenericMarshalling__i_Compile._IContentsTraceStep> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IContentsTraceStep create(Dafny.ISequence<byte> data, Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV> val) {
      return new ContentsTraceStep(data, val);
    }
    public static _IContentsTraceStep create_ContentsTraceStep(Dafny.ISequence<byte> data, Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV> val) {
      return create(data, val);
    }
    public bool is_ContentsTraceStep { get { return true; } }
    public Dafny.ISequence<byte> dtor_data {
      get {
        return this._data;
      }
    }
    public Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV> dtor_val {
      get {
        return this._val;
      }
    }
  }

  public partial class __default {
    public static _System._ITuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>> parse__Uint64(Dafny.ISequence<byte> data) {
      if (((ulong)(data).LongCount) >= (Native____NativeTypes__i_Compile.__default.Uint64Size())) {
        return _System.Tuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Common____GenericMarshalling__i_Compile._IV>.create_Some(Common____GenericMarshalling__i_Compile.V.create_VUint64(Common____Util__i_Compile.__default.SeqByteToUint64((data).Take(Native____NativeTypes__i_Compile.__default.Uint64Size())))), (data).Drop(Native____NativeTypes__i_Compile.__default.Uint64Size()));
      } else {
        return _System.Tuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Common____GenericMarshalling__i_Compile._IV>.create_None(), Dafny.Sequence<byte>.FromElements());
      }
    }
    public static void ParseUint64(byte[] data, ulong index, out bool success, out Common____GenericMarshalling__i_Compile._IV v, out ulong rest__index)
    {
      success = false;
      v = Common____GenericMarshalling__i_Compile.V.Default();
      rest__index = 0;
      if ((((ulong)(data).LongLength) >= (8UL)) && ((index) <= (((ulong)(data).LongLength) - (8UL)))) {
        ulong _130_result;
        _130_result = (((((((((ulong)((data)[(int)(new BigInteger(index))])) * (72057594037927936UL)) + (((ulong)((data)[(int)((new BigInteger(index)) + (BigInteger.One))])) * (281474976710656UL))) + (((ulong)((data)[(int)((new BigInteger(index)) + (new BigInteger(2)))])) * (1099511627776UL))) + (((ulong)((data)[(int)((new BigInteger(index)) + (new BigInteger(3)))])) * (4294967296UL))) + (((ulong)((data)[(int)((new BigInteger(index)) + (new BigInteger(4)))])) * (16777216UL))) + (((ulong)((data)[(int)((new BigInteger(index)) + (new BigInteger(5)))])) * (65536UL))) + (((ulong)((data)[(int)((new BigInteger(index)) + (new BigInteger(6)))])) * (256UL))) + ((ulong)((data)[(int)((new BigInteger(index)) + (new BigInteger(7)))]));
        success = true;
        v = Common____GenericMarshalling__i_Compile.V.create_VUint64(_130_result);
        rest__index = (index) + (Native____NativeTypes__i_Compile.__default.Uint64Size());
      } else {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Parse uint64 fails\n")));
        success = false;
        rest__index = (ulong)(data).LongLength;
      }
    }
    public static _System._ITuple2<Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>, Dafny.ISequence<byte>> parse__Array__contents(Dafny.ISequence<byte> data, Common____GenericMarshalling__i_Compile._IG eltType, ulong len)
    {
      if ((len) == (0UL)) {
        return _System.Tuple2<Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>.create_Some(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements()), data);
      } else {
        _System._ITuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>> _let_tmp_rhs2 = Common____GenericMarshalling__i_Compile.__default.parse__Val(data, eltType);
        Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV> _131_val = _let_tmp_rhs2.dtor__0;
        Dafny.ISequence<byte> _132_rest1 = _let_tmp_rhs2.dtor__1;
        _System._ITuple2<Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>, Dafny.ISequence<byte>> _let_tmp_rhs3 = Common____GenericMarshalling__i_Compile.__default.parse__Array__contents(_132_rest1, eltType, (len) - (1UL));
        Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>> _133_others = _let_tmp_rhs3.dtor__0;
        Dafny.ISequence<byte> _134_rest2 = _let_tmp_rhs3.dtor__1;
        if ((!((_131_val).is_None)) && (!((_133_others).is_None))) {
          return _System.Tuple2<Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>.create_Some(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.Concat(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements((_131_val).dtor_v), (_133_others).dtor_v)), _134_rest2);
        } else {
          return _System.Tuple2<Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>.create_None(), Dafny.Sequence<byte>.FromElements());
        }
      }
    }
    public static void ParseArrayContents(byte[] data, ulong index, Common____GenericMarshalling__i_Compile._IG eltType, ulong len, out bool success, out Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> v, out ulong rest__index)
    {
      success = false;
      v = Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.Empty;
      rest__index = 0;
      Common____GenericMarshalling__i_Compile._IV[] _135_vArr;
      Common____GenericMarshalling__i_Compile._IV[] _nw5 = Dafny.ArrayHelpers.InitNewArray1<Common____GenericMarshalling__i_Compile._IV>(Common____GenericMarshalling__i_Compile.V.Default(), Dafny.Helpers.ToIntChecked(len, "array size exceeds memory limit"));
      _135_vArr = _nw5;
      success = true;
      ulong _136_i;
      _136_i = 0UL;
      ulong _137_next__val__index;
      _137_next__val__index = index;
      while ((_136_i) < (len)) {
        bool _138_some1;
        Common____GenericMarshalling__i_Compile._IV _139_val;
        ulong _140_rest1;
        bool _out11;
        Common____GenericMarshalling__i_Compile._IV _out12;
        ulong _out13;
        Common____GenericMarshalling__i_Compile.__default.ParseVal(data, _137_next__val__index, eltType, out _out11, out _out12, out _out13);
        _138_some1 = _out11;
        _139_val = _out12;
        _140_rest1 = _out13;
        if (!(_138_some1)) {
          success = false;
          rest__index = (ulong)(data).LongLength;
          return ;
        }
        (_135_vArr)[(int)((_136_i))] = _139_val;
        _137_next__val__index = _140_rest1;
        _136_i = (_136_i) + (1UL);
      }
      success = true;
      rest__index = _137_next__val__index;
      v = Dafny.Helpers.SeqFromArray(_135_vArr);
    }
    public static _System._ITuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>> parse__Array(Dafny.ISequence<byte> data, Common____GenericMarshalling__i_Compile._IG eltType)
    {
      _System._ITuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>> _let_tmp_rhs4 = Common____GenericMarshalling__i_Compile.__default.parse__Uint64(data);
      Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV> _141_len = _let_tmp_rhs4.dtor__0;
      Dafny.ISequence<byte> _142_rest = _let_tmp_rhs4.dtor__1;
      if (!((_141_len).is_None)) {
        _System._ITuple2<Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>, Dafny.ISequence<byte>> _let_tmp_rhs5 = Common____GenericMarshalling__i_Compile.__default.parse__Array__contents(_142_rest, eltType, ((_141_len).dtor_v).dtor_u);
        Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>> _143_contents = _let_tmp_rhs5.dtor__0;
        Dafny.ISequence<byte> _144_remainder = _let_tmp_rhs5.dtor__1;
        if (!((_143_contents).is_None)) {
          return _System.Tuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Common____GenericMarshalling__i_Compile._IV>.create_Some(Common____GenericMarshalling__i_Compile.V.create_VArray((_143_contents).dtor_v)), _144_remainder);
        } else {
          return _System.Tuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Common____GenericMarshalling__i_Compile._IV>.create_None(), Dafny.Sequence<byte>.FromElements());
        }
      } else {
        return _System.Tuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Common____GenericMarshalling__i_Compile._IV>.create_None(), Dafny.Sequence<byte>.FromElements());
      }
    }
    public static void ParseArray(byte[] data, ulong index, Common____GenericMarshalling__i_Compile._IG eltType, out bool success, out Common____GenericMarshalling__i_Compile._IV v, out ulong rest__index)
    {
      success = false;
      v = Common____GenericMarshalling__i_Compile.V.Default();
      rest__index = 0;
      bool _145_some1;
      Common____GenericMarshalling__i_Compile._IV _146_len;
      ulong _147_rest;
      bool _out14;
      Common____GenericMarshalling__i_Compile._IV _out15;
      ulong _out16;
      Common____GenericMarshalling__i_Compile.__default.ParseUint64(data, index, out _out14, out _out15, out _out16);
      _145_some1 = _out14;
      _146_len = _out15;
      _147_rest = _out16;
      if (_145_some1) {
        bool _148_some2;
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> _149_contents;
        ulong _150_remainder;
        bool _out17;
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> _out18;
        ulong _out19;
        Common____GenericMarshalling__i_Compile.__default.ParseArrayContents(data, _147_rest, eltType, (_146_len).dtor_u, out _out17, out _out18, out _out19);
        _148_some2 = _out17;
        _149_contents = _out18;
        _150_remainder = _out19;
        if (_148_some2) {
          success = true;
          v = Common____GenericMarshalling__i_Compile.V.create_VArray(_149_contents);
          rest__index = _150_remainder;
        } else {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Parse array fails\n")));
          success = false;
          rest__index = (ulong)(data).LongLength;
        }
      } else {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Parse array fails\n")));
        success = false;
        rest__index = (ulong)(data).LongLength;
      }
    }
    public static _System._ITuple2<Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>, Dafny.ISequence<byte>> parse__Tuple__contents(Dafny.ISequence<byte> data, Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> eltTypes)
    {
      if ((eltTypes).Equals((Dafny.Sequence<Common____GenericMarshalling__i_Compile._IG>.FromElements()))) {
        return _System.Tuple2<Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>.create_Some(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements()), data);
      } else {
        _System._ITuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>> _let_tmp_rhs6 = Common____GenericMarshalling__i_Compile.__default.parse__Val(data, (eltTypes).Select(BigInteger.Zero));
        Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV> _151_val = _let_tmp_rhs6.dtor__0;
        Dafny.ISequence<byte> _152_rest1 = _let_tmp_rhs6.dtor__1;
        _System._ITuple2<Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>, Dafny.ISequence<byte>> _let_tmp_rhs7 = Common____GenericMarshalling__i_Compile.__default.parse__Tuple__contents(_152_rest1, (eltTypes).Drop(BigInteger.One));
        Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>> _153_contents = _let_tmp_rhs7.dtor__0;
        Dafny.ISequence<byte> _154_rest2 = _let_tmp_rhs7.dtor__1;
        if ((!((_151_val).is_None)) && (!((_153_contents).is_None))) {
          return _System.Tuple2<Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>.create_Some(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.Concat(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements((_151_val).dtor_v), (_153_contents).dtor_v)), _154_rest2);
        } else {
          return _System.Tuple2<Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>.create_None(), Dafny.Sequence<byte>.FromElements());
        }
      }
    }
    public static void ParseTupleContents(byte[] data, ulong index, Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> eltTypes, out bool success, out Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> v, out ulong rest__index)
    {
      success = false;
      v = Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.Empty;
      rest__index = 0;
      Common____GenericMarshalling__i_Compile._IV[] _155_vArr;
      Common____GenericMarshalling__i_Compile._IV[] _nw6 = Dafny.ArrayHelpers.InitNewArray1<Common____GenericMarshalling__i_Compile._IV>(Common____GenericMarshalling__i_Compile.V.Default(), Dafny.Helpers.ToIntChecked(new BigInteger((eltTypes).Count), "array size exceeds memory limit"));
      _155_vArr = _nw6;
      success = true;
      BigInteger _156_i;
      _156_i = BigInteger.Zero;
      ulong _157_next__val__index;
      _157_next__val__index = index;
      while ((_156_i) < (new BigInteger((eltTypes).Count))) {
        bool _158_some1;
        Common____GenericMarshalling__i_Compile._IV _159_val;
        ulong _160_rest1;
        bool _out20;
        Common____GenericMarshalling__i_Compile._IV _out21;
        ulong _out22;
        Common____GenericMarshalling__i_Compile.__default.ParseVal(data, _157_next__val__index, (eltTypes).Select(_156_i), out _out20, out _out21, out _out22);
        _158_some1 = _out20;
        _159_val = _out21;
        _160_rest1 = _out22;
        if (!(_158_some1)) {
          success = false;
          rest__index = (ulong)(data).LongLength;
          return ;
        }
        (_155_vArr)[(int)((_156_i))] = _159_val;
        _157_next__val__index = _160_rest1;
        _156_i = (_156_i) + (BigInteger.One);
      }
      success = true;
      rest__index = _157_next__val__index;
      v = Dafny.Helpers.SeqFromArray(_155_vArr);
    }
    public static _System._ITuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>> parse__Tuple(Dafny.ISequence<byte> data, Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> eltTypes)
    {
      _System._ITuple2<Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>>, Dafny.ISequence<byte>> _let_tmp_rhs8 = Common____GenericMarshalling__i_Compile.__default.parse__Tuple__contents(data, eltTypes);
      Logic____Option__i_Compile._IOption<Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV>> _161_contents = _let_tmp_rhs8.dtor__0;
      Dafny.ISequence<byte> _162_rest = _let_tmp_rhs8.dtor__1;
      if (!((_161_contents).is_None)) {
        return _System.Tuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Common____GenericMarshalling__i_Compile._IV>.create_Some(Common____GenericMarshalling__i_Compile.V.create_VTuple((_161_contents).dtor_v)), _162_rest);
      } else {
        return _System.Tuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Common____GenericMarshalling__i_Compile._IV>.create_None(), Dafny.Sequence<byte>.FromElements());
      }
    }
    public static void ParseTuple(byte[] data, ulong index, Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> eltTypes, out bool success, out Common____GenericMarshalling__i_Compile._IV v, out ulong rest__index)
    {
      success = false;
      v = Common____GenericMarshalling__i_Compile.V.Default();
      rest__index = 0;
      bool _163_some;
      Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> _164_contents;
      ulong _165_rest;
      bool _out23;
      Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> _out24;
      ulong _out25;
      Common____GenericMarshalling__i_Compile.__default.ParseTupleContents(data, index, eltTypes, out _out23, out _out24, out _out25);
      _163_some = _out23;
      _164_contents = _out24;
      _165_rest = _out25;
      if (_163_some) {
        success = true;
        v = Common____GenericMarshalling__i_Compile.V.create_VTuple(_164_contents);
        rest__index = _165_rest;
      } else {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Parse tuple fails\n")));
        success = false;
        rest__index = (ulong)(data).LongLength;
      }
    }
    public static _System._ITuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>> parse__ByteArray(Dafny.ISequence<byte> data) {
      _System._ITuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>> _let_tmp_rhs9 = Common____GenericMarshalling__i_Compile.__default.parse__Uint64(data);
      Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV> _166_len = _let_tmp_rhs9.dtor__0;
      Dafny.ISequence<byte> _167_rest = _let_tmp_rhs9.dtor__1;
      if ((!((_166_len).is_None)) && ((((_166_len).dtor_v).dtor_u) <= ((ulong)(_167_rest).LongCount))) {
        return _System.Tuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Common____GenericMarshalling__i_Compile._IV>.create_Some(Common____GenericMarshalling__i_Compile.V.create_VByteArray((_167_rest).Subsequence(BigInteger.Zero, ((_166_len).dtor_v).dtor_u))), (_167_rest).Drop(((_166_len).dtor_v).dtor_u));
      } else {
        return _System.Tuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Common____GenericMarshalling__i_Compile._IV>.create_None(), Dafny.Sequence<byte>.FromElements());
      }
    }
    public static void ParseByteArray(byte[] data, ulong index, out bool success, out Common____GenericMarshalling__i_Compile._IV v, out ulong rest__index)
    {
      success = false;
      v = Common____GenericMarshalling__i_Compile.V.Default();
      rest__index = 0;
      bool _168_some;
      Common____GenericMarshalling__i_Compile._IV _169_len;
      ulong _170_rest;
      bool _out26;
      Common____GenericMarshalling__i_Compile._IV _out27;
      ulong _out28;
      Common____GenericMarshalling__i_Compile.__default.ParseUint64(data, index, out _out26, out _out27, out _out28);
      _168_some = _out26;
      _169_len = _out27;
      _170_rest = _out28;
      if ((_168_some) && (((_169_len).dtor_u) <= (((ulong)(data).LongLength) - (_170_rest)))) {
        Dafny.ISequence<byte> _171_rest__seq;
        _171_rest__seq = Dafny.Helpers.SeqFromArray(data).Drop(_170_rest);
        success = true;
        v = Common____GenericMarshalling__i_Compile.V.create_VByteArray(Dafny.Helpers.SeqFromArray(data).Subsequence(_170_rest, (_170_rest) + ((_169_len).dtor_u)));
        rest__index = (_170_rest) + ((_169_len).dtor_u);
      } else {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Parse byte array fails\n")));
        success = false;
        rest__index = (ulong)(data).LongLength;
      }
    }
    public static _System._ITuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>> parse__Case(Dafny.ISequence<byte> data, Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> cases)
    {
      _System._ITuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>> _let_tmp_rhs10 = Common____GenericMarshalling__i_Compile.__default.parse__Uint64(data);
      Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV> _172_caseID = _let_tmp_rhs10.dtor__0;
      Dafny.ISequence<byte> _173_rest1 = _let_tmp_rhs10.dtor__1;
      if ((!((_172_caseID).is_None)) && ((((_172_caseID).dtor_v).dtor_u) < ((ulong)(cases).LongCount))) {
        _System._ITuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>> _let_tmp_rhs11 = Common____GenericMarshalling__i_Compile.__default.parse__Val(_173_rest1, (cases).Select(((_172_caseID).dtor_v).dtor_u));
        Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV> _174_val = _let_tmp_rhs11.dtor__0;
        Dafny.ISequence<byte> _175_rest2 = _let_tmp_rhs11.dtor__1;
        if (!((_174_val).is_None)) {
          return _System.Tuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Common____GenericMarshalling__i_Compile._IV>.create_Some(Common____GenericMarshalling__i_Compile.V.create_VCase(((_172_caseID).dtor_v).dtor_u, (_174_val).dtor_v)), _175_rest2);
        } else {
          return _System.Tuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Common____GenericMarshalling__i_Compile._IV>.create_None(), Dafny.Sequence<byte>.FromElements());
        }
      } else {
        return _System.Tuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>>.create(Logic____Option__i_Compile.Option<Common____GenericMarshalling__i_Compile._IV>.create_None(), Dafny.Sequence<byte>.FromElements());
      }
    }
    public static void ParseCase(byte[] data, ulong index, Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> cases, out bool success, out Common____GenericMarshalling__i_Compile._IV v, out ulong rest__index)
    {
      success = false;
      v = Common____GenericMarshalling__i_Compile.V.Default();
      rest__index = 0;
      bool _176_some1;
      Common____GenericMarshalling__i_Compile._IV _177_caseID;
      ulong _178_rest1;
      bool _out29;
      Common____GenericMarshalling__i_Compile._IV _out30;
      ulong _out31;
      Common____GenericMarshalling__i_Compile.__default.ParseUint64(data, index, out _out29, out _out30, out _out31);
      _176_some1 = _out29;
      _177_caseID = _out30;
      _178_rest1 = _out31;
      if ((_176_some1) && (((_177_caseID).dtor_u) < ((ulong)(cases).LongCount))) {
        bool _179_some2;
        Common____GenericMarshalling__i_Compile._IV _180_val;
        ulong _181_rest2;
        bool _out32;
        Common____GenericMarshalling__i_Compile._IV _out33;
        ulong _out34;
        Common____GenericMarshalling__i_Compile.__default.ParseVal(data, _178_rest1, (cases).Select((_177_caseID).dtor_u), out _out32, out _out33, out _out34);
        _179_some2 = _out32;
        _180_val = _out33;
        _181_rest2 = _out34;
        if (_179_some2) {
          success = true;
          v = Common____GenericMarshalling__i_Compile.V.create_VCase((_177_caseID).dtor_u, _180_val);
          rest__index = _181_rest2;
        } else {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Parse case fails\n")));
          success = false;
          rest__index = (ulong)(data).LongLength;
        }
      } else {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Parse case fails\n")));
        success = false;
        rest__index = (ulong)(data).LongLength;
      }
    }
    public static _System._ITuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>> parse__Val(Dafny.ISequence<byte> data, Common____GenericMarshalling__i_Compile._IG grammar)
    {
      Common____GenericMarshalling__i_Compile._IG _source0 = grammar;
      if (_source0.is_GUint64) {
        return Common____GenericMarshalling__i_Compile.__default.parse__Uint64(data);
      } else if (_source0.is_GArray) {
        Common____GenericMarshalling__i_Compile._IG _182___mcc_h0 = _source0.dtor_elt;
        Common____GenericMarshalling__i_Compile._IG _183_elt = _182___mcc_h0;
        return Common____GenericMarshalling__i_Compile.__default.parse__Array(data, _183_elt);
      } else if (_source0.is_GTuple) {
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> _184___mcc_h1 = _source0.dtor_t;
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> _185_t = _184___mcc_h1;
        return Common____GenericMarshalling__i_Compile.__default.parse__Tuple(data, _185_t);
      } else if (_source0.is_GByteArray) {
        return Common____GenericMarshalling__i_Compile.__default.parse__ByteArray(data);
      } else {
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> _186___mcc_h2 = _source0.dtor_cases;
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> _187_cases = _186___mcc_h2;
        return Common____GenericMarshalling__i_Compile.__default.parse__Case(data, _187_cases);
      }
    }
    public static void ParseVal(byte[] data, ulong index, Common____GenericMarshalling__i_Compile._IG grammar, out bool success, out Common____GenericMarshalling__i_Compile._IV v, out ulong rest__index)
    {
      success = false;
      v = Common____GenericMarshalling__i_Compile.V.Default();
      rest__index = 0;
      Common____GenericMarshalling__i_Compile._IG _source1 = grammar;
      if (_source1.is_GUint64) {
        bool _out35;
        Common____GenericMarshalling__i_Compile._IV _out36;
        ulong _out37;
        Common____GenericMarshalling__i_Compile.__default.ParseUint64(data, index, out _out35, out _out36, out _out37);
        success = _out35;
        v = _out36;
        rest__index = _out37;
      } else if (_source1.is_GArray) {
        Common____GenericMarshalling__i_Compile._IG _188___mcc_h0 = _source1.dtor_elt;
        Common____GenericMarshalling__i_Compile._IG _189_elt = _188___mcc_h0;
        bool _out38;
        Common____GenericMarshalling__i_Compile._IV _out39;
        ulong _out40;
        Common____GenericMarshalling__i_Compile.__default.ParseArray(data, index, _189_elt, out _out38, out _out39, out _out40);
        success = _out38;
        v = _out39;
        rest__index = _out40;
      } else if (_source1.is_GTuple) {
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> _190___mcc_h1 = _source1.dtor_t;
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> _191_t = _190___mcc_h1;
        bool _out41;
        Common____GenericMarshalling__i_Compile._IV _out42;
        ulong _out43;
        Common____GenericMarshalling__i_Compile.__default.ParseTuple(data, index, _191_t, out _out41, out _out42, out _out43);
        success = _out41;
        v = _out42;
        rest__index = _out43;
      } else if (_source1.is_GByteArray) {
        bool _out44;
        Common____GenericMarshalling__i_Compile._IV _out45;
        ulong _out46;
        Common____GenericMarshalling__i_Compile.__default.ParseByteArray(data, index, out _out44, out _out45, out _out46);
        success = _out44;
        v = _out45;
        rest__index = _out46;
      } else {
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> _192___mcc_h2 = _source1.dtor_cases;
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> _193_cases = _192___mcc_h2;
        bool _out47;
        Common____GenericMarshalling__i_Compile._IV _out48;
        ulong _out49;
        Common____GenericMarshalling__i_Compile.__default.ParseCase(data, index, _193_cases, out _out47, out _out48, out _out49);
        success = _out47;
        v = _out48;
        rest__index = _out49;
      }
    }
    public static void Demarshall(byte[] data, Common____GenericMarshalling__i_Compile._IG grammar, out bool success, out Common____GenericMarshalling__i_Compile._IV v)
    {
      success = false;
      v = Common____GenericMarshalling__i_Compile.V.Default();
      ulong _194_rest = 0;
      bool _out50;
      Common____GenericMarshalling__i_Compile._IV _out51;
      ulong _out52;
      Common____GenericMarshalling__i_Compile.__default.ParseVal(data, 0UL, grammar, out _out50, out _out51, out _out52);
      success = _out50;
      v = _out51;
      _194_rest = _out52;
      if ((success) && ((_194_rest) == ((ulong)(data).LongLength))) {
      } else {
        success = false;
      }
    }
    public static ulong ComputeSeqSum(Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> s)
    {
      ulong size = 0;
      if (((ulong)(s).LongCount) == (0UL)) {
        size = 0UL;
      } else {
        ulong _195_v__size;
        ulong _out53;
        _out53 = Common____GenericMarshalling__i_Compile.__default.ComputeSizeOf((s).Select(BigInteger.Zero));
        _195_v__size = _out53;
        ulong _196_rest__size;
        ulong _out54;
        _out54 = Common____GenericMarshalling__i_Compile.__default.ComputeSeqSum((s).Drop(BigInteger.One));
        _196_rest__size = _out54;
        size = (_195_v__size) + (_196_rest__size);
      }
      return size;
    }
    public static ulong ComputeSizeOf(Common____GenericMarshalling__i_Compile._IV val)
    {
      ulong size = 0;
      Common____GenericMarshalling__i_Compile._IV _source2 = val;
      if (_source2.is_VUint64) {
        ulong _197___mcc_h0 = _source2.dtor_u;
        size = 8UL;
      } else if (_source2.is_VArray) {
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> _198___mcc_h1 = _source2.dtor_a;
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> _199_a = _198___mcc_h1;
        ulong _200_v;
        ulong _out55;
        _out55 = Common____GenericMarshalling__i_Compile.__default.ComputeSeqSum(_199_a);
        _200_v = _out55;
        if ((_200_v) == (0UL)) {
          size = 8UL;
        } else {
          size = (8UL) + (_200_v);
        }
      } else if (_source2.is_VTuple) {
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> _201___mcc_h2 = _source2.dtor_t;
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> _202_t = _201___mcc_h2;
        ulong _out56;
        _out56 = Common____GenericMarshalling__i_Compile.__default.ComputeSeqSum(_202_t);
        size = _out56;
      } else if (_source2.is_VByteArray) {
        Dafny.ISequence<byte> _203___mcc_h3 = _source2.dtor_b;
        Dafny.ISequence<byte> _204_b = _203___mcc_h3;
        size = (8UL) + ((ulong)(_204_b).LongCount);
      } else {
        ulong _205___mcc_h4 = _source2.dtor_c;
        Common____GenericMarshalling__i_Compile._IV _206___mcc_h5 = _source2.dtor_val;
        Common____GenericMarshalling__i_Compile._IV _207_v = _206___mcc_h5;
        ulong _208_c = _205___mcc_h4;
        ulong _209_vs;
        ulong _out57;
        _out57 = Common____GenericMarshalling__i_Compile.__default.ComputeSizeOf(_207_v);
        _209_vs = _out57;
        size = (8UL) + (_209_vs);
      }
      return size;
    }
    public static void MarshallUint64(ulong n, byte[] data, ulong index)
    {
      Common____MarshallInt__i_Compile.__default.MarshallUint64__guts(n, data, index);
      _System._ITuple2<Logic____Option__i_Compile._IOption<Common____GenericMarshalling__i_Compile._IV>, Dafny.ISequence<byte>> _210_tuple;
      _210_tuple = Common____GenericMarshalling__i_Compile.__default.parse__Uint64(Dafny.Helpers.SeqFromArray(data).Drop(index));
    }
    public static ulong MarshallArrayContents(Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> contents, Common____GenericMarshalling__i_Compile._IG eltType, byte[] data, ulong index)
    {
      ulong size = 0;
      BigInteger _211_i;
      _211_i = BigInteger.Zero;
      ulong _212_cur__index;
      _212_cur__index = index;
      while ((_211_i) < (new BigInteger((contents).Count))) {
        ulong _213_item__size;
        ulong _out58;
        _out58 = Common____GenericMarshalling__i_Compile.__default.MarshallVal((contents).Select(_211_i), eltType, data, _212_cur__index);
        _213_item__size = _out58;
        _212_cur__index = (_212_cur__index) + (_213_item__size);
        _211_i = (_211_i) + (BigInteger.One);
      }
      size = (_212_cur__index) - (index);
      return size;
    }
    public static ulong MarshallArray(Common____GenericMarshalling__i_Compile._IV val, Common____GenericMarshalling__i_Compile._IG grammar, byte[] data, ulong index)
    {
      ulong size = 0;
      Common____GenericMarshalling__i_Compile.__default.MarshallUint64((ulong)((val).dtor_a).LongCount, data, index);
      ulong _214_contents__size;
      ulong _out59;
      _out59 = Common____GenericMarshalling__i_Compile.__default.MarshallArrayContents((val).dtor_a, (grammar).dtor_elt, data, (index) + (Native____NativeTypes__i_Compile.__default.Uint64Size()));
      _214_contents__size = _out59;
      size = (8UL) + (_214_contents__size);
      return size;
    }
    public static ulong MarshallTupleContents(Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> contents, Dafny.ISequence<Common____GenericMarshalling__i_Compile._IG> eltTypes, byte[] data, ulong index)
    {
      ulong size = 0;
      BigInteger _215_i;
      _215_i = BigInteger.Zero;
      ulong _216_cur__index;
      _216_cur__index = index;
      while ((_215_i) < (new BigInteger((contents).Count))) {
        ulong _217_item__size;
        ulong _out60;
        _out60 = Common____GenericMarshalling__i_Compile.__default.MarshallVal((contents).Select(_215_i), (eltTypes).Select(_215_i), data, _216_cur__index);
        _217_item__size = _out60;
        _216_cur__index = (_216_cur__index) + (_217_item__size);
        _215_i = (_215_i) + (BigInteger.One);
      }
      size = (_216_cur__index) - (index);
      return size;
    }
    public static ulong MarshallTuple(Common____GenericMarshalling__i_Compile._IV val, Common____GenericMarshalling__i_Compile._IG grammar, byte[] data, ulong index)
    {
      ulong size = 0;
      ulong _out61;
      _out61 = Common____GenericMarshalling__i_Compile.__default.MarshallTupleContents((val).dtor_t, (grammar).dtor_t, data, index);
      size = _out61;
      return size;
    }
    public static void MarshallBytes(Dafny.ISequence<byte> bytes, byte[] data, ulong index)
    {
      Native____Io__s_Compile.Arrays.CopySeqIntoArray<byte>(bytes, 0UL, data, index, (ulong)(bytes).LongCount);
    }
    public static ulong MarshallByteArray(Common____GenericMarshalling__i_Compile._IV val, Common____GenericMarshalling__i_Compile._IG grammar, byte[] data, ulong index)
    {
      ulong size = 0;
      Common____GenericMarshalling__i_Compile.__default.MarshallUint64((ulong)((val).dtor_b).LongCount, data, index);
      Common____GenericMarshalling__i_Compile.__default.MarshallBytes((val).dtor_b, data, (index) + (8UL));
      size = (8UL) + ((ulong)((val).dtor_b).LongCount);
      return size;
    }
    public static ulong MarshallCase(Common____GenericMarshalling__i_Compile._IV val, Common____GenericMarshalling__i_Compile._IG grammar, byte[] data, ulong index)
    {
      ulong size = 0;
      Common____GenericMarshalling__i_Compile.__default.MarshallUint64((val).dtor_c, data, index);
      ulong _218_val__size;
      ulong _out62;
      _out62 = Common____GenericMarshalling__i_Compile.__default.MarshallVal((val).dtor_val, ((grammar).dtor_cases).Select((val).dtor_c), data, (index) + (8UL));
      _218_val__size = _out62;
      size = (8UL) + (_218_val__size);
      return size;
    }
    public static ulong MarshallVUint64(Common____GenericMarshalling__i_Compile._IV val, Common____GenericMarshalling__i_Compile._IG grammar, byte[] data, ulong index)
    {
      ulong size = 0;
      Common____GenericMarshalling__i_Compile.__default.MarshallUint64((val).dtor_u, data, index);
      size = 8UL;
      return size;
      return size;
    }
    public static ulong MarshallVal(Common____GenericMarshalling__i_Compile._IV val, Common____GenericMarshalling__i_Compile._IG grammar, byte[] data, ulong index)
    {
      ulong size = 0;
      Common____GenericMarshalling__i_Compile._IV _source3 = val;
      if (_source3.is_VUint64) {
        ulong _219___mcc_h0 = _source3.dtor_u;
        ulong _out63;
        _out63 = Common____GenericMarshalling__i_Compile.__default.MarshallVUint64(val, grammar, data, index);
        size = _out63;
      } else if (_source3.is_VArray) {
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> _220___mcc_h1 = _source3.dtor_a;
        ulong _out64;
        _out64 = Common____GenericMarshalling__i_Compile.__default.MarshallArray(val, grammar, data, index);
        size = _out64;
      } else if (_source3.is_VTuple) {
        Dafny.ISequence<Common____GenericMarshalling__i_Compile._IV> _221___mcc_h2 = _source3.dtor_t;
        ulong _out65;
        _out65 = Common____GenericMarshalling__i_Compile.__default.MarshallTuple(val, grammar, data, index);
        size = _out65;
      } else if (_source3.is_VByteArray) {
        Dafny.ISequence<byte> _222___mcc_h3 = _source3.dtor_b;
        ulong _out66;
        _out66 = Common____GenericMarshalling__i_Compile.__default.MarshallByteArray(val, grammar, data, index);
        size = _out66;
      } else {
        ulong _223___mcc_h4 = _source3.dtor_c;
        Common____GenericMarshalling__i_Compile._IV _224___mcc_h5 = _source3.dtor_val;
        ulong _out67;
        _out67 = Common____GenericMarshalling__i_Compile.__default.MarshallCase(val, grammar, data, index);
        size = _out67;
      }
      return size;
    }
    public static byte[] Marshall(Common____GenericMarshalling__i_Compile._IV val, Common____GenericMarshalling__i_Compile._IG grammar)
    {
      byte[] data = new byte[0];
      ulong _225_size;
      ulong _out68;
      _out68 = Common____GenericMarshalling__i_Compile.__default.ComputeSizeOf(val);
      _225_size = _out68;
      byte[] _nw7 = new byte[Dafny.Helpers.ToIntChecked(_225_size, "array size exceeds memory limit")];
      data = _nw7;
      ulong _226_computed__size;
      ulong _out69;
      _out69 = Common____GenericMarshalling__i_Compile.__default.MarshallVal(val, grammar, data, 0UL);
      _226_computed__size = _out69;
      return data;
    }
  }
} // end of namespace Common____GenericMarshalling__i_Compile
namespace CausalMesh__Message__i_Compile {

  public interface _IMessage {
    bool is_Message__Read { get; }
    bool is_Message__Read__Reply { get; }
    bool is_Message__Write { get; }
    bool is_Message__Write__Reply { get; }
    bool is_Message__Propagation { get; }
    BigInteger dtor_opn__read { get; }
    BigInteger dtor_key__read { get; }
    Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps__read { get; }
    BigInteger dtor_opn__rreply { get; }
    BigInteger dtor_key__rreply { get; }
    Dafny.ISequence<BigInteger> dtor_vc__rreply { get; }
    Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps__rreply { get; }
    BigInteger dtor_opn__write { get; }
    BigInteger dtor_key__write { get; }
    Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps__write { get; }
    Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> dtor_local { get; }
    BigInteger dtor_opn__wreply { get; }
    BigInteger dtor_key__wreply { get; }
    Dafny.ISequence<BigInteger> dtor_vc__wreply { get; }
    BigInteger dtor_key { get; }
    CausalMesh__Types__i_Compile._IMeta dtor_meta { get; }
    BigInteger dtor_start { get; }
    BigInteger dtor_round { get; }
    _IMessage DowncastClone();
  }
  public abstract class Message : _IMessage {
    public Message() { }
    private static readonly CausalMesh__Message__i_Compile._IMessage theDefault = create_Message__Read(BigInteger.Zero, BigInteger.Zero, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty);
    public static CausalMesh__Message__i_Compile._IMessage Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<CausalMesh__Message__i_Compile._IMessage> _TYPE = new Dafny.TypeDescriptor<CausalMesh__Message__i_Compile._IMessage>(CausalMesh__Message__i_Compile.Message.Default());
    public static Dafny.TypeDescriptor<CausalMesh__Message__i_Compile._IMessage> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IMessage create_Message__Read(BigInteger opn__read, BigInteger key__read, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps__read) {
      return new Message_Message__Read(opn__read, key__read, deps__read);
    }
    public static _IMessage create_Message__Read__Reply(BigInteger opn__rreply, BigInteger key__rreply, Dafny.ISequence<BigInteger> vc__rreply, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps__rreply) {
      return new Message_Message__Read__Reply(opn__rreply, key__rreply, vc__rreply, deps__rreply);
    }
    public static _IMessage create_Message__Write(BigInteger opn__write, BigInteger key__write, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps__write, Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> local) {
      return new Message_Message__Write(opn__write, key__write, deps__write, local);
    }
    public static _IMessage create_Message__Write__Reply(BigInteger opn__wreply, BigInteger key__wreply, Dafny.ISequence<BigInteger> vc__wreply) {
      return new Message_Message__Write__Reply(opn__wreply, key__wreply, vc__wreply);
    }
    public static _IMessage create_Message__Propagation(BigInteger key, CausalMesh__Types__i_Compile._IMeta meta, BigInteger start, BigInteger round) {
      return new Message_Message__Propagation(key, meta, start, round);
    }
    public bool is_Message__Read { get { return this is Message_Message__Read; } }
    public bool is_Message__Read__Reply { get { return this is Message_Message__Read__Reply; } }
    public bool is_Message__Write { get { return this is Message_Message__Write; } }
    public bool is_Message__Write__Reply { get { return this is Message_Message__Write__Reply; } }
    public bool is_Message__Propagation { get { return this is Message_Message__Propagation; } }
    public BigInteger dtor_opn__read {
      get {
        var d = this;
        return ((Message_Message__Read)d)._opn__read;
      }
    }
    public BigInteger dtor_key__read {
      get {
        var d = this;
        return ((Message_Message__Read)d)._key__read;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps__read {
      get {
        var d = this;
        return ((Message_Message__Read)d)._deps__read;
      }
    }
    public BigInteger dtor_opn__rreply {
      get {
        var d = this;
        return ((Message_Message__Read__Reply)d)._opn__rreply;
      }
    }
    public BigInteger dtor_key__rreply {
      get {
        var d = this;
        return ((Message_Message__Read__Reply)d)._key__rreply;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_vc__rreply {
      get {
        var d = this;
        return ((Message_Message__Read__Reply)d)._vc__rreply;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps__rreply {
      get {
        var d = this;
        return ((Message_Message__Read__Reply)d)._deps__rreply;
      }
    }
    public BigInteger dtor_opn__write {
      get {
        var d = this;
        return ((Message_Message__Write)d)._opn__write;
      }
    }
    public BigInteger dtor_key__write {
      get {
        var d = this;
        return ((Message_Message__Write)d)._key__write;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps__write {
      get {
        var d = this;
        return ((Message_Message__Write)d)._deps__write;
      }
    }
    public Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> dtor_local {
      get {
        var d = this;
        return ((Message_Message__Write)d)._local;
      }
    }
    public BigInteger dtor_opn__wreply {
      get {
        var d = this;
        return ((Message_Message__Write__Reply)d)._opn__wreply;
      }
    }
    public BigInteger dtor_key__wreply {
      get {
        var d = this;
        return ((Message_Message__Write__Reply)d)._key__wreply;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_vc__wreply {
      get {
        var d = this;
        return ((Message_Message__Write__Reply)d)._vc__wreply;
      }
    }
    public BigInteger dtor_key {
      get {
        var d = this;
        return ((Message_Message__Propagation)d)._key;
      }
    }
    public CausalMesh__Types__i_Compile._IMeta dtor_meta {
      get {
        var d = this;
        return ((Message_Message__Propagation)d)._meta;
      }
    }
    public BigInteger dtor_start {
      get {
        var d = this;
        return ((Message_Message__Propagation)d)._start;
      }
    }
    public BigInteger dtor_round {
      get {
        var d = this;
        return ((Message_Message__Propagation)d)._round;
      }
    }
    public abstract _IMessage DowncastClone();
  }
  public class Message_Message__Read : Message {
    public readonly BigInteger _opn__read;
    public readonly BigInteger _key__read;
    public readonly Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _deps__read;
    public Message_Message__Read(BigInteger opn__read, BigInteger key__read, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps__read) {
      this._opn__read = opn__read;
      this._key__read = key__read;
      this._deps__read = deps__read;
    }
    public override _IMessage DowncastClone() {
      if (this is _IMessage dt) { return dt; }
      return new Message_Message__Read(_opn__read, _key__read, _deps__read);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__Message__i_Compile.Message_Message__Read;
      return oth != null && this._opn__read == oth._opn__read && this._key__read == oth._key__read && object.Equals(this._deps__read, oth._deps__read);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._opn__read));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key__read));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._deps__read));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__Message__i_Compile.Message.Message_Read";
      s += "(";
      s += Dafny.Helpers.ToString(this._opn__read);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key__read);
      s += ", ";
      s += Dafny.Helpers.ToString(this._deps__read);
      s += ")";
      return s;
    }
  }
  public class Message_Message__Read__Reply : Message {
    public readonly BigInteger _opn__rreply;
    public readonly BigInteger _key__rreply;
    public readonly Dafny.ISequence<BigInteger> _vc__rreply;
    public readonly Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _deps__rreply;
    public Message_Message__Read__Reply(BigInteger opn__rreply, BigInteger key__rreply, Dafny.ISequence<BigInteger> vc__rreply, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps__rreply) {
      this._opn__rreply = opn__rreply;
      this._key__rreply = key__rreply;
      this._vc__rreply = vc__rreply;
      this._deps__rreply = deps__rreply;
    }
    public override _IMessage DowncastClone() {
      if (this is _IMessage dt) { return dt; }
      return new Message_Message__Read__Reply(_opn__rreply, _key__rreply, _vc__rreply, _deps__rreply);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__Message__i_Compile.Message_Message__Read__Reply;
      return oth != null && this._opn__rreply == oth._opn__rreply && this._key__rreply == oth._key__rreply && object.Equals(this._vc__rreply, oth._vc__rreply) && object.Equals(this._deps__rreply, oth._deps__rreply);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._opn__rreply));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key__rreply));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._vc__rreply));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._deps__rreply));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__Message__i_Compile.Message.Message_Read_Reply";
      s += "(";
      s += Dafny.Helpers.ToString(this._opn__rreply);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key__rreply);
      s += ", ";
      s += Dafny.Helpers.ToString(this._vc__rreply);
      s += ", ";
      s += Dafny.Helpers.ToString(this._deps__rreply);
      s += ")";
      return s;
    }
  }
  public class Message_Message__Write : Message {
    public readonly BigInteger _opn__write;
    public readonly BigInteger _key__write;
    public readonly Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _deps__write;
    public readonly Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> _local;
    public Message_Message__Write(BigInteger opn__write, BigInteger key__write, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps__write, Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> local) {
      this._opn__write = opn__write;
      this._key__write = key__write;
      this._deps__write = deps__write;
      this._local = local;
    }
    public override _IMessage DowncastClone() {
      if (this is _IMessage dt) { return dt; }
      return new Message_Message__Write(_opn__write, _key__write, _deps__write, _local);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__Message__i_Compile.Message_Message__Write;
      return oth != null && this._opn__write == oth._opn__write && this._key__write == oth._key__write && object.Equals(this._deps__write, oth._deps__write) && object.Equals(this._local, oth._local);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._opn__write));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key__write));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._deps__write));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._local));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__Message__i_Compile.Message.Message_Write";
      s += "(";
      s += Dafny.Helpers.ToString(this._opn__write);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key__write);
      s += ", ";
      s += Dafny.Helpers.ToString(this._deps__write);
      s += ", ";
      s += Dafny.Helpers.ToString(this._local);
      s += ")";
      return s;
    }
  }
  public class Message_Message__Write__Reply : Message {
    public readonly BigInteger _opn__wreply;
    public readonly BigInteger _key__wreply;
    public readonly Dafny.ISequence<BigInteger> _vc__wreply;
    public Message_Message__Write__Reply(BigInteger opn__wreply, BigInteger key__wreply, Dafny.ISequence<BigInteger> vc__wreply) {
      this._opn__wreply = opn__wreply;
      this._key__wreply = key__wreply;
      this._vc__wreply = vc__wreply;
    }
    public override _IMessage DowncastClone() {
      if (this is _IMessage dt) { return dt; }
      return new Message_Message__Write__Reply(_opn__wreply, _key__wreply, _vc__wreply);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__Message__i_Compile.Message_Message__Write__Reply;
      return oth != null && this._opn__wreply == oth._opn__wreply && this._key__wreply == oth._key__wreply && object.Equals(this._vc__wreply, oth._vc__wreply);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._opn__wreply));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key__wreply));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._vc__wreply));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__Message__i_Compile.Message.Message_Write_Reply";
      s += "(";
      s += Dafny.Helpers.ToString(this._opn__wreply);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key__wreply);
      s += ", ";
      s += Dafny.Helpers.ToString(this._vc__wreply);
      s += ")";
      return s;
    }
  }
  public class Message_Message__Propagation : Message {
    public readonly BigInteger _key;
    public readonly CausalMesh__Types__i_Compile._IMeta _meta;
    public readonly BigInteger _start;
    public readonly BigInteger _round;
    public Message_Message__Propagation(BigInteger key, CausalMesh__Types__i_Compile._IMeta meta, BigInteger start, BigInteger round) {
      this._key = key;
      this._meta = meta;
      this._start = start;
      this._round = round;
    }
    public override _IMessage DowncastClone() {
      if (this is _IMessage dt) { return dt; }
      return new Message_Message__Propagation(_key, _meta, _start, _round);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__Message__i_Compile.Message_Message__Propagation;
      return oth != null && this._key == oth._key && object.Equals(this._meta, oth._meta) && this._start == oth._start && this._round == oth._round;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._meta));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._start));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._round));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__Message__i_Compile.Message.Message_Propagation";
      s += "(";
      s += Dafny.Helpers.ToString(this._key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._meta);
      s += ", ";
      s += Dafny.Helpers.ToString(this._start);
      s += ", ";
      s += Dafny.Helpers.ToString(this._round);
      s += ")";
      return s;
    }
  }

} // end of namespace CausalMesh__Message__i_Compile
namespace CausalMesh__CMessage__i_Compile {

  public interface _ICMessage {
    bool is_CMessage__Read { get; }
    bool is_CMessage__Read__Reply { get; }
    bool is_CMessage__Write { get; }
    bool is_CMessage__Write__Reply { get; }
    bool is_CMessage__Propagation { get; }
    BigInteger dtor_opn__read { get; }
    BigInteger dtor_key__read { get; }
    Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps__read { get; }
    BigInteger dtor_opn__rreply { get; }
    BigInteger dtor_key__rreply { get; }
    Dafny.ISequence<BigInteger> dtor_vc__rreply { get; }
    Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps__rreply { get; }
    BigInteger dtor_opn__write { get; }
    BigInteger dtor_key__write { get; }
    Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps__write { get; }
    Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> dtor_local { get; }
    Dafny.ISequence<BigInteger> dtor_mvc { get; }
    BigInteger dtor_opn__wreply { get; }
    BigInteger dtor_key__wreply { get; }
    Dafny.ISequence<BigInteger> dtor_vc__wreply { get; }
    BigInteger dtor_key { get; }
    CausalMesh__CTypes__i_Compile._ICMeta dtor_meta { get; }
    BigInteger dtor_start { get; }
    BigInteger dtor_round { get; }
    _ICMessage DowncastClone();
  }
  public abstract class CMessage : _ICMessage {
    public CMessage() { }
    private static readonly CausalMesh__CMessage__i_Compile._ICMessage theDefault = create_CMessage__Read(BigInteger.Zero, BigInteger.Zero, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty);
    public static CausalMesh__CMessage__i_Compile._ICMessage Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<CausalMesh__CMessage__i_Compile._ICMessage> _TYPE = new Dafny.TypeDescriptor<CausalMesh__CMessage__i_Compile._ICMessage>(CausalMesh__CMessage__i_Compile.CMessage.Default());
    public static Dafny.TypeDescriptor<CausalMesh__CMessage__i_Compile._ICMessage> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICMessage create_CMessage__Read(BigInteger opn__read, BigInteger key__read, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps__read) {
      return new CMessage_CMessage__Read(opn__read, key__read, deps__read);
    }
    public static _ICMessage create_CMessage__Read__Reply(BigInteger opn__rreply, BigInteger key__rreply, Dafny.ISequence<BigInteger> vc__rreply, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps__rreply) {
      return new CMessage_CMessage__Read__Reply(opn__rreply, key__rreply, vc__rreply, deps__rreply);
    }
    public static _ICMessage create_CMessage__Write(BigInteger opn__write, BigInteger key__write, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps__write, Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> local, Dafny.ISequence<BigInteger> mvc) {
      return new CMessage_CMessage__Write(opn__write, key__write, deps__write, local, mvc);
    }
    public static _ICMessage create_CMessage__Write__Reply(BigInteger opn__wreply, BigInteger key__wreply, Dafny.ISequence<BigInteger> vc__wreply) {
      return new CMessage_CMessage__Write__Reply(opn__wreply, key__wreply, vc__wreply);
    }
    public static _ICMessage create_CMessage__Propagation(BigInteger key, CausalMesh__CTypes__i_Compile._ICMeta meta, BigInteger start, BigInteger round) {
      return new CMessage_CMessage__Propagation(key, meta, start, round);
    }
    public bool is_CMessage__Read { get { return this is CMessage_CMessage__Read; } }
    public bool is_CMessage__Read__Reply { get { return this is CMessage_CMessage__Read__Reply; } }
    public bool is_CMessage__Write { get { return this is CMessage_CMessage__Write; } }
    public bool is_CMessage__Write__Reply { get { return this is CMessage_CMessage__Write__Reply; } }
    public bool is_CMessage__Propagation { get { return this is CMessage_CMessage__Propagation; } }
    public BigInteger dtor_opn__read {
      get {
        var d = this;
        return ((CMessage_CMessage__Read)d)._opn__read;
      }
    }
    public BigInteger dtor_key__read {
      get {
        var d = this;
        return ((CMessage_CMessage__Read)d)._key__read;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps__read {
      get {
        var d = this;
        return ((CMessage_CMessage__Read)d)._deps__read;
      }
    }
    public BigInteger dtor_opn__rreply {
      get {
        var d = this;
        return ((CMessage_CMessage__Read__Reply)d)._opn__rreply;
      }
    }
    public BigInteger dtor_key__rreply {
      get {
        var d = this;
        return ((CMessage_CMessage__Read__Reply)d)._key__rreply;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_vc__rreply {
      get {
        var d = this;
        return ((CMessage_CMessage__Read__Reply)d)._vc__rreply;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps__rreply {
      get {
        var d = this;
        return ((CMessage_CMessage__Read__Reply)d)._deps__rreply;
      }
    }
    public BigInteger dtor_opn__write {
      get {
        var d = this;
        return ((CMessage_CMessage__Write)d)._opn__write;
      }
    }
    public BigInteger dtor_key__write {
      get {
        var d = this;
        return ((CMessage_CMessage__Write)d)._key__write;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps__write {
      get {
        var d = this;
        return ((CMessage_CMessage__Write)d)._deps__write;
      }
    }
    public Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> dtor_local {
      get {
        var d = this;
        return ((CMessage_CMessage__Write)d)._local;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_mvc {
      get {
        var d = this;
        return ((CMessage_CMessage__Write)d)._mvc;
      }
    }
    public BigInteger dtor_opn__wreply {
      get {
        var d = this;
        return ((CMessage_CMessage__Write__Reply)d)._opn__wreply;
      }
    }
    public BigInteger dtor_key__wreply {
      get {
        var d = this;
        return ((CMessage_CMessage__Write__Reply)d)._key__wreply;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_vc__wreply {
      get {
        var d = this;
        return ((CMessage_CMessage__Write__Reply)d)._vc__wreply;
      }
    }
    public BigInteger dtor_key {
      get {
        var d = this;
        return ((CMessage_CMessage__Propagation)d)._key;
      }
    }
    public CausalMesh__CTypes__i_Compile._ICMeta dtor_meta {
      get {
        var d = this;
        return ((CMessage_CMessage__Propagation)d)._meta;
      }
    }
    public BigInteger dtor_start {
      get {
        var d = this;
        return ((CMessage_CMessage__Propagation)d)._start;
      }
    }
    public BigInteger dtor_round {
      get {
        var d = this;
        return ((CMessage_CMessage__Propagation)d)._round;
      }
    }
    public abstract _ICMessage DowncastClone();
  }
  public class CMessage_CMessage__Read : CMessage {
    public readonly BigInteger _opn__read;
    public readonly BigInteger _key__read;
    public readonly Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _deps__read;
    public CMessage_CMessage__Read(BigInteger opn__read, BigInteger key__read, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps__read) {
      this._opn__read = opn__read;
      this._key__read = key__read;
      this._deps__read = deps__read;
    }
    public override _ICMessage DowncastClone() {
      if (this is _ICMessage dt) { return dt; }
      return new CMessage_CMessage__Read(_opn__read, _key__read, _deps__read);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__CMessage__i_Compile.CMessage_CMessage__Read;
      return oth != null && this._opn__read == oth._opn__read && this._key__read == oth._key__read && object.Equals(this._deps__read, oth._deps__read);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._opn__read));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key__read));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._deps__read));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__CMessage__i_Compile.CMessage.CMessage_Read";
      s += "(";
      s += Dafny.Helpers.ToString(this._opn__read);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key__read);
      s += ", ";
      s += Dafny.Helpers.ToString(this._deps__read);
      s += ")";
      return s;
    }
  }
  public class CMessage_CMessage__Read__Reply : CMessage {
    public readonly BigInteger _opn__rreply;
    public readonly BigInteger _key__rreply;
    public readonly Dafny.ISequence<BigInteger> _vc__rreply;
    public readonly Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _deps__rreply;
    public CMessage_CMessage__Read__Reply(BigInteger opn__rreply, BigInteger key__rreply, Dafny.ISequence<BigInteger> vc__rreply, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps__rreply) {
      this._opn__rreply = opn__rreply;
      this._key__rreply = key__rreply;
      this._vc__rreply = vc__rreply;
      this._deps__rreply = deps__rreply;
    }
    public override _ICMessage DowncastClone() {
      if (this is _ICMessage dt) { return dt; }
      return new CMessage_CMessage__Read__Reply(_opn__rreply, _key__rreply, _vc__rreply, _deps__rreply);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__CMessage__i_Compile.CMessage_CMessage__Read__Reply;
      return oth != null && this._opn__rreply == oth._opn__rreply && this._key__rreply == oth._key__rreply && object.Equals(this._vc__rreply, oth._vc__rreply) && object.Equals(this._deps__rreply, oth._deps__rreply);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._opn__rreply));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key__rreply));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._vc__rreply));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._deps__rreply));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__CMessage__i_Compile.CMessage.CMessage_Read_Reply";
      s += "(";
      s += Dafny.Helpers.ToString(this._opn__rreply);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key__rreply);
      s += ", ";
      s += Dafny.Helpers.ToString(this._vc__rreply);
      s += ", ";
      s += Dafny.Helpers.ToString(this._deps__rreply);
      s += ")";
      return s;
    }
  }
  public class CMessage_CMessage__Write : CMessage {
    public readonly BigInteger _opn__write;
    public readonly BigInteger _key__write;
    public readonly Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _deps__write;
    public readonly Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _local;
    public readonly Dafny.ISequence<BigInteger> _mvc;
    public CMessage_CMessage__Write(BigInteger opn__write, BigInteger key__write, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps__write, Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> local, Dafny.ISequence<BigInteger> mvc) {
      this._opn__write = opn__write;
      this._key__write = key__write;
      this._deps__write = deps__write;
      this._local = local;
      this._mvc = mvc;
    }
    public override _ICMessage DowncastClone() {
      if (this is _ICMessage dt) { return dt; }
      return new CMessage_CMessage__Write(_opn__write, _key__write, _deps__write, _local, _mvc);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__CMessage__i_Compile.CMessage_CMessage__Write;
      return oth != null && this._opn__write == oth._opn__write && this._key__write == oth._key__write && object.Equals(this._deps__write, oth._deps__write) && object.Equals(this._local, oth._local) && object.Equals(this._mvc, oth._mvc);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._opn__write));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key__write));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._deps__write));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._local));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._mvc));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__CMessage__i_Compile.CMessage.CMessage_Write";
      s += "(";
      s += Dafny.Helpers.ToString(this._opn__write);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key__write);
      s += ", ";
      s += Dafny.Helpers.ToString(this._deps__write);
      s += ", ";
      s += Dafny.Helpers.ToString(this._local);
      s += ", ";
      s += Dafny.Helpers.ToString(this._mvc);
      s += ")";
      return s;
    }
  }
  public class CMessage_CMessage__Write__Reply : CMessage {
    public readonly BigInteger _opn__wreply;
    public readonly BigInteger _key__wreply;
    public readonly Dafny.ISequence<BigInteger> _vc__wreply;
    public CMessage_CMessage__Write__Reply(BigInteger opn__wreply, BigInteger key__wreply, Dafny.ISequence<BigInteger> vc__wreply) {
      this._opn__wreply = opn__wreply;
      this._key__wreply = key__wreply;
      this._vc__wreply = vc__wreply;
    }
    public override _ICMessage DowncastClone() {
      if (this is _ICMessage dt) { return dt; }
      return new CMessage_CMessage__Write__Reply(_opn__wreply, _key__wreply, _vc__wreply);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__CMessage__i_Compile.CMessage_CMessage__Write__Reply;
      return oth != null && this._opn__wreply == oth._opn__wreply && this._key__wreply == oth._key__wreply && object.Equals(this._vc__wreply, oth._vc__wreply);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._opn__wreply));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key__wreply));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._vc__wreply));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__CMessage__i_Compile.CMessage.CMessage_Write_Reply";
      s += "(";
      s += Dafny.Helpers.ToString(this._opn__wreply);
      s += ", ";
      s += Dafny.Helpers.ToString(this._key__wreply);
      s += ", ";
      s += Dafny.Helpers.ToString(this._vc__wreply);
      s += ")";
      return s;
    }
  }
  public class CMessage_CMessage__Propagation : CMessage {
    public readonly BigInteger _key;
    public readonly CausalMesh__CTypes__i_Compile._ICMeta _meta;
    public readonly BigInteger _start;
    public readonly BigInteger _round;
    public CMessage_CMessage__Propagation(BigInteger key, CausalMesh__CTypes__i_Compile._ICMeta meta, BigInteger start, BigInteger round) {
      this._key = key;
      this._meta = meta;
      this._start = start;
      this._round = round;
    }
    public override _ICMessage DowncastClone() {
      if (this is _ICMessage dt) { return dt; }
      return new CMessage_CMessage__Propagation(_key, _meta, _start, _round);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__CMessage__i_Compile.CMessage_CMessage__Propagation;
      return oth != null && this._key == oth._key && object.Equals(this._meta, oth._meta) && this._start == oth._start && this._round == oth._round;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._key));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._meta));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._start));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._round));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__CMessage__i_Compile.CMessage.CMessage_Propagation";
      s += "(";
      s += Dafny.Helpers.ToString(this._key);
      s += ", ";
      s += Dafny.Helpers.ToString(this._meta);
      s += ", ";
      s += Dafny.Helpers.ToString(this._start);
      s += ", ";
      s += Dafny.Helpers.ToString(this._round);
      s += ")";
      return s;
    }
  }

  public interface _ICPacket {
    bool is_CPacket { get; }
    Native____Io__s_Compile._IEndPoint dtor_dst { get; }
    Native____Io__s_Compile._IEndPoint dtor_src { get; }
    CausalMesh__CMessage__i_Compile._ICMessage dtor_msg { get; }
    _ICPacket DowncastClone();
  }
  public class CPacket : _ICPacket {
    public readonly Native____Io__s_Compile._IEndPoint _dst;
    public readonly Native____Io__s_Compile._IEndPoint _src;
    public readonly CausalMesh__CMessage__i_Compile._ICMessage _msg;
    public CPacket(Native____Io__s_Compile._IEndPoint dst, Native____Io__s_Compile._IEndPoint src, CausalMesh__CMessage__i_Compile._ICMessage msg) {
      this._dst = dst;
      this._src = src;
      this._msg = msg;
    }
    public _ICPacket DowncastClone() {
      if (this is _ICPacket dt) { return dt; }
      return new CPacket(_dst, _src, _msg);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__CMessage__i_Compile.CPacket;
      return oth != null && object.Equals(this._dst, oth._dst) && object.Equals(this._src, oth._src) && object.Equals(this._msg, oth._msg);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._dst));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._src));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._msg));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__CMessage__i_Compile.CPacket.CPacket";
      s += "(";
      s += Dafny.Helpers.ToString(this._dst);
      s += ", ";
      s += Dafny.Helpers.ToString(this._src);
      s += ", ";
      s += Dafny.Helpers.ToString(this._msg);
      s += ")";
      return s;
    }
    private static readonly CausalMesh__CMessage__i_Compile._ICPacket theDefault = create(Native____Io__s_Compile.EndPoint.Default(), Native____Io__s_Compile.EndPoint.Default(), CausalMesh__CMessage__i_Compile.CMessage.Default());
    public static CausalMesh__CMessage__i_Compile._ICPacket Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<CausalMesh__CMessage__i_Compile._ICPacket> _TYPE = new Dafny.TypeDescriptor<CausalMesh__CMessage__i_Compile._ICPacket>(CausalMesh__CMessage__i_Compile.CPacket.Default());
    public static Dafny.TypeDescriptor<CausalMesh__CMessage__i_Compile._ICPacket> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICPacket create(Native____Io__s_Compile._IEndPoint dst, Native____Io__s_Compile._IEndPoint src, CausalMesh__CMessage__i_Compile._ICMessage msg) {
      return new CPacket(dst, src, msg);
    }
    public static _ICPacket create_CPacket(Native____Io__s_Compile._IEndPoint dst, Native____Io__s_Compile._IEndPoint src, CausalMesh__CMessage__i_Compile._ICMessage msg) {
      return create(dst, src, msg);
    }
    public bool is_CPacket { get { return true; } }
    public Native____Io__s_Compile._IEndPoint dtor_dst {
      get {
        return this._dst;
      }
    }
    public Native____Io__s_Compile._IEndPoint dtor_src {
      get {
        return this._src;
      }
    }
    public CausalMesh__CMessage__i_Compile._ICMessage dtor_msg {
      get {
        return this._msg;
      }
    }
  }

} // end of namespace CausalMesh__CMessage__i_Compile
namespace Collections____Maps2__i_Compile {

} // end of namespace Collections____Maps2__i_Compile
namespace CausalMesh__PullDeps__i_Compile {

} // end of namespace CausalMesh__PullDeps__i_Compile
namespace CausalMesh__CPullDeps__i_Compile {

  public partial class __default {
    public static Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> CAddMetaToMetaMap(Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> todos, CausalMesh__CTypes__i_Compile._ICMeta m)
    {
      if ((todos).Contains(((m).dtor_key))) {
        return Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update(todos, (m).dtor_key, CausalMesh__CTypes__i_Compile.__default.CVCMerge(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(todos,(m).dtor_key), (m).dtor_vc));
      } else {
        return Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update(todos, (m).dtor_key, (m).dtor_vc);
      }
    }
    public static void CGetMetasOfAllDeps3(Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> icache, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> todos, out Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> icache_k, out Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> res)
    {
      icache_k = Dafny.Map<BigInteger, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>.Empty;
      res = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty;
      if ((new BigInteger((deps).Count)).Sign == 0) {
        icache_k = icache;
        res = todos;
      } else {
        BigInteger _227_k;
        foreach (BigInteger _assign_such_that_4 in (deps).Keys.Elements) {
          _227_k = (BigInteger)_assign_such_that_4;
          if ((deps).Contains((_227_k))) {
            goto after__ASSIGN_SUCH_THAT_4;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 85)");
      after__ASSIGN_SUCH_THAT_4: ;
        Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _228_new__deps;
        _228_new__deps = Collections____Maps__i_Compile.__default.RemoveElt<BigInteger, Dafny.ISequence<BigInteger>>(deps, _227_k);
        if (((todos).Contains((_227_k))) && ((CausalMesh__CTypes__i_Compile.__default.CVCHappendsBefore(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(deps,_227_k), Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(todos,_227_k))) || (CausalMesh__CTypes__i_Compile.__default.CVCEq(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(deps,_227_k), Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(todos,_227_k))))) {
          Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _out70;
          Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _out71;
          CausalMesh__CPullDeps__i_Compile.__default.CGetMetasOfAllDeps3(icache, _228_new__deps, todos, out _out70, out _out71);
          icache_k = _out70;
          res = _out71;
        } else if ((icache).Contains((_227_k))) {
          Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta> _229_metas;
          _229_metas = Dafny.Helpers.Id<Func<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, BigInteger, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>>((_230_icache, _231_k, _232_deps) => ((System.Func<Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>)(() => {
            var _coll8 = new System.Collections.Generic.List<CausalMesh__CTypes__i_Compile._ICMeta>();
            foreach (CausalMesh__CTypes__i_Compile._ICMeta _compr_8 in (Dafny.Map<BigInteger, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>.Select(_230_icache,_231_k)).Elements) {
              CausalMesh__CTypes__i_Compile._ICMeta _233_m = (CausalMesh__CTypes__i_Compile._ICMeta)_compr_8;
              if (((Dafny.Map<BigInteger, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>.Select(_230_icache,_231_k)).Contains((_233_m))) && ((CausalMesh__CTypes__i_Compile.__default.CVCHappendsBefore((_233_m).dtor_vc, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_232_deps,_231_k))) || (CausalMesh__CTypes__i_Compile.__default.CVCEq((_233_m).dtor_vc, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_232_deps,_231_k))))) {
                _coll8.Add(_233_m);
              }
            }
            return Dafny.Set<CausalMesh__CTypes__i_Compile._ICMeta>.FromCollection(_coll8);
          }))())(icache, _227_k, deps);
          if ((new BigInteger((_229_metas).Count)).Sign == 1) {
            res = todos;
            CausalMesh__CTypes__i_Compile._ICMeta _234_initial;
            _234_initial = CausalMesh__CTypes__i_Compile.__default.CEmptyMeta(_227_k);
            CausalMesh__CTypes__i_Compile._ICMeta _235_merged;
            CausalMesh__CTypes__i_Compile._ICMeta _out72;
            _out72 = CausalMesh__CTypes__i_Compile.__default.CFoldMetaSet(_234_initial, _229_metas);
            _235_merged = _out72;
            var _pat_let_tv0 = deps;
            var _pat_let_tv1 = _227_k;
            CausalMesh__CTypes__i_Compile._ICMeta _236_meta;
            _236_meta = Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(_235_merged, _pat_let7_0 => Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(_pat_let7_0, _237_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CTypes__i_Compile._ICMeta>(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_pat_let_tv0,_pat_let_tv1), _pat_let8_0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CTypes__i_Compile._ICMeta>(_pat_let8_0, _238_dt__update_hvc_h0 => CausalMesh__CTypes__i_Compile.CMeta.create((_237_dt__update__tmp_h0).dtor_key, _238_dt__update_hvc_h0, (_237_dt__update__tmp_h0).dtor_deps)))));
            Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _239_new__cache;
            _239_new__cache = Dafny.Map<BigInteger, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>.Update(icache, _227_k, Dafny.Set<CausalMesh__CTypes__i_Compile._ICMeta>.Difference(Dafny.Map<BigInteger, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>.Select(icache,_227_k), _229_metas));
            Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _240_new__icache_k;
            Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _241_res_k;
            Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _out73;
            Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _out74;
            CausalMesh__CPullDeps__i_Compile.__default.CGetMetasOfAllDeps3(_239_new__cache, (_235_merged).dtor_deps, todos, out _out73, out _out74);
            _240_new__icache_k = _out73;
            _241_res_k = _out74;
            Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _242_todos_k;
            _242_todos_k = CausalMesh__CPullDeps__i_Compile.__default.CAddMetaToMetaMap(_241_res_k, _236_meta);
            Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _out75;
            Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _out76;
            CausalMesh__CPullDeps__i_Compile.__default.CGetMetasOfAllDeps3(_240_new__icache_k, _228_new__deps, _242_todos_k, out _out75, out _out76);
            icache_k = _out75;
            res = _out76;
          } else {
            CausalMesh__CTypes__i_Compile._ICMeta _243_initial;
            _243_initial = CausalMesh__CTypes__i_Compile.__default.CEmptyMeta(_227_k);
            var _pat_let_tv2 = deps;
            var _pat_let_tv3 = _227_k;
            CausalMesh__CTypes__i_Compile._ICMeta _244_meta;
            _244_meta = Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(_243_initial, _pat_let9_0 => Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(_pat_let9_0, _245_dt__update__tmp_h1 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CTypes__i_Compile._ICMeta>(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_pat_let_tv2,_pat_let_tv3), _pat_let10_0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CTypes__i_Compile._ICMeta>(_pat_let10_0, _246_dt__update_hvc_h1 => CausalMesh__CTypes__i_Compile.CMeta.create((_245_dt__update__tmp_h1).dtor_key, _246_dt__update_hvc_h1, (_245_dt__update__tmp_h1).dtor_deps)))));
            Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _247_todos_k;
            _247_todos_k = CausalMesh__CPullDeps__i_Compile.__default.CAddMetaToMetaMap(todos, _244_meta);
            Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _out77;
            Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _out78;
            CausalMesh__CPullDeps__i_Compile.__default.CGetMetasOfAllDeps3(icache, _228_new__deps, _247_todos_k, out _out77, out _out78);
            icache_k = _out77;
            res = _out78;
          }
        } else {
          CausalMesh__CTypes__i_Compile._ICMeta _248_initial;
          _248_initial = CausalMesh__CTypes__i_Compile.__default.CEmptyMeta(_227_k);
          var _pat_let_tv4 = deps;
          var _pat_let_tv5 = _227_k;
          CausalMesh__CTypes__i_Compile._ICMeta _249_meta;
          _249_meta = Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(_248_initial, _pat_let11_0 => Dafny.Helpers.Let<CausalMesh__CTypes__i_Compile._ICMeta, CausalMesh__CTypes__i_Compile._ICMeta>(_pat_let11_0, _250_dt__update__tmp_h2 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CTypes__i_Compile._ICMeta>(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_pat_let_tv4,_pat_let_tv5), _pat_let12_0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CTypes__i_Compile._ICMeta>(_pat_let12_0, _251_dt__update_hvc_h2 => CausalMesh__CTypes__i_Compile.CMeta.create((_250_dt__update__tmp_h2).dtor_key, _251_dt__update_hvc_h2, (_250_dt__update__tmp_h2).dtor_deps)))));
          Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _252_todos_k;
          _252_todos_k = CausalMesh__CPullDeps__i_Compile.__default.CAddMetaToMetaMap(todos, _249_meta);
          Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _out79;
          Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _out80;
          CausalMesh__CPullDeps__i_Compile.__default.CGetMetasOfAllDeps3(icache, _228_new__deps, _252_todos_k, out _out79, out _out80);
          icache_k = _out79;
          res = _out80;
        }
      }
    }
  }
} // end of namespace CausalMesh__CPullDeps__i_Compile
namespace CausalMesh__Properties__i_Compile {

} // end of namespace CausalMesh__Properties__i_Compile
namespace CausalMesh__Cache__i_Compile {

  public interface _IServer {
    bool is_Server { get; }
    BigInteger dtor_id { get; }
    Dafny.ISequence<BigInteger> dtor_gvc { get; }
    BigInteger dtor_next { get; }
    Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__Types__i_Compile._IMeta>> dtor_icache { get; }
    Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> dtor_ccache { get; }
    _IServer DowncastClone();
  }
  public class Server : _IServer {
    public readonly BigInteger _id;
    public readonly Dafny.ISequence<BigInteger> _gvc;
    public readonly BigInteger _next;
    public readonly Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__Types__i_Compile._IMeta>> _icache;
    public readonly Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> _ccache;
    public Server(BigInteger id, Dafny.ISequence<BigInteger> gvc, BigInteger next, Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__Types__i_Compile._IMeta>> icache, Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> ccache) {
      this._id = id;
      this._gvc = gvc;
      this._next = next;
      this._icache = icache;
      this._ccache = ccache;
    }
    public _IServer DowncastClone() {
      if (this is _IServer dt) { return dt; }
      return new Server(_id, _gvc, _next, _icache, _ccache);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__Cache__i_Compile.Server;
      return oth != null && this._id == oth._id && object.Equals(this._gvc, oth._gvc) && this._next == oth._next && object.Equals(this._icache, oth._icache) && object.Equals(this._ccache, oth._ccache);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._gvc));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._next));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._icache));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ccache));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__Cache__i_Compile.Server.Server";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._gvc);
      s += ", ";
      s += Dafny.Helpers.ToString(this._next);
      s += ", ";
      s += Dafny.Helpers.ToString(this._icache);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ccache);
      s += ")";
      return s;
    }
    private static readonly CausalMesh__Cache__i_Compile._IServer theDefault = create(BigInteger.Zero, Dafny.Sequence<BigInteger>.Empty, BigInteger.Zero, Dafny.Map<BigInteger, Dafny.ISet<CausalMesh__Types__i_Compile._IMeta>>.Empty, Dafny.Map<BigInteger, CausalMesh__Types__i_Compile._IMeta>.Empty);
    public static CausalMesh__Cache__i_Compile._IServer Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<CausalMesh__Cache__i_Compile._IServer> _TYPE = new Dafny.TypeDescriptor<CausalMesh__Cache__i_Compile._IServer>(CausalMesh__Cache__i_Compile.Server.Default());
    public static Dafny.TypeDescriptor<CausalMesh__Cache__i_Compile._IServer> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IServer create(BigInteger id, Dafny.ISequence<BigInteger> gvc, BigInteger next, Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__Types__i_Compile._IMeta>> icache, Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> ccache) {
      return new Server(id, gvc, next, icache, ccache);
    }
    public static _IServer create_Server(BigInteger id, Dafny.ISequence<BigInteger> gvc, BigInteger next, Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__Types__i_Compile._IMeta>> icache, Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> ccache) {
      return create(id, gvc, next, icache, ccache);
    }
    public bool is_Server { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_gvc {
      get {
        return this._gvc;
      }
    }
    public BigInteger dtor_next {
      get {
        return this._next;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__Types__i_Compile._IMeta>> dtor_icache {
      get {
        return this._icache;
      }
    }
    public Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> dtor_ccache {
      get {
        return this._ccache;
      }
    }
  }

  public interface _IClient {
    bool is_Client { get; }
    BigInteger dtor_id { get; }
    BigInteger dtor_opn { get; }
    Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> dtor_local { get; }
    Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps { get; }
    _IClient DowncastClone();
  }
  public class Client : _IClient {
    public readonly BigInteger _id;
    public readonly BigInteger _opn;
    public readonly Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> _local;
    public readonly Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _deps;
    public Client(BigInteger id, BigInteger opn, Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> local, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps) {
      this._id = id;
      this._opn = opn;
      this._local = local;
      this._deps = deps;
    }
    public _IClient DowncastClone() {
      if (this is _IClient dt) { return dt; }
      return new Client(_id, _opn, _local, _deps);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__Cache__i_Compile.Client;
      return oth != null && this._id == oth._id && this._opn == oth._opn && object.Equals(this._local, oth._local) && object.Equals(this._deps, oth._deps);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._opn));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._local));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._deps));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__Cache__i_Compile.Client.Client";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._opn);
      s += ", ";
      s += Dafny.Helpers.ToString(this._local);
      s += ", ";
      s += Dafny.Helpers.ToString(this._deps);
      s += ")";
      return s;
    }
    private static readonly CausalMesh__Cache__i_Compile._IClient theDefault = create(BigInteger.Zero, BigInteger.Zero, Dafny.Map<BigInteger, CausalMesh__Types__i_Compile._IMeta>.Empty, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty);
    public static CausalMesh__Cache__i_Compile._IClient Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<CausalMesh__Cache__i_Compile._IClient> _TYPE = new Dafny.TypeDescriptor<CausalMesh__Cache__i_Compile._IClient>(CausalMesh__Cache__i_Compile.Client.Default());
    public static Dafny.TypeDescriptor<CausalMesh__Cache__i_Compile._IClient> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IClient create(BigInteger id, BigInteger opn, Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> local, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps) {
      return new Client(id, opn, local, deps);
    }
    public static _IClient create_Client(BigInteger id, BigInteger opn, Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> local, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps) {
      return create(id, opn, local, deps);
    }
    public bool is_Client { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public BigInteger dtor_opn {
      get {
        return this._opn;
      }
    }
    public Dafny.IMap<BigInteger,CausalMesh__Types__i_Compile._IMeta> dtor_local {
      get {
        return this._local;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dtor_deps {
      get {
        return this._deps;
      }
    }
  }

} // end of namespace CausalMesh__Cache__i_Compile
namespace CausalMesh__CCache__i_Compile {

  public interface _ICServer {
    bool is_CServer { get; }
    BigInteger dtor_id { get; }
    Native____Io__s_Compile._IEndPoint dtor_endpoint { get; }
    Dafny.ISequence<BigInteger> dtor_gvc { get; }
    BigInteger dtor_next { get; }
    Native____Io__s_Compile._IEndPoint dtor_next__endpoint { get; }
    Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> dtor_icache { get; }
    Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> dtor_ccache { get; }
    _ICServer DowncastClone();
  }
  public class CServer : _ICServer {
    public readonly BigInteger _id;
    public readonly Native____Io__s_Compile._IEndPoint _endpoint;
    public readonly Dafny.ISequence<BigInteger> _gvc;
    public readonly BigInteger _next;
    public readonly Native____Io__s_Compile._IEndPoint _next__endpoint;
    public readonly Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _icache;
    public readonly Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _ccache;
    public CServer(BigInteger id, Native____Io__s_Compile._IEndPoint endpoint, Dafny.ISequence<BigInteger> gvc, BigInteger next, Native____Io__s_Compile._IEndPoint next__endpoint, Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> icache, Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> ccache) {
      this._id = id;
      this._endpoint = endpoint;
      this._gvc = gvc;
      this._next = next;
      this._next__endpoint = next__endpoint;
      this._icache = icache;
      this._ccache = ccache;
    }
    public _ICServer DowncastClone() {
      if (this is _ICServer dt) { return dt; }
      return new CServer(_id, _endpoint, _gvc, _next, _next__endpoint, _icache, _ccache);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__CCache__i_Compile.CServer;
      return oth != null && this._id == oth._id && object.Equals(this._endpoint, oth._endpoint) && object.Equals(this._gvc, oth._gvc) && this._next == oth._next && object.Equals(this._next__endpoint, oth._next__endpoint) && object.Equals(this._icache, oth._icache) && object.Equals(this._ccache, oth._ccache);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._id));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._endpoint));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._gvc));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._next));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._next__endpoint));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._icache));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._ccache));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__CCache__i_Compile.CServer.CServer";
      s += "(";
      s += Dafny.Helpers.ToString(this._id);
      s += ", ";
      s += Dafny.Helpers.ToString(this._endpoint);
      s += ", ";
      s += Dafny.Helpers.ToString(this._gvc);
      s += ", ";
      s += Dafny.Helpers.ToString(this._next);
      s += ", ";
      s += Dafny.Helpers.ToString(this._next__endpoint);
      s += ", ";
      s += Dafny.Helpers.ToString(this._icache);
      s += ", ";
      s += Dafny.Helpers.ToString(this._ccache);
      s += ")";
      return s;
    }
    private static readonly CausalMesh__CCache__i_Compile._ICServer theDefault = create(BigInteger.Zero, Native____Io__s_Compile.EndPoint.Default(), Dafny.Sequence<BigInteger>.Empty, BigInteger.Zero, Native____Io__s_Compile.EndPoint.Default(), Dafny.Map<BigInteger, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>.Empty, Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Empty);
    public static CausalMesh__CCache__i_Compile._ICServer Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<CausalMesh__CCache__i_Compile._ICServer> _TYPE = new Dafny.TypeDescriptor<CausalMesh__CCache__i_Compile._ICServer>(CausalMesh__CCache__i_Compile.CServer.Default());
    public static Dafny.TypeDescriptor<CausalMesh__CCache__i_Compile._ICServer> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICServer create(BigInteger id, Native____Io__s_Compile._IEndPoint endpoint, Dafny.ISequence<BigInteger> gvc, BigInteger next, Native____Io__s_Compile._IEndPoint next__endpoint, Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> icache, Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> ccache) {
      return new CServer(id, endpoint, gvc, next, next__endpoint, icache, ccache);
    }
    public static _ICServer create_CServer(BigInteger id, Native____Io__s_Compile._IEndPoint endpoint, Dafny.ISequence<BigInteger> gvc, BigInteger next, Native____Io__s_Compile._IEndPoint next__endpoint, Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> icache, Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> ccache) {
      return create(id, endpoint, gvc, next, next__endpoint, icache, ccache);
    }
    public bool is_CServer { get { return true; } }
    public BigInteger dtor_id {
      get {
        return this._id;
      }
    }
    public Native____Io__s_Compile._IEndPoint dtor_endpoint {
      get {
        return this._endpoint;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_gvc {
      get {
        return this._gvc;
      }
    }
    public BigInteger dtor_next {
      get {
        return this._next;
      }
    }
    public Native____Io__s_Compile._IEndPoint dtor_next__endpoint {
      get {
        return this._next__endpoint;
      }
    }
    public Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> dtor_icache {
      get {
        return this._icache;
      }
    }
    public Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> dtor_ccache {
      get {
        return this._ccache;
      }
    }
  }

  public partial class __default {
    public static void CReceiveRead(CausalMesh__CCache__i_Compile._ICServer s, CausalMesh__CMessage__i_Compile._ICPacket p, out CausalMesh__CCache__i_Compile._ICServer s_k, out Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> sp)
    {
      s_k = CausalMesh__CCache__i_Compile.CServer.Default();
      sp = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.Empty;
      Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _253_new__icache;
      Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _254_new__ccache;
      Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _out81;
      Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _out82;
      CausalMesh__CCache__i_Compile.__default.CPullDeps3((s).dtor_icache, (s).dtor_ccache, ((p).dtor_msg).dtor_deps__read, out _out81, out _out82);
      _253_new__icache = _out81;
      _254_new__ccache = _out82;
      if (!(_254_new__ccache).Contains((((p).dtor_msg).dtor_key__read))) {
        _254_new__ccache = Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Update(_254_new__ccache, ((p).dtor_msg).dtor_key__read, CausalMesh__CTypes__i_Compile.__default.CEmptyMeta(((p).dtor_msg).dtor_key__read));
      } else {
        _254_new__ccache = _254_new__ccache;
      }
      var _pat_let_tv6 = _254_new__ccache;
      var _pat_let_tv7 = _253_new__icache;
      CausalMesh__CCache__i_Compile._ICServer _255_t1;
      _255_t1 = Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(s, _pat_let13_0 => Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(_pat_let13_0, _256_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let_tv6, _pat_let14_0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let14_0, _257_dt__update_hccache_h0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let_tv7, _pat_let15_0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let15_0, _258_dt__update_hicache_h0 => CausalMesh__CCache__i_Compile.CServer.create((_256_dt__update__tmp_h0).dtor_id, (_256_dt__update__tmp_h0).dtor_endpoint, (_256_dt__update__tmp_h0).dtor_gvc, (_256_dt__update__tmp_h0).dtor_next, (_256_dt__update__tmp_h0).dtor_next__endpoint, _258_dt__update_hicache_h0, _257_dt__update_hccache_h0)))))));
      CausalMesh__CMessage__i_Compile._ICPacket _259_rep;
      _259_rep = CausalMesh__CMessage__i_Compile.CPacket.create((p).dtor_src, (s).dtor_endpoint, CausalMesh__CMessage__i_Compile.CMessage.create_CMessage__Read__Reply(((p).dtor_msg).dtor_opn__read, ((p).dtor_msg).dtor_key__read, (Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Select(_254_new__ccache,((p).dtor_msg).dtor_key__read)).dtor_vc, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements()));
      s_k = _255_t1;
      sp = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.FromElements(_259_rep);
    }
    public static Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> FilterSatisfiedDependency2(Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> dep, Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> ccache)
    {
      Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> res = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Empty;
      res = Dafny.Helpers.Id<Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>, Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>>((_260_dep, _261_ccache) => ((System.Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>>)(() => {
        var _coll9 = new System.Collections.Generic.List<Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>>();
        foreach (BigInteger _compr_9 in (_260_dep).Keys.Elements) {
          BigInteger _262_k = (BigInteger)_compr_9;
          if (((_260_dep).Contains((_262_k))) && ((!(_261_ccache).Contains((_262_k))) || ((!(CausalMesh__CTypes__i_Compile.__default.CVCEq(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_260_dep,_262_k), (Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Select(_261_ccache,_262_k)).dtor_vc))) && (!(CausalMesh__CTypes__i_Compile.__default.CVCHappendsBefore(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_260_dep,_262_k), (Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Select(_261_ccache,_262_k)).dtor_vc)))))) {
            _coll9.Add(new Dafny.Pair<BigInteger,Dafny.ISequence<BigInteger>>(_262_k, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(_260_dep,_262_k)));
          }
        }
        return Dafny.Map<BigInteger,Dafny.ISequence<BigInteger>>.FromCollection(_coll9);
      }))())(dep, ccache);
      return res;
    }
    public static void CReceiveRead__I1(CausalMesh__CCache__i_Compile._ICServer s, CausalMesh__CMessage__i_Compile._ICPacket p, out CausalMesh__CCache__i_Compile._ICServer s_k, out Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> sp)
    {
      s_k = CausalMesh__CCache__i_Compile.CServer.Default();
      sp = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.Empty;
      Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _263_new__dep;
      Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _out83;
      _out83 = CausalMesh__CCache__i_Compile.__default.FilterSatisfiedDependency2(((p).dtor_msg).dtor_deps__read, (s).dtor_ccache);
      _263_new__dep = _out83;
      Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _264_new__icache;
      Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _265_new__ccache;
      Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _out84;
      Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _out85;
      CausalMesh__CCache__i_Compile.__default.CPullDeps3((s).dtor_icache, (s).dtor_ccache, _263_new__dep, out _out84, out _out85);
      _264_new__icache = _out84;
      _265_new__ccache = _out85;
      if (!(_265_new__ccache).Contains((((p).dtor_msg).dtor_key__read))) {
        _265_new__ccache = Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Update(_265_new__ccache, ((p).dtor_msg).dtor_key__read, CausalMesh__CTypes__i_Compile.__default.CEmptyMeta(((p).dtor_msg).dtor_key__read));
      }
      var _pat_let_tv8 = _265_new__ccache;
      var _pat_let_tv9 = _264_new__icache;
      CausalMesh__CCache__i_Compile._ICServer _266_t1;
      _266_t1 = Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(s, _pat_let16_0 => Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(_pat_let16_0, _267_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let_tv8, _pat_let17_0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let17_0, _268_dt__update_hccache_h0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let_tv9, _pat_let18_0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let18_0, _269_dt__update_hicache_h0 => CausalMesh__CCache__i_Compile.CServer.create((_267_dt__update__tmp_h0).dtor_id, (_267_dt__update__tmp_h0).dtor_endpoint, (_267_dt__update__tmp_h0).dtor_gvc, (_267_dt__update__tmp_h0).dtor_next, (_267_dt__update__tmp_h0).dtor_next__endpoint, _269_dt__update_hicache_h0, _268_dt__update_hccache_h0)))))));
      CausalMesh__CMessage__i_Compile._ICPacket _270_rep;
      _270_rep = CausalMesh__CMessage__i_Compile.CPacket.create((p).dtor_src, (s).dtor_endpoint, CausalMesh__CMessage__i_Compile.CMessage.create_CMessage__Read__Reply(((p).dtor_msg).dtor_opn__read, ((p).dtor_msg).dtor_key__read, (Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Select(_265_new__ccache,((p).dtor_msg).dtor_key__read)).dtor_vc, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements()));
      s_k = _266_t1;
      sp = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.FromElements(_270_rep);
    }
    public static void CReceivePropagate(CausalMesh__CCache__i_Compile._ICServer s, CausalMesh__CMessage__i_Compile._ICPacket p, out CausalMesh__CCache__i_Compile._ICServer s_k, out Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> sp)
    {
      s_k = CausalMesh__CCache__i_Compile.CServer.Default();
      sp = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.Empty;
      if (((s).dtor_next) == (((p).dtor_msg).dtor_start)) {
        if ((((p).dtor_msg).dtor_round) == (new BigInteger(2))) {
          Dafny.ISequence<BigInteger> _271_vcs;
          _271_vcs = (((p).dtor_msg).dtor_meta).dtor_vc;
          Dafny.ISequence<BigInteger> _272_new__gvc;
          _272_new__gvc = CausalMesh__CTypes__i_Compile.__default.CVCMerge((s).dtor_gvc, _271_vcs);
          Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _273_new__deps;
          _273_new__deps = (((p).dtor_msg).dtor_meta).dtor_deps;
          Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _274_new__icache;
          Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _275_new__ccache;
          Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _out86;
          Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _out87;
          CausalMesh__CCache__i_Compile.__default.CPullDeps3((s).dtor_icache, (s).dtor_ccache, _273_new__deps, out _out86, out _out87);
          _274_new__icache = _out86;
          _275_new__ccache = _out87;
          Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _276_new__ccache_k;
          _276_new__ccache_k = CausalMesh__CCache__i_Compile.__default.CInsertIntoCCache(_275_new__ccache, ((p).dtor_msg).dtor_meta);
          Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _277_new__icache_k;
          _277_new__icache_k = CausalMesh__CCache__i_Compile.__default.CAddMetaToICache(_274_new__icache, ((p).dtor_msg).dtor_meta);
          var _pat_let_tv10 = _276_new__ccache_k;
          var _pat_let_tv11 = _277_new__icache_k;
          var _pat_let_tv12 = _272_new__gvc;
          s_k = Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(s, _pat_let19_0 => Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(_pat_let19_0, _278_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let_tv10, _pat_let20_0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let20_0, _279_dt__update_hccache_h0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let_tv11, _pat_let21_0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let21_0, _280_dt__update_hicache_h0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let_tv12, _pat_let22_0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let22_0, _281_dt__update_hgvc_h0 => CausalMesh__CCache__i_Compile.CServer.create((_278_dt__update__tmp_h0).dtor_id, (_278_dt__update__tmp_h0).dtor_endpoint, _281_dt__update_hgvc_h0, (_278_dt__update__tmp_h0).dtor_next, (_278_dt__update__tmp_h0).dtor_next__endpoint, _280_dt__update_hicache_h0, _279_dt__update_hccache_h0)))))))));
          sp = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.FromElements();
        } else {
          Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _282_new__icache;
          _282_new__icache = CausalMesh__CCache__i_Compile.__default.CAddMetaToICache((s).dtor_icache, ((p).dtor_msg).dtor_meta);
          var _pat_let_tv13 = _282_new__icache;
          s_k = Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(s, _pat_let23_0 => Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(_pat_let23_0, _283_dt__update__tmp_h2 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let_tv13, _pat_let24_0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let24_0, _284_dt__update_hicache_h2 => CausalMesh__CCache__i_Compile.CServer.create((_283_dt__update__tmp_h2).dtor_id, (_283_dt__update__tmp_h2).dtor_endpoint, (_283_dt__update__tmp_h2).dtor_gvc, (_283_dt__update__tmp_h2).dtor_next, (_283_dt__update__tmp_h2).dtor_next__endpoint, _284_dt__update_hicache_h2, (_283_dt__update__tmp_h2).dtor_ccache)))));
          CausalMesh__CMessage__i_Compile._ICPacket _285_propagate;
          _285_propagate = CausalMesh__CMessage__i_Compile.CPacket.create((s).dtor_next__endpoint, (s).dtor_endpoint, Dafny.Helpers.Let<CausalMesh__CMessage__i_Compile._ICMessage, CausalMesh__CMessage__i_Compile._ICMessage>((p).dtor_msg, _pat_let25_0 => Dafny.Helpers.Let<CausalMesh__CMessage__i_Compile._ICMessage, CausalMesh__CMessage__i_Compile._ICMessage>(_pat_let25_0, _286_dt__update__tmp_h4 => Dafny.Helpers.Let<BigInteger, CausalMesh__CMessage__i_Compile._ICMessage>(new BigInteger(2), _pat_let26_0 => Dafny.Helpers.Let<BigInteger, CausalMesh__CMessage__i_Compile._ICMessage>(_pat_let26_0, _287_dt__update_hround_h0 => CausalMesh__CMessage__i_Compile.CMessage.create_CMessage__Propagation((_286_dt__update__tmp_h4).dtor_key, (_286_dt__update__tmp_h4).dtor_meta, (_286_dt__update__tmp_h4).dtor_start, _287_dt__update_hround_h0))))));
          sp = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.FromElements(_285_propagate);
        }
      } else {
        Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _288_new__icache;
        _288_new__icache = CausalMesh__CCache__i_Compile.__default.CAddMetaToICache((s).dtor_icache, ((p).dtor_msg).dtor_meta);
        var _pat_let_tv14 = _288_new__icache;
        s_k = Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(s, _pat_let27_0 => Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(_pat_let27_0, _289_dt__update__tmp_h8 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let_tv14, _pat_let28_0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let28_0, _290_dt__update_hicache_h4 => CausalMesh__CCache__i_Compile.CServer.create((_289_dt__update__tmp_h8).dtor_id, (_289_dt__update__tmp_h8).dtor_endpoint, (_289_dt__update__tmp_h8).dtor_gvc, (_289_dt__update__tmp_h8).dtor_next, (_289_dt__update__tmp_h8).dtor_next__endpoint, _290_dt__update_hicache_h4, (_289_dt__update__tmp_h8).dtor_ccache)))));
        CausalMesh__CMessage__i_Compile._ICPacket _291_propagate;
        _291_propagate = CausalMesh__CMessage__i_Compile.CPacket.create((s).dtor_next__endpoint, (s).dtor_endpoint, (p).dtor_msg);
        sp = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.FromElements(_291_propagate);
      }
    }
    public static void CReceiveWrite(CausalMesh__CCache__i_Compile._ICServer s, CausalMesh__CMessage__i_Compile._ICPacket p, out CausalMesh__CCache__i_Compile._ICServer s_k, out Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> sp)
    {
      s_k = CausalMesh__CCache__i_Compile.CServer.Default();
      sp = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.Empty;
      Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta> _292_local__metas;
      _292_local__metas = Dafny.Helpers.Id<Func<CausalMesh__CMessage__i_Compile._ICPacket, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>>((_293_p) => ((System.Func<Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>)(() => {
        var _coll10 = new System.Collections.Generic.List<CausalMesh__CTypes__i_Compile._ICMeta>();
        foreach (CausalMesh__CTypes__i_Compile._ICMeta _compr_10 in ((((_293_p).dtor_msg).dtor_local).Values).Elements) {
          CausalMesh__CTypes__i_Compile._ICMeta _294_m = (CausalMesh__CTypes__i_Compile._ICMeta)_compr_10;
          if (((((_293_p).dtor_msg).dtor_local).Values).Contains((_294_m))) {
            _coll10.Add(_294_m);
          }
        }
        return Dafny.Set<CausalMesh__CTypes__i_Compile._ICMeta>.FromCollection(_coll10);
      }))())(p);
      Dafny.ISet<Dafny.ISequence<BigInteger>> _295_vcs__local;
      _295_vcs__local = Dafny.Helpers.Id<Func<Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>, Dafny.ISet<Dafny.ISequence<BigInteger>>>>((_296_local__metas) => ((System.Func<Dafny.ISet<Dafny.ISequence<BigInteger>>>)(() => {
        var _coll11 = new System.Collections.Generic.List<Dafny.ISequence<BigInteger>>();
        foreach (CausalMesh__CTypes__i_Compile._ICMeta _compr_11 in (_296_local__metas).Elements) {
          CausalMesh__CTypes__i_Compile._ICMeta _297_m = (CausalMesh__CTypes__i_Compile._ICMeta)_compr_11;
          if ((_296_local__metas).Contains((_297_m))) {
            _coll11.Add((_297_m).dtor_vc);
          }
        }
        return Dafny.Set<Dafny.ISequence<BigInteger>>.FromCollection(_coll11);
      }))())(_292_local__metas);
      Dafny.ISet<Dafny.ISequence<BigInteger>> _298_vcs__deps;
      _298_vcs__deps = Dafny.Helpers.Id<Func<CausalMesh__CMessage__i_Compile._ICPacket, Dafny.ISet<Dafny.ISequence<BigInteger>>>>((_299_p) => ((System.Func<Dafny.ISet<Dafny.ISequence<BigInteger>>>)(() => {
        var _coll12 = new System.Collections.Generic.List<Dafny.ISequence<BigInteger>>();
        foreach (BigInteger _compr_12 in (((_299_p).dtor_msg).dtor_deps__write).Keys.Elements) {
          BigInteger _300_k = (BigInteger)_compr_12;
          if ((((_299_p).dtor_msg).dtor_deps__write).Contains((_300_k))) {
            _coll12.Add(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(((_299_p).dtor_msg).dtor_deps__write,_300_k));
          }
        }
        return Dafny.Set<Dafny.ISequence<BigInteger>>.FromCollection(_coll12);
      }))())(p);
      Dafny.ISequence<BigInteger> _301_merged__vc;
      Dafny.ISequence<BigInteger> _out88;
      _out88 = CausalMesh__CTypes__i_Compile.__default.CFoldVC((s).dtor_gvc, _295_vcs__local);
      _301_merged__vc = _out88;
      Dafny.ISequence<BigInteger> _302_merged__vc2;
      Dafny.ISequence<BigInteger> _out89;
      _out89 = CausalMesh__CTypes__i_Compile.__default.CFoldVC(_301_merged__vc, _298_vcs__deps);
      _302_merged__vc2 = _out89;
      Dafny.ISequence<BigInteger> _303_new__vc;
      _303_new__vc = CausalMesh__CCache__i_Compile.__default.CAdvanceVC(_302_merged__vc2, (s).dtor_id);
      Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _304_merged__deps;
      Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _out90;
      _out90 = CausalMesh__CTypes__i_Compile.__default.CFoldDependencyFromMetaSet(((p).dtor_msg).dtor_deps__write, _292_local__metas);
      _304_merged__deps = _out90;
      CausalMesh__CTypes__i_Compile._ICMeta _305_meta;
      _305_meta = CausalMesh__CTypes__i_Compile.CMeta.create(((p).dtor_msg).dtor_key__write, _303_new__vc, _304_merged__deps);
      Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _306_new__icache;
      _306_new__icache = CausalMesh__CCache__i_Compile.__default.CAddMetaToICache((s).dtor_icache, _305_meta);
      CausalMesh__CMessage__i_Compile._ICPacket _307_wreply;
      _307_wreply = CausalMesh__CMessage__i_Compile.CPacket.create((p).dtor_src, (s).dtor_endpoint, CausalMesh__CMessage__i_Compile.CMessage.create_CMessage__Write__Reply(((p).dtor_msg).dtor_opn__write, ((p).dtor_msg).dtor_key__write, _303_new__vc));
      CausalMesh__CMessage__i_Compile._ICPacket _308_propagate;
      _308_propagate = CausalMesh__CMessage__i_Compile.CPacket.create((s).dtor_next__endpoint, (s).dtor_endpoint, CausalMesh__CMessage__i_Compile.CMessage.create_CMessage__Propagation(((p).dtor_msg).dtor_key__write, _305_meta, (s).dtor_id, BigInteger.One));
      var _pat_let_tv15 = _306_new__icache;
      var _pat_let_tv16 = _303_new__vc;
      s_k = Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(s, _pat_let29_0 => Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(_pat_let29_0, _309_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let_tv15, _pat_let30_0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let30_0, _310_dt__update_hicache_h0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let_tv16, _pat_let31_0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let31_0, _311_dt__update_hgvc_h0 => CausalMesh__CCache__i_Compile.CServer.create((_309_dt__update__tmp_h0).dtor_id, (_309_dt__update__tmp_h0).dtor_endpoint, _311_dt__update_hgvc_h0, (_309_dt__update__tmp_h0).dtor_next, (_309_dt__update__tmp_h0).dtor_next__endpoint, _310_dt__update_hicache_h0, (_309_dt__update__tmp_h0).dtor_ccache)))))));
      sp = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.Concat(Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.FromElements(_307_wreply), Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.FromElements(_308_propagate));
    }
    public static void CReceiveWrite__I1(CausalMesh__CCache__i_Compile._ICServer s, CausalMesh__CMessage__i_Compile._ICPacket p, out CausalMesh__CCache__i_Compile._ICServer s_k, out Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> sp)
    {
      s_k = CausalMesh__CCache__i_Compile.CServer.Default();
      sp = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.Empty;
      Dafny.ISet<Dafny.ISequence<BigInteger>> _312_vcs__deps;
      _312_vcs__deps = Dafny.Helpers.Id<Func<CausalMesh__CMessage__i_Compile._ICPacket, Dafny.ISet<Dafny.ISequence<BigInteger>>>>((_313_p) => ((System.Func<Dafny.ISet<Dafny.ISequence<BigInteger>>>)(() => {
        var _coll13 = new System.Collections.Generic.List<Dafny.ISequence<BigInteger>>();
        foreach (BigInteger _compr_13 in (((_313_p).dtor_msg).dtor_deps__write).Keys.Elements) {
          BigInteger _314_k = (BigInteger)_compr_13;
          if ((((_313_p).dtor_msg).dtor_deps__write).Contains((_314_k))) {
            _coll13.Add(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(((_313_p).dtor_msg).dtor_deps__write,_314_k));
          }
        }
        return Dafny.Set<Dafny.ISequence<BigInteger>>.FromCollection(_coll13);
      }))())(p);
      Dafny.ISequence<BigInteger> _315_merged__vc;
      _315_merged__vc = CausalMesh__CTypes__i_Compile.__default.CVCMerge((s).dtor_gvc, ((p).dtor_msg).dtor_mvc);
      Dafny.ISequence<BigInteger> _316_new__vc;
      _316_new__vc = CausalMesh__CCache__i_Compile.__default.CAdvanceVC(_315_merged__vc, (s).dtor_id);
      CausalMesh__CTypes__i_Compile._ICMeta _317_meta;
      _317_meta = CausalMesh__CTypes__i_Compile.CMeta.create(((p).dtor_msg).dtor_key__write, _316_new__vc, ((p).dtor_msg).dtor_deps__write);
      Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _318_new__icache;
      _318_new__icache = CausalMesh__CCache__i_Compile.__default.CAddMetaToICache((s).dtor_icache, _317_meta);
      CausalMesh__CMessage__i_Compile._ICPacket _319_wreply;
      _319_wreply = CausalMesh__CMessage__i_Compile.CPacket.create((p).dtor_src, (s).dtor_endpoint, CausalMesh__CMessage__i_Compile.CMessage.create_CMessage__Write__Reply(((p).dtor_msg).dtor_opn__write, ((p).dtor_msg).dtor_key__write, _316_new__vc));
      CausalMesh__CMessage__i_Compile._ICPacket _320_propagate;
      _320_propagate = CausalMesh__CMessage__i_Compile.CPacket.create((s).dtor_next__endpoint, (s).dtor_endpoint, CausalMesh__CMessage__i_Compile.CMessage.create_CMessage__Propagation(((p).dtor_msg).dtor_key__write, _317_meta, (s).dtor_id, BigInteger.One));
      var _pat_let_tv17 = _318_new__icache;
      var _pat_let_tv18 = _316_new__vc;
      s_k = Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(s, _pat_let32_0 => Dafny.Helpers.Let<CausalMesh__CCache__i_Compile._ICServer, CausalMesh__CCache__i_Compile._ICServer>(_pat_let32_0, _321_dt__update__tmp_h0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let_tv17, _pat_let33_0 => Dafny.Helpers.Let<Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let33_0, _322_dt__update_hicache_h0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let_tv18, _pat_let34_0 => Dafny.Helpers.Let<Dafny.ISequence<BigInteger>, CausalMesh__CCache__i_Compile._ICServer>(_pat_let34_0, _323_dt__update_hgvc_h0 => CausalMesh__CCache__i_Compile.CServer.create((_321_dt__update__tmp_h0).dtor_id, (_321_dt__update__tmp_h0).dtor_endpoint, _323_dt__update_hgvc_h0, (_321_dt__update__tmp_h0).dtor_next, (_321_dt__update__tmp_h0).dtor_next__endpoint, _322_dt__update_hicache_h0, (_321_dt__update__tmp_h0).dtor_ccache)))))));
      sp = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.Concat(Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.FromElements(_319_wreply), Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.FromElements(_320_propagate));
    }
    public static BigInteger CCircle(BigInteger id, BigInteger nodes)
    {
      if ((nodes) == (BigInteger.One)) {
        return id;
      } else if ((id) == ((nodes) - (BigInteger.One))) {
        return BigInteger.Zero;
      } else {
        return (id) + (BigInteger.One);
      }
    }
    public static Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> CInsertIntoCCache(Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> c, CausalMesh__CTypes__i_Compile._ICMeta m)
    {
      if ((c).Contains(((m).dtor_key))) {
        return Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Update(c, (m).dtor_key, CausalMesh__CTypes__i_Compile.__default.CMetaMerge(Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Select(c,(m).dtor_key), m));
      } else {
        return Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Update(c, (m).dtor_key, m);
      }
    }
    public static Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> CAddMetasToICache(Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> c, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta> metas)
    {
    TAIL_CALL_START: ;
      Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> res = Dafny.Map<BigInteger, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>.Empty;
      if ((new BigInteger((metas).Count)).Sign == 0) {
        res = c;
      } else {
        CausalMesh__CTypes__i_Compile._ICMeta _324_m;
        foreach (CausalMesh__CTypes__i_Compile._ICMeta _assign_such_that_5 in (metas).Elements) {
          _324_m = (CausalMesh__CTypes__i_Compile._ICMeta)_assign_such_that_5;
          if ((metas).Contains((_324_m))) {
            goto after__ASSIGN_SUCH_THAT_5;
          }
        }
        throw new System.Exception("assign-such-that search produced no value (line 752)");
      after__ASSIGN_SUCH_THAT_5: ;
        Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta> _325_new__metas;
        _325_new__metas = Dafny.Set<CausalMesh__CTypes__i_Compile._ICMeta>.Difference(metas, Dafny.Set<CausalMesh__CTypes__i_Compile._ICMeta>.FromElements(_324_m));
        Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _in8 = CausalMesh__CCache__i_Compile.__default.CAddMetaToICache(c, _324_m);
        Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta> _in9 = _325_new__metas;
        c = _in8;
        metas = _in9;
        goto TAIL_CALL_START;
      }
      return res;
    }
    public static Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> CAddMetaToICache(Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> c, CausalMesh__CTypes__i_Compile._ICMeta m)
    {
      if ((c).Contains(((m).dtor_key))) {
        Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _326_r = Dafny.Map<BigInteger, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>.Update(c, (m).dtor_key, Dafny.Set<CausalMesh__CTypes__i_Compile._ICMeta>.Union(Dafny.Map<BigInteger, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>.Select(c,(m).dtor_key), Dafny.Set<CausalMesh__CTypes__i_Compile._ICMeta>.FromElements(m)));
        return _326_r;
      } else {
        Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _327_r = Dafny.Map<BigInteger, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>.Update(c, (m).dtor_key, Dafny.Set<CausalMesh__CTypes__i_Compile._ICMeta>.FromElements(m));
        return _327_r;
      }
    }
    public static void CPullDeps3(Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> icache, Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> ccache, Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> deps, out Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> icache_k, out Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> ccache_k)
    {
      icache_k = Dafny.Map<BigInteger, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>.Empty;
      ccache_k = Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Empty;
      Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _328_new__icache;
      Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _329_todos;
      Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _out91;
      Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _out92;
      CausalMesh__CPullDeps__i_Compile.__default.CGetMetasOfAllDeps3(icache, deps, Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements(), out _out91, out _out92);
      _328_new__icache = _out91;
      _329_todos = _out92;
      Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _330_new__cache;
      _330_new__cache = CausalMesh__CTypes__i_Compile.__default.CMergeVCIntoCCache(ccache, _329_todos);
      icache_k = _328_new__icache;
      ccache_k = _330_new__cache;
    }
    public static Dafny.ISequence<BigInteger> CAdvanceVC(Dafny.ISequence<BigInteger> vc, BigInteger i)
    {
      return Dafny.Sequence<BigInteger>.Update(vc, i, ((vc).Select(i)) + (BigInteger.One));
    }
    public static Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> CInitICache() {
      return Dafny.Map<BigInteger, Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>>.FromElements();
    }
    public static Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> CInitCCache() {
      return Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.FromElements();
    }
    public static CausalMesh__CCache__i_Compile._ICServer CServerInit(BigInteger id, Dafny.ISequence<Native____Io__s_Compile._IEndPoint> endpoints)
    {
      BigInteger _331_t1 = id;
      BigInteger _332_t2 = CausalMesh__CCache__i_Compile.__default.CCircle(id, CausalMesh__Types__i_Compile.__default.Nodes);
      Dafny.ISequence<BigInteger> _333_t3 = CausalMesh__CTypes__i_Compile.__default.CEmptyVC();
      Dafny.IMap<BigInteger,Dafny.ISet<CausalMesh__CTypes__i_Compile._ICMeta>> _334_t4 = CausalMesh__CCache__i_Compile.__default.CInitICache();
      Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _335_t5 = CausalMesh__CCache__i_Compile.__default.CInitCCache();
      Native____Io__s_Compile._IEndPoint _336_end = (endpoints).Select(id);
      Native____Io__s_Compile._IEndPoint _337_next__end = (endpoints).Select(_332_t2);
      return CausalMesh__CCache__i_Compile.CServer.create(_331_t1, _336_end, _333_t3, _332_t2, _337_next__end, _334_t4, _335_t5);
    }
  }
} // end of namespace CausalMesh__CCache__i_Compile
namespace CausalMesh__PacketParsing__i_Compile {

  public partial class __default {
    public static Common____GenericMarshalling__i_Compile._IG EndPoint__grammar() {
      return Common____GenericMarshalling__i_Compile.G.create_GUint64();
    }
    public static Common____GenericMarshalling__i_Compile._IG CVectorClock__grammar() {
      return Common____GenericMarshalling__i_Compile.G.create_GArray(Common____GenericMarshalling__i_Compile.G.create_GUint64());
    }
    public static Common____GenericMarshalling__i_Compile._IG CDependency__grammar() {
      return Common____GenericMarshalling__i_Compile.G.create_GArray(Common____GenericMarshalling__i_Compile.G.create_GTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IG>.FromElements(Common____GenericMarshalling__i_Compile.G.create_GUint64(), CausalMesh__PacketParsing__i_Compile.__default.CVectorClock__grammar())));
    }
    public static Common____GenericMarshalling__i_Compile._IG CMeta__grammar() {
      return Common____GenericMarshalling__i_Compile.G.create_GTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IG>.FromElements(Common____GenericMarshalling__i_Compile.G.create_GUint64(), CausalMesh__PacketParsing__i_Compile.__default.CVectorClock__grammar(), CausalMesh__PacketParsing__i_Compile.__default.CDependency__grammar()));
    }
    public static Common____GenericMarshalling__i_Compile._IG CLocal__grammar() {
      return Common____GenericMarshalling__i_Compile.G.create_GArray(Common____GenericMarshalling__i_Compile.G.create_GTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IG>.FromElements(Common____GenericMarshalling__i_Compile.G.create_GUint64(), CausalMesh__PacketParsing__i_Compile.__default.CMeta__grammar())));
    }
    public static Common____GenericMarshalling__i_Compile._IG CMessage__Read__grmamar() {
      return Common____GenericMarshalling__i_Compile.G.create_GTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IG>.FromElements(Common____GenericMarshalling__i_Compile.G.create_GUint64(), Common____GenericMarshalling__i_Compile.G.create_GUint64(), CausalMesh__PacketParsing__i_Compile.__default.CDependency__grammar()));
    }
    public static Common____GenericMarshalling__i_Compile._IG CMessage__ReadReply__grammar() {
      return Common____GenericMarshalling__i_Compile.G.create_GTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IG>.FromElements(Common____GenericMarshalling__i_Compile.G.create_GUint64(), Common____GenericMarshalling__i_Compile.G.create_GUint64(), CausalMesh__PacketParsing__i_Compile.__default.CVectorClock__grammar(), CausalMesh__PacketParsing__i_Compile.__default.CDependency__grammar()));
    }
    public static Common____GenericMarshalling__i_Compile._IG CMessage__Write__grammar() {
      return Common____GenericMarshalling__i_Compile.G.create_GTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IG>.FromElements(Common____GenericMarshalling__i_Compile.G.create_GUint64(), Common____GenericMarshalling__i_Compile.G.create_GUint64(), CausalMesh__PacketParsing__i_Compile.__default.CDependency__grammar(), CausalMesh__PacketParsing__i_Compile.__default.CLocal__grammar(), CausalMesh__PacketParsing__i_Compile.__default.CVectorClock__grammar()));
    }
    public static Common____GenericMarshalling__i_Compile._IG CMessage__WriteReply__grammar() {
      return Common____GenericMarshalling__i_Compile.G.create_GTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IG>.FromElements(Common____GenericMarshalling__i_Compile.G.create_GUint64(), Common____GenericMarshalling__i_Compile.G.create_GUint64(), CausalMesh__PacketParsing__i_Compile.__default.CVectorClock__grammar()));
    }
    public static Common____GenericMarshalling__i_Compile._IG CMessage__Propagate__grammar() {
      return Common____GenericMarshalling__i_Compile.G.create_GTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IG>.FromElements(Common____GenericMarshalling__i_Compile.G.create_GUint64(), CausalMesh__PacketParsing__i_Compile.__default.CMeta__grammar(), Common____GenericMarshalling__i_Compile.G.create_GUint64(), Common____GenericMarshalling__i_Compile.G.create_GUint64()));
    }
    public static Common____GenericMarshalling__i_Compile._IG CMessage__grammar() {
      return Common____GenericMarshalling__i_Compile.G.create_GTaggedUnion(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IG>.FromElements(CausalMesh__PacketParsing__i_Compile.__default.CMessage__Read__grmamar(), CausalMesh__PacketParsing__i_Compile.__default.CMessage__ReadReply__grammar(), CausalMesh__PacketParsing__i_Compile.__default.CMessage__Write__grammar(), CausalMesh__PacketParsing__i_Compile.__default.CMessage__WriteReply__grammar(), CausalMesh__PacketParsing__i_Compile.__default.CMessage__Propagate__grammar()));
    }
    public static Common____GenericMarshalling__i_Compile._IV MarshallEndPoint(Native____Io__s_Compile._IEndPoint c)
    {
      Common____GenericMarshalling__i_Compile._IV val = Common____GenericMarshalling__i_Compile.V.Default();
      val = Common____GenericMarshalling__i_Compile.V.create_VUint64(Common____NodeIdentity__i_Compile.__default.ConvertEndPointToUint64(c));
      return val;
    }
    public static Native____Io__s_Compile._IEndPoint parse__EndPoint(Common____GenericMarshalling__i_Compile._IV val) {
      if (((val).dtor_u) <= (281474976710655UL)) {
        return Common____NodeIdentity__i_Compile.__default.ConvertUint64ToEndPoint((val).dtor_u);
      } else {
        return Native____Io__s_Compile.EndPoint.create(Dafny.Sequence<byte>.FromElements((byte)(0), (byte)(0), (byte)(0), (byte)(0)), (ushort)(0));
      }
    }
    public static Common____GenericMarshalling__i_Compile._IV MarshallCVectorClock(Dafny.ISequence<BigInteger> c)
    {
      Common____GenericMarshalling__i_Compile._IV val = Common____GenericMarshalling__i_Compile.V.Default();
      Common____GenericMarshalling__i_Compile._IV[] _338_vcs;
      Common____GenericMarshalling__i_Compile._IV[] _nw8 = Dafny.ArrayHelpers.InitNewArray1<Common____GenericMarshalling__i_Compile._IV>(Common____GenericMarshalling__i_Compile.V.Default(), Dafny.Helpers.ToIntChecked((ulong)(c).LongCount, "array size exceeds memory limit"));
      _338_vcs = _nw8;
      ulong _339_i;
      _339_i = 0UL;
      while ((_339_i) < ((ulong)(c).LongCount)) {
        ulong _340_single;
        _340_single = 0UL;
        if ((((c).Select(_339_i)).Sign != -1) && (((c).Select(_339_i)) < (new BigInteger(18446744073709551615UL)))) {
          _340_single = (ulong)((c).Select(_339_i));
        } else {
          _340_single = 18446744073709551615UL;
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall CVectorClock overflow\n")));
        }
        (_338_vcs)[(int)((_339_i))] = Common____GenericMarshalling__i_Compile.V.create_VUint64(_340_single);
        _339_i = (_339_i) + (1UL);
      }
      val = Common____GenericMarshalling__i_Compile.V.create_VArray(Dafny.Helpers.SeqFromArray(_338_vcs));
      return val;
    }
    public static Dafny.ISequence<BigInteger> parse__CVectorClock(Common____GenericMarshalling__i_Compile._IV val) {
      if ((new BigInteger(((val).dtor_a).Count)).Sign == 0) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else {
        BigInteger _341_c = new BigInteger((((val).dtor_a).Select(BigInteger.Zero)).dtor_u);
        Common____GenericMarshalling__i_Compile._IV _342_restVal = Common____GenericMarshalling__i_Compile.V.create_VArray(((val).dtor_a).Drop(BigInteger.One));
        Dafny.ISequence<BigInteger> _343_rest = CausalMesh__PacketParsing__i_Compile.__default.parse__CVectorClock(_342_restVal);
        return Dafny.Sequence<BigInteger>.Concat(Dafny.Sequence<BigInteger>.FromElements(_341_c), _343_rest);
      }
    }
    public static bool Uint64InRange(BigInteger i) {
      return ((i).Sign != -1) && ((i) < (new BigInteger(18446744073709551615UL)));
    }
    public static bool CDependencyInRange(Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> d) {
      return Dafny.Helpers.Id<Func<Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>>, bool>>((_344_d) => Dafny.Helpers.Quantifier<BigInteger>((_344_d).Keys.Elements, true, (((_forall_var_5) => {
        BigInteger _345_k = (BigInteger)_forall_var_5;
        return !((_344_d).Contains((_345_k))) || (CausalMesh__PacketParsing__i_Compile.__default.Uint64InRange(_345_k));
      }))))(d);
    }
    public static Common____GenericMarshalling__i_Compile._IV MarshallCDependency(Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> d)
    {
      Common____GenericMarshalling__i_Compile._IV val = Common____GenericMarshalling__i_Compile.V.Default();
      if (CausalMesh__PacketParsing__i_Compile.__default.CDependencyInRange(d)) {
        if ((new BigInteger((d).Count)).Sign == 0) {
          val = Common____GenericMarshalling__i_Compile.V.create_VArray(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements());
        } else {
          BigInteger _346_k;
          foreach (BigInteger _assign_such_that_6 in (d).Keys.Elements) {
            _346_k = (BigInteger)_assign_such_that_6;
            if ((d).Contains((_346_k))) {
              goto after__ASSIGN_SUCH_THAT_6;
            }
          }
          throw new System.Exception("assign-such-that search produced no value (line 129)");
        after__ASSIGN_SUCH_THAT_6: ;
          ulong _347_kk;
          _347_kk = 0UL;
          if (((_346_k).Sign != -1) && ((_346_k) < (new BigInteger(18446744073709551615UL)))) {
            _347_kk = (ulong)(_346_k);
          } else {
            _347_kk = 18446744073709551615UL;
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall CDependency overflow\n")));
          }
          Common____GenericMarshalling__i_Compile._IV _348_marshalled__k;
          _348_marshalled__k = Common____GenericMarshalling__i_Compile.V.create_VUint64(_347_kk);
          Common____GenericMarshalling__i_Compile._IV _349_marshalled__vc;
          Common____GenericMarshalling__i_Compile._IV _out93;
          _out93 = CausalMesh__PacketParsing__i_Compile.__default.MarshallCVectorClock(Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Select(d,_346_k));
          _349_marshalled__vc = _out93;
          Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _350_remainder;
          _350_remainder = Collections____Maps__i_Compile.__default.RemoveElt<BigInteger, Dafny.ISequence<BigInteger>>(d, _346_k);
          Common____GenericMarshalling__i_Compile._IV _351_marshalled__remainder;
          Common____GenericMarshalling__i_Compile._IV _out94;
          _out94 = CausalMesh__PacketParsing__i_Compile.__default.MarshallCDependency(_350_remainder);
          _351_marshalled__remainder = _out94;
          val = Common____GenericMarshalling__i_Compile.V.create_VArray(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.Concat(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements(Common____GenericMarshalling__i_Compile.V.create_VTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements(_348_marshalled__k, _349_marshalled__vc))), (_351_marshalled__remainder).dtor_a));
        }
      } else {
        val = Common____GenericMarshalling__i_Compile.V.create_VArray(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements());
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall CDependency overflow\n")));
      }
      return val;
    }
    public static Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> parse__CDependency(Common____GenericMarshalling__i_Compile._IV val) {
      if ((new BigInteger(((val).dtor_a).Count)).Sign == 0) {
        return Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.FromElements();
      } else {
        Common____GenericMarshalling__i_Compile._IV _352_tuple = ((val).dtor_a).Select(BigInteger.Zero);
        BigInteger _353_k = new BigInteger((((_352_tuple).dtor_t).Select(BigInteger.Zero)).dtor_u);
        Dafny.ISequence<BigInteger> _354_vc = CausalMesh__PacketParsing__i_Compile.__default.parse__CVectorClock(((_352_tuple).dtor_t).Select(BigInteger.One));
        Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _355_others = CausalMesh__PacketParsing__i_Compile.__default.parse__CDependency(Common____GenericMarshalling__i_Compile.V.create_VArray(((val).dtor_a).Drop(BigInteger.One)));
        Dafny.IMap<BigInteger,Dafny.ISequence<BigInteger>> _356_m = Dafny.Map<BigInteger, Dafny.ISequence<BigInteger>>.Update(_355_others, _353_k, _354_vc);
        return _356_m;
      }
    }
    public static Common____GenericMarshalling__i_Compile._IV MarshallCMeta(CausalMesh__CTypes__i_Compile._ICMeta m)
    {
      Common____GenericMarshalling__i_Compile._IV val = Common____GenericMarshalling__i_Compile.V.Default();
      ulong _357_kk;
      _357_kk = 0UL;
      if ((((m).dtor_key).Sign != -1) && (((m).dtor_key) < (new BigInteger(18446744073709551615UL)))) {
        _357_kk = (ulong)((m).dtor_key);
      } else {
        _357_kk = 18446744073709551615UL;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall CMeta overflow\n")));
      }
      Common____GenericMarshalling__i_Compile._IV _358_marshalled__k;
      _358_marshalled__k = Common____GenericMarshalling__i_Compile.V.create_VUint64(_357_kk);
      Common____GenericMarshalling__i_Compile._IV _359_marshalled__vc;
      Common____GenericMarshalling__i_Compile._IV _out95;
      _out95 = CausalMesh__PacketParsing__i_Compile.__default.MarshallCVectorClock((m).dtor_vc);
      _359_marshalled__vc = _out95;
      Common____GenericMarshalling__i_Compile._IV _360_marshalled__dep;
      Common____GenericMarshalling__i_Compile._IV _out96;
      _out96 = CausalMesh__PacketParsing__i_Compile.__default.MarshallCDependency((m).dtor_deps);
      _360_marshalled__dep = _out96;
      val = Common____GenericMarshalling__i_Compile.V.create_VTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements(_358_marshalled__k, _359_marshalled__vc, _360_marshalled__dep));
      return val;
    }
    public static CausalMesh__CTypes__i_Compile._ICMeta parse__CMeta(Common____GenericMarshalling__i_Compile._IV val) {
      return CausalMesh__CTypes__i_Compile.CMeta.create(new BigInteger((((val).dtor_t).Select(BigInteger.Zero)).dtor_u), CausalMesh__PacketParsing__i_Compile.__default.parse__CVectorClock(((val).dtor_t).Select(BigInteger.One)), CausalMesh__PacketParsing__i_Compile.__default.parse__CDependency(((val).dtor_t).Select(new BigInteger(2))));
    }
    public static bool LocalInRange(Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> d) {
      return Dafny.Helpers.Id<Func<Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta>, bool>>((_361_d) => Dafny.Helpers.Quantifier<BigInteger>((_361_d).Keys.Elements, true, (((_forall_var_6) => {
        BigInteger _362_k = (BigInteger)_forall_var_6;
        return !((_361_d).Contains((_362_k))) || (CausalMesh__PacketParsing__i_Compile.__default.Uint64InRange(_362_k));
      }))))(d);
    }
    public static Common____GenericMarshalling__i_Compile._IV MarshallLocal(Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> m)
    {
      Common____GenericMarshalling__i_Compile._IV val = Common____GenericMarshalling__i_Compile.V.Default();
      if (CausalMesh__PacketParsing__i_Compile.__default.LocalInRange(m)) {
        if ((new BigInteger((m).Count)).Sign == 0) {
          val = Common____GenericMarshalling__i_Compile.V.create_VArray(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements());
        } else {
          BigInteger _363_k;
          foreach (BigInteger _assign_such_that_7 in (m).Keys.Elements) {
            _363_k = (BigInteger)_assign_such_that_7;
            if ((m).Contains((_363_k))) {
              goto after__ASSIGN_SUCH_THAT_7;
            }
          }
          throw new System.Exception("assign-such-that search produced no value (line 209)");
        after__ASSIGN_SUCH_THAT_7: ;
          ulong _364_kk;
          _364_kk = 0UL;
          if (((_363_k).Sign != -1) && ((_363_k) < (new BigInteger(18446744073709551615UL)))) {
            _364_kk = (ulong)(_363_k);
          } else {
            _364_kk = 18446744073709551615UL;
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall Local overflow\n")));
          }
          Common____GenericMarshalling__i_Compile._IV _365_marshalled__k;
          _365_marshalled__k = Common____GenericMarshalling__i_Compile.V.create_VUint64(_364_kk);
          Common____GenericMarshalling__i_Compile._IV _366_marshalled__meta;
          Common____GenericMarshalling__i_Compile._IV _out97;
          _out97 = CausalMesh__PacketParsing__i_Compile.__default.MarshallCMeta(Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Select(m,_363_k));
          _366_marshalled__meta = _out97;
          Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _367_remainder;
          _367_remainder = Collections____Maps__i_Compile.__default.RemoveElt<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>(m, _363_k);
          Common____GenericMarshalling__i_Compile._IV _368_marshalled__remainder;
          Common____GenericMarshalling__i_Compile._IV _out98;
          _out98 = CausalMesh__PacketParsing__i_Compile.__default.MarshallLocal(_367_remainder);
          _368_marshalled__remainder = _out98;
          val = Common____GenericMarshalling__i_Compile.V.create_VArray(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.Concat(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements(Common____GenericMarshalling__i_Compile.V.create_VTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements(_365_marshalled__k, _366_marshalled__meta))), (_368_marshalled__remainder).dtor_a));
        }
      } else {
        val = Common____GenericMarshalling__i_Compile.V.create_VArray(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements());
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall Local overflow\n")));
      }
      return val;
    }
    public static Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> parse__Local(Common____GenericMarshalling__i_Compile._IV val) {
      if ((new BigInteger(((val).dtor_a).Count)).Sign == 0) {
        return Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.FromElements();
      } else {
        Common____GenericMarshalling__i_Compile._IV _369_tuple = ((val).dtor_a).Select(BigInteger.Zero);
        BigInteger _370_k = new BigInteger((((_369_tuple).dtor_t).Select(BigInteger.Zero)).dtor_u);
        CausalMesh__CTypes__i_Compile._ICMeta _371_m = CausalMesh__PacketParsing__i_Compile.__default.parse__CMeta(((_369_tuple).dtor_t).Select(BigInteger.One));
        Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _372_others = CausalMesh__PacketParsing__i_Compile.__default.parse__Local(Common____GenericMarshalling__i_Compile.V.create_VArray(((val).dtor_a).Drop(BigInteger.One)));
        Dafny.IMap<BigInteger,CausalMesh__CTypes__i_Compile._ICMeta> _373_r = Dafny.Map<BigInteger, CausalMesh__CTypes__i_Compile._ICMeta>.Update(_372_others, _370_k, _371_m);
        return _373_r;
      }
    }
    public static bool MsgReadInRange(CausalMesh__CMessage__i_Compile._ICMessage c) {
      return (CausalMesh__PacketParsing__i_Compile.__default.Uint64InRange((c).dtor_opn__read)) && (CausalMesh__PacketParsing__i_Compile.__default.Uint64InRange((c).dtor_key__read));
    }
    public static Common____GenericMarshalling__i_Compile._IV MarshallRead(CausalMesh__CMessage__i_Compile._ICMessage c)
    {
      Common____GenericMarshalling__i_Compile._IV val = Common____GenericMarshalling__i_Compile.V.Default();
      ulong _374_opn;
      _374_opn = 0UL;
      if ((((c).dtor_opn__read).Sign != -1) && (((c).dtor_opn__read) < (new BigInteger(18446744073709551615UL)))) {
        _374_opn = (ulong)((c).dtor_opn__read);
      } else {
        _374_opn = 18446744073709551615UL;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall Message Read overflow\n")));
      }
      ulong _375_kk;
      _375_kk = 0UL;
      if ((((c).dtor_key__read).Sign != -1) && (((c).dtor_key__read) < (new BigInteger(18446744073709551615UL)))) {
        _375_kk = (ulong)((c).dtor_key__read);
      } else {
        _375_kk = 18446744073709551615UL;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall Message Read overflow\n")));
      }
      Common____GenericMarshalling__i_Compile._IV _376_deps;
      Common____GenericMarshalling__i_Compile._IV _out99;
      _out99 = CausalMesh__PacketParsing__i_Compile.__default.MarshallCDependency((c).dtor_deps__read);
      _376_deps = _out99;
      val = Common____GenericMarshalling__i_Compile.V.create_VTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements(Common____GenericMarshalling__i_Compile.V.create_VUint64(_374_opn), Common____GenericMarshalling__i_Compile.V.create_VUint64(_375_kk), _376_deps));
      return val;
    }
    public static CausalMesh__CMessage__i_Compile._ICMessage parse__Read(Common____GenericMarshalling__i_Compile._IV val) {
      return CausalMesh__CMessage__i_Compile.CMessage.create_CMessage__Read(new BigInteger((((val).dtor_t).Select(BigInteger.Zero)).dtor_u), new BigInteger((((val).dtor_t).Select(BigInteger.One)).dtor_u), CausalMesh__PacketParsing__i_Compile.__default.parse__CDependency(((val).dtor_t).Select(new BigInteger(2))));
    }
    public static Common____GenericMarshalling__i_Compile._IV MarshallReadReply(CausalMesh__CMessage__i_Compile._ICMessage c)
    {
      Common____GenericMarshalling__i_Compile._IV val = Common____GenericMarshalling__i_Compile.V.Default();
      ulong _377_opn;
      _377_opn = 0UL;
      if ((((c).dtor_opn__rreply).Sign != -1) && (((c).dtor_opn__rreply) < (new BigInteger(18446744073709551615UL)))) {
        _377_opn = (ulong)((c).dtor_opn__rreply);
      } else {
        _377_opn = 18446744073709551615UL;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall Message Read Reply overflow\n")));
      }
      ulong _378_kk;
      _378_kk = 0UL;
      if ((((c).dtor_key__rreply).Sign != -1) && (((c).dtor_key__rreply) < (new BigInteger(18446744073709551615UL)))) {
        _378_kk = (ulong)((c).dtor_key__rreply);
      } else {
        _378_kk = 18446744073709551615UL;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall Message Read Reply overflow\n")));
      }
      Common____GenericMarshalling__i_Compile._IV _379_vc;
      Common____GenericMarshalling__i_Compile._IV _out100;
      _out100 = CausalMesh__PacketParsing__i_Compile.__default.MarshallCVectorClock((c).dtor_vc__rreply);
      _379_vc = _out100;
      Common____GenericMarshalling__i_Compile._IV _380_deps;
      Common____GenericMarshalling__i_Compile._IV _out101;
      _out101 = CausalMesh__PacketParsing__i_Compile.__default.MarshallCDependency((c).dtor_deps__rreply);
      _380_deps = _out101;
      val = Common____GenericMarshalling__i_Compile.V.create_VTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements(Common____GenericMarshalling__i_Compile.V.create_VUint64(_377_opn), Common____GenericMarshalling__i_Compile.V.create_VUint64(_378_kk), _379_vc, _380_deps));
      return val;
    }
    public static CausalMesh__CMessage__i_Compile._ICMessage parse__ReadReply(Common____GenericMarshalling__i_Compile._IV val) {
      return CausalMesh__CMessage__i_Compile.CMessage.create_CMessage__Read__Reply(new BigInteger((((val).dtor_t).Select(BigInteger.Zero)).dtor_u), new BigInteger((((val).dtor_t).Select(BigInteger.One)).dtor_u), CausalMesh__PacketParsing__i_Compile.__default.parse__CVectorClock(((val).dtor_t).Select(new BigInteger(2))), CausalMesh__PacketParsing__i_Compile.__default.parse__CDependency(((val).dtor_t).Select(new BigInteger(3))));
    }
    public static Common____GenericMarshalling__i_Compile._IV MarshallWrite(CausalMesh__CMessage__i_Compile._ICMessage c)
    {
      Common____GenericMarshalling__i_Compile._IV val = Common____GenericMarshalling__i_Compile.V.Default();
      ulong _381_opn;
      _381_opn = 0UL;
      if ((((c).dtor_opn__write).Sign != -1) && (((c).dtor_opn__write) < (new BigInteger(18446744073709551615UL)))) {
        _381_opn = (ulong)((c).dtor_opn__write);
      } else {
        _381_opn = 18446744073709551615UL;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall Message Write overflow\n")));
      }
      ulong _382_kk;
      _382_kk = 0UL;
      if ((((c).dtor_key__write).Sign != -1) && (((c).dtor_key__write) < (new BigInteger(18446744073709551615UL)))) {
        _382_kk = (ulong)((c).dtor_key__write);
      } else {
        _382_kk = 18446744073709551615UL;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall Message Write overflow\n")));
      }
      Common____GenericMarshalling__i_Compile._IV _383_local;
      Common____GenericMarshalling__i_Compile._IV _out102;
      _out102 = CausalMesh__PacketParsing__i_Compile.__default.MarshallLocal((c).dtor_local);
      _383_local = _out102;
      Common____GenericMarshalling__i_Compile._IV _384_deps;
      Common____GenericMarshalling__i_Compile._IV _out103;
      _out103 = CausalMesh__PacketParsing__i_Compile.__default.MarshallCDependency((c).dtor_deps__write);
      _384_deps = _out103;
      Common____GenericMarshalling__i_Compile._IV _385_vc;
      Common____GenericMarshalling__i_Compile._IV _out104;
      _out104 = CausalMesh__PacketParsing__i_Compile.__default.MarshallCVectorClock((c).dtor_mvc);
      _385_vc = _out104;
      val = Common____GenericMarshalling__i_Compile.V.create_VTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements(Common____GenericMarshalling__i_Compile.V.create_VUint64(_381_opn), Common____GenericMarshalling__i_Compile.V.create_VUint64(_382_kk), _384_deps, _383_local, _385_vc));
      return val;
    }
    public static CausalMesh__CMessage__i_Compile._ICMessage parse__Write(Common____GenericMarshalling__i_Compile._IV val) {
      return CausalMesh__CMessage__i_Compile.CMessage.create_CMessage__Write(new BigInteger((((val).dtor_t).Select(BigInteger.Zero)).dtor_u), new BigInteger((((val).dtor_t).Select(BigInteger.One)).dtor_u), CausalMesh__PacketParsing__i_Compile.__default.parse__CDependency(((val).dtor_t).Select(new BigInteger(2))), CausalMesh__PacketParsing__i_Compile.__default.parse__Local(((val).dtor_t).Select(new BigInteger(3))), CausalMesh__PacketParsing__i_Compile.__default.parse__CVectorClock(((val).dtor_t).Select(new BigInteger(4))));
    }
    public static Common____GenericMarshalling__i_Compile._IV MarshallWriteReply(CausalMesh__CMessage__i_Compile._ICMessage c)
    {
      Common____GenericMarshalling__i_Compile._IV val = Common____GenericMarshalling__i_Compile.V.Default();
      ulong _386_opn;
      _386_opn = 0UL;
      if ((((c).dtor_opn__wreply).Sign != -1) && (((c).dtor_opn__wreply) < (new BigInteger(18446744073709551615UL)))) {
        _386_opn = (ulong)((c).dtor_opn__wreply);
      } else {
        _386_opn = 18446744073709551615UL;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall Message Write Reply overflow\n")));
      }
      ulong _387_kk;
      _387_kk = 0UL;
      if ((((c).dtor_key__wreply).Sign != -1) && (((c).dtor_key__wreply) < (new BigInteger(18446744073709551615UL)))) {
        _387_kk = (ulong)((c).dtor_key__wreply);
      } else {
        _387_kk = 18446744073709551615UL;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall Message Write Reply overflow\n")));
      }
      Common____GenericMarshalling__i_Compile._IV _388_vc;
      Common____GenericMarshalling__i_Compile._IV _out105;
      _out105 = CausalMesh__PacketParsing__i_Compile.__default.MarshallCVectorClock((c).dtor_vc__wreply);
      _388_vc = _out105;
      val = Common____GenericMarshalling__i_Compile.V.create_VTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements(Common____GenericMarshalling__i_Compile.V.create_VUint64(_386_opn), Common____GenericMarshalling__i_Compile.V.create_VUint64(_387_kk), _388_vc));
      return val;
    }
    public static CausalMesh__CMessage__i_Compile._ICMessage parse__WriteReply(Common____GenericMarshalling__i_Compile._IV val) {
      return CausalMesh__CMessage__i_Compile.CMessage.create_CMessage__Write__Reply(new BigInteger((((val).dtor_t).Select(BigInteger.Zero)).dtor_u), new BigInteger((((val).dtor_t).Select(BigInteger.One)).dtor_u), CausalMesh__PacketParsing__i_Compile.__default.parse__CVectorClock(((val).dtor_t).Select(new BigInteger(2))));
    }
    public static Common____GenericMarshalling__i_Compile._IV MarshallPropagation(CausalMesh__CMessage__i_Compile._ICMessage c)
    {
      Common____GenericMarshalling__i_Compile._IV val = Common____GenericMarshalling__i_Compile.V.Default();
      ulong _389_kk;
      _389_kk = 0UL;
      if ((((c).dtor_key).Sign != -1) && (((c).dtor_key) < (new BigInteger(18446744073709551615UL)))) {
        _389_kk = (ulong)((c).dtor_key);
      } else {
        _389_kk = 18446744073709551615UL;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall Message Propagation overflow\n")));
      }
      ulong _390_start;
      _390_start = 0UL;
      if ((((c).dtor_start).Sign != -1) && (((c).dtor_start) < (new BigInteger(18446744073709551615UL)))) {
        _390_start = (ulong)((c).dtor_start);
      } else {
        _390_start = 18446744073709551615UL;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall Message Propagation overflow\n")));
      }
      ulong _391_round;
      _391_round = 0UL;
      if ((((c).dtor_round).Sign != -1) && (((c).dtor_round) < (new BigInteger(18446744073709551615UL)))) {
        _391_round = (ulong)((c).dtor_round);
      } else {
        _391_round = 18446744073709551615UL;
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Marshall Message Propagation overflow\n")));
      }
      Common____GenericMarshalling__i_Compile._IV _392_m;
      Common____GenericMarshalling__i_Compile._IV _out106;
      _out106 = CausalMesh__PacketParsing__i_Compile.__default.MarshallCMeta((c).dtor_meta);
      _392_m = _out106;
      val = Common____GenericMarshalling__i_Compile.V.create_VTuple(Dafny.Sequence<Common____GenericMarshalling__i_Compile._IV>.FromElements(Common____GenericMarshalling__i_Compile.V.create_VUint64(_389_kk), _392_m, Common____GenericMarshalling__i_Compile.V.create_VUint64(_390_start), Common____GenericMarshalling__i_Compile.V.create_VUint64(_391_round)));
      return val;
    }
    public static CausalMesh__CMessage__i_Compile._ICMessage parse__Propagation(Common____GenericMarshalling__i_Compile._IV val) {
      return CausalMesh__CMessage__i_Compile.CMessage.create_CMessage__Propagation(new BigInteger((((val).dtor_t).Select(BigInteger.Zero)).dtor_u), CausalMesh__PacketParsing__i_Compile.__default.parse__CMeta(((val).dtor_t).Select(BigInteger.One)), new BigInteger((((val).dtor_t).Select(new BigInteger(2))).dtor_u), new BigInteger((((val).dtor_t).Select(new BigInteger(3))).dtor_u));
    }
    public static CausalMesh__CMessage__i_Compile._ICMessage parse__Message(Common____GenericMarshalling__i_Compile._IV val) {
      if (((val).dtor_c) == (0UL)) {
        return CausalMesh__PacketParsing__i_Compile.__default.parse__Read((val).dtor_val);
      } else if (((val).dtor_c) == (1UL)) {
        return CausalMesh__PacketParsing__i_Compile.__default.parse__ReadReply((val).dtor_val);
      } else if (((val).dtor_c) == (2UL)) {
        return CausalMesh__PacketParsing__i_Compile.__default.parse__Write((val).dtor_val);
      } else if (((val).dtor_c) == (3UL)) {
        return CausalMesh__PacketParsing__i_Compile.__default.parse__WriteReply((val).dtor_val);
      } else if (((val).dtor_c) == (4UL)) {
        return CausalMesh__PacketParsing__i_Compile.__default.parse__Propagation((val).dtor_val);
      } else {
        return CausalMesh__PacketParsing__i_Compile.__default.parse__Read(val);
      }
    }
    public static CausalMesh__CMessage__i_Compile._ICMessage DemarshallData(byte[] data, Common____GenericMarshalling__i_Compile._IG msg__grammar)
    {
      CausalMesh__CMessage__i_Compile._ICMessage msg = CausalMesh__CMessage__i_Compile.CMessage.Default();
      bool _393_success;
      Common____GenericMarshalling__i_Compile._IV _394_val;
      bool _out107;
      Common____GenericMarshalling__i_Compile._IV _out108;
      Common____GenericMarshalling__i_Compile.__default.Demarshall(data, msg__grammar, out _out107, out _out108);
      _393_success = _out107;
      _394_val = _out108;
      if (_393_success) {
        msg = CausalMesh__PacketParsing__i_Compile.__default.parse__Message(_394_val);
      } else {
        Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Parse message fail\n")));
      }
      return msg;
    }
    public static Common____GenericMarshalling__i_Compile._IV MarshallMessage(CausalMesh__CMessage__i_Compile._ICMessage c)
    {
      Common____GenericMarshalling__i_Compile._IV val = Common____GenericMarshalling__i_Compile.V.Default();
      if ((c).is_CMessage__Read) {
        Common____GenericMarshalling__i_Compile._IV _395_msg;
        Common____GenericMarshalling__i_Compile._IV _out109;
        _out109 = CausalMesh__PacketParsing__i_Compile.__default.MarshallRead(c);
        _395_msg = _out109;
        val = Common____GenericMarshalling__i_Compile.V.create_VCase(0UL, _395_msg);
      } else if ((c).is_CMessage__Read__Reply) {
        Common____GenericMarshalling__i_Compile._IV _396_msg;
        Common____GenericMarshalling__i_Compile._IV _out110;
        _out110 = CausalMesh__PacketParsing__i_Compile.__default.MarshallReadReply(c);
        _396_msg = _out110;
        val = Common____GenericMarshalling__i_Compile.V.create_VCase(1UL, _396_msg);
      } else if ((c).is_CMessage__Write) {
        Common____GenericMarshalling__i_Compile._IV _397_msg;
        Common____GenericMarshalling__i_Compile._IV _out111;
        _out111 = CausalMesh__PacketParsing__i_Compile.__default.MarshallWrite(c);
        _397_msg = _out111;
        val = Common____GenericMarshalling__i_Compile.V.create_VCase(2UL, _397_msg);
      } else if ((c).is_CMessage__Write__Reply) {
        Common____GenericMarshalling__i_Compile._IV _398_msg;
        Common____GenericMarshalling__i_Compile._IV _out112;
        _out112 = CausalMesh__PacketParsing__i_Compile.__default.MarshallWriteReply(c);
        _398_msg = _out112;
        val = Common____GenericMarshalling__i_Compile.V.create_VCase(3UL, _398_msg);
      } else if ((c).is_CMessage__Propagation) {
        Common____GenericMarshalling__i_Compile._IV _399_msg;
        Common____GenericMarshalling__i_Compile._IV _out113;
        _out113 = CausalMesh__PacketParsing__i_Compile.__default.MarshallPropagation(c);
        _399_msg = _out113;
        val = Common____GenericMarshalling__i_Compile.V.create_VCase(4UL, _399_msg);
      }
      return val;
    }
    public static byte[] MarshallData(CausalMesh__CMessage__i_Compile._ICMessage msg)
    {
      byte[] data = new byte[0];
      Common____GenericMarshalling__i_Compile._IV _400_val;
      Common____GenericMarshalling__i_Compile._IV _out114;
      _out114 = CausalMesh__PacketParsing__i_Compile.__default.MarshallMessage(msg);
      _400_val = _out114;
      byte[] _out115;
      _out115 = Common____GenericMarshalling__i_Compile.__default.Marshall(_400_val, CausalMesh__PacketParsing__i_Compile.__default.CMessage__grammar());
      data = _out115;
      return data;
    }
  }
} // end of namespace CausalMesh__PacketParsing__i_Compile
namespace CausalMesh__ServerImpl__i_Compile {

  public partial class ServerImpl {
    public ServerImpl() {
      this.server = CausalMesh__CCache__i_Compile.CServer.Default();
      this.netClient = ((Native____Io__s_Compile.UdpClient)null);
      this.localAddr = Native____Io__s_Compile.EndPoint.Default();
      this.msg__grammar = Common____GenericMarshalling__i_Compile.G.Default();
    }
    public CausalMesh__CCache__i_Compile._ICServer server {get; set;}
    public Native____Io__s_Compile.UdpClient netClient {get; set;}
    public Native____Io__s_Compile._IEndPoint localAddr {get; set;}
    public Common____GenericMarshalling__i_Compile._IG msg__grammar {get; set;}
    public void __ctor()
    {
      (this).netClient = (Native____Io__s_Compile.UdpClient)null;
    }
    public void ConstructUdpClient(Native____Io__s_Compile._IEndPoint ep, out bool ok, out Native____Io__s_Compile.UdpClient client)
    {
      ok = false;
      client = ((Native____Io__s_Compile.UdpClient)null);
      Native____Io__s_Compile._IEndPoint _401_my__ep;
      _401_my__ep = ep;
      byte[] _402_ip__byte__array;
      byte[] _nw9 = new byte[Dafny.Helpers.ToIntChecked(new BigInteger(((_401_my__ep).dtor_addr).Count), "array size exceeds memory limit")];
      _402_ip__byte__array = _nw9;
      Common____Util__i_Compile.__default.seqIntoArrayOpt<byte>((_401_my__ep).dtor_addr, _402_ip__byte__array);
      Native____Io__s_Compile.IPEndPoint _403_ip__endpoint = default(Native____Io__s_Compile.IPEndPoint);
      bool _out116;
      Native____Io__s_Compile.IPEndPoint _out117;
      Native____Io__s_Compile.IPEndPoint.Construct(_402_ip__byte__array, (_401_my__ep).dtor_port, out _out116, out _out117);
      ok = _out116;
      _403_ip__endpoint = _out117;
      if (!(ok)) {
        return ;
      }
      bool _out118;
      Native____Io__s_Compile.UdpClient _out119;
      Native____Io__s_Compile.UdpClient.Construct(_403_ip__endpoint, out _out118, out _out119);
      ok = _out118;
      client = _out119;
    }
    public bool Server__Init(BigInteger id, Dafny.ISequence<Native____Io__s_Compile._IEndPoint> eps)
    {
      bool ok = false;
      bool _out120;
      Native____Io__s_Compile.UdpClient _out121;
      (this).ConstructUdpClient((eps).Select(id), out _out120, out _out121);
      ok = _out120;
      (this).netClient = _out121;
      if (ok) {
        (this).server = CausalMesh__CCache__i_Compile.__default.CServerInit(id, eps);
        (this).localAddr = (eps).Select(id);
        (this).msg__grammar = CausalMesh__PacketParsing__i_Compile.__default.CMessage__grammar();
      }
      return ok;
    }
  }

} // end of namespace CausalMesh__ServerImpl__i_Compile
namespace CausalMesh__Network__i_Compile {

  public interface _IReceiveResult {
    bool is_RRFail { get; }
    bool is_RRTimeout { get; }
    bool is_RRPacket { get; }
    CausalMesh__CMessage__i_Compile._ICPacket dtor_cpacket { get; }
    _IReceiveResult DowncastClone();
  }
  public abstract class ReceiveResult : _IReceiveResult {
    public ReceiveResult() { }
    private static readonly CausalMesh__Network__i_Compile._IReceiveResult theDefault = create_RRFail();
    public static CausalMesh__Network__i_Compile._IReceiveResult Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<CausalMesh__Network__i_Compile._IReceiveResult> _TYPE = new Dafny.TypeDescriptor<CausalMesh__Network__i_Compile._IReceiveResult>(CausalMesh__Network__i_Compile.ReceiveResult.Default());
    public static Dafny.TypeDescriptor<CausalMesh__Network__i_Compile._IReceiveResult> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IReceiveResult create_RRFail() {
      return new ReceiveResult_RRFail();
    }
    public static _IReceiveResult create_RRTimeout() {
      return new ReceiveResult_RRTimeout();
    }
    public static _IReceiveResult create_RRPacket(CausalMesh__CMessage__i_Compile._ICPacket cpacket) {
      return new ReceiveResult_RRPacket(cpacket);
    }
    public bool is_RRFail { get { return this is ReceiveResult_RRFail; } }
    public bool is_RRTimeout { get { return this is ReceiveResult_RRTimeout; } }
    public bool is_RRPacket { get { return this is ReceiveResult_RRPacket; } }
    public CausalMesh__CMessage__i_Compile._ICPacket dtor_cpacket {
      get {
        var d = this;
        return ((ReceiveResult_RRPacket)d)._cpacket;
      }
    }
    public abstract _IReceiveResult DowncastClone();
  }
  public class ReceiveResult_RRFail : ReceiveResult {
    public ReceiveResult_RRFail() {
    }
    public override _IReceiveResult DowncastClone() {
      if (this is _IReceiveResult dt) { return dt; }
      return new ReceiveResult_RRFail();
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__Network__i_Compile.ReceiveResult_RRFail;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__Network__i_Compile.ReceiveResult.RRFail";
      return s;
    }
  }
  public class ReceiveResult_RRTimeout : ReceiveResult {
    public ReceiveResult_RRTimeout() {
    }
    public override _IReceiveResult DowncastClone() {
      if (this is _IReceiveResult dt) { return dt; }
      return new ReceiveResult_RRTimeout();
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__Network__i_Compile.ReceiveResult_RRTimeout;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__Network__i_Compile.ReceiveResult.RRTimeout";
      return s;
    }
  }
  public class ReceiveResult_RRPacket : ReceiveResult {
    public readonly CausalMesh__CMessage__i_Compile._ICPacket _cpacket;
    public ReceiveResult_RRPacket(CausalMesh__CMessage__i_Compile._ICPacket cpacket) {
      this._cpacket = cpacket;
    }
    public override _IReceiveResult DowncastClone() {
      if (this is _IReceiveResult dt) { return dt; }
      return new ReceiveResult_RRPacket(_cpacket);
    }
    public override bool Equals(object other) {
      var oth = other as CausalMesh__Network__i_Compile.ReceiveResult_RRPacket;
      return oth != null && object.Equals(this._cpacket, oth._cpacket);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._cpacket));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CausalMesh__Network__i_Compile.ReceiveResult.RRPacket";
      s += "(";
      s += Dafny.Helpers.ToString(this._cpacket);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static Native____Io__s_Compile._IEndPoint GetEndPoint(Native____Io__s_Compile.IPEndPoint ipe)
    {
      Native____Io__s_Compile._IEndPoint ep = Native____Io__s_Compile.EndPoint.Default();
      byte[] _404_addr;
      byte[] _out122;
      _out122 = (ipe).GetAddress();
      _404_addr = _out122;
      ushort _405_port;
      _405_port = (ipe).GetPort();
      ep = Native____Io__s_Compile.EndPoint.create(Dafny.Helpers.SeqFromArray(_404_addr), _405_port);
      return ep;
    }
    public static CausalMesh__Network__i_Compile._IReceiveResult Receive(Native____Io__s_Compile.UdpClient udpClient, Native____Io__s_Compile._IEndPoint localAddr, Common____GenericMarshalling__i_Compile._IG msg__grammar)
    {
      CausalMesh__Network__i_Compile._IReceiveResult rr = CausalMesh__Network__i_Compile.ReceiveResult.Default();
      int _406_timeout;
      _406_timeout = 0;
      bool _407_ok;
      bool _408_timedOut;
      Native____Io__s_Compile.IPEndPoint _409_remote;
      byte[] _410_buffer;
      bool _out123;
      bool _out124;
      Native____Io__s_Compile.IPEndPoint _out125;
      byte[] _out126;
      (udpClient).Receive(_406_timeout, out _out123, out _out124, out _out125, out _out126);
      _407_ok = _out123;
      _408_timedOut = _out124;
      _409_remote = _out125;
      _410_buffer = _out126;
      if (!(_407_ok)) {
        rr = CausalMesh__Network__i_Compile.ReceiveResult.create_RRFail();
        return rr;
      }
      if (_408_timedOut) {
        rr = CausalMesh__Network__i_Compile.ReceiveResult.create_RRTimeout();
        return rr;
      }
      ulong _411_start__time;
      ulong _out127;
      _out127 = Native____Io__s_Compile.Time.GetDebugTimeTicks();
      _411_start__time = _out127;
      CausalMesh__CMessage__i_Compile._ICMessage _412_cmessage;
      CausalMesh__CMessage__i_Compile._ICMessage _out128;
      _out128 = CausalMesh__PacketParsing__i_Compile.__default.DemarshallData(_410_buffer, msg__grammar);
      _412_cmessage = _out128;
      ulong _413_end__time;
      ulong _out129;
      _out129 = Native____Io__s_Compile.Time.GetDebugTimeTicks();
      _413_end__time = _out129;
      Native____Io__s_Compile._IEndPoint _414_srcEp;
      Native____Io__s_Compile._IEndPoint _out130;
      _out130 = CausalMesh__Network__i_Compile.__default.GetEndPoint(_409_remote);
      _414_srcEp = _out130;
      CausalMesh__CMessage__i_Compile._ICPacket _415_cpacket;
      _415_cpacket = CausalMesh__CMessage__i_Compile.CPacket.create(localAddr, _414_srcEp, _412_cmessage);
      rr = CausalMesh__Network__i_Compile.ReceiveResult.create_RRPacket(_415_cpacket);
      return rr;
    }
    public static bool SendPacketSequence(Native____Io__s_Compile.UdpClient udpClient, Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> packets)
    {
      bool ok = false;
      Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> _416_cpackets;
      _416_cpackets = packets;
      BigInteger _417_j;
      _417_j = BigInteger.Zero;
      ok = true;
      BigInteger _418_i;
      _418_i = BigInteger.Zero;
      while ((_418_i) < (new BigInteger((_416_cpackets).Count))) {
        CausalMesh__CMessage__i_Compile._ICPacket _419_cpacket;
        _419_cpacket = (_416_cpackets).Select(_418_i);
        Native____Io__s_Compile._IEndPoint _420_dstEp;
        _420_dstEp = (_419_cpacket).dtor_dst;
        if ((new BigInteger(((_420_dstEp).dtor_addr).Count)) < (BigInteger.Parse("18446744073709551616"))) {
          byte[] _421_dstAddrAry;
          byte[] _out131;
          _out131 = Common____Util__i_Compile.__default.seqToArrayOpt<byte>(Native____NativeTypes__s_Compile.@byte._TypeDescriptor(), (_420_dstEp).dtor_addr);
          _421_dstAddrAry = _out131;
          Native____Io__s_Compile.IPEndPoint _422_remote = default(Native____Io__s_Compile.IPEndPoint);
          bool _out132;
          Native____Io__s_Compile.IPEndPoint _out133;
          Native____Io__s_Compile.IPEndPoint.Construct(_421_dstAddrAry, (_420_dstEp).dtor_port, out _out132, out _out133);
          ok = _out132;
          _422_remote = _out133;
          if (!(ok)) {
            return ok;
          }
          byte[] _423_buffer;
          byte[] _out134;
          _out134 = CausalMesh__PacketParsing__i_Compile.__default.MarshallData((_419_cpacket).dtor_msg);
          _423_buffer = _out134;
          if ((new BigInteger((_423_buffer).Length)) <= (new BigInteger(18446744073709551615UL))) {
            bool _out135;
            _out135 = (udpClient).Send(_422_remote, _423_buffer);
            ok = _out135;
            if (!(ok)) {
              return ok;
            }
          } else {
            Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Packet is too large\n")));
          }
        } else {
          Dafny.Helpers.Print((Dafny.Sequence<char>.FromString("Dst has wrong adress\n")));
        }
        _418_i = (_418_i) + (BigInteger.One);
      }
      return ok;
    }
  }
} // end of namespace CausalMesh__Network__i_Compile
namespace CausalMesh__ServerImplMain__i_Compile {

  public partial class __default {
    public static bool Replica__Next__ProcessPacketX(CausalMesh__ServerImpl__i_Compile.ServerImpl r)
    {
      bool ok = false;
      CausalMesh__Network__i_Compile._IReceiveResult _424_rr = CausalMesh__Network__i_Compile.ReceiveResult.Default();
      CausalMesh__Network__i_Compile._IReceiveResult _out136;
      _out136 = CausalMesh__Network__i_Compile.__default.Receive(r.netClient, r.localAddr, r.msg__grammar);
      _424_rr = _out136;
      if ((_424_rr).is_RRFail) {
        ok = false;
        return ok;
      } else if ((_424_rr).is_RRTimeout) {
        ok = true;
        CausalMesh__ServerImplMain__i_Compile.__default.ReplicaNextProcessPacketTimeout(r);
      } else {
        bool _425_marshallable;
        _425_marshallable = true;
        if (!(_425_marshallable)) {
          ok = true;
        } else if ((((_424_rr).dtor_cpacket).dtor_msg).is_CMessage__Read) {
          bool _out137;
          _out137 = CausalMesh__ServerImplMain__i_Compile.__default.ServerNextProcessRead(r, (_424_rr).dtor_cpacket);
          ok = _out137;
        } else if ((((_424_rr).dtor_cpacket).dtor_msg).is_CMessage__Write) {
          bool _out138;
          _out138 = CausalMesh__ServerImplMain__i_Compile.__default.ServerNextProcessWrite(r, (_424_rr).dtor_cpacket);
          ok = _out138;
        } else if ((((_424_rr).dtor_cpacket).dtor_msg).is_CMessage__Propagation) {
          bool _out139;
          _out139 = CausalMesh__ServerImplMain__i_Compile.__default.ServerNextProcessPropagation(r, (_424_rr).dtor_cpacket);
          ok = _out139;
        } else {
          ok = true;
        }
      }
      return ok;
    }
    public static bool ReplicaNextMainProcessPacketX(CausalMesh__ServerImpl__i_Compile.ServerImpl r)
    {
      bool ok = false;
      bool _out140;
      _out140 = CausalMesh__ServerImplMain__i_Compile.__default.Replica__Next__ProcessPacketX(r);
      ok = _out140;
      if (!(ok)) {
        return ok;
      }
      return ok;
    }
    public static bool Server__Next__main(CausalMesh__ServerImpl__i_Compile.ServerImpl r)
    {
      bool ok = false;
      bool _out141;
      _out141 = CausalMesh__ServerImplMain__i_Compile.__default.ReplicaNextMainProcessPacketX(r);
      ok = _out141;
      return ok;
    }
    public static bool DeliverPackets(CausalMesh__ServerImpl__i_Compile.ServerImpl r, Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> packets)
    {
      bool ok = false;
      bool _out142;
      _out142 = CausalMesh__Network__i_Compile.__default.SendPacketSequence(r.netClient, packets);
      ok = _out142;
      return ok;
    }
    public static bool ServerNextProcessRead(CausalMesh__ServerImpl__i_Compile.ServerImpl r, CausalMesh__CMessage__i_Compile._ICPacket cpacket)
    {
      bool ok = false;
      Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> _426_sent__packets = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.Empty;
      CausalMesh__CCache__i_Compile._ICServer _out143;
      Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> _out144;
      CausalMesh__CCache__i_Compile.__default.CReceiveRead__I1(r.server, cpacket, out _out143, out _out144);
      (r).server = _out143;
      _426_sent__packets = _out144;
      bool _out145;
      _out145 = CausalMesh__ServerImplMain__i_Compile.__default.DeliverPackets(r, _426_sent__packets);
      ok = _out145;
      return ok;
    }
    public static bool ServerNextProcessWrite(CausalMesh__ServerImpl__i_Compile.ServerImpl r, CausalMesh__CMessage__i_Compile._ICPacket cpacket)
    {
      bool ok = false;
      Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> _427_sent__packets = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.Empty;
      CausalMesh__CCache__i_Compile._ICServer _out146;
      Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> _out147;
      CausalMesh__CCache__i_Compile.__default.CReceiveWrite__I1(r.server, cpacket, out _out146, out _out147);
      (r).server = _out146;
      _427_sent__packets = _out147;
      bool _out148;
      _out148 = CausalMesh__ServerImplMain__i_Compile.__default.DeliverPackets(r, _427_sent__packets);
      ok = _out148;
      return ok;
    }
    public static bool ServerNextProcessPropagation(CausalMesh__ServerImpl__i_Compile.ServerImpl r, CausalMesh__CMessage__i_Compile._ICPacket cpacket)
    {
      bool ok = false;
      Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> _428_sent__packets = Dafny.Sequence<CausalMesh__CMessage__i_Compile._ICPacket>.Empty;
      CausalMesh__CCache__i_Compile._ICServer _out149;
      Dafny.ISequence<CausalMesh__CMessage__i_Compile._ICPacket> _out150;
      CausalMesh__CCache__i_Compile.__default.CReceivePropagate(r.server, cpacket, out _out149, out _out150);
      (r).server = _out149;
      _428_sent__packets = _out150;
      bool _out151;
      _out151 = CausalMesh__ServerImplMain__i_Compile.__default.DeliverPackets(r, _428_sent__packets);
      ok = _out151;
      return ok;
    }
    public static void ReplicaNextProcessPacketTimeout(CausalMesh__ServerImpl__i_Compile.ServerImpl r)
    {
    }
  }
} // end of namespace CausalMesh__ServerImplMain__i_Compile
namespace Host__i_Compile {

  public interface _ICScheduler {
    bool is_CScheduler { get; }
    CausalMesh__ServerImpl__i_Compile.ServerImpl dtor_replica__impl { get; }
  }
  public class CScheduler : _ICScheduler {
    public readonly CausalMesh__ServerImpl__i_Compile.ServerImpl _replica__impl;
    public CScheduler(CausalMesh__ServerImpl__i_Compile.ServerImpl replica__impl) {
      this._replica__impl = replica__impl;
    }
    public static CausalMesh__ServerImpl__i_Compile.ServerImpl DowncastClone(CausalMesh__ServerImpl__i_Compile.ServerImpl _this) {
      return _this;
    }
    public override bool Equals(object other) {
      var oth = other as Host__i_Compile.CScheduler;
      return oth != null && this._replica__impl == oth._replica__impl;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._replica__impl));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Host__i_Compile.CScheduler.CScheduler";
      s += "(";
      s += Dafny.Helpers.ToString(this._replica__impl);
      s += ")";
      return s;
    }
    private static readonly CausalMesh__ServerImpl__i_Compile.ServerImpl theDefault = default(CausalMesh__ServerImpl__i_Compile.ServerImpl);
    public static CausalMesh__ServerImpl__i_Compile.ServerImpl Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<CausalMesh__ServerImpl__i_Compile.ServerImpl> _TYPE = new Dafny.TypeDescriptor<CausalMesh__ServerImpl__i_Compile.ServerImpl>(default(CausalMesh__ServerImpl__i_Compile.ServerImpl));
    public static Dafny.TypeDescriptor<CausalMesh__ServerImpl__i_Compile.ServerImpl> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICScheduler create(CausalMesh__ServerImpl__i_Compile.ServerImpl replica__impl) {
      return new CScheduler(replica__impl);
    }
    public static _ICScheduler create_CScheduler(CausalMesh__ServerImpl__i_Compile.ServerImpl replica__impl) {
      return create(replica__impl);
    }
    public bool is_CScheduler { get { return true; } }
    public CausalMesh__ServerImpl__i_Compile.ServerImpl dtor_replica__impl {
      get {
        return this._replica__impl;
      }
    }
  }

  public partial class __default {
    public static void HostInitImpl(out bool ok, out CausalMesh__ServerImpl__i_Compile.ServerImpl host__state, out Dafny.ISequence<Native____Io__s_Compile._IEndPoint> config, out Native____Io__s_Compile._IEndPoint id)
    {
      ok = false;
      host__state = default(CausalMesh__ServerImpl__i_Compile.ServerImpl);
      config = Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.Empty;
      id = Native____Io__s_Compile.EndPoint.Default();
      Dafny.ISequence<Native____Io__s_Compile._IEndPoint> _429_pconfig = Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.Empty;
      BigInteger _430_my__index = BigInteger.Zero;
      bool _out152;
      Dafny.ISequence<Native____Io__s_Compile._IEndPoint> _out153;
      BigInteger _out154;
      CausalMesh__CmdParser__i_Compile.__default.parse__cmd__line(out _out152, out _out153, out _out154);
      ok = _out152;
      _429_pconfig = _out153;
      _430_my__index = _out154;
      CausalMesh__ServerImpl__i_Compile.ServerImpl _431_repImpl;
      CausalMesh__ServerImpl__i_Compile.ServerImpl _nw10 = new CausalMesh__ServerImpl__i_Compile.ServerImpl();
      _nw10.__ctor();
      _431_repImpl = _nw10;
      host__state = _431_repImpl;
      if (!(ok)) {
        return ;
      }
      id = (_429_pconfig).Select(_430_my__index);
      CausalMesh__ServerImpl__i_Compile.ServerImpl _432_scheduler;
      CausalMesh__ServerImpl__i_Compile.ServerImpl _nw11 = new CausalMesh__ServerImpl__i_Compile.ServerImpl();
      _nw11.__ctor();
      _432_scheduler = _nw11;
      bool _out155;
      _out155 = (_432_scheduler).Server__Init(_430_my__index, _429_pconfig);
      ok = _out155;
      host__state = _432_scheduler;
      config = _429_pconfig;
    }
    public static void HostNextImpl(CausalMesh__ServerImpl__i_Compile.ServerImpl host__state, out bool ok, out CausalMesh__ServerImpl__i_Compile.ServerImpl host__state_k)
    {
      ok = false;
      host__state_k = default(CausalMesh__ServerImpl__i_Compile.ServerImpl);
      CausalMesh__ServerImpl__i_Compile.ServerImpl _433_repImpl;
      CausalMesh__ServerImpl__i_Compile.ServerImpl _nw12 = new CausalMesh__ServerImpl__i_Compile.ServerImpl();
      _nw12.__ctor();
      _433_repImpl = _nw12;
      host__state_k = _433_repImpl;
      bool _434_okay;
      bool _out156;
      _out156 = CausalMesh__ServerImplMain__i_Compile.__default.Server__Next__main((host__state));
      _434_okay = _out156;
      Dafny.ISequence<Environment__s_Compile._ILIoOp<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>>> _435_netEventLog;
      _435_netEventLog = Dafny.Sequence<Environment__s_Compile._ILIoOp<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>>>.FromElements();
      if (_434_okay) {
        host__state_k = (host__state);
      } else {
      }
      ok = _434_okay;
    }
  }
} // end of namespace Host__i_Compile
namespace CM__DistributedSystem__i_Compile {


  public interface _IDS__State {
    bool is_DS__State { get; }
    Dafny.ISequence<Native____Io__s_Compile._IEndPoint> dtor_config { get; }
    Environment__s_Compile._ILEnvironment<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>> dtor_environment { get; }
    Dafny.IMap<Native____Io__s_Compile._IEndPoint,CausalMesh__ServerImpl__i_Compile.ServerImpl> dtor_servers { get; }
    Dafny.ISet<Native____Io__s_Compile._IEndPoint> dtor_clients { get; }
    _IDS__State DowncastClone();
  }
  public class DS__State : _IDS__State {
    public readonly Dafny.ISequence<Native____Io__s_Compile._IEndPoint> _config;
    public readonly Environment__s_Compile._ILEnvironment<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>> _environment;
    public readonly Dafny.IMap<Native____Io__s_Compile._IEndPoint,CausalMesh__ServerImpl__i_Compile.ServerImpl> _servers;
    public readonly Dafny.ISet<Native____Io__s_Compile._IEndPoint> _clients;
    public DS__State(Dafny.ISequence<Native____Io__s_Compile._IEndPoint> config, Environment__s_Compile._ILEnvironment<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>> environment, Dafny.IMap<Native____Io__s_Compile._IEndPoint,CausalMesh__ServerImpl__i_Compile.ServerImpl> servers, Dafny.ISet<Native____Io__s_Compile._IEndPoint> clients) {
      this._config = config;
      this._environment = environment;
      this._servers = servers;
      this._clients = clients;
    }
    public _IDS__State DowncastClone() {
      if (this is _IDS__State dt) { return dt; }
      return new DS__State(_config, _environment, _servers, _clients);
    }
    public override bool Equals(object other) {
      var oth = other as CM__DistributedSystem__i_Compile.DS__State;
      return oth != null && object.Equals(this._config, oth._config) && object.Equals(this._environment, oth._environment) && object.Equals(this._servers, oth._servers) && object.Equals(this._clients, oth._clients);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._config));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._environment));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._servers));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._clients));
      return (int) hash;
    }
    public override string ToString() {
      string s = "CM__DistributedSystem__i_Compile.DS_State.DS_State";
      s += "(";
      s += Dafny.Helpers.ToString(this._config);
      s += ", ";
      s += Dafny.Helpers.ToString(this._environment);
      s += ", ";
      s += Dafny.Helpers.ToString(this._servers);
      s += ", ";
      s += Dafny.Helpers.ToString(this._clients);
      s += ")";
      return s;
    }
    private static readonly CM__DistributedSystem__i_Compile._IDS__State theDefault = create(Dafny.Sequence<Native____Io__s_Compile._IEndPoint>.Empty, Environment__s_Compile.LEnvironment<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>>.Default(), Dafny.Map<Native____Io__s_Compile._IEndPoint, CausalMesh__ServerImpl__i_Compile.ServerImpl>.Empty, Dafny.Set<Native____Io__s_Compile._IEndPoint>.Empty);
    public static CM__DistributedSystem__i_Compile._IDS__State Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<CM__DistributedSystem__i_Compile._IDS__State> _TYPE = new Dafny.TypeDescriptor<CM__DistributedSystem__i_Compile._IDS__State>(CM__DistributedSystem__i_Compile.DS__State.Default());
    public static Dafny.TypeDescriptor<CM__DistributedSystem__i_Compile._IDS__State> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDS__State create(Dafny.ISequence<Native____Io__s_Compile._IEndPoint> config, Environment__s_Compile._ILEnvironment<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>> environment, Dafny.IMap<Native____Io__s_Compile._IEndPoint,CausalMesh__ServerImpl__i_Compile.ServerImpl> servers, Dafny.ISet<Native____Io__s_Compile._IEndPoint> clients) {
      return new DS__State(config, environment, servers, clients);
    }
    public static _IDS__State create_DS__State(Dafny.ISequence<Native____Io__s_Compile._IEndPoint> config, Environment__s_Compile._ILEnvironment<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>> environment, Dafny.IMap<Native____Io__s_Compile._IEndPoint,CausalMesh__ServerImpl__i_Compile.ServerImpl> servers, Dafny.ISet<Native____Io__s_Compile._IEndPoint> clients) {
      return create(config, environment, servers, clients);
    }
    public bool is_DS__State { get { return true; } }
    public Dafny.ISequence<Native____Io__s_Compile._IEndPoint> dtor_config {
      get {
        return this._config;
      }
    }
    public Environment__s_Compile._ILEnvironment<Native____Io__s_Compile._IEndPoint, Dafny.ISequence<byte>> dtor_environment {
      get {
        return this._environment;
      }
    }
    public Dafny.IMap<Native____Io__s_Compile._IEndPoint,CausalMesh__ServerImpl__i_Compile.ServerImpl> dtor_servers {
      get {
        return this._servers;
      }
    }
    public Dafny.ISet<Native____Io__s_Compile._IEndPoint> dtor_clients {
      get {
        return this._clients;
      }
    }
  }
} // end of namespace CM__DistributedSystem__i_Compile
namespace Main__i_Compile {

  public partial class __default {
    public static void _Main(Dafny.ISequence<Dafny.ISequence<char>> __noArgsParameter)
    {
      bool _436_ok;
      CausalMesh__ServerImpl__i_Compile.ServerImpl _437_host__state;
      Dafny.ISequence<Native____Io__s_Compile._IEndPoint> _438_config;
      Native____Io__s_Compile._IEndPoint _439_id;
      bool _out157;
      CausalMesh__ServerImpl__i_Compile.ServerImpl _out158;
      Dafny.ISequence<Native____Io__s_Compile._IEndPoint> _out159;
      Native____Io__s_Compile._IEndPoint _out160;
      Host__i_Compile.__default.HostInitImpl(out _out157, out _out158, out _out159, out _out160);
      _436_ok = _out157;
      _437_host__state = _out158;
      _438_config = _out159;
      _439_id = _out160;
      while (_436_ok) {
        bool _out161;
        CausalMesh__ServerImpl__i_Compile.ServerImpl _out162;
        Host__i_Compile.__default.HostNextImpl(_437_host__state, out _out161, out _out162);
        _436_ok = _out161;
        _437_host__state = _out162;
      }
    }
  }
} // end of namespace Main__i_Compile
namespace _module {

} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => Main__i_Compile.__default._Main(Dafny.Sequence<Dafny.ISequence<char>>.FromMainArguments(args)));
  }
}

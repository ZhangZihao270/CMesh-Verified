include "CTypes.dfy"
include "CMessage.dfy"
include "../Common/GenericMarshalling.i.dfy"

module CausalMesh_PacketParsing_i {
import opened Native__Io_s
import opened Native__NativeTypes_s
import opened Collections__Maps_i
import opened Common__GenericMarshalling_i
import opened Common__NodeIdentity_i
import opened Common__UdpClient_i
import opened Common__Util_i
// import opened AppStateMachine_s
import opened Environment_s
import opened Math__mul_i
import opened Math__mul_nonlinear_i
import opened CausalMesh_CTypes_i
import opened CausalMesh_CMessage_i
import opened CausalMesh_Types_i

function method EndPoint_grammar() : G { GUint64 }
function method CVectorClock_grammar() : G { GArray(GUint64) }
function method CDependency_grammar() : G { GArray(GTuple([GUint64, CVectorClock_grammar()]))}
function method CMeta_grammar() : G { GTuple([GUint64, CVectorClock_grammar(), CDependency_grammar()]) }
function method CLocal_grammar() : G { GArray(GTuple([GUint64, CMeta_grammar()])) }

function method CMessage_Read_grmamar() : G {GTuple([GUint64, GUint64, CDependency_grammar()])}
function method CMessage_ReadReply_grammar() : G {GTuple([GUint64, GUint64, CVectorClock_grammar(), CDependency_grammar()])}
function method CMessage_Write_grammar() : G {GTuple([GUint64, GUint64, CDependency_grammar(), CLocal_grammar(), CVectorClock_grammar()])}
function method CMessage_WriteReply_grammar() : G {GTuple([GUint64, GUint64, CVectorClock_grammar()])}
function method CMessage_Propagate_grammar() : G {GTuple([GUint64, CMeta_grammar(), GUint64, GUint64])}

function method CMessage_grammar() : G {GTaggedUnion([
    CMessage_Read_grmamar(),
    CMessage_ReadReply_grammar(),
    CMessage_Write_grammar(),
    CMessage_WriteReply_grammar(),
    CMessage_Propagate_grammar()
])}

method MarshallEndPoint(c:EndPoint) returns (val:V)
    requires EndPointIsValidIPV4(c)
    ensures  ValInGrammar(val, EndPoint_grammar())
    ensures  ValidVal(val)
    ensures  parse_EndPoint(val) == c
{
    // val := VByteArray(c.public_key);
    val := VUint64(ConvertEndPointToUint64(c));
    lemma_Uint64EndPointRelationships();
}

function method parse_EndPoint(val:V) : EndPoint
    requires ValInGrammar(val, EndPoint_grammar())
    ensures  EndPointIsAbstractable(parse_EndPoint(val))
{
    if val.u <= 0xffffffffffff then
        ConvertUint64ToEndPoint(val.u)
    else
        EndPoint([0,0,0,0], 0)
}

lemma {:axiom} lemma_VCLength(c:CVectorClock)
    ensures |c| < 0xffff_ffff_ffff_ffff

method MarshallCVectorClock(c:CVectorClock) returns (val:V)
    ensures ValInGrammar(val, CVectorClock_grammar())
{
    lemma_VCLength(c);
    assert |c| < 0xffff_ffff_ffff_ffff;
    var vcs := new V[|c| as uint64];

    var i:uint64 := 0;

    while i < |c| as uint64
        invariant 0 <= i as int <= |c|
        invariant forall j :: 0 <= j < i ==> ValInGrammar(vcs[j], CVectorClock_grammar().elt)
    {
        var single := 0;
        if 0 <= c[i] < 0xffff_ffff_ffff_ffff {
            single := c[i] as uint64;
        } else {
            single := 0xffff_ffff_ffff_ffff;
            print "Marshall CVectorClock overflow\n";
        }
        vcs[i] := VUint64(single);
        i := i + 1;
    }
    val := VArray(vcs[..]);
    assert ValInGrammar(val, CVectorClock_grammar());
}

function method parse_CVectorClock(val:V) : CVectorClock
    requires ValInGrammar(val, CVectorClock_grammar())
    decreases |val.a|
{
    assert val.VArray?;
    assert forall v :: v in val.a ==> ValInGrammar(v, CVectorClock_grammar().elt);
    assert forall i :: i in val.a ==> i.VUint64?;
    if |val.a| == 0 then
        []
    else 
        var c := val.a[0].u as int;
        var restVal:V := VArray(val.a[1..]);
        var rest := parse_CVectorClock(restVal);
        [c] + rest
}

predicate method Uint64InRange(i:int)
{
    0 <= i < 0xffff_ffff_ffff_ffff
}



predicate method CDependencyInRange(d:CDependency)
{
    forall k :: k in d ==> Uint64InRange(k)
}


method MarshallCDependency(d:CDependency) returns (val:V)
    ensures ValInGrammar(val, CDependency_grammar())
    decreases |d|
{
    if CDependencyInRange(d) {
        if |d| == 0 {
            val := VArray([]);
        } else {
            var k :| k in d;
            var kk := 0;
            if 0 <= k < 0xffff_ffff_ffff_ffff {
                kk := k as uint64;
            } else {
                kk := 0xffff_ffff_ffff_ffff;
                print "Marshall CDependency overflow\n";
            }
            var marshalled_k := VUint64(kk);
            var marshalled_vc := MarshallCVectorClock(d[k]);
            // assert ValInGrammar(marshalled_vc, )
            var remainder := RemoveElt(d, k);
            var marshalled_remainder := MarshallCDependency(remainder);
            assert ValInGrammar(marshalled_remainder, CDependency_grammar());
            assert ValInGrammar(VTuple([marshalled_k, marshalled_vc]), CDependency_grammar().elt);
            val := VArray([VTuple([marshalled_k, marshalled_vc])] + marshalled_remainder.a);
            assert ValInGrammar(val, CDependency_grammar());
        }
    } else {
        val := VArray([]);
        print "Marshall CDependency overflow\n";
    }
}


function method parse_CDependency(val:V) : CDependency
    requires ValInGrammar(val, CDependency_grammar())
    decreases |val.a|
{
    if |val.a| == 0 then
        map[]
    else
        var tuple := val.a[0];
        assert ValInGrammar(tuple, CDependency_grammar().elt);
        var k := tuple.t[0].u as int;
        var vc := parse_CVectorClock(tuple.t[1]);
        var others := parse_CDependency(VArray(val.a[1..]));
        var m := others[k := vc];
        m
}

method MarshallCMeta(m:CMeta) returns (val:V)
    ensures ValInGrammar(val, CMeta_grammar())
{
    var kk := 0;
    if 0 <= m.key < 0xffff_ffff_ffff_ffff {
        kk := m.key as uint64;
    } else {
        kk := 0xffff_ffff_ffff_ffff;
        print "Marshall CMeta overflow\n";
    }
    var marshalled_k := VUint64(kk);
    var marshalled_vc := MarshallCVectorClock(m.vc);
    assert ValInGrammar(marshalled_vc, CVectorClock_grammar());
    var marshalled_dep := MarshallCDependency(m.deps);
    assert ValInGrammar(marshalled_dep, CDependency_grammar());
    val := VTuple([marshalled_k, marshalled_vc, marshalled_dep]);
    assert ValInGrammar(val, CMeta_grammar());
}

function method parse_CMeta(val:V) : CMeta
    requires ValInGrammar(val, CMeta_grammar())
{
    assert ValInGrammar(val, CMeta_grammar());
    CMeta(val.t[0].u as int, parse_CVectorClock(val.t[1]), parse_CDependency(val.t[2]))
}


predicate method LocalInRange(d:map<int, CMeta>)
{
    forall k :: k in d ==> Uint64InRange(k)
}

method MarshallLocal(m:map<int, CMeta>) returns (val:V)
    ensures ValInGrammar(val, CLocal_grammar())
{
    if LocalInRange(m) {
        if |m| == 0 {
            val := VArray([]);
        } else {
            var k :| k in m;
            var kk := 0;
            if 0 <= k < 0xffff_ffff_ffff_ffff {
                kk := k as uint64;
            } else {
                kk := 0xffff_ffff_ffff_ffff;
                print "Marshall Local overflow\n";
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
        print "Marshall Local overflow\n";
    }
}


function method parse_Local(val:V) : map<int, CMeta>
    requires ValInGrammar(val, CLocal_grammar())
    decreases |val.a|
{
    if |val.a| == 0 then 
        map[]
    else 
        assert ValInGrammar(val, CLocal_grammar());
        var tuple := val.a[0];
        assert ValInGrammar(tuple, CLocal_grammar().elt);
        // assert ValInGrammar()
        var k := tuple.t[0].u as int;
        var m := parse_CMeta(tuple.t[1]);
        var others := parse_Local(VArray(val.a[1..]));
        var r := others[k := m];
        r
}

predicate method MsgReadInRange(c:CMessage)
    requires c.CMessage_Read?
{
    && Uint64InRange(c.opn_read)
    && Uint64InRange(c.key_read)
}

method MarshallRead(c:CMessage) returns (val:V)
    requires c.CMessage_Read?
    ensures ValInGrammar(val, CMessage_Read_grmamar())
{
    var opn:uint64 := 0;
    if 0 <= c.opn_read < 0xffff_ffff_ffff_ffff {
        opn := c.opn_read as uint64;
    } else {
        opn := 0xffff_ffff_ffff_ffff;
        print "Marshall Message Read overflow\n";
    }

    var kk:uint64 := 0;
    if 0 <= c.key_read < 0xffff_ffff_ffff_ffff {
        kk := c.key_read as uint64;
    } else {
        kk := 0xffff_ffff_ffff_ffff;
        print "Marshall Message Read overflow\n";
    }

    var deps := MarshallCDependency(c.deps_read);
    val := VTuple([VUint64(opn), VUint64(kk), deps]);
}

function method parse_Read(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Read_grmamar())
{
    assert ValInGrammar(val, CMessage_Read_grmamar());
    CMessage_Read(val.t[0].u as int, val.t[1].u as int, parse_CDependency(val.t[2]))
}

method MarshallReadReply(c:CMessage) returns (val:V)
    requires c.CMessage_Read_Reply?
    ensures ValInGrammar(val, CMessage_ReadReply_grammar())
{
    var opn:uint64 := 0;
    if 0 <= c.opn_rreply < 0xffff_ffff_ffff_ffff {
        opn := c.opn_rreply as uint64;
    } else {
        opn := 0xffff_ffff_ffff_ffff;
        print "Marshall Message Read Reply overflow\n";
    }

    var kk:uint64 := 0;
    if 0 <= c.key_rreply < 0xffff_ffff_ffff_ffff {
        kk := c.key_rreply as uint64;
    } else {
        kk := 0xffff_ffff_ffff_ffff;
        print "Marshall Message Read Reply overflow\n";
    }
    var vc := MarshallCVectorClock(c.vc_rreply);
    var deps := MarshallCDependency(c.deps_rreply);
    val := VTuple([VUint64(opn), VUint64(kk), vc, deps]);
}

function method parse_ReadReply(val:V) : CMessage
    requires ValInGrammar(val, CMessage_ReadReply_grammar())
{
    assert ValInGrammar(val, CMessage_ReadReply_grammar());
    CMessage_Read_Reply(val.t[0].u as int, val.t[1].u as int, parse_CVectorClock(val.t[2]), parse_CDependency(val.t[3]))
}

method MarshallWrite(c:CMessage) returns (val:V)
    requires c.CMessage_Write?
    ensures ValInGrammar(val, CMessage_Write_grammar())
{
    var opn:uint64 := 0;
    if 0 <= c.opn_write < 0xffff_ffff_ffff_ffff {
        opn := c.opn_write as uint64;
    } else {
        opn := 0xffff_ffff_ffff_ffff;
        print "Marshall Message Write overflow\n";
    }

    var kk:uint64 := 0;
    if 0 <= c.key_write < 0xffff_ffff_ffff_ffff {
        kk := c.key_write as uint64;
    } else {
        kk := 0xffff_ffff_ffff_ffff;
        print "Marshall Message Write overflow\n";
    }
    var local := MarshallLocal(c.local);
    var deps := MarshallCDependency(c.deps_write);
    var vc := MarshallCVectorClock(c.mvc);
    val := VTuple([VUint64(opn), VUint64(kk), deps, local, vc]);
}


function method parse_Write(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Write_grammar())
{
    assert ValInGrammar(val, CMessage_Write_grammar());
    CMessage_Write(val.t[0].u as int, val.t[1].u as int, parse_CDependency(val.t[2]), parse_Local(val.t[3]), parse_CVectorClock(val.t[4]))
}

method MarshallWriteReply(c:CMessage) returns (val:V)
    requires c.CMessage_Write_Reply?
    ensures ValInGrammar(val, CMessage_WriteReply_grammar())
{
    var opn:uint64 := 0;
    if 0 <= c.opn_wreply < 0xffff_ffff_ffff_ffff {
        opn := c.opn_wreply as uint64;
    } else {
        opn := 0xffff_ffff_ffff_ffff;
        print "Marshall Message Write Reply overflow\n";
    }

    var kk:uint64 := 0;
    if 0 <= c.key_wreply < 0xffff_ffff_ffff_ffff {
        kk := c.key_wreply as uint64;
    } else {
        kk := 0xffff_ffff_ffff_ffff;
        print "Marshall Message Write Reply overflow\n";
    }
    var vc := MarshallCVectorClock(c.vc_wreply);
    val := VTuple([VUint64(opn), VUint64(kk), vc]);
}

function method parse_WriteReply(val:V) : CMessage
    requires ValInGrammar(val, CMessage_WriteReply_grammar())
{
    assert ValInGrammar(val, CMessage_WriteReply_grammar());
    CMessage_Write_Reply(val.t[0].u as int, val.t[1].u as int, parse_CVectorClock(val.t[2]))
}


method MarshallPropagation(c:CMessage) returns (val:V)
    requires c.CMessage_Propagation?
    ensures ValInGrammar(val, CMessage_Propagate_grammar())
{
    var kk:uint64 := 0;
    if 0 <= c.key < 0xffff_ffff_ffff_ffff {
        kk := c.key as uint64;
    } else {
        kk := 0xffff_ffff_ffff_ffff;
        print "Marshall Message Propagation overflow\n";
    }
     
    var start:uint64 := 0;
    if 0 <= c.start < 0xffff_ffff_ffff_ffff {
        start := c.start as uint64;
    } else {
        start := 0xffff_ffff_ffff_ffff;
        print "Marshall Message Propagation overflow\n";
    }

    var round:uint64 := 0;
    if 0 <= c.round < 0xffff_ffff_ffff_ffff {
        round := c.round as uint64;
    } else {
        round := 0xffff_ffff_ffff_ffff;
        print "Marshall Message Propagation overflow\n";
    }

    var m := MarshallCMeta(c.meta);
    val := VTuple([VUint64(kk), m, VUint64(start), VUint64(round)]);
}


function method parse_Propagation(val:V) : CMessage
    requires ValInGrammar(val, CMessage_Propagate_grammar())
{
    assert ValInGrammar(val, CMessage_Propagate_grammar());
    CMessage_Propagation(val.t[0].u as int, parse_CMeta(val.t[1]), val.t[2].u as int, val.t[3].u as int)
}

function method parse_Message(val:V) : CMessage
    requires ValInGrammar(val, CMessage_grammar())
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
        assert false;
        parse_Read(val)
}

lemma {:axiom} lemma_DemarshallData(data:array<byte>, msg_grammar:G)
    ensures data.Length < 0x1_0000_0000_0000_0000
    ensures ValidGrammar(msg_grammar)

method DemarshallData(data:array<byte>, msg_grammar:G) returns (msg:CMessage)
    requires msg_grammar == CMessage_grammar()
    // requires ValidGrammar()
{
    lemma_DemarshallData(data, msg_grammar);
    assert data.Length < 0x1_0000_0000_0000_0000;
    assert ValidGrammar(msg_grammar);
    var success, val := Demarshall(data, msg_grammar);
    if success {
        assert ValInGrammar(val, msg_grammar);
        msg := parse_Message(val);
    } else {
        // msg := CMessage
        print "Parse message fail\n";
    }
}

method MarshallMessage(c:CMessage) returns (val:V)
    ensures ValInGrammar(val, CMessage_grammar())
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

lemma {:axiom} lemma_MarshallData(val:V)
    ensures ValidVal(val)
    ensures 0 <= SizeOfV(val) < 0x1_0000_0000_0000_0000

method MarshallData(msg:CMessage) returns (data:array<byte>)
{
    var val := MarshallMessage(msg);
    lemma_MarshallData(val);
    data := Marshall(val, CMessage_grammar());
}

}
include "../../Protocol/CausalMesh/message.dfy"
include "../Common/NodeIdentity.i.dfy"
include "CTypes.dfy"
include "../Common/GenericRefinement.i.dfy"
include "../../Common/Native/Io.s.dfy"
include "../../Common/Framework/Environment.s.dfy"

module CausalMesh_CMessage_i {
import opened CausalMesh_CTypes_i
import opened CausalMesh_Message_i
import opened GenericRefinement_i
import opened Common__NodeIdentity_i
import opened Native__Io_s
import opened Environment_s
import opened CausalMesh_Types_i

datatype CMessage = 
CMessage_Read(
    opn_read: int, 
    key_read: CKey, 
    deps_read: CDependency
)
    | 
CMessage_Read_Reply(
    opn_rreply: int, 
    key_rreply: CKey, 
    vc_rreply: CVectorClock, 
    deps_rreply: CDependency
)
    | 
CMessage_Write(
    opn_write: int, 
    key_write: CKey, 
    deps_write: CDependency, 
    local: map<CKey, CMeta>,
    mvc: CVectorClock
)
    | 
CMessage_Write_Reply(
    opn_wreply: int, 
    key_wreply: CKey, 
    vc_wreply: CVectorClock
)
    | 
CMessage_Propagation(
    key: CKey, 
    meta: CMeta, 
    start: int, 
    round: int
)

predicate WriteMessageHasMVCLargerThanAllDepsAndLocals(s:CMessage)
    requires s.CMessage_Write?
    // requires 
    requires CDependencyValid(s.deps_write)
    requires forall i :: i in s.local ==> CMetaValid(s.local[i])
    requires CVectorClockValid(s.mvc)
{
    && (forall k :: k in s.deps_write ==> CVCEq(s.deps_write[k], s.mvc) || CVCHappendsBefore(s.deps_write[k], s.mvc))
    && (forall k :: k in s.local ==> CVCEq(s.local[k].vc, s.mvc) || CVCHappendsBefore(s.local[k].vc, s.mvc))
}

predicate WriteMessageDepsContainsLocal(s:CMessage)
    requires s.CMessage_Write?
    requires CDependencyValid(s.deps_write)
    requires forall i :: i in s.local ==> CMetaValid(s.local[i])
{
    forall k :: k in s.local ==> k in s.deps_write && (CVCEq(s.local[k].vc, s.deps_write[k]) || CVCHappendsBefore(s.local[k].vc, s.deps_write[k]))
}

predicate CMessageIsValid(s: CMessage) 
{
    match s
    case CMessage_Read(opn_read, key_read, deps_read) => CMessageIsAbstractable(s) && CKeyIsValid(s.key_read) && CDependencyIsValid(s.deps_read)
    case CMessage_Read_Reply(opn_rreply, key_rreply, vc_rreply, deps_rreply) => CMessageIsAbstractable(s) && CKeyIsValid(s.key_rreply) && CVectorClockIsValid(s.vc_rreply) && CDependencyIsValid(s.deps_rreply)
    case CMessage_Write(opn_write, key_write, deps_write, local, mvc) => CMessageIsAbstractable(s) && CKeyIsValid(s.key_write) && CDependencyIsValid(s.deps_write) && CVectorClockIsValid(s.mvc) && (forall i :: i in s.local ==> CKeyIsValid(i) && CMetaIsValid(s.local[i]))
    case CMessage_Write_Reply(opn_wreply, key_wreply, vc_wreply) => CMessageIsAbstractable(s) && CKeyIsValid(s.key_wreply) && CVectorClockIsValid(s.vc_wreply)
    case CMessage_Propagation(key, meta, start, round) => CMessageIsAbstractable(s) && CKeyIsValid(s.key) && CMetaIsValid(s.meta)

}

predicate CMessageIsAbstractable(s: CMessage) 
{
    match s
    case CMessage_Read(opn_read, key_read, deps_read) => CKeyIsAbstractable(s.key_read) && CDependencyIsAbstractable(s.deps_read)
    case CMessage_Read_Reply(opn_rreply, key_rreply, vc_rreply, deps_rreply) => CKeyIsAbstractable(s.key_rreply) && CVectorClockIsAbstractable(s.vc_rreply) && CDependencyIsAbstractable(s.deps_rreply)
    case CMessage_Write(opn_write, key_write, deps_write, local, mvc) => CKeyIsAbstractable(s.key_write) && CDependencyIsAbstractable(s.deps_write) && CVectorClockIsAbstractable(s.mvc) && (forall i :: i in s.local ==> CKeyIsAbstractable(i) && CMetaIsAbstractable(s.local[i]))
    case CMessage_Write_Reply(opn_wreply, key_wreply, vc_wreply) => CKeyIsAbstractable(s.key_wreply) && CVectorClockIsAbstractable(s.vc_wreply)
    case CMessage_Propagation(key, meta, start, round) => CKeyIsAbstractable(s.key) && CMetaIsAbstractable(s.meta)

}

function AbstractifyCMessageToMessage(s: CMessage) : Message 
    requires CMessageIsAbstractable(s)
{
    match s
    case CMessage_Read(opn_read, key_read, deps_read) => Message_Read(s.opn_read, AbstractifyCKeyToKey(s.key_read), AbstractifyCDependencyToDependency(s.deps_read))
    case CMessage_Read_Reply(opn_rreply, key_rreply, vc_rreply, deps_rreply) => Message_Read_Reply(s.opn_rreply, AbstractifyCKeyToKey(s.key_rreply), AbstractifyCVectorClockToVectorClock(s.vc_rreply), AbstractifyCDependencyToDependency(s.deps_rreply))
    case CMessage_Write(opn_write, key_write, deps_write, local, mvc) => Message_Write(s.opn_write, AbstractifyCKeyToKey(s.key_write), AbstractifyCDependencyToDependency(s.deps_write), AbstractifyMap(s.local, AbstractifyCKeyToKey, AbstractifyCMetaToMeta, AbstractifyCKeyToKey))
    case CMessage_Write_Reply(opn_wreply, key_wreply, vc_wreply) => Message_Write_Reply(s.opn_wreply, AbstractifyCKeyToKey(s.key_wreply), AbstractifyCVectorClockToVectorClock(s.vc_wreply))
    case CMessage_Propagation(key, meta, start, round) => Message_Propagation(AbstractifyCKeyToKey(s.key), AbstractifyCMetaToMeta(s.meta), s.start, s.round)

}

predicate CMessageValid(m:CMessage)
{
    match m 
        // case Message_Invalid() => true
        case CMessage_Read(_,key_read, deps_read) => key_read in Keys_domain && CDependencyValid(deps_read)
        case CMessage_Read_Reply(_,key_rreply, vc_rreply, deps_rreply) => key_rreply in Keys_domain && CVectorClockValid(vc_rreply) && CDependencyValid(deps_rreply) 
        case CMessage_Write(_,key_write, deps_write, local, mvc) => key_write in Keys_domain && CDependencyValid(deps_write) && CVectorClockValid(mvc) && (forall k :: k in local ==> CMetaValid(local[k]) && local[k].key == k) && WriteMessageDepsContainsLocal(m) && WriteMessageHasMVCLargerThanAllDepsAndLocals(m)
        case CMessage_Write_Reply(_,key_wreply, vc_wreply) => key_wreply in Keys_domain && CVectorClockValid(vc_wreply) 
        case CMessage_Propagation(key, meta, start, round) => key in Keys_domain && (CMetaValid(meta) && meta.key == key) && 0 <= start < Nodes
}

datatype CPacket = CPacket(dst:EndPoint, src:EndPoint, msg:CMessage)

predicate CPacketIsValid(cp:CPacket)
{
    && CPacketIsAbstractable(cp)
    && CMessageIsValid(cp.msg)
    && EndPointIsValid(cp.src)
    && EndPointIsValid(cp.dst)
}

predicate CPacketIsAbstractable(cp:CPacket)
{
    && CMessageIsAbstractable(cp.msg)
    && EndPointIsAbstractable(cp.src)
    && EndPointIsAbstractable(cp.dst)
}

function AbstractifyCPacketToPacket(cp: CPacket): Packet
requires CPacketIsAbstractable(cp)
{
    LPacket(AbstractifyEndPointToID(cp.dst), AbstractifyEndPointToID(cp.src), AbstractifyCMessageToMessage(cp.msg))
}

function AbstractifyCPacketSeq(s:seq<CPacket>) : seq<Packet>
requires forall i :: 0 <= i < |s| ==> CPacketIsAbstractable(s[i])
ensures var cs := AbstractifyCPacketSeq(s);
        &&  |cs| == |s|
        &&  (forall i :: 0 <= i < |s| ==> cs[i] == AbstractifyCPacketToPacket(s[i]))
        && (forall i :: i in cs ==> exists x :: x in s && i == AbstractifyCPacketToPacket(x))
{
    var cs := if |s| == 0 then
                []
                else
                [AbstractifyCPacketToPacket(s[0])] + AbstractifyCPacketSeq(s[1..]);
    cs
}

predicate CPacketValid(p:CPacket)
{
    && CMessageValid(p.msg)
}

function AbstractifyEndPointToID(endpoint:EndPoint) : int
    // requires EndPointIsAbstractable(endpoint)
{
    endpoint.port as int
}


}
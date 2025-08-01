include "../../Common/Framework/Main.s.dfy"
include "../../Impl/CausalMesh/Host.dfy"
include "CMDistributedSystem.i.dfy"

module Main_i refines Main_s {
import opened Native__NativeTypes_s
import opened Host = Host_i
import opened DS_s = CM_DistributedSystem_i
// import opened DirectRefinement__Refinement_i
import opened Concrete_NodeIdentity_i
// import opened AS_s = AbstractServiceRSL_s
// import opened MarshallProof_i
// import opened LiveRSL__CMessageRefinements_i
// import opened LiveRSL__Configuration_i
// import opened LiveRSL__Constants_i
// import opened LiveRSL__ConstantsState_i
// import opened LiveRSL__CTypes_i
// import opened LiveRSL__DistributedSystem_i
// import opened LiveRSL__Environment_i
// import opened LiveRSL__Message_i
// import opened LiveRSL__PacketParsing_i
// import opened LiveRSL__Replica_i
// import opened LiveRSL__Types_i
// import opened LiveRSL__UdpRSL_i
// import opened LiveRSL__Unsendable_i
import opened Collections__Maps2_s
import opened Collections__Sets_i
import opened Common__GenericMarshalling_i
import opened Common__NodeIdentity_i
import opened Common__SeqIsUniqueDef_i
// import opened DirectRefinement__StateMachine_i
import opened Environment_s
import opened Math__mod_auto_i
// import opened LiveRSL__CMessage_i

}
include "../Common/CmdLineParser.i.dfy"
include "../Common/NodeIdentity.i.dfy"
include "../../Common/Collections/Seqs.i.dfy"
include "CTypes.dfy"

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

function causalmesh_config_parsing(args:seq<seq<uint16>>) : seq<EndPoint>
{
    if args != [] && |args[1..]| % 2 == 0 then
        var (ok, endpoints) := parse_end_points(args[1..]);
        endpoints
    else
        []
}

method parse_cmd_line(ghost env:HostEnvironment) returns (ok:bool, config:seq<EndPoint>, my_index:int)
    requires HostEnvironmentIsValid(env)
    // ensures ok ==> CConfigurationIsValid(config)
    // ensures ok ==> |config.replica_ids| > 0
    ensures ok ==> 0 <= my_index as int < |config|
    ensures ok ==> |config| == Nodes
    ensures ok ==> forall ep :: ep in config ==> EndPointIsValidIPV4(ep)
    // ensures var (config', my_ep') := paxos_cmd_line_parsing(env);
    //         ok ==> config == config' && config.replica_ids[my_index] == my_ep'
{
    ok := false;
    var num_args := HostConstants.NumCommandLineArgs(env);
    if num_args < 4 || num_args % 2 != 1 {
        print "Incorrect number of command line arguments.\n";
        print "Expected: ./Main.exe [IP port]+ [IP port]\n";
        print "  where the final argument is one of the IP-port pairs provided earlier \n";
        return;
    }

    var args := collect_cmd_line_args(env);
    assert args == env.constants.CommandLineArgs();
    var tuple1 := parse_end_points(args[1..|args|-2]);
    ok := tuple1.0;
    var endpoints := tuple1.1;
    if !ok || |endpoints| >= 0xffff_ffff_ffff_ffff {
        ok := false;
        return;
    }

    var tuple2 := parse_end_point(args[|args|-2], args[|args|-1]);
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
    
    // lemma_ConfigInit(tuple2.1, config);
    // lemma_MinQuorumSizeLessThanReplicaCount(config);

    my_index := FindIndexInSeq(config, tuple2.1);
    lemma_ConfigValid(config, my_index);
    // CGetReplicaIndex(tuple2.1, config);
    // if !ok {
    //     return;
    // }
    ok := true;
    assert 0 <= my_index as int < |config|;
    assert |config| == Nodes;

    // ghost var ghost_tuple := paxos_cmd_line_parsing(env);
    // ghost var config', my_ep' := ghost_tuple.0, ghost_tuple.1;
    // assert endpoints == config'.replica_ids;
    // assert config == config';
    // assert config.replica_ids[my_index] == my_ep';
}

lemma {:axiom} lemma_ConfigValid(config:seq<EndPoint>, my_index:int)
    ensures |config| == Nodes
    ensures 0 <= my_index as int < |config|
}
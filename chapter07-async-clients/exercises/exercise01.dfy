//#title KV Spec with Asynchronous Client Interface
//#desc Modify the KV spec to encode asynchronous client requests.

// You are given datatypes to represent outstanding requests and completed
// replies waiting to be delivered to the client. Your task is to fill out the
// action predicates to model the asynchronous arrival of requests,
// serialization (moment of processing) points, and delivery of replies.

// You'll re-use your chapter06 protocol here, but the main focus is to modify
// the spec to capture linearizability, a property that arises because client
// requests take time to process.

// You'll also construct specific execution traces that demonstrate specific
// concurrent and sequential executions.

include "UtilitiesLibrary.dfy"

// See chapter06-refine/exercises/exercise01 for documentation on this module.
// (Here we give concrete types because we want to instantiate the module for
// pseudoliveness tests at the end.)
module Types {
  type Key = string

  function AllKeys() : set<Key>
  {
    { "cat", "dog", "bird", "elephant" }
  }

  type Value = int

  function DefaultValue() : Value { 0 }

  function InitialMap() : map<Key, Value>
  {
    map key | key in AllKeys() :: DefaultValue()
  }

  // The Input and Output types describe the application-visible interface to the service.
  type Nonce = nat
  // The application chooses a nonce (so it can identify which replies belong to it --
  // think something like an RPC ID), and fills in the input parameters. The output reply
  // has a copy of the input (so the app can check the nonce) and any output result
  // (e.g. the value of a query).
  datatype Input =
    | InsertRequest(nonce:Nonce, key:Key, value:Value)
    | QueryRequest(nonce:Nonce, key:Key)

  datatype Output =
    | InsertReply(request: Input)
    | QueryReply(request: Input, output: Value)
}

// This module defines a Map state machine that serves as the system specification.
// In separate steps it should collect input requests from the client, service
// them atomically, then deliver output replies. Requests that are outstanding
// simultaneously can be serviced in any order (since the spec can
// nondeterministically select the order to service them); requests that don't
// overlap must affect each other in temporal order (linearizability).

module MapSpec {
  import opened Types
  import opened UtilitiesLibrary

  datatype Variables = Variables(mapp:map<Key, Value>,
    requests:set<Input>, replies:set<Output>)

  predicate Init(v: Variables)
  {
    && v.mapp == InitialMap()
/*{*/
    // Initialize the rest of the state here
/*}*/
  }

  predicate AcceptRequest(v:Variables, v':Variables, request: Input)
  {
/*{*/
    false // Define this predicate
/*}*/
  }

  predicate DeliverReply(v:Variables, v':Variables, reply: Output)
  {
/*{*/
    false // Define this predicate
/*}*/
  }

  predicate InsertOp(v:Variables, v':Variables, request: Input)
  {
/*{*/
    false // Replace me. Reference InsertOp from exercise 1 in chapter 6.
/*}*/
  }

  predicate QueryOp(v:Variables, v':Variables, request: Input, output: Value)
  {
/*{*/
    false // Replace me. Reference QueryOp from exercise 1 in chapter 6.
/*}*/
  }

  datatype Step =
    | AcceptRequestStep(request:Input)
    | DeliverReplyStep(reply: Output)
    | InsertOpStep(request:Input)
    | QueryOpStep(request:Input, output:Value)
    | NoOpStep()

  predicate NextStep(v: Variables, v': Variables, step:Step)
  {
    match step
      case AcceptRequestStep(request) => AcceptRequest(v, v', request)
      case DeliverReplyStep(reply) => DeliverReply(v, v', reply)
      case InsertOpStep(request) => InsertOp(v, v', request)
      case QueryOpStep(request, output) => QueryOp(v, v', request, output)
      case NoOpStep => v' == v
  }

  predicate Next(v: Variables, v': Variables)
  {
    exists step :: NextStep(v, v', step)
  }

  // Here are some point tests to confirm that the protocol allows various
  // desired behavior: two possible resulting states for executions with
  // overlapping insert requests, and one possible state for an execution with
  // non-overlapping insert requests.

  // We'll materialize behaviors explicitly (as a sequence of states) so we can
  // goof around with proofs about what this spec might say.
  predicate ValidBehavior(execution:seq<Variables>, steps:seq<Step>)
  {
    && |execution| == |steps| + 1
    && Init(execution[0])
    && (forall i | 0<=i<|steps| :: NextStep(execution[i], execution[i+1], steps[i]))
  }

  // Show a pair of executions that both start out with
  // concurrently-outstanding requests, and which produce different results.
  lemma PseudoLiveness1()
  {
    var req3 := InsertRequest(100, "cat", 3);
    var req4 := InsertRequest(101, "cat", 4);

    var executionA:seq<Variables> := [
/*{*/
/*}*/
      ];
    // At step 2 of the execution, both requests should be outstanding
    // simultaneously.
    assert executionA[2] == Variables(InitialMap(), {req3, req4}, {});
    // req3 is the last writer for executionA
    assert Last(executionA) == Variables(InitialMap()["cat" := 3], {}, {});

    // We'll need Step witnesses for ValidBehavior
    var stepsA := [
/*{*/
/*}*/
      ];
    assert ValidBehavior(executionA, stepsA);

    var executionB:seq<Variables> := [
/*{*/
/*}*/
      ];

    // At step 2 of the execution, both requests should be outstanding
    // simultaneously.
    assert executionB[2] == Variables(InitialMap(), {req3, req4}, {});
    // req4 is the last writer for executionB
    assert Last(executionB) == Variables(InitialMap()["cat" := 4], {}, {});

    var stepsB := [
/*{*/
/*}*/
      ];
    assert ValidBehavior(executionB, stepsB);
  }

  // Show an execution in which one request completes before the other; only
  // one outcome is possible.
  lemma PseudoLiveness2()
  {
    var req3 := InsertRequest(100, "cat", 3);
    var req4 := InsertRequest(101, "cat", 4);

    var executionC:seq<Variables> := [
/*{*/
/*}*/
      ];

    // At which index can we see that req3 is completed?
    var req3DoneIndex := /*{*/ -1 /*}*/;
    assert executionC[req3DoneIndex].requests == {};
    assert executionC[req3DoneIndex].replies == {InsertReply(req3)};

    // At which later index can we see that req4 is submitted?
    var req4BeginsIndex := /*{*/ -1 /*}*/;
    assert req3DoneIndex < req4BeginsIndex;
    assert executionC[req4BeginsIndex].requests == {req4};
    assert executionC[req4BeginsIndex].replies == {};

    // When the execution completes, req4 was the last writer.
    assert Last(executionC) == Variables(InitialMap()["cat" := 4], {}, {});

    var stepsC := [
/*{*/
/*}*/
      ];
    assert ValidBehavior(executionC, stepsC);
  }
}





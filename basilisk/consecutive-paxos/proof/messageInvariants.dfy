/// This file is auto-generated from /Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/basilisk/paxosBB/automate_gen2/distributedSystem.dfy
/// Generated 05/24/2025 20:52 Pacific Standard Time
include "../spec/spec.dfy"

module MessageInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem

// All msg have a valid source
ghost predicate ValidMessages(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall msg | msg in v.network.sentMsgs
  ::
  if msg.Prepare? then 0 <= msg.Src() < |c.leaders|
  else if msg.Propose? then 0 <= msg.Src() < |c.leaders|
  else if msg.Promise? then 0 <= msg.Src() < |c.acceptors|
  else if msg.Accept? then 0 <= msg.Src() < |c.acceptors|
  else true
}

ghost predicate {:opaque} ExistingMessage(v: Variables, msg: Message) {
  msg in v.network.sentMsgs
}

ghost predicate SendPrepareValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Prepare?
  ::
  (exists i ::
    && v.ValidHistoryIdxStrict(i)
    && LeaderHost.SendPrepare(c.leaders[msg.Src()], v.History(i).leaders[msg.Src()], v.History(i+1).leaders[msg.Src()], msg)
  )
}

ghost predicate SendProposeValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Propose?
  ::
  (exists i ::
    && v.ValidHistoryIdxStrict(i)
    && LeaderHost.SendPropose(c.leaders[msg.Src()], v.History(i).leaders[msg.Src()], v.History(i+1).leaders[msg.Src()], msg)
  )
}

ghost predicate SendPromiseValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Promise?
  ::
  SendPromiseValidityBody(c, v, msg)
}

ghost predicate SendPromiseValidityBody(c: Constants, v: Variables, msg: Message)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires msg in v.network.sentMsgs
  requires msg.Promise?
{
  exists i, inMsg ::
    && v.ValidHistoryIdxStrict(i)
    && ExistingMessage(v, inMsg)
    && AcceptorHost.ReceivePrepareSendPromise(c.acceptors[msg.Src()], v.History(i).acceptors[msg.Src()], v.History(i+1).acceptors[msg.Src()], inMsg, msg)
}

ghost predicate SendAcceptValidity(c: Constants, v: Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
{
  forall msg | msg in v.network.sentMsgs && msg.Accept?
  ::
  SendAcceptValidityBody(c, v, msg)
}

ghost predicate SendAcceptValidityBody(c: Constants, v: Variables, msg: Message)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires msg in v.network.sentMsgs
  requires msg.Accept?
{
  exists i, inMsg ::
    && v.ValidHistoryIdxStrict(i)
    && ExistingMessage(v, inMsg)
    && AcceptorHost.ReceiveProposeSendAccept(c.acceptors[msg.Src()], v.History(i).acceptors[msg.Src()], v.History(i+1).acceptors[msg.Src()], inMsg, msg)
}

ghost predicate {:opaque} LeaderHostReceiveValidity(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i |
    && v.ValidHistoryIdx(i)
    && 0 <= idx < |c.leaders|
    && v.History(i).leaders[idx] !=  v.History(0).leaders[idx]
  ::
     (exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).leaders[idx] != v.History(j+1).leaders[idx])
       && (v.History(j+1).leaders[idx] == v.History(i).leaders[idx])
       && LeaderHost.NextStep(c.leaders[idx], v.History(j).leaders[idx], v.History(j+1).leaders[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
     )
}

ghost predicate {:opaque} LeaderHostReceiveValidityPost(c: Constants, v: Variables, i: nat, idx: int)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.leaders|
{
    exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).leaders[idx] != v.History(j+1).leaders[idx])
       && (v.History(j+1).leaders[idx] == v.History(i).leaders[idx])
       && LeaderHost.NextStep(c.leaders[idx], v.History(j).leaders[idx], v.History(j+1).leaders[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
}

ghost predicate {:opaque} AcceptorHostReceiveValidity(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i |
    && v.ValidHistoryIdx(i)
    && 0 <= idx < |c.acceptors|
    && v.History(i).acceptors[idx] !=  v.History(0).acceptors[idx]
  ::
     (exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).acceptors[idx] != v.History(j+1).acceptors[idx])
       && (v.History(j+1).acceptors[idx] == v.History(i).acceptors[idx])
       && AcceptorHost.NextStep(c.acceptors[idx], v.History(j).acceptors[idx], v.History(j+1).acceptors[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
     )
}

ghost predicate {:opaque} AcceptorHostReceiveValidityPost(c: Constants, v: Variables, i: nat, idx: int)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.acceptors|
{
    exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).acceptors[idx] != v.History(j+1).acceptors[idx])
       && (v.History(j+1).acceptors[idx] == v.History(i).acceptors[idx])
       && AcceptorHost.NextStep(c.acceptors[idx], v.History(j).acceptors[idx], v.History(j+1).acceptors[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
}

ghost predicate {:opaque} LearnerHostReceiveValidity(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i |
    && v.ValidHistoryIdx(i)
    && 0 <= idx < |c.learners|
    && v.History(i).learners[idx] !=  v.History(0).learners[idx]
  ::
     (exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).learners[idx] != v.History(j+1).learners[idx])
       && (v.History(j+1).learners[idx] == v.History(i).learners[idx])
       && LearnerHost.NextStep(c.learners[idx], v.History(j).learners[idx], v.History(j+1).learners[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
     )
}

ghost predicate {:opaque} LearnerHostReceiveValidityPost(c: Constants, v: Variables, i: nat, idx: int)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.learners|
{
    exists j, step, msgOps ::
       && 0 <= j < i
       && (v.History(j).learners[idx] != v.History(j+1).learners[idx])
       && (v.History(j+1).learners[idx] == v.History(i).learners[idx])
       && LearnerHost.NextStep(c.learners[idx], v.History(j).learners[idx], v.History(j+1).learners[idx], step, msgOps)
       && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs)
}

ghost predicate MessageInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && ValidVariables(c, v)
  && ValidMessages(c, v)
  && SendPrepareValidity(c, v)
  && SendProposeValidity(c, v)
  && SendPromiseValidity(c, v)
  && SendAcceptValidity(c, v)
  && LeaderHostReceiveValidity(c, v)
  && AcceptorHostReceiveValidity(c, v)
  && LearnerHostReceiveValidity(c, v)
}

// Base obligation
lemma InitImpliesMessageInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MessageInv(c, v)
{
  InitImpliesValidVariables(c, v);
  reveal_LeaderHostReceiveValidity();
  reveal_AcceptorHostReceiveValidity();
  reveal_LearnerHostReceiveValidity();
}

// Inductive obligation
lemma MessageInvInductive(c: Constants, v: Variables, v': Variables)
  requires MessageInv(c, v)
  requires Next(c, v, v')
  ensures MessageInv(c, v')

{
  InvNextValidVariables(c, v, v');
  InvNextSendPrepareValidity(c, v, v');
  InvNextSendProposeValidity(c, v, v');
  InvNextSendPromiseValidity(c, v, v');
  InvNextSendAcceptValidity(c, v, v');
  InvNextLeaderHostReceiveValidity(c, v, v');
  InvNextAcceptorHostReceiveValidity(c, v, v');
  InvNextLearnerHostReceiveValidity(c, v, v');
}

/***************************************************************************************
*                                     Aux Proofs                                       *
***************************************************************************************/

lemma InvNextSendPrepareValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendPrepareValidity(c, v)
  requires Next(c, v, v')
  ensures SendPrepareValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Prepare?
  ensures
  (exists i ::
    && v'.ValidHistoryIdxStrict(i)
    && LeaderHost.SendPrepare(c.leaders[msg.Src()], v'.History(i).leaders[msg.Src()], v'.History(i+1).leaders[msg.Src()], msg)
  ) {
    VariableNextProperties(c, v, v');
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert LeaderHost.SendPrepare(c.leaders[msg.Src()], v'.History(i).leaders[msg.Src()], v'.History(i+1).leaders[msg.Src()], msg);
    }
  }
}

lemma InvNextSendProposeValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendProposeValidity(c, v)
  requires Next(c, v, v')
  ensures SendProposeValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Propose?
  ensures
  (exists i ::
    && v'.ValidHistoryIdxStrict(i)
    && LeaderHost.SendPropose(c.leaders[msg.Src()], v'.History(i).leaders[msg.Src()], v'.History(i+1).leaders[msg.Src()], msg)
  ) {
    VariableNextProperties(c, v, v');
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      assert LeaderHost.SendPropose(c.leaders[msg.Src()], v'.History(i).leaders[msg.Src()], v'.History(i+1).leaders[msg.Src()], msg);
    }
  }
}

lemma InvNextSendPromiseValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendPromiseValidity(c, v)
  requires Next(c, v, v')
  ensures SendPromiseValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Promise?
  ensures SendPromiseValidityBody(c, v', msg)
  {
    VariableNextProperties(c, v, v');
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var inMsg := dsStep.msgOps.recv.value;
      assert AcceptorHost.ReceivePrepareSendPromise(c.acceptors[msg.Src()], v'.History(i).acceptors[msg.Src()], v'.History(i+1).acceptors[msg.Src()], inMsg, msg);
      assert ExistingMessage(v', inMsg) by {
        reveal_ExistingMessage();
      }
    } else {
      // witness and trigger
      var i, inMsg :| v.ValidHistoryIdxStrict(i) && ExistingMessage(v, inMsg) && AcceptorHost.ReceivePrepareSendPromise(c.acceptors[msg.Src()], v.History(i).acceptors[msg.Src()], v.History(i+1).acceptors[msg.Src()], inMsg, msg);
      assert ExistingMessage(v', inMsg) by {
        reveal_ExistingMessage();
      }
    }
  }
}

lemma InvNextSendAcceptValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendAcceptValidity(c, v)
  requires Next(c, v, v')
  ensures SendAcceptValidity(c, v')
{
  forall msg | msg in v'.network.sentMsgs && msg.Accept?
  ensures SendAcceptValidityBody(c, v', msg)
  {
    VariableNextProperties(c, v, v');
    if msg !in v.network.sentMsgs {
      // witness and trigger
      var i := |v.history|-1;
      var dsStep :| NextStep(c, v.Last(), v'.Last(), v.network, v'.network, dsStep);
      var inMsg := dsStep.msgOps.recv.value;
      assert AcceptorHost.ReceiveProposeSendAccept(c.acceptors[msg.Src()], v'.History(i).acceptors[msg.Src()], v'.History(i+1).acceptors[msg.Src()], inMsg, msg);
      assert ExistingMessage(v', inMsg) by {
        reveal_ExistingMessage();
      }
    } else {
      // witness and trigger
      var i, inMsg :| v.ValidHistoryIdxStrict(i) && ExistingMessage(v, inMsg) && AcceptorHost.ReceiveProposeSendAccept(c.acceptors[msg.Src()], v.History(i).acceptors[msg.Src()], v.History(i+1).acceptors[msg.Src()], inMsg, msg);
      assert ExistingMessage(v', inMsg) by {
        reveal_ExistingMessage();
      }
    }
  }
}

lemma LeaderHostReceiveSkolemization(c: Constants, v: Variables, i: nat, idx: int)
returns (j: nat, step: LeaderHost.Step, msgOps: MessageOps)
  requires v.WF(c)
  requires LeaderHostReceiveValidity(c, v)
  requires 0 <= idx < |c.leaders|
  requires v.ValidHistoryIdx(i)
  requires v.History(i).leaders[idx] != v.History(0).leaders[idx]
  ensures v.ValidHistoryIdxStrict(j)
  ensures 0 <= j < i 
  ensures v.History(j).leaders[idx] != v.History(j+1).leaders[idx]
  ensures v.History(j+1).leaders[idx] == v.History(i).leaders[idx]
  ensures LeaderHost.NextStep(c.leaders[idx], v.History(j).leaders[idx], v.History(j+1).leaders[idx], step, msgOps)
  ensures msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs
{
  reveal_LeaderHostReceiveValidity();
  j, step, msgOps :|
      && 0 <= j < i
      && (v.History(j).leaders[idx] != v.History(j+1).leaders[idx])
      && (v.History(j+1).leaders[idx] == v.History(i).leaders[idx])
      && LeaderHost.NextStep(c.leaders[idx], v.History(j).leaders[idx], v.History(j+1).leaders[idx], step, msgOps)
      && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs);
}

lemma InvNextLeaderHostReceiveValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires LeaderHostReceiveValidity(c, v)
  requires Next(c, v, v')
  ensures LeaderHostReceiveValidity(c, v')
{
  forall idx, i |
    && v'.ValidHistoryIdx(i)
    && 0 <= idx < |c.leaders|
    && v'.History(i).leaders[idx] != v'.History(0).leaders[idx]
  ensures
    LeaderHostReceiveValidityPost(c, v', i, idx)
  {
    VariableNextProperties(c, v, v');
    if v'.ValidHistoryIdxStrict(i) {
      assert LeaderHostReceiveValidityPost(c, v', i, idx) by {
       reveal_LeaderHostReceiveValidity();
       reveal_LeaderHostReceiveValidityPost();
      }
    } else {
      if v'.History(i-1).leaders[idx] == v'.History(i).leaders[idx] {
        var k, step, msgOps := LeaderHostReceiveSkolemization(c, v, i-1, idx);
        // triggers
        assert 0 <= k < i;
        assert v'.History(k).leaders[idx] != v'.History(k+1).leaders[idx];
        assert v'.History(k+1).leaders[idx] == v'.History(i).leaders[idx];
        assert LeaderHost.NextStep(c.leaders[idx], v'.History(k).leaders[idx], v'.History(k+1).leaders[idx], step, msgOps);
      } else {
        // triggers
        assert v'.History(i-1).leaders[idx] != v'.History(i).leaders[idx];
        var j := i-1;
        assert 0 <= j < i;
        assert j + 1 == i;
        assert v'.History(j+1).leaders[idx] == v'.History(i).leaders[idx];
      }
      assert LeaderHostReceiveValidityPost(c, v', i, idx) by {
       reveal_LeaderHostReceiveValidity();
       reveal_LeaderHostReceiveValidityPost();
      }
    }
  }
  assert LeaderHostReceiveValidity(c, v') by {
    reveal_LeaderHostReceiveValidity();
    reveal_LeaderHostReceiveValidityPost();
  }
}

lemma AcceptorHostReceiveSkolemization(c: Constants, v: Variables, i: nat, idx: int)
returns (j: nat, step: AcceptorHost.Step, msgOps: MessageOps)
  requires v.WF(c)
  requires AcceptorHostReceiveValidity(c, v)
  requires 0 <= idx < |c.acceptors|
  requires v.ValidHistoryIdx(i)
  requires v.History(i).acceptors[idx] != v.History(0).acceptors[idx]
  ensures v.ValidHistoryIdxStrict(j)
  ensures 0 <= j < i 
  ensures v.History(j).acceptors[idx] != v.History(j+1).acceptors[idx]
  ensures v.History(j+1).acceptors[idx] == v.History(i).acceptors[idx]
  ensures AcceptorHost.NextStep(c.acceptors[idx], v.History(j).acceptors[idx], v.History(j+1).acceptors[idx], step, msgOps)
  ensures msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs
{
  reveal_AcceptorHostReceiveValidity();
  j, step, msgOps :|
      && 0 <= j < i
      && (v.History(j).acceptors[idx] != v.History(j+1).acceptors[idx])
      && (v.History(j+1).acceptors[idx] == v.History(i).acceptors[idx])
      && AcceptorHost.NextStep(c.acceptors[idx], v.History(j).acceptors[idx], v.History(j+1).acceptors[idx], step, msgOps)
      && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs);
}

lemma InvNextAcceptorHostReceiveValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires AcceptorHostReceiveValidity(c, v)
  requires Next(c, v, v')
  ensures AcceptorHostReceiveValidity(c, v')
{
  forall idx, i |
    && v'.ValidHistoryIdx(i)
    && 0 <= idx < |c.acceptors|
    && v'.History(i).acceptors[idx] != v'.History(0).acceptors[idx]
  ensures
    AcceptorHostReceiveValidityPost(c, v', i, idx)
  {
    VariableNextProperties(c, v, v');
    if v'.ValidHistoryIdxStrict(i) {
      assert AcceptorHostReceiveValidityPost(c, v', i, idx) by {
       reveal_AcceptorHostReceiveValidity();
       reveal_AcceptorHostReceiveValidityPost();
      }
    } else {
      if v'.History(i-1).acceptors[idx] == v'.History(i).acceptors[idx] {
        var k, step, msgOps := AcceptorHostReceiveSkolemization(c, v, i-1, idx);
        // triggers
        assert 0 <= k < i;
        assert v'.History(k).acceptors[idx] != v'.History(k+1).acceptors[idx];
        assert v'.History(k+1).acceptors[idx] == v'.History(i).acceptors[idx];
        assert AcceptorHost.NextStep(c.acceptors[idx], v'.History(k).acceptors[idx], v'.History(k+1).acceptors[idx], step, msgOps);
      } else {
        // triggers
        assert v'.History(i-1).acceptors[idx] != v'.History(i).acceptors[idx];
        var j := i-1;
        assert 0 <= j < i;
        assert j + 1 == i;
        assert v'.History(j+1).acceptors[idx] == v'.History(i).acceptors[idx];
      }
      assert AcceptorHostReceiveValidityPost(c, v', i, idx) by {
       reveal_AcceptorHostReceiveValidity();
       reveal_AcceptorHostReceiveValidityPost();
      }
    }
  }
  assert AcceptorHostReceiveValidity(c, v') by {
    reveal_AcceptorHostReceiveValidity();
    reveal_AcceptorHostReceiveValidityPost();
  }
}

lemma LearnerHostReceiveSkolemization(c: Constants, v: Variables, i: nat, idx: int)
returns (j: nat, step: LearnerHost.Step, msgOps: MessageOps)
  requires v.WF(c)
  requires LearnerHostReceiveValidity(c, v)
  requires 0 <= idx < |c.learners|
  requires v.ValidHistoryIdx(i)
  requires v.History(i).learners[idx] != v.History(0).learners[idx]
  ensures v.ValidHistoryIdxStrict(j)
  ensures 0 <= j < i 
  ensures v.History(j).learners[idx] != v.History(j+1).learners[idx]
  ensures v.History(j+1).learners[idx] == v.History(i).learners[idx]
  ensures LearnerHost.NextStep(c.learners[idx], v.History(j).learners[idx], v.History(j+1).learners[idx], step, msgOps)
  ensures msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs
{
  reveal_LearnerHostReceiveValidity();
  j, step, msgOps :|
      && 0 <= j < i
      && (v.History(j).learners[idx] != v.History(j+1).learners[idx])
      && (v.History(j+1).learners[idx] == v.History(i).learners[idx])
      && LearnerHost.NextStep(c.learners[idx], v.History(j).learners[idx], v.History(j+1).learners[idx], step, msgOps)
      && (msgOps.recv.Some? ==> msgOps.recv.value in v.network.sentMsgs);
}

lemma InvNextLearnerHostReceiveValidity(c: Constants, v: Variables, v': Variables)
  requires v.WF(c)
  requires LearnerHostReceiveValidity(c, v)
  requires Next(c, v, v')
  ensures LearnerHostReceiveValidity(c, v')
{
  forall idx, i |
    && v'.ValidHistoryIdx(i)
    && 0 <= idx < |c.learners|
    && v'.History(i).learners[idx] != v'.History(0).learners[idx]
  ensures
    LearnerHostReceiveValidityPost(c, v', i, idx)
  {
    VariableNextProperties(c, v, v');
    if v'.ValidHistoryIdxStrict(i) {
      assert LearnerHostReceiveValidityPost(c, v', i, idx) by {
       reveal_LearnerHostReceiveValidity();
       reveal_LearnerHostReceiveValidityPost();
      }
    } else {
      if v'.History(i-1).learners[idx] == v'.History(i).learners[idx] {
        var k, step, msgOps := LearnerHostReceiveSkolemization(c, v, i-1, idx);
        // triggers
        assert 0 <= k < i;
        assert v'.History(k).learners[idx] != v'.History(k+1).learners[idx];
        assert v'.History(k+1).learners[idx] == v'.History(i).learners[idx];
        assert LearnerHost.NextStep(c.learners[idx], v'.History(k).learners[idx], v'.History(k+1).learners[idx], step, msgOps);
      } else {
        // triggers
        assert v'.History(i-1).learners[idx] != v'.History(i).learners[idx];
        var j := i-1;
        assert 0 <= j < i;
        assert j + 1 == i;
        assert v'.History(j+1).learners[idx] == v'.History(i).learners[idx];
      }
      assert LearnerHostReceiveValidityPost(c, v', i, idx) by {
       reveal_LearnerHostReceiveValidity();
       reveal_LearnerHostReceiveValidityPost();
      }
    }
  }
  assert LearnerHostReceiveValidity(c, v') by {
    reveal_LearnerHostReceiveValidity();
    reveal_LearnerHostReceiveValidityPost();
  }
}

/***************************************************************************************
*                                  Skolemizations                                      *
***************************************************************************************/

lemma SendPrepareSkolemization(c: Constants, v: Variables, msg: Message)
returns (i: nat)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendPrepareValidity(c, v)
  requires msg in v.network.sentMsgs
  requires msg.Prepare?
  ensures v.ValidHistoryIdxStrict(i)
  ensures LeaderHost.SendPrepare(c.leaders[msg.Src()], v.History(i).leaders[msg.Src()], v.History(i+1).leaders[msg.Src()], msg)
{
  i :|
      && v.ValidHistoryIdxStrict(i)
      && LeaderHost.SendPrepare(c.leaders[msg.Src()], v.History(i).leaders[msg.Src()], v.History(i+1).leaders[msg.Src()], msg);
}

lemma SendProposeSkolemization(c: Constants, v: Variables, msg: Message)
returns (i: nat)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendProposeValidity(c, v)
  requires msg in v.network.sentMsgs
  requires msg.Propose?
  ensures v.ValidHistoryIdxStrict(i)
  ensures LeaderHost.SendPropose(c.leaders[msg.Src()], v.History(i).leaders[msg.Src()], v.History(i+1).leaders[msg.Src()], msg)
{
  i :|
      && v.ValidHistoryIdxStrict(i)
      && LeaderHost.SendPropose(c.leaders[msg.Src()], v.History(i).leaders[msg.Src()], v.History(i+1).leaders[msg.Src()], msg);
}

lemma SendPromiseSkolemization(c: Constants, v: Variables, msg: Message)
returns (i: nat, inMsg: Message)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendPromiseValidity(c, v)
  requires msg in v.network.sentMsgs
  requires msg.Promise?
  ensures v.ValidHistoryIdxStrict(i)
  ensures inMsg in v.network.sentMsgs
  ensures AcceptorHost.ReceivePrepareSendPromise(c.acceptors[msg.Src()], v.History(i).acceptors[msg.Src()], v.History(i+1).acceptors[msg.Src()], inMsg, msg)
{
  i, inMsg :|
      && v.ValidHistoryIdxStrict(i)
      && ExistingMessage(v, inMsg)
      && AcceptorHost.ReceivePrepareSendPromise(c.acceptors[msg.Src()], v.History(i).acceptors[msg.Src()], v.History(i+1).acceptors[msg.Src()], inMsg, msg);
  assert inMsg in v.network.sentMsgs by {
    reveal_ExistingMessage();
  }
}

lemma SendAcceptSkolemization(c: Constants, v: Variables, msg: Message)
returns (i: nat, inMsg: Message)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires SendAcceptValidity(c, v)
  requires msg in v.network.sentMsgs
  requires msg.Accept?
  ensures v.ValidHistoryIdxStrict(i)
  ensures inMsg in v.network.sentMsgs
  ensures AcceptorHost.ReceiveProposeSendAccept(c.acceptors[msg.Src()], v.History(i).acceptors[msg.Src()], v.History(i+1).acceptors[msg.Src()], inMsg, msg)
{
  i, inMsg :|
      && v.ValidHistoryIdxStrict(i)
      && ExistingMessage(v, inMsg)
      && AcceptorHost.ReceiveProposeSendAccept(c.acceptors[msg.Src()], v.History(i).acceptors[msg.Src()], v.History(i+1).acceptors[msg.Src()], inMsg, msg);
  assert inMsg in v.network.sentMsgs by {
    reveal_ExistingMessage();
  }
}

ghost predicate ReceivePromise2WitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: Value, a2: MonotonicNatOption)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.leaders|
{
  && a1 == v.History(i).leaders[idx].receivedPromisesAndValue.value
  && a2 == v.History(i).leaders[idx].highestHeardBallot
  && (v.History(i).leaders[idx].receivedPromisesAndValue.value != v.History(0).leaders[idx].receivedPromisesAndValue.value || v.History(i).leaders[idx].highestHeardBallot != v.History(0).leaders[idx].highestHeardBallot)
}

lemma ReceivePromise2StepSkolemization(c: Constants, v: Variables, i: nat, idx: int, a1: Value, a2: MonotonicNatOption)
  returns (j: nat, inMsg: Message)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires LeaderHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.leaders|
  requires ReceivePromise2WitnessCondition(c, v, i, idx, a1, a2)
  ensures 0 <= j < i
  ensures !ReceivePromise2WitnessCondition(c, v, j, idx, a1, a2)
  ensures ReceivePromise2WitnessCondition(c, v, j+1, idx, a1, a2)
  ensures LeaderHost.ReceivePromise2(c.leaders[idx], v.History(j).leaders[idx], v.History(j+1).leaders[idx], inMsg)
  ensures inMsg in v.network.sentMsgs
  decreases i
{
  reveal_ValidHistory();
  var xj, xstep, xmsgOps := LeaderHostReceiveSkolemization(c, v, i, idx);
  if !ReceivePromise2WitnessCondition(c, v, xj, idx, a1, a2) {
    j, inMsg := xj, xmsgOps.recv.value;
  } else {
    j, inMsg := ReceivePromise2StepSkolemization(c, v, xj, idx, a1, a2);
  }
}

ghost predicate ReceivePromise1ReceivePromise2WitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: nat)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.leaders|
{
  && a1 in v.History(i).leaders[idx].receivedPromisesAndValue.promises
  && (v.History(i).leaders[idx].receivedPromisesAndValue.promises != v.History(0).leaders[idx].receivedPromisesAndValue.promises)
}

lemma ReceivePromise1ReceivePromise2StepSkolemization(c: Constants, v: Variables, i: nat, idx: int, a1: nat)
  returns (j: nat, inMsg: Message)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires LeaderHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.leaders|
  requires ReceivePromise1ReceivePromise2WitnessCondition(c, v, i, idx, a1)
  ensures 0 <= j < i
  ensures !ReceivePromise1ReceivePromise2WitnessCondition(c, v, j, idx, a1)
  ensures ReceivePromise1ReceivePromise2WitnessCondition(c, v, j+1, idx, a1)
  ensures LeaderHost.ReceivePromise1(c.leaders[idx], v.History(j).leaders[idx], v.History(j+1).leaders[idx], inMsg) || LeaderHost.ReceivePromise2(c.leaders[idx], v.History(j).leaders[idx], v.History(j+1).leaders[idx], inMsg)
  ensures inMsg in v.network.sentMsgs
  decreases i
{
  reveal_ValidHistory();
  var xj, xstep, xmsgOps := LeaderHostReceiveSkolemization(c, v, i, idx);
  if !ReceivePromise1ReceivePromise2WitnessCondition(c, v, xj, idx, a1) {
    j, inMsg := xj, xmsgOps.recv.value;
  } else {
    j, inMsg := ReceivePromise1ReceivePromise2StepSkolemization(c, v, xj, idx, a1);
  }
}

ghost predicate ReceiveProposeSendAcceptWitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: MonotonicVBOption)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.acceptors|
{
  && a1 == v.History(i).acceptors[idx].acceptedVB
  && (v.History(i).acceptors[idx].acceptedVB != v.History(0).acceptors[idx].acceptedVB)
}

lemma ReceiveProposeSendAcceptStepSkolemization(c: Constants, v: Variables, i: nat, idx: int, a1: MonotonicVBOption)
  returns (j: nat, inMsg: Message, outMsg: Message)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires AcceptorHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.acceptors|
  requires ReceiveProposeSendAcceptWitnessCondition(c, v, i, idx, a1)
  ensures 0 <= j < i
  ensures !ReceiveProposeSendAcceptWitnessCondition(c, v, j, idx, a1)
  ensures ReceiveProposeSendAcceptWitnessCondition(c, v, j+1, idx, a1)
  ensures AcceptorHost.ReceiveProposeSendAccept(c.acceptors[idx], v.History(j).acceptors[idx], v.History(j+1).acceptors[idx], inMsg, outMsg)
  ensures inMsg in v.network.sentMsgs
  decreases i
{
  reveal_ValidHistory();
  var xj, xstep, xmsgOps := AcceptorHostReceiveSkolemization(c, v, i, idx);
  if !ReceiveProposeSendAcceptWitnessCondition(c, v, xj, idx, a1) {
    j, inMsg, outMsg := xj, xmsgOps.recv.value, xmsgOps.send.value;
  } else {
    j, inMsg, outMsg := ReceiveProposeSendAcceptStepSkolemization(c, v, xj, idx, a1);
  }
}

ghost predicate ReceivePrepareSendPromiseReceiveProposeSendAcceptWitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: MonotonicNatOption)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.acceptors|
{
  && a1 == v.History(i).acceptors[idx].promised
  && (v.History(i).acceptors[idx].promised != v.History(0).acceptors[idx].promised)
}

lemma ReceivePrepareSendPromiseReceiveProposeSendAcceptStepSkolemization(c: Constants, v: Variables, i: nat, idx: int, a1: MonotonicNatOption)
  returns (j: nat, inMsg: Message, outMsg: Message)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires AcceptorHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.acceptors|
  requires ReceivePrepareSendPromiseReceiveProposeSendAcceptWitnessCondition(c, v, i, idx, a1)
  ensures 0 <= j < i
  ensures !ReceivePrepareSendPromiseReceiveProposeSendAcceptWitnessCondition(c, v, j, idx, a1)
  ensures ReceivePrepareSendPromiseReceiveProposeSendAcceptWitnessCondition(c, v, j+1, idx, a1)
  ensures AcceptorHost.ReceivePrepareSendPromise(c.acceptors[idx], v.History(j).acceptors[idx], v.History(j+1).acceptors[idx], inMsg, outMsg) || AcceptorHost.ReceiveProposeSendAccept(c.acceptors[idx], v.History(j).acceptors[idx], v.History(j+1).acceptors[idx], inMsg, outMsg)
  ensures inMsg in v.network.sentMsgs
  decreases i
{
  reveal_ValidHistory();
  var xj, xstep, xmsgOps := AcceptorHostReceiveSkolemization(c, v, i, idx);
  if !ReceivePrepareSendPromiseReceiveProposeSendAcceptWitnessCondition(c, v, xj, idx, a1) {
    j, inMsg, outMsg := xj, xmsgOps.recv.value, xmsgOps.send.value;
  } else {
    j, inMsg, outMsg := ReceivePrepareSendPromiseReceiveProposeSendAcceptStepSkolemization(c, v, xj, idx, a1);
  }
}

ghost predicate ReceiveAcceptWitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: ValBal, a2: AcceptorId)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.learners|
{
  && a1 in v.History(i).learners[idx].receivedAccepts.m
  && a2 in v.History(i).learners[idx].receivedAccepts.m[a1]
  && (v.History(i).learners[idx].receivedAccepts.m != v.History(0).learners[idx].receivedAccepts.m)
}

lemma ReceiveAcceptStepSkolemization(c: Constants, v: Variables, i: nat, idx: int, a1: ValBal, a2: AcceptorId)
  returns (j: nat, inMsg: Message)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires LearnerHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.learners|
  requires ReceiveAcceptWitnessCondition(c, v, i, idx, a1, a2)
  ensures 0 <= j < i
  ensures !ReceiveAcceptWitnessCondition(c, v, j, idx, a1, a2)
  ensures ReceiveAcceptWitnessCondition(c, v, j+1, idx, a1, a2)
  ensures LearnerHost.ReceiveAccept(c.learners[idx], v.History(j).learners[idx], v.History(j+1).learners[idx], inMsg)
  ensures inMsg in v.network.sentMsgs
  decreases i
{
  reveal_ValidHistory();
  var xj, xstep, xmsgOps := LearnerHostReceiveSkolemization(c, v, i, idx);
  if !ReceiveAcceptWitnessCondition(c, v, xj, idx, a1, a2) {
    j, inMsg := xj, xmsgOps.recv.value;
  } else {
    j, inMsg := ReceiveAcceptStepSkolemization(c, v, xj, idx, a1, a2);
  }
}

ghost predicate NextLearnStepWitnessCondition(c: Constants, v: Variables, i: nat, idx: int, a1: Option<Value>)
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.learners|
{
  && a1 == v.History(i).learners[idx].learned
  && (v.History(i).learners[idx].learned != v.History(0).learners[idx].learned)
}

lemma NextLearnStepStepSkolemization(c: Constants, v: Variables, i: nat, idx: int, a1: Option<Value>)
  returns (j: nat, step: LearnerHost.Step, msgOps: MessageOps)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires LearnerHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires 0 <= idx < |c.learners|
  requires NextLearnStepWitnessCondition(c, v, i, idx, a1)
  ensures 0 <= j < i
  ensures !NextLearnStepWitnessCondition(c, v, j, idx, a1)
  ensures NextLearnStepWitnessCondition(c, v, j+1, idx, a1)
  ensures LearnerHost.NextStep(c.learners[idx], v.History(j).learners[idx], v.History(j+1).learners[idx], step, msgOps)
  decreases i
{
  reveal_ValidHistory();
  var xj, xstep, xmsgOps := LearnerHostReceiveSkolemization(c, v, i, idx);
  if !NextLearnStepWitnessCondition(c, v, xj, idx, a1) {
    j, step, msgOps := xj, xstep, xmsgOps;
  } else {
    j, step, msgOps := NextLearnStepStepSkolemization(c, v, xj, idx, a1);
  }
}

} // end module MessageInvariants

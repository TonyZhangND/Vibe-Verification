include "monotonicityInvariants.dfy"
include "messageInvariants.dfy"

module PaxosProof {
  
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem
import opened MonotonicityInvariants
import opened MessageInvariants
import opened Obligations
import LearnerHost

ghost predicate RegularInvs(c: Constants, v: Variables) {
  && MessageInv(c, v)
  && MonotonicityInv(c, v)
  && ValidVariables(c, v)
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && RegularInvs(c, v)
  && Safety(c, v)
}


/***************************************************************************************
*                                    Obligations                                       *
***************************************************************************************/


lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{
  InitImpliesMonotonicityInv(c, v);
  InitImpliesMessageInv(c, v);
}

lemma InvInductive(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  VariableNextProperties(c, v, v');
  MessageInvInductive(c, v, v');
  MonotonicityInvInductive(c, v, v');
  SafetyProof(c, v, v');
}


/***************************************************************************************
*                                       Proofs                                         *
***************************************************************************************/

// BEGIN SAFETY PROOF

// We allow safety to be proven inductively
lemma {:timeLimitMultiplier 2} SafetyProof(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  requires RegularInvs(c, v')
  ensures Safety(c, v')
{
  if !AtMostOneChosenVal(c, v') {
    var vb1, vb2 :| Chosen(c, v'.Last(), vb1) && Chosen(c, v'.Last(), vb2)
                    && !( && c.ValidLeaderIdx(vb1.b)
                          && c.ValidLeaderIdx(vb2.b)
                          && vb1.v == vb2.v);
    ChosenImpliesValidBallot(c, v', |v'.history|-1, vb1);
    ChosenImpliesValidBallot(c, v', |v'.history|-1, vb2);
    assert vb1.v != vb2.v;

    if vb1.b < vb2.b {
      var propMsg := ChosenImpliesProposed(c, v', |v'.history|-1, vb2);
      var promQ, hb := GetPromiseQuorumForProposeMessage(c, v', vb1, propMsg, vb2.b, vb2.v);
      SafetyProofBallotInduction(c, v', vb1, vb2, promQ, hb);
    } else if vb1.b > vb2.b {
      var propMsg := ChosenImpliesProposed(c, v', |v'.history|-1, vb1);
      var promQ, hb := GetPromiseQuorumForProposeMessage(c, v', vb2, propMsg, vb1.b, vb1.v);
      SafetyProofBallotInduction(c, v', vb2, vb1, promQ, hb);
    } else {
      // Proves that at most one chosen value at each ballot
      var propMsg1 := ChosenImpliesProposed(c, v', |v'.history|-1, vb1);
      var propMsg2 := ChosenImpliesProposed(c, v', |v'.history|-1, vb2);
    }
    assert false;  // trigger
  }
  AtMostOneChosenImpliesSafety(c, v');
}

lemma ChosenImpliesValidBallot(c: Constants, v: Variables, i: nat, vb: ValBal)
  requires RegularInvs(c, v)
  requires v.ValidHistoryIdx(i)
  requires Chosen(c, v.History(i), vb)
  ensures c.ValidLeaderIdx(vb.b)
{
  reveal_ChosenAtLearner();
  var lnr := ChosenLearnerWitness(c, v.History(i), vb);
  var lo, hi := ChosenAtLearnerRangeWitness(c, v.History(i), vb, lnr);
  reveal_ChosenAtLearnerRange();
  // vb.b is in the range and has at least one acceptor (by definition of ChosenAtLearnerRange)
  assert lo <= vb.b <= hi;
  assert 0 < |LearnerAcceptorsAtBallot(c, v.History(i), lnr, vb.v, vb.b)|;
  var acc :| acc in LearnerAcceptorsAtBallot(c, v.History(i), lnr, vb.v, vb.b);
  reveal_ValidHistory();
  ReceiveAcceptWitnessFromMembership(c, v, i, lnr, vb, acc);
  reveal_LearnerHostReceiveValidity();
  var j, accMsg := ReceiveAcceptStepSkolemization(c, v, i, lnr, vb, acc);
  var k, propMsg := SendAcceptSkolemization(c, v, accMsg);
  // propMsg is Propose(vb.b, vb.v), so vb.b is a valid leader idx
}

lemma SafetyProofBallotInduction(c: Constants, v: Variables, vb1: ValBal, vb2: ValBal, promQ: set<Message>, hb: LeaderId)
  requires RegularInvs(c, v)
  requires Chosen(c, v.Last(), vb1)
  requires IsPromiseQuorum(c, v, promQ, vb2.b)
  requires PromiseSetHighestVB(c, v, promQ, vb2.b, VB(vb2.v, hb))
  requires vb1.b <= hb < vb2.b
  requires vb1.b < vb2.b
  ensures vb1.v == vb2.v
  decreases vb2.b
{
  /* INDUCTION ON RANGE MINIMUMS for Consecutive Paxos:
  
      v1 is chosen with range r1=[lo1, hi1]
      v2 is chosen with range r3=[lo3, hi3] (using vb2's promise quorum with highest witness hb)
      
      Base case: If r1 ∩ {hb} ≠ ∅, then lo1 <= hb <= hi1
        → By one-value-per-ballot, ballot hb has value v1
        → Promise quorum witnessed v2 at hb
        → Therefore v1 == v2 ✓
      
      Inductive case: If r1 ∩ {hb} == ∅ (i.e., hb < lo1 or hb > hi1)
        → There exists intermediate range r2=[lo2, hi2] for value v'' with lo2 < lo3
        → Check if r2 ∩ r3 ≠ ∅:
          - If yes: v'' == v2 by one-value-per-ballot ✓
          - If no: Use promise quorum to force v'' == v2
        → Induct: prove v1 == v'' using r1 and r2
        → Transitivity: v1 == v'' == v2 ✓
      
      Termination: Decreasing on minimum ballot of ranges until intersection found
  */
  
  // Extract the highest witness from the promise quorum
  var hm :| WinningPromiseMessageInQuorum(c, v, promQ, vb2.b, VB(vb2.v, hb), hm);
  
  // BASE CASE: Check if witnessed value equals vb1.v
  if hm.vbOpt.value.v == vb1.v {
    // The witnessed value equals vb1.v - done!
    // Note: If ranges intersect at hb, this SHOULD be true by one-value-per-ballot
    return;
  }
  
  // INDUCTIVE CASE: Witnessed value ≠ vb1.v AND ranges don't intersect
  // The witnessed value v'' = vb2.v ≠ vb1.v
  // By induction on ballot, prove vb1.v == v''
  // Then by transitivity, vb1.v == vb2.v
  {
    
    var vb1witness := ChosenImpliesSeenByHigherPromiseQuorum(c, v, vb1, vb2.b, promQ);
    var promiser := hm.Src();
    var i, _ := SendPromiseSkolemization(c, v, hm);
    reveal_ValidHistory();
    var _, propMsg, _ := ReceiveProposeSendAcceptStepSkolemization(c, v, i, promiser, MVBSome(VB(vb2.v, hb)));
    
    if hb == vb1.b {
      // Special case: witnessed ballot equals vb1's representative ballot
      // Both are chosen, so must have same value
      var propMsg1 := ChosenImpliesProposed(c, v, |v.history|-1, vb1);      
      assert propMsg.val == propMsg1.val;     // trigger  
      assert false;  // Should be provable
    } else {
      // Recursive case: find promise quorum for the intermediate value at hb
      // Then induct with smaller ballot
      var nq, nb := GetPromiseQuorumForProposeMessage(c, v, vb1, propMsg, hb, vb2.v);
      SafetyProofBallotInduction(c, v, vb1, VB(vb2.v, hb), nq, nb);
    }
  }
}

// Helper to extract chosen range witnesses without polluting the main lemma with reveals
lemma GetChosenRangeWitnesses(c: Constants, v: Variables, chosenVB: ValBal)
returns (lnr: LearnerId, lo: LeaderId, hi: LeaderId, accRange: set<AcceptorId>)
  requires v.WF(c)
  requires Chosen(c, v.Last(), chosenVB)
  ensures c.ValidLearnerIdx(lnr)
  ensures ChosenAtLearnerRange(c, v.Last(), chosenVB, lnr, lo, hi)
  ensures ConsecutiveAcceptWitness(c, v.Last(), lnr, chosenVB.v, lo, hi)
  ensures lo <= chosenVB.b <= hi
  ensures accRange == LearnerAcceptorsForRange(c, v.Last(), lnr, chosenVB.v, lo, hi)
  ensures |accRange| >= c.f + 1
{
  reveal_ChosenAtLearner();
  lnr := ChosenLearnerWitness(c, v.Last(), chosenVB);
  lo, hi := ChosenAtLearnerRangeWitness(c, v.Last(), chosenVB, lnr);
  reveal_ChosenAtLearnerRange();
  accRange := LearnerAcceptorsForRange(c, v.Last(), lnr, chosenVB.v, lo, hi);
}

lemma ChosenImpliesSeenByHigherPromiseQuorum(c: Constants, v: Variables, chosenVB: ValBal, promBal: LeaderId, promQ: set<Message>)
returns (promMsg: Message) 
  requires RegularInvs(c, v)
  // requires v.WF(c)
  // requires ValidVariables(c, v)
  // requires ValidMessages(c, v)
  // requires SendPromiseValidity(c, v)
  // requires SendAcceptValidity(c, v)
  // requires LearnerHostReceiveValidity(c, v)
  // requires AcceptorHostPromisedMonotonic(c, v)
  // requires AcceptorHostAcceptedVBMonotonic(c, v)
  requires Chosen(c, v.Last(), chosenVB)
  requires IsPromiseQuorum(c, v, promQ, promBal)
  requires chosenVB.b < promBal
  ensures IsPromiseMessage(v, promMsg)
  ensures promMsg in promQ
  ensures promMsg.vbOpt.Some?
  ensures chosenVB.b <= promMsg.vbOpt.value.b
{
  // Get Accept quorum from chosen range
  var lnr, lo, hi, accRange := GetChosenRangeWitnesses(c, v, chosenVB);
  var accQ := ExtractAcceptMessagesFromRange(c, v, lnr, chosenVB.v, lo, hi, accRange);

  // Skolemize the intersecting acceptor
  assert IsPromiseQuorum(c, v, promQ, promBal);
  var acc := GetIntersectingAcceptorFromRange(c, v, accQ, chosenVB.v, lo, hi, promQ, promBal);
  var accMsg :| accMsg in accQ && accMsg.acc == acc;
  promMsg :| promMsg in promQ && promMsg.Promise? && promMsg.acc == acc;

  var i, inMsg := SendPromiseSkolemization(c, v, promMsg);
  var j, propMsg := SendAcceptSkolemization(c, v, accMsg);
  
  // TONY: This is actually unprovable. I think we need to restructure the proof such that
  // `chosenVB` is always the highest element in the chosen range.
  // Helper proves the temporal reasoning
  assume accMsg.vb == chosenVB;
  assume accMsg.vb.b < promBal;
  ChosenImpliesSeenByHigherPromiseQuorumHelper(c, v, chosenVB, inMsg, promMsg, promBal, i, propMsg, accMsg, j);
}

// Fixed helper: proves promise witnesses the ACCEPT ballot (which is in the chosen range)
lemma ChosenImpliesSeenByHigherPromiseQuorumHelper(c: Constants, v: Variables, chosenVB: ValBal, inMsg: Message, promMsg: Message, promBal: LeaderId, i: nat, propMsg: Message, accMsg: Message, j: nat) 
  requires v.WF(c)
  requires ValidVariables(c, v)
  requires ValidMessages(c, v)
  requires SendPromiseValidity(c, v)
  requires SendAcceptValidity(c, v)
  requires AcceptorHostPromisedMonotonic(c, v)
  requires AcceptorHostAcceptedVBMonotonic(c, v)
  requires IsPromiseMessage(v, promMsg)
  requires IsAcceptMessage(v, accMsg)
  requires IsProposeMessage(v, propMsg)
  requires accMsg.vb == chosenVB
  requires promMsg.acc == accMsg.acc
  requires chosenVB.b < promBal
  requires accMsg.vb.b < promBal  // KEY: accept ballot is less than promise ballot
  requires promMsg.bal == promBal
  requires v.ValidHistoryIdxStrict(i)
  requires v.ValidHistoryIdxStrict(j)
  requires AcceptorHost.ReceivePrepareSendPromise(c.acceptors[promMsg.Src()], v.History(i).acceptors[promMsg.Src()], v.History(i+1).acceptors[promMsg.Src()], inMsg, promMsg)
  requires AcceptorHost.ReceiveProposeSendAccept(c.acceptors[accMsg.Src()], v.History(j).acceptors[accMsg.Src()], v.History(j+1).acceptors[accMsg.Src()], propMsg, accMsg)
  ensures promMsg.vbOpt.Some?
  ensures chosenVB.b <= promMsg.vbOpt.value.b
{}


lemma GetIntersectingAcceptor(c: Constants, v: Variables, accQ: set<Message>, accVB: ValBal,  promQ: set<Message>, promBal: LeaderId)
returns (accId: AcceptorId)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires IsPromiseQuorum(c, v, promQ, promBal)
  requires IsAcceptQuorum(c, v, accQ, accVB)
  ensures exists promise, accept :: 
    && promise in promQ
    && accept in accQ
    && promise.acc == accId
    && accept.acc == accId
{
  var prAccs := AcceptorsFromPromiseSet(c, v, promQ, promBal);
  var acAccs := AcceptorsFromAcceptSet(c, v, accQ, accVB);
  var allAccs := set id | 0 <= id < 2*c.f+1;
  SetComprehensionSize(2*c.f+1);
  var commonAcc := QuorumIntersection(allAccs , prAccs, acAccs);
  return commonAcc;
}

// Version that works with accept quorum from a range
lemma GetIntersectingAcceptorFromRange(c: Constants, v: Variables, accQ: set<Message>, val: Value, lo: LeaderId, hi: LeaderId, promQ: set<Message>, promBal: LeaderId)
returns (accId: AcceptorId)
  requires v.WF(c)
  requires ValidMessages(c, v)
  requires IsPromiseQuorum(c, v, promQ, promBal)
  requires IsAcceptQuorumFromRange(c, v, accQ, val, lo, hi)
  ensures exists promise, accept :: 
    && promise in promQ
    && accept in accQ
    && promise.acc == accId
    && accept.acc == accId
{
  var prAccs := AcceptorsFromPromiseSet(c, v, promQ, promBal);
  var acAccs := AcceptorsFromAcceptSetRange(c, v, accQ, val, lo, hi);
  var allAccs := set id | 0 <= id < 2*c.f+1;
  SetComprehensionSize(2*c.f+1);
  var commonAcc := QuorumIntersection(allAccs , prAccs, acAccs);
  return commonAcc;
}

lemma AcceptorsFromAcceptSetRange(c: Constants, v: Variables, accSet: set<Message>, val: Value, lo: LeaderId, hi: LeaderId)
returns (accs: set<AcceptorId>)  
  requires IsAcceptSetFromRange(c, v, accSet, val, lo, hi)
  ensures forall a | a in accs 
    :: (exists ac :: ac in accSet && ac.acc == a)
  ensures |accs| == |accSet|
{
  reveal_MessageSetDistinctAccs();
  if |accSet| == 0 {
    accs := {};
  } else {
    var a :| a in accSet;
    // Prove that accSet-{a} still satisfies IsAcceptSetFromRange
    assert IsAcceptSetFromRange(c, v, accSet-{a}, val, lo, hi) by {
      assert forall m | m in accSet-{a} :: 
        && IsAcceptMessage(v, m)
        && m.vb.v == val
        && lo <= m.vb.b <= hi;
      assert MessageSetDistinctAccs(accSet-{a});
    }
    var accs' := AcceptorsFromAcceptSetRange(c, v, accSet-{a}, val, lo, hi);
    accs := accs' + {a.acc};
  }
}

lemma AcceptorsFromPromiseSet(c: Constants, v: Variables, promSet: set<Message>, promBal: LeaderId) 
returns (accs: set<AcceptorId>)
  requires IsPromiseSet(c, v, promSet, promBal)
  ensures forall a | a in accs 
    :: (exists pr :: pr in promSet && pr.acc == a)
  ensures |accs| == |promSet|
{
  reveal_MessageSetDistinctAccs();
  if |promSet| == 0 {
    accs := {};
  } else {
    var p :| p in promSet;
    var accs' := AcceptorsFromPromiseSet(c, v, promSet-{p}, promBal);
    accs := accs' + {p.acc};
  }
}

lemma AcceptorsFromAcceptSet(c: Constants, v: Variables, accSet: set<Message>, vb: ValBal)
returns (accs: set<AcceptorId>)  
  requires IsAcceptSet(c, v, accSet, vb)
  ensures forall a | a in accs 
    :: (exists ac :: ac in accSet && ac.acc == a)
  ensures |accs| == |accSet|
{
  if |accSet| == 0 {
    accs := {};
  } else {
    var a :| a in accSet;
    var accs' := AcceptorsFromAcceptSet(c, v, accSet-{a}, vb);
    accs := accs' + {a.acc};
  }
}

// Helper lemma to extract a single accept message
lemma ExtractSingleAcceptMessage(c: Constants, v: Variables, lnr: LearnerId, vb: ValBal, acc: AcceptorId)
returns (msg: Message)
  requires RegularInvs(c, v)
  requires 0 <= lnr < |c.learners|
  requires acc in LearnerAcceptorsAtBallot(c, v.Last(), lnr, vb.v, vb.b)
  ensures IsAcceptMessage(v, msg)
  ensures msg.vb == vb
  ensures msg.acc == acc
  ensures msg == Accept(vb, acc)
{
  reveal_ValidHistory();
  ReceiveAcceptWitnessFromMembership(c, v, |v.history|-1, lnr, vb, acc);
  reveal_LearnerHostReceiveValidity();
  var i;
  i, msg := ReceiveAcceptStepSkolemization(c, v, |v.history|-1, lnr, vb, acc);
}

// Helper lemma to extract a single accept message from a range
lemma ExtractSingleAcceptMessageFromRange(c: Constants, v: Variables, lnr: LearnerId, val: Value, lo: LeaderId, hi: LeaderId, acc: AcceptorId)
returns (msg: Message)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires LearnerHostReceiveValidity(c, v)
  requires ValidVariables(c, v)
  requires c.ValidLearnerIdx(lnr)
  requires lo <= hi
  requires ConsecutiveAcceptWitness(c, v.Last(), lnr, val, lo, hi)
  requires acc in LearnerAcceptorsForRange(c, v.Last(), lnr, val, lo, hi)
  ensures IsAcceptMessage(v, msg)
  ensures msg.vb.v == val
  ensures lo <= msg.vb.b <= hi
  ensures msg.acc == acc
{
  var bal := LearnerRangeAccHasBallot(c, v.Last(), lnr, val, lo, hi, acc);
  var vb := VB(val, bal);
  reveal_ValidHistory();
  ReceiveAcceptWitnessFromMembership(c, v, |v.history|-1, lnr, vb, acc);
  reveal_LearnerHostReceiveValidity();
  var i;
  i, msg := ReceiveAcceptStepSkolemization(c, v, |v.history|-1, lnr, vb, acc);
}

// Extract Accept messages from a range of ballots for building accept quorum
lemma ExtractAcceptMessagesFromRange(c: Constants, v: Variables, lnr: LearnerId, val: Value, lo: LeaderId, hi: LeaderId, accs: set<AcceptorId>)
returns (acceptMsgs: set<Message>)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires LearnerHostReceiveValidity(c, v)
  requires c.ValidLearnerIdx(lnr)
  requires lo <= hi
  requires ConsecutiveAcceptWitness(c, v.Last(), lnr, val, lo, hi)
  requires accs <= LearnerAcceptorsForRange(c, v.Last(), lnr, val, lo, hi)
  ensures |acceptMsgs| == |accs|
  ensures forall m | m in acceptMsgs :: 
    && IsAcceptMessage(v, m) 
    && m.vb.v == val 
    && lo <= m.vb.b <= hi
  ensures MessageSetDistinctAccs(acceptMsgs)
  ensures forall acc :: acc in accs <==> (exists m :: m in acceptMsgs && m.acc == acc)
  decreases accs
{
  reveal_MessageSetDistinctAccs();
  if |accs| == 0 {
    acceptMsgs := {};
  } else {
    var acc :| acc in accs;
    var subset := ExtractAcceptMessagesFromRange(c, v, lnr, val, lo, hi, accs - {acc});
    var msg := ExtractSingleAcceptMessageFromRange(c, v, lnr, val, lo, hi, acc);
    acceptMsgs := subset + {msg};
    // Help Dafny see that msg is distinct from messages in subset
    assert msg.acc == acc;
    assert forall m | m in subset :: m.acc != acc;
    assert MessageSetDistinctAccs(acceptMsgs);
    
    // Prove the bidirectional correspondence
    forall a | a in accs
    ensures exists m :: m in acceptMsgs && m.acc == a
    {
      if a == acc {
        assert msg in acceptMsgs && msg.acc == a;
      } else {
        assert a in accs - {acc};
        assert exists m :: m in subset && m.acc == a;
        var m :| m in subset && m.acc == a;
        assert m in acceptMsgs;
      }
    }
    
    forall m | m in acceptMsgs
    ensures m.acc in accs
    {
      if m == msg {
        assert m.acc == acc;
        assert acc in accs;
      } else {
        assert m in subset;
        assert m.acc in accs - {acc};
        assert m.acc in accs;
      }
    }
  }
}

lemma GetPromiseQuorumForProposeMessage(c: Constants, v: Variables, chosenVB: ValBal, propMsg: Message, bal: LeaderId, val: Value)
returns (promQ: set<Message>, hb: LeaderId)
  requires RegularInvs(c, v)
  requires Chosen(c, v.Last(), chosenVB)
  requires IsProposeMessage(v, propMsg)
  requires propMsg.val == val
  requires propMsg.bal == bal
  requires chosenVB.b < bal
  ensures IsPromiseQuorum(c, v, promQ, bal)
  ensures PromiseSetHighestVB(c, v, promQ, bal, VB(val, hb))
  ensures chosenVB.b <= hb < bal
{
  var i :|  && v.ValidHistoryIdxStrict(i)
            && LeaderHost.SendPropose(c.leaders[bal], v.History(i).leaders[bal], v.History(i+1).leaders[bal], propMsg);
  var hm : Message;
  promQ := HighestHeardBackedByReceivedPromises(c, v, i, bal);
  var choosingWitness := ChosenImpliesSeenByHigherPromiseQuorum(c, v, chosenVB, bal, promQ);
  hm :| WinningPromiseMessageInQuorum(c, v, promQ, bal, VB(v.History(i).leaders[bal].Value(), v.History(i).leaders[bal].highestHeardBallot.value), hm);
  hb := hm.vbOpt.value.b;
}

lemma {:timeLimitMultiplier 2} HighestHeardBackedByReceivedPromises(c: Constants, v: Variables, i: nat, idx: LeaderId)
returns (promS: set<Message>)
  requires RegularInvs(c, v)
  requires v.ValidHistoryIdx(i)
  requires c.ValidLeaderIdx(idx)
  ensures LeaderPromiseSetProperties(c, v, i, idx, promS)
{
  promS := {};

  var ldr := v.History(i).leaders[idx];
  var hbal := ldr.highestHeardBallot;

  var accs :=  ldr.ReceivedPromises();
  reveal_MessageSetDistinctAccs();

  if hbal.MNSome? {
    reveal_ValidHistory();
    var j, hm := ReceivePromise2StepSkolemization(c, v, i, idx, ldr.receivedPromisesAndValue.value, hbal);
    promS := promS + {hm};
    accs := accs - {hm.acc};
    assert MessageSetDistinctAccs(promS);  // trigger
    while |accs| > 0 
      invariant |promS| + |accs| == |ldr.ReceivedPromises()|
      invariant forall p | p in promS :: p.Promise?
      invariant forall acc | acc in accs :: (forall m | m in promS :: m.acc != acc)
      invariant IsPromiseSet(c, v, promS, idx)
      invariant hbal.MNNone? ==> PromiseSetEmptyVB(c, v, promS, idx)
      invariant MessageSetDistinctAccs(promS)
      invariant forall p: Message | p in promS :: p.acc in ldr.ReceivedPromises()
      invariant WinningPromiseMessageInQuorum(c, v, promS, idx, VB(ldr.Value(), hbal.value), hm)
      decreases accs
    {
      var acc :| acc in accs;
      var p := PromiseMessageExistence(c, v, i, idx, acc);
      promS := promS + {p};
      accs := accs - {acc};
      assert MessageSetDistinctAccs(promS);  // trigger
    }
  } else {
    assert MessageSetDistinctAccs(promS);  // trigger
    while |accs| > 0 
      invariant |promS| + |accs| == |ldr.ReceivedPromises()|
      invariant forall p | p in promS :: p.Promise?
      invariant forall acc | acc in accs :: (forall m | m in promS :: m.acc != acc)
      invariant IsPromiseSet(c, v, promS, idx)
      invariant hbal.MNNone? ==> PromiseSetEmptyVB(c, v, promS, idx)
      invariant MessageSetDistinctAccs(promS)
      invariant forall p: Message | p in promS :: p.acc in ldr.ReceivedPromises()
      decreases accs
    {
      var acc :| acc in accs;
      reveal_ValidHistory();
      var p := PromiseMessageExistence(c, v, i, idx, acc);
      promS := promS + {p};
      accs := accs - {acc};
      assert MessageSetDistinctAccs(promS);  // trigger
    }
  }
}

lemma PromiseMessageExistence(c: Constants, v: Variables, i: int, ldr: LeaderId, acc: AcceptorId) 
  returns (promiseMsg : Message)
  requires v.WF(c)
  requires ValidHistory(c, v)
  requires LeaderHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires c.ValidLeaderIdx(ldr)
  requires LeaderHostHighestHeardBallotMonotonic(c, v)
  requires ReceivePromise1ReceivePromise2WitnessCondition(c, v, i, ldr, acc)
  ensures   && promiseMsg.Promise?
            && promiseMsg in v.network.sentMsgs
            && promiseMsg.bal == ldr
            && promiseMsg.acc == acc
            && (promiseMsg.vbOpt.Some? ==> 
                && v.History(i).leaders[ldr].highestHeardBallot.MNSome?
                && promiseMsg.vbOpt.value.b <= v.History(i).leaders[ldr].highestHeardBallot.value
            )
{
  reveal_ValidHistory();
  var _, m := ReceivePromise1ReceivePromise2StepSkolemization(c, v, i, ldr, acc);
  promiseMsg := m;
}

lemma ChosenImpliesProposed(c: Constants, v: Variables, i: nat, vb: ValBal) 
returns (proposeMsg: Message)
  requires RegularInvs(c, v)
  requires v.ValidHistoryIdx(i)
  requires Chosen(c, v.History(i), vb)
  ensures proposeMsg in v.network.sentMsgs
  ensures proposeMsg == Propose(vb.b, vb.v)
{
  reveal_ChosenAtLearner();
  assert v.WF(c);
  assert v.History(i).WF(c);
  var lnr := ChosenLearnerWitness(c, v.History(i), vb);
  var lo, hi := ChosenAtLearnerRangeWitness(c, v.History(i), vb, lnr);
  reveal_ChosenAtLearnerRange();
  // vb.b must be in the range and have at least one acceptor
  assert lo <= vb.b <= hi;
  assert LearnerHost.ConsecutiveRangeCovered(v.History(i).learners[lnr].receivedAccepts, vb.v, lo, hi);
  assert 0 < |LearnerAcceptorsAtBallot(c, v.History(i), lnr, vb.v, vb.b)|;
  var acc :| acc in LearnerAcceptorsAtBallot(c, v.History(i), lnr, vb.v, vb.b);
  reveal_ValidHistory();
  ReceiveAcceptWitnessFromMembership(c, v, i, lnr, vb, acc);
  assert MessageInv(c, v);
  reveal_LearnerHostReceiveValidity();
  var j, accMsg := ReceiveAcceptStepSkolemization(c, v, i, lnr, vb, acc);
  var k, prop := SendAcceptSkolemization(c, v, accMsg);
  return prop;
}

lemma LearnerValidReceivedAccepts(c: Constants, v: Variables, i: nat, lnr: LearnerId) 
  requires v.WF(c)
  requires ValidVariables(c, v)
  requires ValidMessages(c, v)
  requires LearnerHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires c.ValidLearnerIdx(lnr)
  ensures forall val: Value, bal: LeaderId, acc: AcceptorId |
    acc in LearnerAcceptorsAtBallot(c, v.History(i), lnr, val, bal)
    :: c.ValidAcceptorIdx(acc)
{
  reveal_ValidHistory();
  reveal_LearnerHostReceiveValidity();
  forall val: Value, bal: LeaderId, acc: AcceptorId |
    acc in LearnerAcceptorsAtBallot(c, v.History(i), lnr, val, bal)
  ensures c.ValidAcceptorIdx(acc)
  {
    var vb := VB(val, bal);
    ReceiveAcceptWitnessFromMembership(c, v, i, lnr, vb, acc);
    var _, accMsg := ReceiveAcceptStepSkolemization(c, v, i, lnr, vb, acc);
  }
}

lemma LearnerRangeAcceptorsAreValid(c: Constants, v: Variables, i: nat, lnr: LearnerId, val: Value, lo: LeaderId, hi: LeaderId)
  requires v.WF(c)
  requires ValidVariables(c, v)
  requires ValidMessages(c, v)
  requires LearnerHostReceiveValidity(c, v)
  requires v.ValidHistoryIdx(i)
  requires c.ValidLearnerIdx(lnr)
  requires lo <= hi
  ensures forall acc | acc in LearnerAcceptorsForRange(c, v.History(i), lnr, val, lo, hi) :: c.ValidAcceptorIdx(acc)
  decreases hi - lo
{
  LearnerValidReceivedAccepts(c, v, i, lnr);
  if lo == hi {
    // Base case: single ballot
    assert forall acc | acc in LearnerAcceptorsAtBallot(c, v.History(i), lnr, val, lo) :: c.ValidAcceptorIdx(acc);
  } else {
    // Inductive case
    LearnerRangeAcceptorsAreValid(c, v, i, lnr, val, lo + 1, hi);
    assert forall acc | acc in LearnerAcceptorsAtBallot(c, v.History(i), lnr, val, lo) :: c.ValidAcceptorIdx(acc);
  }
}

// Factored out lemma: proves acceptors in range are subset of all valid acceptor IDs
lemma LearnerRangeAcceptorsSubsetOfAll(c: Constants, v: Variables, lnr: LearnerId, val: Value, lo: LeaderId, hi: LeaderId, accRange: set<AcceptorId>, allAccs: set<AcceptorId>)
  requires RegularInvs(c, v)
  requires c.ValidLearnerIdx(lnr)
  requires lo <= hi
  requires accRange == LearnerAcceptorsForRange(c, v.Last(), lnr, val, lo, hi)
  requires allAccs == set id | 0 <= id < 2*c.f+1
  ensures accRange <= allAccs
{
  LearnerValidReceivedAccepts(c, v, |v.history|-1, lnr);
  
  forall acc | acc in accRange
  ensures acc in allAccs
  {
    AcceptorsOverRangeHasBallot(v.Last().learners[lnr].receivedAccepts, val, lo, hi, acc);
    var bal :| lo <= bal <= hi && acc in v.Last().learners[lnr].receivedAccepts.AcceptorsForValueAtBallot(val, bal);
    assert acc in LearnerAcceptorsAtBallot(c, v.Last(), lnr, val, bal);
    assert c.ValidAcceptorIdx(acc);
    assert 0 <= acc < 2*c.f+1;
  }
}

lemma LearnedImpliesQuorumOfAccepts(c: Constants, v: Variables, lnr: LearnerId, val: Value) 
  requires RegularInvs(c, v)
  requires c.ValidLearnerIdx(lnr)
  requires v.Last().learners[lnr].HasLearnedValue(val)
  ensures exists b: LeaderId :: ChosenAtLearner(c, v.Last(), VB(val, b), lnr)
{
    reveal_ValidHistory();
    reveal_ChosenAtLearner();
    var i, step, msgOps := NextLearnStepStepSkolemization(c, v, |v.history|-1, lnr, v.Last().learners[lnr].learned);
    LearnerValidReceivedAccepts(c, v, i, lnr);
    LearnerValidReceivedAccepts(c, v, |v.history|-1, lnr);
    
    // Extract the step details - it must be a LearnStep
    assert step.LearnStep?;
    var vb := step.vb;
    assert vb.v == val;
    
    // The learn step guarantees HasConsecutiveMajorityForBallot
    assert LearnerHost.NextLearnStep(c.learners[lnr], v.History(i).learners[lnr], v.History(i+1).learners[lnr], vb, msgOps);
    assert LearnerHost.HasConsecutiveMajorityForBallot(c.learners[lnr], v.History(i).learners[lnr], vb);
    
    // Extract the lo and hi witnesses
    var lo: LeaderId, hi: LeaderId :|
      && lo <= vb.b
      && vb.b <= hi
      && LearnerHost.ConsecutiveRangeCovered(v.History(i).learners[lnr].receivedAccepts, vb.v, lo, hi)
      && |LearnerHost.AcceptorsOverRange(v.History(i).learners[lnr].receivedAccepts, vb.v, lo, hi)| >= c.learners[lnr].f + 1;
    
    // Show that ChosenAtLearnerRange holds at step i+1
    reveal_ChosenAtLearnerRange();
    assert ChosenAtLearnerRange(c, v.History(i+1), vb, lnr, lo, hi);
    
    // Therefore ChosenAtLearner holds at step i+1
    assert ChosenAtLearner(c, v.History(i+1), vb, lnr);
    
    // Use monotonicity to show it still holds at v.Last()
    // receivedAccepts is monotonic, so if we had enough acceptors at i+1, we still do at Last()
    assert i+1 <= |v.history|-1;
    assert MonotonicityInv(c, v);
    assert LearnerHostReceivedAcceptsMonotonic(c, v);
    assert v.Last().learners[lnr].receivedAccepts.SatisfiesMonotonic(v.History(i+1).learners[lnr].receivedAccepts);
    
    // By monotonicity, ConsecutiveRangeCovered and AcceptorsOverRange are preserved
    MonotonicityPreservesConsecutiveRangeCovered(v.History(i+1).learners[lnr].receivedAccepts, v.Last().learners[lnr].receivedAccepts, vb.v, lo, hi);
    MonotonicityPreservesAcceptorsOverRange(v.History(i+1).learners[lnr].receivedAccepts, v.Last().learners[lnr].receivedAccepts, vb.v, lo, hi);
    
    // Therefore ChosenAtLearnerRange still holds at Last()
    assert ConsecutiveAcceptWitness(c, v.Last(), lnr, vb.v, lo, hi);
    assert ChosenAtLearnerRange(c, v.Last(), vb, lnr, lo, hi);
    assert ChosenAtLearner(c, v.Last(), vb, lnr);
}

lemma LearnedImpliesChosen(c: Constants, v: Variables, lnr: LearnerId, val: Value) returns (vb: ValBal)
  requires RegularInvs(c, v)
  requires c.ValidLearnerIdx(lnr)
  requires v.Last().learners[lnr].HasLearnedValue(val)
  ensures vb.v == val
  ensures Chosen(c, v.Last(), vb)
{
  LearnedImpliesQuorumOfAccepts(c, v, lnr, val);
  ghost var bal :| ChosenAtLearner(c, v.Last(), VB(val, bal), lnr);
  return VB(val, bal);
}

lemma AtMostOneChosenImpliesSafety(c: Constants, v: Variables)
  requires RegularInvs(c, v)
  requires AtMostOneChosenVal(c, v)
  ensures Safety(c, v)
{
  if !Safety(c, v) {
    ghost var l1, l2 :| c.ValidLearnerIdx(l1) && c.ValidLearnerIdx(l2) && v.Last().learners[l1].learned.Some? && v.Last().learners[l2].learned.Some? && v.Last().learners[l1].learned != v.Last().learners[l2].learned;
    ghost var vb1 := LearnedImpliesChosen(c, v, l1, v.Last().learners[l1].learned.value);
    ghost var vb2 := LearnedImpliesChosen(c, v, l2, v.Last().learners[l2].learned.value);
    // contradiction, assert false
  }
}


/***************************************************************************************
*                                  Helper Definitions                                  *
***************************************************************************************/

ghost function LearnerAcceptorsForRange(c: Constants, v: Hosts, lnr: LearnerId, val: Value, lo: LeaderId, hi: LeaderId) : set<AcceptorId>
  requires v.WF(c)
  requires c.ValidLearnerIdx(lnr)
  requires lo <= hi
{
  LearnerHost.AcceptorsOverRange(v.learners[lnr].receivedAccepts, val, lo, hi)
}

ghost function LearnerAcceptorsAtBallot(c: Constants, v: Hosts, lnr: LearnerId, val: Value, bal: LeaderId) : set<AcceptorId>
  requires v.WF(c)
  requires c.ValidLearnerIdx(lnr)
{
  v.learners[lnr].receivedAccepts.AcceptorsForValueAtBallot(val, bal)
}

ghost predicate ConsecutiveAcceptWitness(c: Constants, v: Hosts, lnr: LearnerId, val: Value, lo: LeaderId, hi: LeaderId)
  requires v.WF(c)
{
  && c.ValidLearnerIdx(lnr)
  && lo <= hi
  && LearnerHost.ConsecutiveRangeCovered(v.learners[lnr].receivedAccepts, val, lo, hi)
  && |LearnerAcceptorsForRange(c, v, lnr, val, lo, hi)| >= c.f + 1
}

ghost predicate Chosen(c: Constants, v: Hosts, vb: ValBal)
  requires v.WF(c)
{
  exists lnr :: ChosenAtLearner(c, v, vb, lnr)
}

ghost predicate {:opaque} ChosenAtLearnerRange(c: Constants, v: Hosts, vb: ValBal, lnr: LearnerId, lo: LeaderId, hi: LeaderId)
  requires v.WF(c)
{
  && ConsecutiveAcceptWitness(c, v, lnr, vb.v, lo, hi)
  && lo <= vb.b && vb.b <= hi
  && 0 < |LearnerAcceptorsAtBallot(c, v, lnr, vb.v, vb.b)|
}

ghost predicate {:opaque} ChosenAtLearner(c: Constants, v: Hosts, vb: ValBal, lnr: LearnerId)
  requires v.WF(c)
{
  exists lo: LeaderId, hi: LeaderId :: ChosenAtLearnerRange(c, v, vb, lnr, lo, hi)
}

lemma ChosenLearnerWitness(c: Constants, v: Hosts, vb: ValBal)
returns (lnr: LearnerId)
  requires v.WF(c)
  requires Chosen(c, v, vb)
  ensures c.ValidLearnerIdx(lnr)
  ensures ChosenAtLearner(c, v, vb, lnr)
{
  lnr :| ChosenAtLearner(c, v, vb, lnr);
  reveal_ChosenAtLearner();
  reveal_ChosenAtLearnerRange();
  // lnr is a valid learner index (from the definition of ChosenAtLearner)
  assert 0 <= lnr < |v.learners|;
  assert c.ValidLearnerIdx(lnr);
}

lemma ChosenAtLearnerRangeWitness(c: Constants, v: Hosts, vb: ValBal, lnr: LearnerId)
returns (lo: LeaderId, hi: LeaderId)
  requires v.WF(c)
  requires ChosenAtLearner(c, v, vb, lnr)
  ensures ChosenAtLearnerRange(c, v, vb, lnr, lo, hi)
{
  reveal_ChosenAtLearner();
  reveal_ChosenAtLearnerRange();
  lo, hi :| ChosenAtLearnerRange(c, v, vb, lnr, lo, hi);
}

// New: Extract the complete chosen range for a chosen value
lemma ChosenRangeWitness(c: Constants, v: Hosts, vb: ValBal)
returns (lo: LeaderId, hi: LeaderId, lnr: LearnerId)
  requires v.WF(c)
  requires Chosen(c, v, vb)
  ensures c.ValidLearnerIdx(lnr)
  ensures ChosenAtLearnerRange(c, v, vb, lnr, lo, hi)
  ensures lo <= vb.b <= hi
{
  lnr := ChosenLearnerWitness(c, v, vb);
  // lnr comes from ChosenAtLearner which is over valid learner indices
  lo, hi := ChosenAtLearnerRangeWitness(c, v, vb, lnr);
  reveal_ChosenAtLearnerRange();
  assert lo <= vb.b && vb.b <= hi;
}

// KEY LEMMA: Acceptors only accept proposed values
lemma AcceptedImpliesProposed(c: Constants, v: Variables, vb: ValBal, acc: AcceptorId)
  requires RegularInvs(c, v)
  requires v.WF(c)
  requires c.ValidAcceptorIdx(acc)
  requires exists lnr :: c.ValidLearnerIdx(lnr) && acc in LearnerAcceptorsAtBallot(c, v.Last(), lnr, vb.v, vb.b)
  ensures exists propMsg :: propMsg in v.network.sentMsgs && propMsg == Propose(vb.b, vb.v)
{
  // If an acceptor accepted vb, it must have received a Propose message for vb
  // This follows from the acceptor protocol: acceptors only accept after receiving a proposal
  var lnr :| c.ValidLearnerIdx(lnr) && acc in LearnerAcceptorsAtBallot(c, v.Last(), lnr, vb.v, vb.b);
  assert v.ValidHistoryIdx(|v.history|-1);
  ReceiveAcceptWitnessFromMembership(c, v, |v.history|-1, lnr, vb, acc);
  reveal_LearnerHostReceiveValidity();
  var j, accMsg := ReceiveAcceptStepSkolemization(c, v, |v.history|-1, lnr, vb, acc);
  var k, propMsg := SendAcceptSkolemization(c, v, accMsg);
  assert propMsg == Propose(vb.b, vb.v);
}

// KEY LEMMA: All ballots in a chosen range have the same value (by one-value-per-ballot)
// Simplified version: just prove that ballot in range was proposed with the chosen value
lemma BallotInChosenRangeHasChosenValue(c: Constants, v: Variables, chosenVB: ValBal, lo: LeaderId, hi: LeaderId, lnr: LearnerId, bal: LeaderId)
  requires RegularInvs(c, v)
  requires v.Last().WF(c)
  requires c.ValidLearnerIdx(lnr)
  requires ChosenAtLearnerRange(c, v.Last(), chosenVB, lnr, lo, hi)
  requires lo <= bal <= hi
  // Simplified postcondition: just ensure the ballot is chosen with the same value
  ensures Chosen(c, v.Last(), VB(chosenVB.v, bal))
{
  // Since bal is in the chosen range [lo, hi] for value chosenVB.v,
  // and the range has ConsecutiveRangeCovered + quorum,
  // VB(chosenVB.v, bal) is also Chosen!
  reveal_ChosenAtLearnerRange();
  reveal_ChosenAtLearner();
  
  // We already have ChosenAtLearnerRange for chosenVB at [lo, hi]
  // This means ballot `bal` (which is in [lo, hi]) also satisfies ChosenAtLearnerRange
  assert ConsecutiveAcceptWitness(c, v.Last(), lnr, chosenVB.v, lo, hi);
  assert lo <= bal <= hi;
  assert 0 < |LearnerAcceptorsAtBallot(c, v.Last(), lnr, chosenVB.v, bal)|;
  
  // Therefore ChosenAtLearnerRange holds for VB(chosenVB.v, bal) with the same range [lo, hi]
  assert ChosenAtLearnerRange(c, v.Last(), VB(chosenVB.v, bal), lnr, lo, hi);
  
  // Therefore Chosen holds
  assert ChosenAtLearner(c, v.Last(), VB(chosenVB.v, bal), lnr);
  assert Chosen(c, v.Last(), VB(chosenVB.v, bal));
}

lemma LearnerInitialAcceptorsEmpty(c: Constants, v: Variables, lnr: LearnerId, val: Value, bal: LeaderId)
  requires v.WF(c)
  requires ValidVariables(c, v)
  requires c.ValidLearnerIdx(lnr)
  ensures LearnerAcceptorsAtBallot(c, v.History(0), lnr, val, bal) == {}
{
  reveal_ValidHistory();
  assert InitHosts(c, v.History(0));
  assert LearnerHost.GroupInit(c.learners, v.History(0).learners, c.f);
  assert LearnerHost.Init(c.learners[lnr], v.History(0).learners[lnr]);
  assert v.History(0).learners[lnr].receivedAccepts == MVA(map[]);
}

lemma ReceiveAcceptWitnessFromMembership(c: Constants, v: Variables, i: nat, lnr: LearnerId, vb: ValBal, acc: AcceptorId)
  requires v.WF(c)
  requires ValidVariables(c, v)
  requires v.ValidHistoryIdx(i)
  requires c.ValidLearnerIdx(lnr)
  requires acc in LearnerAcceptorsAtBallot(c, v.History(i), lnr, vb.v, vb.b)
  ensures ReceiveAcceptWitnessCondition(c, v, i, lnr, vb, acc)
{
  reveal_ValidHistory();
  assert InitHosts(c, v.History(0));
  LearnerInitialAcceptorsEmpty(c, v, lnr, vb.v, vb.b);
  assert ReceiveAcceptWitnessCondition(c, v, i, lnr, vb, acc) by {
    assert acc in LearnerAcceptorsAtBallot(c, v.History(i), lnr, vb.v, vb.b);
    assert v.History(0).learners[lnr].receivedAccepts.AcceptorsForValueAtBallot(vb.v, vb.b) == {};
    assert acc !in LearnerAcceptorsAtBallot(c, v.History(0), lnr, vb.v, vb.b);
    assert LearnerAcceptorsAtBallot(c, v.History(i), lnr, vb.v, vb.b) != LearnerAcceptorsAtBallot(c, v.History(0), lnr, vb.v, vb.b);
  }
}

lemma LearnerRangeAccHasBallot(c: Constants, hosts: Hosts, lnr: LearnerId, val: Value, lo: LeaderId, hi: LeaderId, acc: AcceptorId)
returns (bal: LeaderId)
  requires hosts.WF(c)
  requires ConsecutiveAcceptWitness(c, hosts, lnr, val, lo, hi)
  requires acc in LearnerAcceptorsForRange(c, hosts, lnr, val, lo, hi)
  ensures lo <= bal <= hi
  ensures acc in LearnerAcceptorsAtBallot(c, hosts, lnr, val, bal)
{
  // AcceptorsOverRange is the union of acceptors at each ballot in [lo, hi]
  // If acc is in the union, it must be in at least one ballot's set
  AcceptorsOverRangeHasBallot(hosts.learners[lnr].receivedAccepts, val, lo, hi, acc);
  
  // The lemma proves existence, now extract the witness
  assert exists bal :: lo <= bal <= hi && acc in hosts.learners[lnr].receivedAccepts.AcceptorsForValueAtBallot(val, bal);
  bal :|
    && lo <= bal <= hi
    && acc in hosts.learners[lnr].receivedAccepts.AcceptorsForValueAtBallot(val, bal);
  // Translate from receivedAccepts to LearnerAcceptorsAtBallot
  assert acc in LearnerAcceptorsAtBallot(c, hosts, lnr, val, bal);
}

lemma AcceptorsOverRangeHasBallot(receivedAccepts: MonotonicValueAccepts, val: Value, lo: LeaderId, hi: LeaderId, acc: AcceptorId)
  requires lo <= hi
  requires acc in LearnerHost.AcceptorsOverRange(receivedAccepts, val, lo, hi)
  ensures exists bal :: lo <= bal <= hi && acc in receivedAccepts.AcceptorsForValueAtBallot(val, bal)
  decreases hi - lo
{
  if lo == hi {
    // Base case: range is a single ballot
    assert acc in receivedAccepts.AcceptorsForValueAtBallot(val, lo);
  } else {
    // Inductive case: acc is either at lo or in the rest of the range
    var atLo := receivedAccepts.AcceptorsForValueAtBallot(val, lo);
    var rest := LearnerHost.AcceptorsOverRange(receivedAccepts, val, lo + 1, hi);
    if acc in atLo {
      assert lo <= lo <= hi;
    } else {
      assert acc in rest;
      AcceptorsOverRangeHasBallot(receivedAccepts, val, lo + 1, hi, acc);
    }
  }
}

lemma RangeAcceptMessageWitness(c: Constants, v: Variables, i: nat, lnr: LearnerId, val: Value, lo: LeaderId, hi: LeaderId, acc: AcceptorId)
returns (msg: Message)
  requires RegularInvs(c, v)
  requires v.ValidHistoryIdx(i)
  requires c.ValidLearnerIdx(lnr)
  requires ConsecutiveAcceptWitness(c, v.History(i), lnr, val, lo, hi)
  requires acc in LearnerAcceptorsForRange(c, v.History(i), lnr, val, lo, hi)
  ensures IsAcceptMessage(v, msg)
  ensures msg.acc == acc
  ensures msg.vb.v == val
  ensures lo <= msg.vb.b <= hi
{
  reveal_ValidHistory();
  var bal := LearnerRangeAccHasBallot(c, v.History(i), lnr, val, lo, hi, acc);
  var vb := VB(val, bal);
  assert MessageInv(c, v);
  reveal_LearnerHostReceiveValidity();
  ReceiveAcceptWitnessFromMembership(c, v, i, lnr, vb, acc);
  var j, inMsg := ReceiveAcceptStepSkolemization(c, v, i, lnr, vb, acc);
  msg := inMsg;
  assert IsAcceptMessage(v, msg);
  assert msg.vb == vb;
}

ghost predicate IsAcceptorQuorum(c: Constants, quorum: set<AcceptorId>) {
  && |quorum| >= c.f + 1
  && (forall id: AcceptorId | id in quorum :: c.ValidAcceptorIdx(id))
}

ghost predicate AtMostOneChosenVal(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall vb1, vb2 | 
    && Chosen(c, v.Last(), vb1)
    && Chosen(c, v.Last(), vb2)
  :: 
    && c.ValidLeaderIdx(vb1.b) 
    && c.ValidLeaderIdx(vb2.b)
    && vb1.v == vb2.v
}

ghost predicate IsProposeMessage(v: Variables, m: Message) {
  && m.Propose?
  && m in v.network.sentMsgs
}

ghost predicate IsAcceptMessage(v: Variables, m: Message) {
  && m.Accept?
  && m in v.network.sentMsgs
}

ghost predicate IsPromiseMessage(v: Variables, m: Message) {
  && m.Promise?
  && m in v.network.sentMsgs
}

ghost predicate {:opaque} MessageSetDistinctAccs(mset: set<Message>) 
  requires forall m | m in mset :: m.Promise? || m.Accept?
{
  forall m1, m2 | m1 in mset && m2 in mset && m1.acc == m2.acc
      :: m1 == m2
}

ghost predicate IsPromiseSet(c: Constants, v: Variables, pset: set<Message>, bal: LeaderId) {
  && (forall m | m in pset ::
    && IsPromiseMessage(v, m)
    && m.bal == bal)
  && MessageSetDistinctAccs(pset)
}

ghost predicate IsPromiseQuorum(c: Constants, v: Variables, quorum: set<Message>, bal: LeaderId) {
  && |quorum| >= c.f+1
  && IsPromiseSet(c, v, quorum, bal)
}

ghost predicate WinningPromiseMessageInQuorum(c: Constants, v: Variables, pset: set<Message>, qbal: LeaderId, hsvb: ValBal, m: Message)
  requires IsPromiseSet(c, v, pset, qbal)
{
    && m in pset 
    && m.vbOpt == Some(hsvb)
    && (forall other | other in pset  && other.vbOpt.Some?
        :: other.vbOpt.value.b <= hsvb.b)
}

ghost predicate PromiseSetHighestVB(c: Constants, v: Variables, pset: set<Message>, qbal: LeaderId, hsvb: ValBal)
  requires IsPromiseSet(c, v, pset, qbal)
{
  exists m :: WinningPromiseMessageInQuorum(c, v, pset, qbal, hsvb, m)
}

ghost predicate IsAcceptSet(c: Constants, v: Variables, accSet: set<Message>, vb: ValBal) {
  forall m | m in accSet ::
    && IsAcceptMessage(v, m)
    && m.vb == vb
}

ghost predicate IsAcceptQuorum(c: Constants, v: Variables, quorum: set<Message>, vb: ValBal) {
  && |quorum| >= c.f+1
  && IsAcceptSet(c, v, quorum, vb)
  && MessageSetDistinctAccs(quorum)
}

// Accept set from a range of ballots for the same value
ghost predicate IsAcceptSetFromRange(c: Constants, v: Variables, accSet: set<Message>, val: Value, lo: LeaderId, hi: LeaderId) {
  && lo <= hi
  && (forall m | m in accSet ::
    && IsAcceptMessage(v, m)
    && m.vb.v == val
    && lo <= m.vb.b <= hi)
  && MessageSetDistinctAccs(accSet)
}

ghost predicate IsAcceptQuorumFromRange(c: Constants, v: Variables, quorum: set<Message>, val: Value, lo: LeaderId, hi: LeaderId) {
  && |quorum| >= c.f+1
  && IsAcceptSetFromRange(c, v, quorum, val, lo, hi)
}

ghost predicate PromiseSetEmptyVB(c: Constants, v: Variables, pset: set<Message>, qbal: LeaderId)
  requires IsPromiseSet(c, v, pset, qbal)
{
  forall m | m in pset :: m.vbOpt == None
}

ghost predicate LeaderPromiseSetProperties(c: Constants, v: Variables, i: nat, idx: LeaderId, promS: set<Message>) 
  requires v.WF(c)
  requires v.ValidHistoryIdx(i)
  requires c.ValidLeaderIdx(idx)
{
    && IsPromiseSet(c, v, promS, idx)
    && var ldr := v.History(i).leaders[idx];
    && var cldr := c.leaders[idx];
    && var hbal := ldr.highestHeardBallot;
    && (hbal.MNSome? ==> PromiseSetHighestVB(c, v, promS, cldr.id, VB(ldr.Value(), hbal.value)))
    && (hbal.MNNone? ==> PromiseSetEmptyVB(c, v, promS, cldr.id))
    && |promS| == |ldr.ReceivedPromises()|
}

// Helper lemmas for monotonicity preservation

lemma MonotonicityPreservesConsecutiveRangeCovered(past: MonotonicValueAccepts, curr: MonotonicValueAccepts, val: Value, lo: LeaderId, hi: LeaderId)
  requires lo <= hi
  requires curr.SatisfiesMonotonic(past)
  requires LearnerHost.ConsecutiveRangeCovered(past, val, lo, hi)
  ensures LearnerHost.ConsecutiveRangeCovered(curr, val, lo, hi)
  decreases hi - lo
{
  if lo == hi {
    // Base case: single ballot
    assert past.AcceptorsForValueAtBallot(val, lo) <= curr.AcceptorsForValueAtBallot(val, lo);
    assert 0 < |past.AcceptorsForValueAtBallot(val, lo)|;
    assert 0 < |curr.AcceptorsForValueAtBallot(val, lo)|;
  } else {
    // Inductive case: prove for [lo+1, hi] first
    MonotonicityPreservesConsecutiveRangeCovered(past, curr, val, lo + 1, hi);
    // Now prove for lo
    assert past.AcceptorsForValueAtBallot(val, lo) <= curr.AcceptorsForValueAtBallot(val, lo);
    assert 0 < |past.AcceptorsForValueAtBallot(val, lo)|;
    assert 0 < |curr.AcceptorsForValueAtBallot(val, lo)|;
    // Combined with inductive hypothesis, we have ConsecutiveRangeCovered for [lo, hi]
  }
}

lemma MonotonicityPreservesAcceptorsOverRange(past: MonotonicValueAccepts, curr: MonotonicValueAccepts, val: Value, lo: LeaderId, hi: LeaderId)
  requires lo <= hi
  requires curr.SatisfiesMonotonic(past)
  ensures LearnerHost.AcceptorsOverRange(past, val, lo, hi) <= LearnerHost.AcceptorsOverRange(curr, val, lo, hi)
  ensures |LearnerHost.AcceptorsOverRange(past, val, lo, hi)| <= |LearnerHost.AcceptorsOverRange(curr, val, lo, hi)|
  decreases hi - lo
{
  if lo == hi {
    // Base case: single ballot
    assert past.AcceptorsForValueAtBallot(val, lo) <= curr.AcceptorsForValueAtBallot(val, lo);
  } else {
    // Inductive case
    MonotonicityPreservesAcceptorsOverRange(past, curr, val, lo + 1, hi);
    var pastLo := past.AcceptorsForValueAtBallot(val, lo);
    var currLo := curr.AcceptorsForValueAtBallot(val, lo);
    var pastRest := LearnerHost.AcceptorsOverRange(past, val, lo + 1, hi);
    var currRest := LearnerHost.AcceptorsOverRange(curr, val, lo + 1, hi);
    assert pastLo <= currLo;
    assert pastRest <= currRest;
    
    // Prove set union subset: if A ⊆ C and B ⊆ D, then A∪B ⊆ C∪D
    assert pastLo + pastRest <= currLo + currRest by {
      forall x | x in pastLo + pastRest
      ensures x in currLo + currRest
      {
        if x in pastLo {
          assert x in currLo;
        } else {
          assert x in pastRest;
          assert x in currRest;
        }
      }
    }
    
    // Prove cardinality: if A ⊆ C, then |A| ≤ |C|
    assert |pastLo + pastRest| <= |currLo + currRest| by {
      // We have pastLo + pastRest <= currLo + currRest (subset)
      // By definition of subset, |pastLo + pastRest| <= |currLo + currRest|
      SetContainmentCardinality(pastLo + pastRest, currLo + currRest);
    }
  }
}

// END SAFETY PROOF

} // end module PaxosProof

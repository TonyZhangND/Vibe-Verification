/// This file is auto-generated from /Users/nudzhang/Documents/UMich2023sp/linear-dist.nosync/basilisk/paxosBB/automate_gen2/distributedSystem.dfy
/// Generated 05/24/2025 20:52 Pacific Standard Time
include "../spec/spec.dfy"

module MonotonicityInvariants {
import opened Types
import opened UtilitiesLibrary
import opened MonotonicityLibrary
import opened DistributedSystem
import LearnerHost

lemma MonotonicValueAcceptsReflexive(curr: MonotonicValueAccepts)
  ensures curr.SatisfiesMonotonic(curr)
{
  forall val | val in curr.m
  {
    forall bal | bal in curr.m[val]
    {
      assert curr.m[val][bal] <= curr.m[val][bal];
      assert |curr.m[val][bal]| <= |curr.m[val][bal]|;
    }
  }
}

lemma MonotonicValueAcceptsTransitive(a: MonotonicValueAccepts, b: MonotonicValueAccepts, c: MonotonicValueAccepts)
  requires b.SatisfiesMonotonic(a)
  requires c.SatisfiesMonotonic(b)
  ensures c.SatisfiesMonotonic(a)
{
  forall val | val in a.m
  {
    assert val in b.m;
    assert val in c.m;
    forall bal | bal in a.m[val]
    {
      assert bal in b.m[val];
      assert bal in c.m[val];
      var s1 := a.m[val][bal];
      var s2 := b.m[val][bal];
      var s3 := c.m[val][bal];
      assert s1 <= s2 by {
        forall x | x in s1
        {
          assert x in s2;
        }
      }
      assert s2 <= s3 by {
        forall x | x in s2
        {
          assert x in s3;
        }
      }
      assert s1 <= s3 by {
        forall x | x in s1
        {
          assert x in s2;
          assert x in s3;
        }
      }
      assert |s1| <= |s2|;
      assert |s2| <= |s3|;
      assert |s1| <= |s3|;
    }
  }
}

ghost predicate LeaderHostReceivedPromisesAndValueMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j |
    && 0 <= idx < |c.leaders|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).leaders[idx].receivedPromisesAndValue.SatisfiesMonotonic(v.History(i).leaders[idx].receivedPromisesAndValue)
}

ghost predicate LeaderHostHighestHeardBallotMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j |
    && 0 <= idx < |c.leaders|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).leaders[idx].highestHeardBallot.SatisfiesMonotonic(v.History(i).leaders[idx].highestHeardBallot)
}

ghost predicate AcceptorHostPromisedMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j |
    && 0 <= idx < |c.acceptors|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).acceptors[idx].promised.SatisfiesMonotonic(v.History(i).acceptors[idx].promised)
}

ghost predicate AcceptorHostAcceptedVBMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j |
    && 0 <= idx < |c.acceptors|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).acceptors[idx].acceptedVB.SatisfiesMonotonic(v.History(i).acceptors[idx].acceptedVB)
}

ghost predicate LearnerHostReceivedAcceptsMonotonic(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall idx, i, j |
    && 0 <= idx < |c.learners|
    && v.ValidHistoryIdx(i)
    && v.ValidHistoryIdx(j)
    && i <= j
  ::
    v.History(j).learners[idx].receivedAccepts.SatisfiesMonotonic(v.History(i).learners[idx].receivedAccepts)
}

ghost predicate MonotonicityInv(c: Constants, v: Variables)
{
  && v.WF(c)
  && LeaderHostReceivedPromisesAndValueMonotonic(c, v)
  && LeaderHostHighestHeardBallotMonotonic(c, v)
  && AcceptorHostPromisedMonotonic(c, v)
  && AcceptorHostAcceptedVBMonotonic(c, v)
  && LearnerHostReceivedAcceptsMonotonic(c, v)
}

// Base obligation
lemma InitImpliesMonotonicityInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures MonotonicityInv(c, v)
{
}

// Inductive obligation
lemma MonotonicityInvInductive(c: Constants, v: Variables, v': Variables)
  requires MonotonicityInv(c, v)
  requires Next(c, v, v')
  ensures MonotonicityInv(c, v')
{
  VariableNextProperties(c, v, v');
}

} // end module MonotonicityInvariants

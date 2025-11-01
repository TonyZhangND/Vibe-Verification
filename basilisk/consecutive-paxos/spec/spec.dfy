include "distributedSystem.dfy"

module Obligations {
  import opened Types
  import opened DistributedSystem
  // import LearnerHost

  // ghost predicate ConsecutiveSupportForLearned(c: Constants, learner: LearnerHost.Variables)
  // {
  //   learner.learned.None? ||
  //   (exists lo: LeaderId, hi: LeaderId ::
  //     && lo <= hi
  //     && LearnerHost.ConsecutiveRangeCovered(learner.receivedAccepts, learner.learned.value, lo, hi)
  //     && |LearnerHost.AcceptorsOverRange(learner.receivedAccepts, learner.learned.value, lo, hi)| >= c.f + 1
  //   )
  // }

  // All learners must learn the same value
  ghost predicate Safety(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall l1, l2 
    {:trigger v.Last().learners[l1].learned == v.Last().learners[l2].learned}
    |
      && c.ValidLearnerIdx(l1)
      && c.ValidLearnerIdx(l2)
      && v.Last().learners[l1].learned.Some?
      && v.Last().learners[l2].learned.Some?
    ::
      v.Last().learners[l1].learned == v.Last().learners[l2].learned
  // && forall l |
  //   && c.ValidLearnerIdx(l)
  //   :: ConsecutiveSupportForLearned(c, v.Last().learners[l])
  }
}

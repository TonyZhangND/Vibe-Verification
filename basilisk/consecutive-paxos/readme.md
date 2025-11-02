# Paxos Bounded Ballots Protocol

This is the version where each proposer has one ballot.
Hosts can receive and send messages in the same step.


Begin with pure Paxos. Then ask LLM to write consecutive Paxos, and prove it correct.

* Codex was able to come up with correct consecutive Paxos protocol spec.
* Codex kinda struggles with the proofs. It can't even get syntax right, ad keep trying add semicolons at the end of `assert-by` statements, which are not needed.
  * Switching to Sonnet 4.5, at commit `c2c0d6fb404104baeb89b2a748ff709761f34c4d`

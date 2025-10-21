# Notes

1. Asked to implement two phase commit using spec mode
   * "I want to implement two phase commit algorithm as python processes that communicate via tcp. There is a coordinator host and an abitrary number of participants".
   * Kiro gave me requirements.md, design.md and tasks.md. At each stage, it asked for my feedback
   * I am surprised at how detailed those documents are, with the absolute minimal amount of prompting that I gave.
2. I asked for a TLA+ specification that can be model-checked to be added to the task list as the first task. It then gave me an amazing output. It shows a good understanding of TLA.

```
TLA+ Specification Files
Core Specification:

TwoPhaseCommit.tla - Complete formal model of the 2PC protocol with coordinator and participant state machines, message passing, and non-deterministic vote preferences
Properties & Verification:

TwoPhaseCommitProperties.tla - Comprehensive safety and liveness properties including your correctness guarantees
Multiple .cfg files - Different configurations for model checking (2, 3, and 5 participants)
Key Features Modeled
✅ Non-deterministic vote preferences - Each participant starts with a random preference
✅ Complete protocol flow - PREPARE → VOTE → COMMIT/ABORT → ACK
✅ Your correctness guarantees:

If any participant commits → all voted commit
If any participant aborts → at least one voted abort ✅ Message-based communication - Models TCP message passing ✅ State machines - Both coordinator and participant state transitions
Ready to Model Check
You can now run model checking with:

# Quick test (2 participants)
tlc TwoPhaseCommit.tla -config TwoPhaseCommitSmall.cfg

# Standard test (3 participants)  
tlc TwoPhaseCommit.tla -config TwoPhaseCommit.cfg
The specification will verify all your safety properties and ensure the algorithm is correct before you implement it in Python. This gives you confidence that your design is sound and will help guide the implementation.

Would you like me to help you run the model checker, or shall we move on to implementing the Python code based on this verified specification?
```

Run the tlc model checker. Kiro fixed syntactic bugs

Then there is a deadlock bug. Kiro fix deadlock bug

```
Great! The model checker is working, but it found a deadlock. Looking at the trace, I can see the issue: the coordinator completes the protocol (state 9) but there's still a participant (p2) that hasn't processed the ABORT message yet. The issue is in my CoordinatorComplete logic - it's completing too early.
```

Syntax error. It is a variable scoping issue.



----------------------- MODULE TwoPhaseCommitProperties -----------------------
EXTENDS TwoPhaseCommit

\* =============================================================================
\* SAFETY PROPERTIES
\* These properties must hold in every reachable state
\* =============================================================================

\* CORRECTNESS GUARANTEE 1: Commit Safety
\* If one participant decides commit, then every participant voted yes
CommitSafetyProperty ==
    (\E p \in Participants : pStates[p] = "COMMITTED") =>
    (\A v \in votes : v.vote = "COMMIT")

\* CORRECTNESS GUARANTEE 2: Abort Safety  
\* If one participant decides abort, then some participant voted no
AbortSafetyProperty ==
    (\E p \in Participants : pStates[p] = "ABORTED") =>
    (\E v \in votes : v.vote = "ABORT")

\* CONSISTENCY: No mixed outcomes
\* No participant commits while another aborts for the same protocol instance
ConsistencyProperty ==
    ~(\E p1, p2 \in Participants : 
        pStates[p1] = "COMMITTED" /\ pStates[p2] = "ABORTED")

\* AGREEMENT: All participants reach the same decision
\* If any participant has decided, all others are moving toward the same decision
AgreementProperty ==
    /\ (\A p1, p2 \in Participants : 
         pStates[p1] = "COMMITTED" => pStates[p2] \in {"VOTED", "COMMITTED"})
    /\ (\A p1, p2 \in Participants : 
         pStates[p1] = "ABORTED" => pStates[p2] \in {"VOTED", "ABORTED"})

\* VALIDITY: Decisions reflect actual votes
\* The coordinator's decision must be based on the actual votes received
ValidityProperty ==
    /\ (cState = "COMMITTING" => \A v \in votes : v.vote = "COMMIT")
    /\ (cState = "ABORTING" => \E v \in votes : v.vote = "ABORT")

\* NON-TRIVIALITY: The protocol can reach both outcomes
\* This is checked by ensuring both commit and abort are reachable
NonTrivialityCommit == <>(cState = "COMMITTING")
NonTrivialityAbort == <>(cState = "ABORTING")

\* =============================================================================
\* LIVENESS PROPERTIES  
\* These properties describe what must eventually happen
\* =============================================================================

\* TERMINATION: The protocol eventually completes
\* Every execution eventually reaches a terminal state
TerminationProperty ==
    <>[](cState = "COMPLETED" /\ 
         \A p \in Participants : pStates[p] \in {"COMMITTED", "ABORTED"})

\* PROGRESS: If all votes are received, a decision is made
\* The coordinator cannot stay in WAITING_FOR_VOTES forever once all votes arrive
ProgressProperty ==
    (Cardinality(votes) = Cardinality(Participants)) ~> 
    (cState \in {"COMMITTING", "ABORTING", "COMPLETED"})

\* CONDITIONAL COMMIT: If all prefer commit, eventually commit
\* When all participants have commit preference, the protocol eventually commits all
ConditionalCommitProperty ==
    (\A p \in Participants : pVotePrefs[p] = TRUE) ~> 
    (\A p \in Participants : pStates[p] = "COMMITTED")

\* CONDITIONAL ABORT: If any prefers abort, eventually abort  
\* When any participant has abort preference, the protocol eventually aborts all
ConditionalAbortProperty ==
    (\E p \in Participants : pVotePrefs[p] = FALSE) ~> 
    (\A p \in Participants : pStates[p] = "ABORTED")

\* RESPONSIVENESS: Participants eventually respond to coordinator messages
\* A participant that receives a PREPARE eventually votes
ResponsivenessVote ==
    \A p \in Participants :
        (\E m \in msgs : m.type = "PREPARE" /\ m.to = p) ~> 
        (pStates[p] = "VOTED")

\* A participant that receives a decision eventually acknowledges
ResponsivenessAck ==
    \A p \in Participants :
        (\E m \in msgs : m.type \in {"COMMIT", "ABORT"} /\ m.to = p) ~> 
        (pStates[p] \in {"COMMITTED", "ABORTED"})

\* =============================================================================
\* INVARIANTS
\* Properties that should hold in every state throughout execution
\* =============================================================================

\* STATE CONSISTENCY: Participant states are consistent with coordinator state
StateConsistencyInvariant ==
    /\ (cState = "INIT" => \A p \in Participants : pStates[p] = "INIT")
    /\ (cState = "COMMITTING" => \A p \in Participants : pStates[p] \in {"VOTED", "COMMITTED"})
    /\ (cState = "ABORTING" => \A p \in Participants : pStates[p] \in {"VOTED", "ABORTED"})
    /\ (cState = "COMPLETED" => \A p \in Participants : pStates[p] \in {"COMMITTED", "ABORTED"})

\* VOTE CONSISTENCY: Votes match participant preferences
VoteConsistencyInvariant ==
    \A v \in votes : 
        /\ v.participant \in Participants
        /\ (v.vote = "COMMIT") = pVotePrefs[v.participant]

\* MESSAGE CONSISTENCY: Messages are well-formed and relevant to current state
MessageConsistencyInvariant ==
    \A m \in msgs :
        /\ m.from \in Participants \cup {Coordinator}
        /\ m.to \in Participants \cup {Coordinator}
        /\ m.from # m.to
        /\ (m.type = "PREPARE" => m.from = Coordinator /\ m.to \in Participants)
        /\ (m.type \in {"VOTE_COMMIT", "VOTE_ABORT"} => m.from \in Participants /\ m.to = Coordinator)
        /\ (m.type \in {"COMMIT", "ABORT"} => m.from = Coordinator /\ m.to \in Participants)
        /\ (m.type = "ACK" => m.from \in Participants /\ m.to = Coordinator)

\* =============================================================================
\* COMBINED PROPERTIES FOR MODEL CHECKING
\* =============================================================================

\* All safety properties combined
AllSafetyProperties ==
    /\ CommitSafetyProperty
    /\ AbortSafetyProperty  
    /\ ConsistencyProperty
    /\ AgreementProperty
    /\ ValidityProperty
    /\ StateConsistencyInvariant
    /\ VoteConsistencyInvariant
    /\ MessageConsistencyInvariant

\* Key liveness properties for model checking
KeyLivenessProperties ==
    /\ TerminationProperty
    /\ ProgressProperty
    /\ ConditionalCommitProperty
    /\ ConditionalAbortProperty

=============================================================================
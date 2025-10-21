--------------------------- MODULE TwoPhaseCommit ---------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    Participants,     \* Set of participant processes
    Coordinator       \* The coordinator process

VARIABLES
    \* Coordinator state
    cState,           \* Coordinator's current state
    votes,            \* Votes received from participants
    
    \* Participant states  
    pStates,          \* Function: participant -> state
    pVotePrefs,       \* Function: participant -> vote preference (TRUE=commit, FALSE=abort)
    
    \* Message channels
    msgs              \* Set of messages in transit

\* Message types
Messages == [type: {"PREPARE", "VOTE_COMMIT", "VOTE_ABORT", "COMMIT", "ABORT", "ACK"},
             from: Participants \cup {Coordinator},
             to: Participants \cup {Coordinator}]

\* Coordinator states
CoordinatorStates == {"INIT", "WAITING_FOR_VOTES", "COMMITTING", "ABORTING", "COMPLETED"}

\* Participant states  
ParticipantStates == {"INIT", "VOTED", "COMMITTED", "ABORTED"}

\* Type invariant
TypeInvariant ==
    /\ cState \in CoordinatorStates
    /\ pStates \in [Participants -> ParticipantStates]
    /\ pVotePrefs \in [Participants -> BOOLEAN]
    /\ votes \subseteq [participant: Participants, vote: {"COMMIT", "ABORT"}]
    /\ msgs \subseteq Messages

\* Initial state
Init ==
    /\ cState = "INIT"
    /\ pStates = [p \in Participants |-> "INIT"]
    /\ pVotePrefs \in [Participants -> BOOLEAN]  \* Non-deterministic vote preferences
    /\ votes = {}
    /\ msgs = {}

\* Coordinator starts the protocol by sending PREPARE to all participants
CoordinatorStartProtocol ==
    /\ cState = "INIT"
    /\ cState' = "WAITING_FOR_VOTES"
    /\ msgs' = msgs \cup {[type |-> "PREPARE", from |-> Coordinator, to |-> p] : p \in Participants}
    /\ UNCHANGED <<pStates, pVotePrefs, votes>>

\* Participant receives PREPARE and responds with vote based on preference
ParticipantVote(p) ==
    /\ pStates[p] = "INIT"
    /\ \E m \in msgs : m.type = "PREPARE" /\ m.to = p /\ m.from = Coordinator
    /\ pStates' = [pStates EXCEPT ![p] = "VOTED"]
    /\ LET voteType == IF pVotePrefs[p] THEN "VOTE_COMMIT" ELSE "VOTE_ABORT"
       IN msgs' = (msgs \ {[type |-> "PREPARE", from |-> Coordinator, to |-> p]}) \cup
                  {[type |-> voteType, from |-> p, to |-> Coordinator]}
    /\ UNCHANGED <<cState, pVotePrefs, votes>>

\* Coordinator receives a vote from a participant
CoordinatorReceiveVote ==
    /\ cState = "WAITING_FOR_VOTES"
    /\ \E m \in msgs : 
        /\ m.to = Coordinator
        /\ m.type \in {"VOTE_COMMIT", "VOTE_ABORT"}
        /\ LET vote == IF m.type = "VOTE_COMMIT" THEN "COMMIT" ELSE "ABORT"
           IN votes' = votes \cup {[participant |-> m.from, vote |-> vote]}
        /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<cState, pStates, pVotePrefs>>

\* Coordinator decides to commit (all participants voted commit)
CoordinatorDecideCommit ==
    /\ cState = "WAITING_FOR_VOTES"
    /\ Cardinality(votes) = Cardinality(Participants)  \* All votes received
    /\ \A v \in votes : v.vote = "COMMIT"              \* All votes are commit
    /\ cState' = "COMMITTING"
    /\ msgs' = msgs \cup {[type |-> "COMMIT", from |-> Coordinator, to |-> p] : p \in Participants}
    /\ UNCHANGED <<pStates, pVotePrefs, votes>>

\* Coordinator decides to abort (at least one participant voted abort)
CoordinatorDecideAbort ==
    /\ cState = "WAITING_FOR_VOTES"
    /\ Cardinality(votes) = Cardinality(Participants)  \* All votes received
    /\ \E v \in votes : v.vote = "ABORT"               \* At least one abort vote
    /\ cState' = "ABORTING"
    /\ msgs' = msgs \cup {[type |-> "ABORT", from |-> Coordinator, to |-> p] : p \in Participants}
    /\ UNCHANGED <<pStates, pVotePrefs, votes>>

\* Participant receives COMMIT decision
ParticipantCommit(p) ==
    /\ pStates[p] = "VOTED"
    /\ \E m \in msgs : m.type = "COMMIT" /\ m.to = p /\ m.from = Coordinator
    /\ pStates' = [pStates EXCEPT ![p] = "COMMITTED"]
    /\ msgs' = (msgs \ {[type |-> "COMMIT", from |-> Coordinator, to |-> p]}) \cup
               {[type |-> "ACK", from |-> p, to |-> Coordinator]}
    /\ UNCHANGED <<cState, pVotePrefs, votes>>

\* Participant receives ABORT decision
ParticipantAbort(p) ==
    /\ pStates[p] = "VOTED"
    /\ \E m \in msgs : m.type = "ABORT" /\ m.to = p /\ m.from = Coordinator
    /\ pStates' = [pStates EXCEPT ![p] = "ABORTED"]
    /\ msgs' = (msgs \ {[type |-> "ABORT", from |-> Coordinator, to |-> p]}) \cup
               {[type |-> "ACK", from |-> p, to |-> Coordinator]}
    /\ UNCHANGED <<cState, pVotePrefs, votes>>

\* Coordinator receives acknowledgment
CoordinatorReceiveAck ==
    /\ cState \in {"COMMITTING", "ABORTING"}
    /\ \E m \in msgs : 
        /\ m.type = "ACK" /\ m.to = Coordinator
        /\ msgs' = msgs \ {m}
    /\ UNCHANGED <<cState, pStates, pVotePrefs, votes>>

\* Coordinator completes when all participants have acknowledged
CoordinatorComplete ==
    /\ cState \in {"COMMITTING", "ABORTING"}
    /\ \A p \in Participants : pStates[p] \in {"COMMITTED", "ABORTED"}
    /\ cState' = "COMPLETED"
    /\ UNCHANGED <<pStates, pVotePrefs, votes, msgs>>

\* Next state relation
Next ==
    \/ CoordinatorStartProtocol
    \/ \E p \in Participants : ParticipantVote(p)
    \/ CoordinatorReceiveVote
    \/ CoordinatorDecideCommit
    \/ CoordinatorDecideAbort
    \/ \E p \in Participants : ParticipantCommit(p)
    \/ \E p \in Participants : ParticipantAbort(p)
    \/ CoordinatorReceiveAck
    \/ CoordinatorComplete

\* Specification
Spec == Init /\ [][Next]_<<cState, pStates, pVotePrefs, votes, msgs>>



\* Essential properties for model checking
CommitSafety ==
    (\E p \in Participants : pStates[p] = "COMMITTED") =>
    (\A v \in votes : v.vote = "COMMIT")

AbortSafety ==
    (\E p \in Participants : pStates[p] = "ABORTED") =>
    (\E v \in votes : v.vote = "ABORT")

Consistency ==
    ~(\E p1, p2 \in Participants : 
        pStates[p1] = "COMMITTED" /\ pStates[p2] = "ABORTED")

Agreement ==
    /\ (\A p1, p2 \in Participants : 
         pStates[p1] = "COMMITTED" => pStates[p2] \in {"VOTED", "COMMITTED"})
    /\ (\A p1, p2 \in Participants : 
         pStates[p1] = "ABORTED" => pStates[p2] \in {"VOTED", "ABORTED"})

EventualTermination ==
    <>[]( cState = "COMPLETED" /\ 
          \A p \in Participants : pStates[p] \in {"COMMITTED", "ABORTED"})

=============================================================================
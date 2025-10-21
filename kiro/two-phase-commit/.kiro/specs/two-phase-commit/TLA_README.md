# TLA+ Specification for Two-Phase Commit

This directory contains the formal TLA+ specification for the two-phase commit protocol implementation.

## Files

- **TwoPhaseCommit.tla** - Main specification module defining the 2PC algorithm
- **TwoPhaseCommitProperties.tla** - Detailed safety and liveness properties
- **TwoPhaseCommit.cfg** - Standard configuration (3 participants)
- **TwoPhaseCommitSmall.cfg** - Small configuration (2 participants) for quick testing
- **TwoPhaseCommitLarge.cfg** - Large configuration (5 participants) for comprehensive testing

## Model Checking with TLC

### Prerequisites

1. Install TLA+ Tools from: https://github.com/tlaplus/tlaplus/releases
2. Ensure `tlc` is in your PATH or use TLA+ Toolbox

### Running Model Checker

#### Quick Test (2 participants)
```bash
tlc TwoPhaseCommit.tla -config TwoPhaseCommitSmall.cfg
```

#### Standard Test (3 participants)  
```bash
tlc TwoPhaseCommit.tla -config TwoPhaseCommit.cfg
```

#### Comprehensive Test (5 participants)
```bash
tlc TwoPhaseCommit.tla -config TwoPhaseCommitLarge.cfg
```

### Expected Results

The model checker should verify:

**Safety Properties:**
- ✅ **CommitSafety**: If any participant commits, all voted commit
- ✅ **AbortSafety**: If any participant aborts, at least one voted abort  
- ✅ **Consistency**: No participant commits while another aborts
- ✅ **Agreement**: All participants reach the same decision

**Liveness Properties:**
- ✅ **EventualTermination**: Protocol eventually completes
- ✅ **EventualCommit**: If all prefer commit, eventually all commit
- ✅ **EventualAbort**: If any prefers abort, eventually all abort

### Interpreting Output

**Success Output:**
```
Model checking completed. No error has been found.
Spec is valid.
```

**If errors are found:**
- TLC will show a counterexample trace
- Review the trace to understand the violation
- Check if it's a genuine bug or a modeling issue

## Key Properties Verified

### Correctness Guarantees (from Requirements)

1. **Requirement 6.1**: "If one participant decides commit, then every participant voted yes"
   - Verified by `CommitSafety` property

2. **Requirement 6.2**: "If one participant decides abort, then at least one participant voted no"  
   - Verified by `AbortSafety` property

3. **Requirement 6.3**: "No participant commits while another aborts"
   - Verified by `Consistency` property

### Protocol Correctness

- **Atomicity**: All participants reach the same decision
- **Validity**: Decisions are based on actual votes
- **Termination**: Protocol eventually completes
- **Non-triviality**: Both commit and abort outcomes are possible

## Model Parameters

### State Space Constraints

The configurations include constraints to make model checking feasible:

- **Message limit**: Bounds the number of messages in transit
- **Symmetry**: Uses participant symmetry to reduce state space
- **Participant count**: Varies from 2-5 participants

### Customizing Parameters

To test with different parameters, modify the `.cfg` files:

```
CONSTANTS
    Participants = {p1, p2, p3, p4}  \* Add/remove participants
    Coordinator = coord

CONSTRAINT
    Cardinality(msgs) <= 12          \* Adjust message limit
```

## Troubleshooting

### State Space Explosion
If model checking takes too long:
1. Reduce participant count
2. Lower message limit constraint  
3. Use smaller configuration file

### Memory Issues
```bash
tlc -Xmx4g TwoPhaseCommit.tla -config TwoPhaseCommit.cfg
```

### Deadlock Detection
Add to configuration:
```
CHECK_DEADLOCK FALSE
```

## Integration with Implementation

This TLA+ specification serves as:

1. **Design Validation**: Verify algorithm correctness before coding
2. **Implementation Guide**: Reference for Python implementation structure
3. **Test Oracle**: Expected behaviors for testing the implementation
4. **Documentation**: Formal specification of the protocol

The Python implementation should maintain the same state transitions and message flows as modeled here.
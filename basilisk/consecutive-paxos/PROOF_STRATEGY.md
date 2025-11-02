# Consecutive Paxos Safety Proof Strategy

## Protocol Correctness Analysis

### Is Consecutive Paxos Safe? YES! ✓

**Key Insight: Discreteness of Ballots**
If value V is chosen at majority consecutive ballots {3, 4}, the **discrete property of ballots** means that no other value can be "sneakily" chosen at some ballot b where 3 < b < 4. Why? Because ballots are integers - there IS no ballot between 3 and 4! This is why "consecutive" is safe: there are no gaps where another value could slip through.

**Informal Argument:**
If value V is chosen across consecutive ballots [lo, hi] by quorum Q, then any later ballot b' > hi that forms a promise quorum Q' must:
1. Intersect with Q (by quorum intersection)
2. Witness at least one ballot in [lo, hi] (the intersecting acceptor accepted in that range)
3. By "one value per ballot" property, all ballots in [lo, hi] must have the same value V
4. By "discreteness of ballots", there are no ballots BETWEEN lo and hi to worry about - the range is complete!
5. Therefore, the promise quorum forces the new proposal to be V

### Why the Current Proof is Struggling

The original Paxos helper lemma `ChosenImpliesSeenByHigherPromiseQuorumHelper` proves:
```dafny
requires accMsg.vb == chosenVB  // All accepts at SAME ballot
ensures promMsg.vbOpt.Some?
ensures chosenVB.b <= promMsg.vbOpt.value.b
```

With Consecutive Paxos, we have:
```dafny
requires accMsg.vb.v == chosenVB.v  // Same value, but...
requires accMsg.vb.b ∈ [lo, hi]      // ...DIFFERENT ballots in range!
ensures promMsg.vbOpt.Some?
ensures ??? <= promMsg.vbOpt.value.b  // What do we prove here?
```

The issue: `accMsg.vb.b` might not equal `chosenVB.b`! We can't prove `chosenVB.b <= promMsg.vbOpt.value.b` directly.

## Correct Proof Approach

### Key Lemma to Prove

Instead of trying to relate `chosenVB.b` to the witnessed ballot, we should prove:

```dafny
lemma ChosenImpliesPromiseQuorumWitnessesRange(...)
  requires Chosen(c, v.Last(), chosenVB)  // Chosen with range [lo, hi]
  requires IsPromiseQuorum(c, v, promQ, promBal)
  requires chosenVB.b < promBal
  ensures exists promMsg, witnessedBal ::
    && promMsg in promQ
    && promMsg.vbOpt.Some?
    && lo <= witnessedBal <= hi
    && witnessedBal <= promMsg.vbOpt.value.b
```

This says: "The promise quorum witnesses SOME ballot in the chosen range."

### Then Use "One Value Per Ballot" + "Discreteness"

Once we know the promise quorum witnessed some ballot `b` in [lo, hi], we need TWO properties:

**Property 1: One Value Per Ballot**
```dafny
lemma OneValuePerBallot(...)
  requires AcceptorAccepted(val1, b)
  requires AcceptorAccepted(val2, b)
  ensures val1 == val2
```
This follows from the fact that each leader has a unique ballot and proposes only one value.

**Property 2: Consecutive Range Completeness (Discreteness)**
```dafny
lemma ConsecutiveRangeComplete(...)
  requires lo <= hi
  requires forall b | lo <= b <= hi :: exists acc :: acc accepted value v at ballot b
  ensures forall b | lo < b < hi :: b is covered
  // In Dafny: this is trivial because lo <= b <= hi already covers all integers in [lo,hi]
```

The key: If we have consecutive ballots [lo, hi], and `ConsecutiveRangeCovered` holds (every ballot in range has at least one acceptor), then by discreteness, there are NO gaps. Any ballot b where lo <= b <= hi is literally in the range - no ballot can "hide" between consecutive integers.

**Property 3: All Ballots in Range Have Same Value**
```dafny
lemma AllBallotsInRangeSameValue(...)
  requires Chosen at range [lo, hi] for value v
  requires lo <= b <= hi
  requires SomeAcceptorAccepted(b)
  ensures AcceptedValue(b) == v
```

Combined with Property 1 (one value per ballot) and Property 2 (discreteness ensures no gaps), this proves safety!

### Combining Them

```dafny
lemma SafetyForConsecutiveBallots(vb1, vb2: ValBal)
  requires Chosen(c, v.Last(), vb1)  // Chosen at range [lo1, hi1]
  requires Chosen(c, v.Last(), vb2)  // Chosen at range [lo2, hi2]
  requires vb1.b < vb2.b
  ensures vb1.v == vb2.v
{
  // Get the promise quorum for vb2.b
  var promQ := GetPromiseQuorumForBallot(vb2.b);
  
  // Promise quorum witnesses some ballot in [lo1, hi1]
  var witnessedBal := ChosenImpliesPromiseQuorumWitnessesRange(vb1, promQ);
  
  // That witnessed ballot had value vb1.v
  assert AcceptorAccepted(vb1.v, witnessedBal);
  
  // The proposal at vb2.b must use the witnessed value
  var proposedAtVb2 := GetProposedValue(vb2.b);
  assert proposedAtVb2 == vb1.v;  // By promise logic
  
  // Since vb2 is chosen, it must equal the proposal
  assert vb2.v == proposedAtVb2;
  assert vb2.v == vb1.v;
}
```

## Implementation Plan

### Step 1: Weaken `ChosenImpliesSeenByHigherPromiseQuorumHelper`

Change from proving a specific relationship about `chosenVB.b` to proving that the promise quorum witnesses SOME ballot in the range:

```dafny
lemma ChosenImpliesSeenByHigherPromiseQuorumHelper(...)
  requires accMsg.vb.v == chosenVB.v
  requires lo <= accMsg.vb.b <= hi
  requires lo <= chosenVB.b <= hi
  ensures promMsg.vbOpt.Some?
  ensures accMsg.vb.b <= promMsg.vbOpt.value.b  // Witnesses the ACCEPT ballot, not chosen ballot
```

### Step 2: Use Range Witness in Main Proof

In `ChosenImpliesSeenByHigherPromiseQuorum`, instead of proving:
```dafny
ensures chosenVB.b <= promMsg.vbOpt.value.b
```

Prove:
```dafny
ensures exists bal :: lo <= bal <= hi && bal <= promMsg.vbOpt.value.b
```

Where [lo, hi] is the chosen range.

### Step 3: Connect Via "One Value Per Ballot"

Add a lemma proving that if two acceptors accepted in the same range [lo, hi], they accepted the same value (because each ballot has unique leader with unique proposed value).

### Step 4: Complete the Safety Proof

Use the above lemmas to prove that if two values are chosen, they must be equal.

## Why This Will Work

1. **Quorum Intersection**: Promise quorum MUST intersect with accept quorum (unchanged)
2. **Range Witness**: The intersection witnesses SOME ballot in the chosen range (new)
3. **One Value Per Ballot**: All ballots in the range have the same value (new property to prove)
4. **Promise Forces Value**: The witnessed value constrains the new proposal (unchanged logic)

This proof strategy respects the reality that accepts happen at different ballots within the range, while still maintaining safety through the combination of quorum intersection and the one-value-per-ballot property.


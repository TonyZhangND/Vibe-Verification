// Loop Invariants Examples
// Following AGENTS.md style: small lemmas, explicit framing, total methods

// Example 1: Array sum with basic invariants
method ArraySum(a: seq<int>) returns (sum: int)
  requires |a| >= 0
  ensures sum == SumSeq(a[..])
{
  sum := 0;
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant sum == SumSeq(a[..i])
    decreases |a| - i
  {
    assert sum == SumSeq(a[..i]);
    sum := sum + a[i];
    i := i + 1;
    
    // Use the lemma to prove the invariant is maintained
    SumSeqExtend(a, i-1);
    assert sum == SumSeq(a[..i]);
  }
  
  // Help the verifier understand the postcondition
  assert a[..i] == a[..];
}

// Ghost function for specification
function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + SumSeq(s[1..])
}

// Lemma: Adding an element extends the sum correctly
lemma SumSeqExtend(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures SumSeq(s[..i]) + s[i] == SumSeq(s[..i+1])
{
  // Use structural induction on the sequence
  if i == 0 {
    // Base case: s[..0] is empty, s[..1] is [s[0]]
    assert s[..0] == [];
    assert s[..1] == [s[0]];

  } else {
    // For the inductive case, we need a different approach
    // We'll prove this by unfolding the definition
    var prefix := s[..i];
    var extended := s[..i+1];
    
    assert extended == prefix + [s[i]];
    SumSeqAppend(prefix, [s[i]]);
  }
}

// Helper lemma: sum of concatenated sequences
lemma SumSeqAppend(s1: seq<int>, s2: seq<int>)
  ensures SumSeq(s1 + s2) == SumSeq(s1) + SumSeq(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
  } else {
    calc {
      SumSeq(s1 + s2);
    == { assert (s1 + s2)[0] == s1[0]; assert (s1 + s2)[1..] == s1[1..] + s2; }
      s1[0] + SumSeq((s1 + s2)[1..]);
    == s1[0] + SumSeq(s1[1..] + s2);
    == { SumSeqAppend(s1[1..], s2); }
      s1[0] + SumSeq(s1[1..]) + SumSeq(s2);
    == SumSeq(s1) + SumSeq(s2);
    }
  }
}

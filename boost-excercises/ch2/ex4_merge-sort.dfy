//#title Sort Specification
//#desc More specification practice.

// You are asked to define the specification (i.e. the postcondition)
// for a sorting method. Note that you are not implementing the method
// itself, just the postcondition; so there is nothing to prove. The
// autograder will check the correctness of your postcondition.
//
// Start by defining the IsSorted() predicate (which should return true
// if the given sequence is sorted). The final postcondition for the
// sort method is SortSpec(), which is currently defined as IsSorted(output),
// though can change that, if needed.

// In the end, the SortSpec predicate will be used as follows:
// method sort(input:seq<int>) returns (output:seq<int>)
//   ensures SortSpec(input, output)
// {
//   ... //body here
// }

predicate IsSorted(seqint:seq<int>)
{
/*{*/
  forall i, j | 0 <= i < j < |seqint| :: seqint[i] <= seqint[j]
/*}*/
}

predicate SortSpec(input:seq<int>, output:seq<int>)
{
/*{*/
  && IsSorted(output)
  && |output| == |input|
  && multiset(output) == multiset(input)
/*}*/
}

// Lemma to help with multiset reasoning
lemma MultisetSliceConcat<T>(s: seq<T>, i: nat)
  requires i <= |s|
  ensures multiset(s) == multiset(s[..i]) + multiset(s[i..])
{
  if i == 0 {
    assert s[..i] == [];
    assert s[i..] == s;
  } else if i == |s| {
    assert s[..i] == s;
    assert s[i..] == [];
  } else {
    assert s == s[..i] + s[i..];
  }
}

// Helper method to merge two sorted sequences
method Merge(left: seq<int>, right: seq<int>) returns (result: seq<int>)
  requires IsSorted(left)
  requires IsSorted(right)
  ensures IsSorted(result)
  ensures multiset(result) == multiset(left) + multiset(right)
  ensures |result| == |left| + |right|
{
  var i := 0;
  var j := 0;
  result := [];
  
  while i < |left| || j < |right|
    invariant 0 <= i <= |left|
    invariant 0 <= j <= |right|
    invariant |result| == i + j
    invariant multiset(result) == multiset(left[..i]) + multiset(right[..j])
    invariant IsSorted(result)
    invariant i < |left| ==> (forall k | 0 <= k < |result| :: result[k] <= left[i])
    invariant j < |right| ==> (forall k | 0 <= k < |result| :: result[k] <= right[j])
    decreases |left| - i + |right| - j
  {
    if i >= |left| {
      assert right[..j+1] == right[..j] + [right[j]];
      result := result + [right[j]];
      j := j + 1;
    } else if j >= |right| {
      assert left[..i+1] == left[..i] + [left[i]];
      result := result + [left[i]];
      i := i + 1;
    } else if left[i] <= right[j] {
      assert left[..i+1] == left[..i] + [left[i]];
      result := result + [left[i]];
      i := i + 1;
    } else {
      assert right[..j+1] == right[..j] + [right[j]];
      result := result + [right[j]];
      j := j + 1;
    }
  }
  
  MultisetSliceConcat(left, i);
  MultisetSliceConcat(right, j);
}

method MergeSort(input: seq<int>) returns (output: seq<int>)
  ensures SortSpec(input, output)
  decreases |input|
{
  if |input| <= 1 {
    return input;
  }
  
  var mid := |input| / 2;
  var left := MergeSort(input[..mid]);
  var right := MergeSort(input[mid..]);
  
  output := Merge(left, right);
  
  MultisetSliceConcat(input, mid);
}

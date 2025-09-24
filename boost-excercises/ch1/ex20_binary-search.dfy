//#desc Method implementation; writing a Hoare spec.

ghost predicate IsSorted(seqint:seq<int>) {
    forall i:nat,j:nat | i<j<|seqint| :: seqint[i] <= seqint[j]
}

// Write down the BinarySearch algorithm, which should return
// the index of the first element of the haystack that is >= to the needle.
// If the needle is present, this should be the index of the needle.
// If needle is bigger than every element, return the length of the
// sequence: It's not a valid index in the sequence, but it's bigger
// than the indices of all the elements that have smaller values.
method BinarySearch(haystack:seq<int>, needle:int) returns (index:nat)
    requires IsSorted(haystack)
    ensures index <= |haystack|
    ensures forall i | 0 <= i < index :: haystack[i] < needle
    ensures forall i | index <= i < |haystack| :: haystack[i] >= needle
{
    var low := 0;
    var high := |haystack|;
    
    while low < high
        invariant 0 <= low <= high <= |haystack|
        invariant forall i | 0 <= i < low :: haystack[i] < needle
        invariant forall i | high <= i < |haystack| :: haystack[i] >= needle
        decreases high - low
    {
        var mid := (low + high) / 2;
        
        if haystack[mid] < needle {
            low := mid + 1;
        } else {
            high := mid;
        }
    }
    
    index := low;
}


//#title Binary Tree Is Sorted
//#desc Prove an implementation meets its spec.
//#desc Practice with proof diagnosis.

// Utility functions
ghost function Last<T>(s: seq<T>): T
  requires |s| > 0
{
  s[|s|-1]
}

function LastElement(s: seq<int>): int
  requires |s| > 0
{
  s[|s|-1]
}

predicate IsSorted(seqint:seq<int>) {
    forall i:nat,j:nat | i<j<|seqint| :: seqint[i] <= seqint[j]
}

// Define a Binary Tree and write a method to check if it is sorted

// A binary tree is a tree data structure in which each (internal) node has a value and at
// most two children, which are referred to as the left child and the right child.

// you should define your Tree datatype here.
datatype Tree = Nil | Node(value: int, left: Tree, right: Tree)


// This lemma is here to guide you in defining the tree in a way
// that will help with the rest of the exercise.
lemma DatatypeCheck()
{
  var emptyTree := Nil;
  var littleTree := Node(9, Nil, Nil);
  var biggerTree := Node(10, littleTree, littleTree); // Note: not sorted
}

// You will find the following function method useful. It is meant to express
// the given tree as a sequence.
//
// Note: a function method is just like a ghost function, except it
// can be used in an "imperative" context (i.e., inside a method)

function TreeAsSequence(tree:Tree) : seq<int>
{
    match tree
    case Nil => []
    case Node(value, left, right) => 
        TreeAsSequence(left) + [value] + TreeAsSequence(right)
}

// If this predicate is true about sorted sequences, then everything
// in seq1 is <= everything in seq2.
ghost predicate SequencesOrderedAtInterface(seq1:seq<int>, seq2:seq<int>)
{
  if |seq1|==0 || |seq2|==0
  then true
  else Last(seq1) <= seq2[0]
}

// Write a recursive definition for what it means for a Tree to be sorted
ghost predicate IsSortedTree(tree:Tree) {
    IsSorted(TreeAsSequence(tree))
}

// You may find it useful to relate your recursive definition of IsSortedTree to
// a sequential representation of the tree structure

datatype TreeSortedness = Unsorted | Empty | Bounded(low: int, high: int)


// Write a recursive implementation that checks if a tree
// is sorted by checking the children, then using TreeAsSequence
// on the children to confirm that both children stay on their
// respective sides of the pivot.
method CheckIfSortedTree(tree:Tree) returns (out: TreeSortedness)
    ensures IsSortedTree(tree) <==> !out.Unsorted?
  /*{*/
  /*}*/
{
  /*{*/
  match tree {
    case Nil =>
      // Empty tree is sorted by definition
      assert IsSortedTree(tree);
      return Empty;
      
    case Node(value, left, right) =>
      // Check if the overall tree sequence is sorted
      var treeSeq := TreeAsSequence(tree);
      
      if !IsSorted(treeSeq) {
        // If the sequence is not sorted, then the tree is not sorted
        assert !IsSortedTree(tree);
        return Unsorted;
      }
      
      // Tree sequence is sorted, so tree is sorted
      assert IsSorted(treeSeq);
      assert IsSortedTree(tree);
      
      // Tree is sorted, determine bounds
      // For a single node tree, bounds are just the value
      if left == Nil && right == Nil {
        return Bounded(value, value);
      }
      
      // For trees with children, find min and max values
      var minVal := treeSeq[0];
      var maxVal := treeSeq[|treeSeq|-1];
      return Bounded(minVal, maxVal);
  }
  /*}*/
}






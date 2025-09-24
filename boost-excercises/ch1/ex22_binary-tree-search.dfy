include "ex21_binary-tree-is-sorted.dfy"

// Note: SequenceIsSorted is the same as IsSorted from ex21, so we'll use IsSorted
lemma SortedTreeMeansSortedSequence(tree:Tree)
    requires IsSortedTree(tree)
    ensures IsSorted(TreeAsSequence(tree))
{
    // This follows directly from the definition of IsSortedTree
    assert IsSortedTree(tree) == IsSorted(TreeAsSequence(tree));
}


method FindInBinaryTree(tree:Tree, needle:int) returns (found:bool)
    requires IsSortedTree(tree)
    ensures found <==> needle in TreeAsSequence(tree)
{
    var treeSeq := TreeAsSequence(tree);
    var low := 0;
    var high := |treeSeq|;
    
    while low < high
        invariant 0 <= low <= high <= |treeSeq|
        invariant forall i | 0 <= i < low :: treeSeq[i] < needle
        invariant forall i | high <= i < |treeSeq| :: needle <= treeSeq[i]
        decreases high - low
    {
        var mid := (low + high) / 2;
        
        if treeSeq[mid] < needle {
            low := mid + 1;
        } else {
            high := mid;
        }
    }
    
    found := low < |treeSeq| && treeSeq[low] == needle;
}

# Notes

Exercises are from [BOOST '25](https://web.eecs.umich.edu/~manosk/oropa/ps1.html).

## Ex 17

* For the function definition, Cursor Tab was able to do it perfectly right away. There was no need for prompting

## Ex 20

* Asked Cursor to implement the `BinarySearch` method according to the description "Implement binary search according to the description". Cursor instantly wrote all of it, including the method post-conditions and loop invariants.

## Ex 21

* Implemented `datatype Tree` myself.
* Asked Cursor "Implement `TreeAsSequence` using an in-order traversal"
  * Cursor found a bug in my `Tree` datatype. It should be a sum type with constructors `Node` and `Nil`. I forgot the `Nil`. Cursor fixed it automatically.
* Asked Cursor "Implement `IsSortedTree`"
  * Cursor knew to use helper functions `IsSorted` and `TreeAsSequence`.
* Asked Cursor "Finally, implement `CheckIfSortedTree`".
  * This is very cool. This is not entirely trivial, and I did not think of a solution myself prior to implementation. Yet Cursor gave a correct implementation.
  * Even more cool, I do not need to inspect what Cursor generated, because the fact that it passes the Dafny verifier tells me that the implementation is correct.

## Ex 22

* Start by setting some context. "Let's tackle exercise 22. Before we begin, I want to let you know that we can call upon the definitions in exercise 21."
* Complete the `FindInBinaryTree` method.
  * Again, it is insane that this works! I gave 0 thoughts to this myself before throwing it to Cursor, and Cursor could figure out all the loop invariants, including the termination clause!

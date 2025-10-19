# Notes

## Ex 1

* Should be a no-brainer. 
* But there is something interesting in proving `CompositeIsntPrime`.
  * Want to prove that for any `p` where `p > 1`,  `p*66` is not a prime.
  * To complete this proof, we need to find a witness `x` such that `2 <= x < p*66` and ``p*66 % x == 0`.
  * `x = p` and `x = 66` are both such witnesses.
  * Dafny believes the latter, `assert (p*66) % 66 == 0;`, and when Cursor chose this as the witness, things were fine.
  * However, in a different run when Cursor chose `p` as the witness, Dafny did not believe `assert (p*66) % p == 0;`, and this led Cursor on an unfruitful wild goose chase to prove this assertion, which I terminated as it wasn't going anywhere.

## Ex 2

* "Implement the `HasDivisorBelow` function"
  * It went ahead and also implemented `HasDivisorBelow_ok` lemma, which is unwanted overzealous behavior.
  * Implementation is all correct though.

## Ex 4

* "Complete the definition for `predicate IsSorted`.
  * 
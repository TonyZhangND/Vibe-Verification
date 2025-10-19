// Implement a predicate that tells whether a natural number is prime.

/*{*/
/*}*/
ghost predicate IsPrimeSpec(candidate:nat)
{
  /*{*/
  candidate >= 2 &&
  forall k | 2 <= k < candidate :: candidate % k != 0
  /*}*/
}

// illustrate IsPrimeSpec on a few examples (note that the verifier is able to
// check these only with some help to find divisors for non-prime numbers)
lemma ConstantObligations()
  ensures !IsPrimeSpec(0)
  ensures !IsPrimeSpec(1)
  ensures IsPrimeSpec(2)
  ensures IsPrimeSpec(3)
  ensures !IsPrimeSpec(4)
  ensures !IsPrimeSpec(6)
  ensures IsPrimeSpec(7)
  ensures !IsPrimeSpec(9)
{
  /*{*/
  // Help the verifier by providing divisors for composite numbers
  assert 4 % 2 == 0;
  assert 6 % 2 == 0;
  assert 9 % 3 == 0;
  // Help the verifier prove 7 is prime by checking all divisors
  assert 7 % 2 != 0;
  assert 7 % 3 != 0;
  assert 7 % 4 != 0;
  assert 7 % 5 != 0;
  assert 7 % 6 != 0;
  /*}*/
}

lemma CompositeIsntPrime(p: nat)
  requires 1 < p
  ensures !IsPrimeSpec(p*66)
{
  /*{*/
  // p*66 is composite because it has divisor 66 (when p >= 2)
  // We need to show there exists k where 2 <= k < p*66 and (p*66) % k == 0
  assert 2 <= 66 < p*66;
  assert (p*66) % 66 == 0;

  // assert (p*66) %p == 0; // This is what Dafny did not believe, and Cursor tried to prove it, but it didn't go anywhere.
  /*}*/
}


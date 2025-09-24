//#title Fibo
//#desc Recursion challenge.

ghost function fibo(val:nat) : nat
{
    if val == 0 then 0
    else if val == 1 then 1
    else fibo(val - 1) + fibo(val - 2)  // Recursive call
}

lemma Check()
  ensures fibo(0) == 0
  ensures fibo(20) == 6765
{
    // No proof needed
}

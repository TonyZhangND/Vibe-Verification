include "../../lib/MonotonicityLibrary.dfy"

module Types {
import opened UtilitiesLibrary

type LeaderId = nat
type AcceptorId = nat
type LearnerId = nat
type Value(!new, ==)
datatype ValBal = VB(v:Value, b:LeaderId)

datatype Message = Prepare(bal:LeaderId)
                | Promise(bal:LeaderId, acc:AcceptorId, vbOpt:Option<ValBal>)  //valbal is the value-ballot pair with which the value was accepted
                | Propose(bal:LeaderId, val:Value)
                | Accept(vb:ValBal, acc:AcceptorId)                 
{
  ghost function Src() : nat {
    if this.Prepare? then bal
    else if this.Promise? then acc
    else if this.Propose? then bal
    else acc
  }
}

datatype MessageOps = MessageOps(recv:Option<Message>, send:Option<Message>)


/// Some custom monotonic datatypes

datatype MonotonicVBOption = MVBSome(value: ValBal) | MVBNone
{
  ghost predicate SatisfiesMonotonic(past: MonotonicVBOption) {
    past.MVBSome? ==> (this.MVBSome? && past.value.b <= this.value.b)
  }

  ghost function ToOption() : Option<ValBal> {
    if this.MVBNone? then None
    else Some(this.value)
  }
}

datatype MonotonicValueAccepts = MVA(m: map<Value, map<LeaderId, set<AcceptorId>>>)
{
  ghost predicate SatisfiesMonotonic(past: MonotonicValueAccepts) {
    forall val |
      val in past.m
    ::
      && val in this.m
      && forall bal |
        bal in past.m[val]
      ::
        && bal in this.m[val]
        && past.m[val][bal] <= this.m[val][bal]
        && |past.m[val][bal]| <= |this.m[val][bal]|
  }

  ghost function AcceptorsForValue(val: Value) : map<LeaderId, set<AcceptorId>> {
    if val in m then m[val] else map[]
  }

  ghost function AcceptorsForValueAtBallot(val: Value, bal: LeaderId) : set<AcceptorId> {
    var perVal := AcceptorsForValue(val);
    if bal in perVal then perVal[bal] else {}
  }

  ghost function BallotsForValue(val: Value) : set<LeaderId> {
    if val in m then set bal | bal in m[val] :: bal else {}
  }
}

ghost function SingletonBallotAcceptors(bal: LeaderId, acc: AcceptorId) : map<LeaderId, set<AcceptorId>> {
  map b: LeaderId | b == bal :: {acc}
}

datatype MonotonicPromisesAndValue = PV(promises: set<AcceptorId>, value: Value, f: nat) 
{
  ghost predicate SatisfiesMonotonic(past: MonotonicPromisesAndValue) {
    && past.promises <= this.promises
    && |past.promises| <= |this.promises|
    && (forall val: Value | |past.promises| >= f+1 && past.value == val
        :: this.value == val
    )
  }
}
}
# AGENTS.md — Dafny Project Guidance

## Purpose
Teach AI agents how to:

- Prove Dafny programs with good structure and style.
- Avoid common SMT pitfalls (framing, triggers, termination).

---

## Project Context

- **Dafny version**: 4.2
- **SMT solver**: Z3
- **Build/verify**: see **Commands** below  
- **Style**: ghost-heavy proofs, small lemmas

> Agents: Prefer **small, compositional lemmas** over monolithic proofs.

## Proof Cookbook

### Hard Rules

- Never write assume statements
- Never add requires clauses to existing predicates, functions, or lemmas
- Never write `assume` statements
- Never write `requires false` as a precondition
- Timeouts are *correctness* issues, not performance issues. Prioritize fixing timeouts over assertion failures.
- A proof is successful only when there are no assertion errors, and no timeouts.

### General practices

- Z3 can handle simple non-inductive equalities on its own, so no need to write `calc` statements for those.

### Style guide

- Always write `forall x | p(x) :: q(x)` instead of `forall x :: p(x) ==> q(x)`
- For ease of reading, always use LT or LTEQ, instead of GT or GTEQ, for inequality expressions. I.e., `x < y` instead of `y > x`, and `x <= y` instead of `y >= x`.

### Spec Skeletons

```dafny
// Total function with explicit domain
function method IdempotentUpdate(s: State, x: T): State
  requires Valid(s)
  ensures  Valid(IdempotentUpdate(s, x))
  decreases |s.log|
{
  ...
}

// Method (with effects)
method Apply(s: State, x: T) returns (s': State)
  requires Valid(s)
  ensures  Valid(s')
  ensures  SpecPost(s, x, s')
  modifies s.heap
  decreases |s.log|
{
  ...
}
```

## Commands

### Verify a file

`dafny /path/to/file.dfy`

### Check one method/lemma quickly

For a method or lemma called `UpdatePreservesInvariants`,
`dafny /proc:*UpdatePreservesInvariants s/path/to/file.dfy`

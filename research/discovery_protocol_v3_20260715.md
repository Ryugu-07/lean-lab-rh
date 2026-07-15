# RH Discovery Protocol V3

Date: 2026-07-15

This protocol supplements, rather than erases, the fixed-gap and anti-gaming rules in Loop
Protocol V2. The `STOP` recorded at commit `5d75abc` closes only the automatic recent-literature
screening campaign. It does not stop the persistent RH goal.

## Global Persistence Rule

- A `STOP` decision applies only to the current branch or campaign unless the user explicitly
  requests a global stop.
- After a local stop, enter `ROUTE_SELECTION`. Do not resume the stopped branch without new
  evidence, but continue through a different route family.
- The Wong and Carvill branches remain rejected. Their Lean counterexamples are preserved and may
  be used as falsification tests, not reopened as proof routes.

## Research Campaign

A campaign contains at most six admitted research loops:

1. `ROUTE_MAP`
2. `CONJECTURE_GENERATION`
3. `ADVERSARIAL_TEST`
4. `PROOF_ATTEMPT_A`
5. `PROOF_ATTEMPT_B_OR_PIVOT`
6. `INDEPENDENT_AUDIT`

A campaign closes as exactly one of:

- `BRIDGE_REDUCED`
- `NEW_RELEVANT_LEAN_THEOREM`
- `KNOWN_THEOREM_FORMALIZED`
- `CONJECTURE_FALSIFIED`
- `BRANCH_ELIMINATED`
- `NO_PROGRESS`

After closure, choose a different route unless an independent audit identifies specific new
evidence for continuing the same route.

## Original-Conjecture Admission

Before a model-generated conjecture is admitted:

- state the mathematical proposition and proposed Lean statement exactly;
- identify its minimal assumptions and fixed-DAG position;
- determine whether it is equivalent to, stronger than, or implies RH;
- test small, finite, symmetric, degenerate, and boundary cases;
- actively seek a contradiction before a proof;
- identify the closest published result;
- explain what genuinely becomes easier if it is proved.

A conjecture that survives these tests remains a candidate. It is not available as a premise until
Lean compilation, target alignment, forbidden-item scans, and the transitive axiom audit pass.
Numerical evidence is always labelled `NUMERICAL_ONLY`.

## Anti-Cycling Rule

For each candidate record the normalized tuple

```text
(statement, assumptions, strategy, unresolved frontier)
```

Do not revisit the same tuple unless there is a new theorem, new source, new counterexample, or a
genuinely different proof mechanism. Mechanical helper lemmas for one mathematical edge remain in
one engineering batch and never count as separate research loops.

## Progress Accounting

Research activity and RH progress are separate fields. A compiled structural theorem may close a
campaign as `NEW_RELEVANT_LEAN_THEOREM` while leaving every RH hard gap unchanged. Claim
`BRIDGE_REDUCED` only when an unconditional fixed external edge is actually reduced.

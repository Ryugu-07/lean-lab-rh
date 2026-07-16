# Post-M1 Governance Pre-Registration

Date: 2026-07-13

Batch ID: `AUDIT-20260713-POST-M1-01`

## Fixed Target

- `node_id`: `M1/D governance`
- `work_class`: `AUDIT`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete
- `exact_mathematical_statement`: no new mathematical theorem; verify that the final M1 iff has
  an exact typed ledger witness and make the independent publication conditions executable.
- `exact_Lean_statement`:

```text
example :
  Mathlib.RiemannHypothesis ↔
    baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure :=
  riemannHypothesis_iff_baezDuarteComplexTarget_mem_kernelClosure
```

## External Admission

The clean-context Arch audit in
`/Users/karasuakamatsu/Downloads/review_rh_m1_audit_20260713.md` requires:

1. the exact iff witness in `TargetChecks.lean`;
2. M1/D/G1 closure to be explicit in the fixed DAG;
3. a publication gate consisting of Sol max theorem review, Lean Zulip statement review, and a
   cross-system novelty audit;
4. `G3` to remain prohibited as an automatic loop target;
5. Burnol's published distance lower bound to be the accepted adjacent research line.

## Frontier Before

- `hard_gap_before`: M1, G1, G2, and D are complete; M2/G3 was historically unselected (open under V4.1).
- `assumption_frontier_before`: the final theorem has an axiom audit and a reverse-only exact
  witness, but no exact iff witness in `TargetChecks.lean`; publication gates are prose only.
- `expected_hard_gap_delta`: none. This batch is governance and cannot be RH progress.
- `batching_reason`: all requested changes are one externally specified governance correction and
  contain no new number-theoretic lemma.

## Result Rules

- `FORMALIZATION_ONLY`: the exact witness compiles and the publication/route gates are recorded.
- `NO_PROGRESS`: any requested gate remains ambiguous or the exact witness does not compile.

## Result

`result_class`: `FORMALIZATION_ONLY`.

The exact iff witness compiles. The fixed DAG now keeps G3 out of the automatic loop, admits G4
only as known mathematics, and records all three publication gates. A clean-context Sol 5.6 max
review completed P1 with no P0-P3 finding and decision `CONTINUE`; P2 and P3 remain pending.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; the current continuation began from a compacted summary,
  and the fixed DAG was reread from disk before edits.

## Verification Record

- `lake env lean LeanLab/Riemann/TargetChecks.lean`: success;
- `lake build`: 8608 jobs, success;
- incomplete-proof scan: no `sorry`, `admit`, or `sorryAx` in project Lean files;
- explicit declaration scan: no project `axiom` or `constant` declarations;
- `git diff --check`: success.
- public governance commit: `fba10e74600b2deda36c8bd9ac73ca34730a4431`;
- public Lean Action CI: run `29224952001`, build job `86737084562`, success.

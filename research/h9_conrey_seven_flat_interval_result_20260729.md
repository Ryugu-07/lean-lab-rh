# H9 Conrey Actual Seven Flat-Interval Result

Date: 2026-07-29

Campaign: `FALSIFICATION-20260729-H9-CONREY-SEVEN-FLAT-INTERVAL-01`

Status: `FULL_ACTUAL_ADJACENT_FAMILY_FLAT_SUCCESS / IMPLEMENTATION_PUBLIC_GREEN`

## Result

The fixed full endpoint compiles without `sorry` in
`LeanLab/Riemann/ConreySevenFlatInterval.lean`.

Lean proves for the genuine Legendre character modulo seven:

1. the exact period table `0,1,1,-1,1,-1,-1`;
2. prefix mass `1` and first moment `0` through `m=3`;
3. the exact discrete sine-transform identity

   ```text
   K_7 * chi_7(n)
     = sin(2*pi*n/7) + sin(4*pi*n/7) - sin(6*pi*n/7);
   ```

4. strict positivity of `K_7`;
5. the exact exponent-two cosine Fourier sum through the second Bernoulli polynomial;
6. cancellation of the six shifted cosine sums for every `x in [3/7,4/7]`;
7. `f_7(x)=0` throughout that interval;
8. `sqrt(2)/3` is an irrational zero of the actual infinite series;
9. `7 % 8 = 7` and `7 % 8 != 3`.

The natural-zero term in the `Nat`-indexed `tsum` is zero. No finite truncation, floating-point
bound, or numerical partial sum is used in the proof.

## Historical reading

Conrey's paper later calls the flat branch unlikely because it would create an interval on which
`f_q` is identically zero. Lean proves that this exact mechanism occurs for a genuine quadratic
character immediately outside the paper's RH-imitation family. Thus the branch is not an
artifact of the earlier generic affine countermodel.

The result also explains why scope cannot be suppressed. Proposition 1 invokes Corollary 1,
stated for `q>3`, squarefree, and `q congruent to 3 mod 8`. The witness `q=7` is `7 mod 8`.
Therefore this campaign does not classify the contextually scoped proposition as false and does
not provide a counterexample in the family used to imply RH.

## Mechanical audit

- production module: 428 lines;
- direct production compile with `-DwarningAsError=true`: pass;
- `Targets.lean` warning-as-error compile: pass;
- one proven Target:
  `H9.conrey-character-sum.actual-seven-flat-interval`;
- exact open successor Target:
  `H9.conrey-character-sum.main-family-flat-exclusion`;
- eight exact TargetChecks: pass;
- eight selected transitive axiom prints: only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden scan for `sorry`, `admit`, `native_decide`, `unsafe`, and declared axioms: empty;
- `git diff --check`: pass;
- full build: `8788/8788`, pass.

## Classification

- `historical_omission_mechanism_delta=1`;
- `actual_quadratic_character_delta=1`;
- `main_family_flat_branch_delta=0`;
- `source_refutation_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Open boundary

No permitted `q congruent to 3 mod 8` flat interval has been certified or excluded. A main-family
repair must prove a nonzero first-moment theorem or otherwise rule out every flat prefix, or
produce an actual permitted-character witness and restate the source consequence. Conjecture 1,
Theorem 3, H9, and RH remain open.

## Publication gate

Freeze the current proof-source state and publish the implementation commit. Public Lean Action
CI is required before immutable evidence or a final ledger is created.

## Public implementation receipt

- frozen implementation: `e259b79773d290435b332c119ad5c81ff0ac16dc`;
- Lean Action run `30400822025`, build job `90414919121`, passed in `2m55s`;
- proof-source diff from the frozen implementation at immutable-evidence creation: empty;
- next gate: docs-only immutable evidence public CI.

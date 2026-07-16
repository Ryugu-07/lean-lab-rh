# RH Route Atlas and Conjecture Factory

Date: 2026-07-17

Status: current route-selection source under
[`rh_governance_current.md`](rh_governance_current.md). Adapted from
`/Users/karasuakamatsu/Downloads/rh_route_atlas_and_conjecture_factory_20260717.md`; numerical
quotas, categorical limits on model discovery, and unreviewed priority claims have been removed
under V4.1.

## Atlas purpose

Candidate selection starts from a stable historical map anchored in primary papers and standard
surveys. Recent manuscripts can enter when they materially affect an atlas route or supply a new
attack angle, but recency alone is not value.

Initial anchors are Bombieri's official Clay problem description, Conrey's *The Riemann
Hypothesis* survey, Sarnak's problem notes, Borwein-Choi-Rooney-Weirathmueller, the relevant
Iwaniec-Kowalski chapters, and Titchmarsh. Technical claims and documented obstructions are traced
from these maps to the original paper before admission.

Every route card records:

- route name and historical span;
- current mathematical status;
- exact statements and definitions;
- documented obstruction, with source and page/theorem location;
- formalization fit and missing mathlib infrastructure;
- what Lean can falsify, certify, or sharpen;
- up to three high-value candidate endpoints;
- nearest failed project attempt and the substantive difference of any re-entry.

The H1, H2, and H6 labels from the historical governance request remain reserved for their source
cards. The available downloaded atlas does not define those identifiers, so this file does not
invent a mapping; the cards must bind them when the original table or a source-audited replacement
is available.

## Initial route families

1. **Function-field RH and Bombieri-Stepanov.** Formalize a successful analogous proof family to
   expose which algebraic, geometric, and amplification structures survive translation to the
   number-field problem. Any priority claim requires a separate novelty audit.
2. **de Bruijn-Newman constant.** Align the `RH ↔ Lambda ≤ 0` convention and audit the proved
   bounds, heat flow, zero motion, and computable finite approximations. Candidate attacks may
   target either a documented bridge or the open sign endpoint.
3. **de Branges/Hilbert-space route.** Formalize the Conrey-Li obstruction to the proposed
   positivity condition, then determine the exact weakest failed premise and possible repairs.
4. **Arithmetic criteria.** Robin, Nicolas, Lagarias, and related divisor-sum criteria offer
   elementary RH-equivalent targets and a comparison family for the existing analytic criteria.
5. **Speiser route.** Align the exact equivalence between RH and the zero set of `zeta'` on the
   left half of the critical strip, including multiplicity and boundary conventions.
6. **Hilbert-Polya and trace/spectral routes.** Convert heuristics into conditional theorems that
   state exactly which self-adjoint realization, trace identity, or positivity property would
   imply RH; attack or falsify those conditions directly when possible.
7. **Classical failed routes.** Pólya, Turán, Mertens, and related claims supply source-grade
   counterexample and obstruction projects that calibrate FALSIFICATION and prevent route reuse.
8. **Nyman-Beurling/Baez-Duarte.** M0/M1 and Burnol infrastructure are compiled. The unconditional
   approximation endpoint M2/G3 is open; prior projection and ladder arguments are obstruction
   nodes, not a prohibition on new attacks.
9. **Weil positivity and explicit formula.** The project has several RH-equivalent compact and
   Gaussian criteria. W2/G7, the unconditional arithmetic positivity mechanism, is open for
   direct proof attempts.

## Obstruction map

An obstruction campaign records the weakest exact false or missing statement, a kernel-checked
counterexample when available, the source route it blocks, and what stronger or different premise
would repair the implication. `OBS` nodes are research assets but are never labeled RH progress
unless a compiled theorem changes the unconditional frontier.

## Conjecture factory

The factory supports constant/rate refinements, extremal test-function search, structural bridge
conjectures, spectral realizations, and any other precise statement with plausible DAG value.
There is no categorical ban on structural conjectures.

Each candidate passes:

1. **Falsification gate:** numerical tests, edge cases, finite models, and adversarial examples.
2. **Consistency gate:** Lean-checked implication comparisons against compiled facts.
3. **Value gate:** exact analysis of what the statement implies, what implies it, and which DAG
   node it unlocks.

A surviving conjecture enters a ranked pool. It remains unavailable as a premise until Lean proves
it. A candidate equivalent to or stronger than RH is allowed, but that strength must be stated.

## Selection rule

After local `STOP` or `NO_PROGRESS`, enter `ROUTE_SELECTION`. Rank candidates by expected
mathematical value, leverage from existing formal infrastructure, clarity of success/failure
criteria, quality of the documented obstruction, and information gained on failure. Direct RH,
W2/G7, and M2/G3 attacks are eligible without approval. Exposure work remains first priority and
may proceed in parallel.

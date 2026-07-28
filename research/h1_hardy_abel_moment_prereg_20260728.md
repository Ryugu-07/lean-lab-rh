# H1 Hardy Abel-Moment Amplification Preregistration

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H1-HARDY-ABEL-MOMENT-01`

Selected node: `H1-HARDY-ABEL-MOMENT-AMPLIFICATION-01`

Mode: `LITERATURE`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_PENDING`

## Exact historical statement

Let

```text
Xi(t) = riemannXi(1/2 + i*t)
K(alpha,p,t) =
  ((exp(alpha*t) + exp(-alpha*t)) * t^(2*p) * Xi(2*t))
    / (1/4 + 4*t^2).
```

For every natural `p`, Hardy's equations (2)--(4) give interior integrability for
`|alpha| < pi/2` and the one-sided Abel limit

```text
lim_(alpha -> (pi/2)-) integral_(0,infinity) K(alpha,p,t) dt
  = (-1)^p * pi * cos(pi/8) / 4^(2*p).
```

The fixed endpoint proves that this exact law forces infinitely many positive real `t` with
`Xi(t)=0`, hence infinitely many actual nontrivial zeta zeros on the critical line.

## Primary-source anchors

G. H. Hardy, *Sur les zeros de la fonction zeta(s) de Riemann*, Comptes rendus de
l'Academie des sciences 158 (1914), 1012--1014:

- page 1012, equation (1), Cahen-Mellin to xi/theta transform;
- page 1013, equations (2)--(3), the `alpha` family and `2p` derivatives;
- page 1014, equations (4)--(6), Abel boundary value and the `2^(2p)` contradiction.

Facsimile registry:
`https://gallica.bnf.fr/ark:/12148/bpt6k3111d.image.f1014.langEN`

Corrected page transcriptions tied to the facsimile:

- `https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1014`
- `https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1015`
- `https://fr.wikisource.org/wiki/Page%3AComptes_rendus_hebdomadaires_des_s%C3%A9ances_de_l%E2%80%99Acad%C3%A9mie_des_sciences%2C_tome_158%2C_1914.djvu/1016`

U. K. Sangale, *A note on Hardy's theorem*, arXiv:1606.00680, is a modern comparison source for
the different Hardy-`Z` signed-versus-absolute-integral proof. It is not used to replace Hardy's
1914 theta-moment mechanism.

## M0 definition alignment

1. Source `Xi(t)` is the project `hardyXi t`, because both are
   `riemannXi(1/2 + i*t)` with the factor `s*(s-1)/2`.
2. Source `Xi(2t)` must remain `hardyXi (2*t)`.
3. `deBruijnNewmanH_zero_eq_riemannXi` uses
   `(1 + i*z)/2`; setting `z=4*t` must compile the exact identity
   `hardyXi(2*t)=8*deBruijnNewmanH 0 (4*t)`.
4. The denominator is literally `1/4 + 4*t^2`; it is strictly positive for real `t`.
5. The source range is `-pi/2 < alpha < pi/2`.
6. The endpoint at `alpha=pi/2` is represented as a left Abel limit, not silently as an
   unconditional Bochner integral.
7. Differentiating `2p` times contributes `t^(2p)` and
   `(-1)^p/4^(2p)` on the cosine term.
8. Both eventual signs must be handled: odd `p` contradicts an eventually positive `Xi`,
   while even `p` contradicts an eventually negative `Xi`.

## Proposed Lean surface

Names may change only to match project style; the mathematical content may not weaken.

```lean
def hardyXiAbelMomentIntegrand (alpha : Real) (p : Nat) (t : Real) : Real :=
  ((Real.exp (alpha * t) + Real.exp (-alpha * t)) *
      t ^ (2 * p) * hardyXi (2 * t)) /
    (1 / 4 + 4 * t ^ 2)

def hardyXiAbelMoment (alpha : Real) (p : Nat) : Real :=
  integral (volume.restrict (Set.Ioi 0))
    (hardyXiAbelMomentIntegrand alpha p)

def HardyXiAbelMomentLaw : Prop :=
  (forall alpha p, |alpha| < Real.pi / 2 ->
    IntegrableOn (hardyXiAbelMomentIntegrand alpha p) (Set.Ioi 0)) /\
  forall p,
    Tendsto (fun alpha => hardyXiAbelMoment alpha p)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds (((-1 : Real) ^ p) * Real.pi * Real.cos (Real.pi / 8) /
        4 ^ (2 * p)))

theorem hardyXi_two_mul_eq_deBruijnNewmanH_zero_four_mul (t : Real) :
    hardyXi (2 * t) =
      8 * (deBruijnNewmanH 0 (4 * t)).re := ...

theorem not_eventually_hardyXi_two_mul_pos
    (hLaw : HardyXiAbelMomentLaw) :
    not (exists T, 1 < T /\ forall t, T < t -> 0 < hardyXi (2 * t)) := ...

theorem not_eventually_hardyXi_two_mul_neg
    (hLaw : HardyXiAbelMomentLaw) :
    not (exists T, 1 < T /\ forall t, T < t -> hardyXi (2 * t) < 0) := ...

theorem exists_hardyXi_zero_above_of_abelMomentLaw
    (hLaw : HardyXiAbelMomentLaw) (T : Real) :
    exists t, T < t /\ hardyXi t = 0 := ...

theorem infinite_criticalLineZeros_of_hardyXiAbelMomentLaw
    (hLaw : HardyXiAbelMomentLaw) :
    Set.Infinite {t : Real |
      IsNontrivialZero (hardyCriticalLinePoint t)} := ...
```

The final statement may use an equivalent set with an explicit `0<t` conjunct if that makes
the unboundedness proof cleaner. The exact actual-zero dictionary must be registered either way.

## Proof spine

1. Import the closed real-coordinate/sign module and the exact H6 `H_0=xi/8` theorem.
2. Prove the `z=4t` normalization by exact complex arithmetic and real reconstruction.
3. Establish continuity/measurability and positivity of every elementary source factor.
4. From the Abel limit, select an interior `alpha` with a negative odd moment or positive even
   moment as required by the assumed eventual sign.
5. Split `Ioi 0` into `Ioc 0 T` and `Ioi T`.
6. Bound the compact initial integral by `K*T^(2p)`, uniformly in the selected interior
   `alpha`.
7. On a fixed interval beyond `2T`, continuity and strict eventual sign give a positive lower
   bound. The tail therefore dominates `C*(2T)^(2p)`.
8. Choose the required parity with `C*2^(2p)>K`, contradicting the two bounds.
9. If there were no zero above some height, continuity on the connected tail would force one
   of the two forbidden eventual signs.
10. Convert unbounded actual `hardyXi` zeros through
    `hardyXi_eq_zero_iff_isNontrivialZero` and conclude set infinitude.

## Success criterion

Full success requires all of the following:

- the exact H1/H6 scaling theorem;
- exact interior integrand and Abel-law definitions;
- both eventual-sign contradictions;
- a zero above every real height under the law;
- an infinite set of actual project nontrivial critical-line zeros under the law;
- one aggregate endpoint in `Targets.lean`;
- exact statement witnesses, including both parities and actual-zero infinitude, in
  `TargetChecks.lean`;
- selected `#print axioms` entries in `AxiomsAudit.lean`;
- no forbidden placeholder or declaration;
- warning-as-error module compilation and full `lake build`;
- public preregistration, frozen implementation, immutable evidence, and final-ledger CI.

## Falsification and local stop

The campaign is falsified if any source normalization in M0 is inconsistent with the project
objects, if the Abel law does not imply both eventual-sign contradictions, or if a
finite/continuous countermodel satisfies the exact law while retaining an eventual sign.

The campaign records a partial obstruction and returns to `ROUTE_SELECTION` if the fixed
conditional endpoint cannot be compiled without adding an analytic premise stronger than the
published Abel law. It must not weaken success to the H1/H6 scaling identity alone.

## Assumption frontier

Before: real/even/continuous `hardyXi`, exact actual-zero dictionary, interval sign consumer,
and `deBruijnNewmanH 0 z = riemannXi((1+i*z)/2)/8` are compiled.

After full success: the whole high-moment contradiction and actual-zero infinitude consumer are
compiled, conditional on `HardyXiAbelMomentLaw`.

Still open: proving `HardyXiAbelMomentLaw` from the source Cahen-Mellin/theta formula, the
Hardy--Littlewood linear count, every positive-proportion result, H1, and RH.

No theorem in this campaign is an unconditional proof of Hardy's theorem unless the source Abel
law itself is later compiled.

## Local implementation result

The fixed endpoint is implemented in the 790-line
`LeanLab/Riemann/HardyAbelMomentAmplification.lean` module. The exact H1/H6 scaling, both
interior parity selectors, both eventual-sign contradictions, a zero above every real height,
actual critical-line zero infinitude, and the aggregate certificate compile.

The proof keeps the quantifier order required by Hardy's amplification: the compact constant is
uniform in `alpha,p`, and each signed tail has a fixed positive interval constant independent of
`alpha,p`. The odd and even branches use powers of 16 to make the `2^(2p)` ratio dominate.

The production module, Targets, 11 exact TargetChecks, and AxiomsAudit compile directly under
warning-as-error. Eight selected transitive axiom prints contain only `propext`,
`Classical.choice`, and `Quot.sound`; forbidden and resource-relaxation scans are empty;
`git diff --check` and the full `8777/8777` build pass.

This is conditional historical-source logic. `HardyXiAbelMomentLaw` is a `Prop` structure
supplied as a theorem hypothesis, not an axiom or compiled source theorem. The implementation
must pass public CI before it is frozen.

Frozen implementation `2d5b5e2e692e8622263142a1205971c611736a78` passed public Lean Action
run `30336360223`, build job `90201998436`, in `2m17s`. The proof source and all registered
statements are now frozen; immutable evidence must be docs-only.

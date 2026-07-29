# H1 Hardy--Littlewood Eta Remainder Final Ledger

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-REMAINDER-01`

Classification: `FULL_SUCCESS / HARDY_LITTLEWOOD_LEMMA3_FORMALIZED`

## Public chain

- preregistration `5402fc312747bf68a0bedcdd6e67b8dd71241ed2`: run `30492875305`,
  job `90714768715`, passed in `1m53s`;
- frozen implementation `e3341491b34959f2b1eb5d4e1fe2f6fc6cb6ac6f`: run `30495767931`,
  job `90724079010`, passed in `2m17s`;
- immutable evidence `4994f8bf406f252ed5f6de467cab30faa2254497`: run `30496035652`,
  job `90724980466`, passed in `1m33s`.

The five-file frozen proof and registration diff remains empty.

## Result

Lean verifies the actual Hardy--Littlewood Lemma 3 remainder
`4*N^(-sigma)` for `sigma>0`, `1<=N`, and `abs(t)<=N`. The proof uses exact logarithmic phase
ratios, denominator separation, inverse-coefficient variation at most one, a phase-block bound
of four, and decreasing-power Abel summation.

The naturally ordered eta sums converge locally uniformly and define a holomorphic function on
`re(s)>0`. Odd/even splitting and the identity theorem identify that function with
`(1-2^(1-s))*riemannZeta(s)` away from `s=1`. The critical-line specialization and the
existing eta-to-Theta transfer also compile.

## Historical finding

The source's full Lemma 2 Fourier-integral proof is not a necessary premise for Lemma 3's eta
conclusion. A direct finite inverse-difference mechanism suffices. This removes a historical
dependency, but it does not remove the later second-moment or counting inputs.

## Remaining route

The eta-remainder and eta-series-identification nodes are closed. The first open successors are
the eta-error second moment, the source-X mean square, and their asymptotic parameter budget.
An unconditional linear critical-zero count, H1, and RH remain open.

The global RH Goal remains active.

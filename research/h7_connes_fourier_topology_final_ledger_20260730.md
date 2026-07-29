# H7 Connes Ground-State Fourier Topology Final Ledger

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H7-CONNES-FOURIER-TOPOLOGY-01`

Classification: `FULL_SUCCESS / FOURIER_TOPOLOGY_IDENTIFIED`

## Public chain

- preregistration `fde35b125edd7de20e80727911fc1dad22471d78`: run `30486451346`,
  job `90693225570`, passed in `1m36s`;
- frozen implementation `2be884b27f505542f11ca380d8ac384b0e4bdfd2`: run `30487452115`,
  job `90696590632`, passed in `2m32s`;
- immutable evidence `68cd1fa4e4e1621c6a37e600dae3e4e3f9bc8a45`: run `30487724579`,
  job `90697494425`, passed in `2m28s`.

The five-file frozen proof and registration diff remains empty.

## Result

Lean proves that `exp(A*abs(x))`-weighted `L1` error controls centered Fourier error uniformly
on the whole closed strip `abs(Im z)<=A`, and proves the two-stage sequence transfer in both the
generic transform and literal ground-state source coordinates.

Lean also proves that smooth compactly supported packets can escape to infinity with unweighted
`L1` and squared `L2` masses tending to zero while their transform at `-i/4` remains one.
Therefore ordinary support-blind convergence cannot fill the approximation premise in the
Connes ground-state route.

The aggregate theorem is `weilGroundStateFourierTopology_endpoint`.

## Remaining route

The topology node is closed. The first actual comparison successor is an
`exp(A*abs(x))`-weighted estimate for `theta_x-k_lambda` for each fixed `A<1/2`; the
simple-even ground-state theorem is separately open. The all-real-zero limit, H7, and RH remain
open.

The global RH Goal remains active.

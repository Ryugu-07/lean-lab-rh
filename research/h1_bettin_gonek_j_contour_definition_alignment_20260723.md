# H1 Bettin--Gonek J-Contour Definition Alignment

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H1-BETTIN-GONEK-J-CONTOUR-01`

Source: Bettin--Gonek, arXiv:1604.02740, equations `(2.3)`--`(2.5)`.

## Source objects

- `bettinGonekH t w` is the already compiled Mellin transform of the literal real-cutoff Mobius
  mollifier, with value `1/((w-1)^2*zeta(w-1/2+it))` on `Re(w)>3/2`.
- `bettinGonekAuxiliaryG rho t w` is the already compiled removable extension of the source
  auxiliary quotient. Away from its patched points it is the displayed `G_t(w)`.
- `bettinGonekJKernel rho t x w` is exactly
  `(w-3/2+it)*x^w / ((w-(rho+1/2-it))*(w+1)^2*(w+it+1)^4)`.
- `bettinGonekJLineIntegral rho t x sigma` is `1/(2*pi)` times the ordinate integral on
  `Re(w)=sigma`. This equals the source `1/(2*pi*i)` contour integral because `dw=i dy`.

## Pole and residue

The selected pole is `rho+1/2-it`. For a nontrivial zeta zero its real part lies strictly between
zero and three, while the other rational poles have real part `-1` and remain outside the closed
rectangle. Removing the selected factor gives the source coefficient

```text
x^(rho+1/2-it) * (rho-1) /
  ((rho+3/2-it)^2 * (rho+3/2)^4).
```

Its norm is the positive scale

```text
norm(rho-1) /
  (norm(rho+3/2-it)^2 * norm(rho+3/2)^4)
```

times `x^(Re(rho)+1/2)`.

## Contour orientation and bounds

The positive rectangle orientation yields right vertical minus left vertical equal to
`2*pi*residue` plus the bottom-minus-top horizontal correction. Both horizontal corrections tend
to zero. On the zero line the actual kernel is bounded by `4/(1+(y+t)^2)`, so the normalized
boundary integral has norm at most `2`, uniformly in `x`.

## Alignment verdict

No sign, `i`, `2*pi`, exponent, pole-location, denominator, or contour-orientation mismatch was
found. The campaign does not align or prove inverse Mellin support, standalone auxiliary decay,
convolution `(2.4)`, moment transfer, Farmer's conjecture, H1, or RH.

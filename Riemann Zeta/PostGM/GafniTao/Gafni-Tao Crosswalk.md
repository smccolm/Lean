# Gafni--Tao v1 paper-to-Lean crosswalk

Authoritative target: `Exceptional_Intervals.tex` from arXiv:2505.24017v1,
SHA-256 recorded in `Sources/SHA256SUMS.txt`. This crosswalk distinguishes a
source statement from a kernel-checked consumer. An `OPEN` row is not supplied
by a declaration with a similar name.

| Source item | Exact convention in the paper | Isolated Lean object | Status |
|---|---|---|---|
| Definition 1.1, `E_delta(X,theta)` | Lebesgue-measurable real `x in [X,2X]`; literal `x<n<=x+x^theta`; `Lambda` includes every prime power; discrepancy threshold `>= delta*x^theta` | `GafniTao.shortIntervalExceptionalSet`, `mangoldtShortSum`, `shortIntervalDiscrepancy`, and `measurableSet_shortIntervalExceptionalSet` in `Extension/GafniTao/ExceptionalSet.lean` | Kernel-checked definition and measurability |
| `mu_delta(theta)` | Infimum of fixed exponents `xi` with one eventual `O_{delta,theta}(X^xi)` bound; no epsilon; value `-infinity` if eventually empty | `FixedPowerBound`, `leastFixedPowerExponent`, `exceptionalExponentDelta`; empty case `exceptionalExponentDelta_eq_bot_of_eventually_empty` | Kernel-checked interfaces; further limiting interfaces remain OPEN |
| `mu(theta)` | `sup_{delta>0} mu_delta(theta)` | `exceptionalExponent`; countable family `countableExceptionalExponent`; equality `exceptionalExponent_eq_countable` | Kernel-checked exact positive-threshold diagonal family; construction of the global exceptional set remains OPEN |
| `A(sigma)` | Least `a` such that for every epsilon, `N(sigma,T) << T^(a(1-sigma)+epsilon)`; multiplicity counted | `ZeroDensityEnvelope`, `zeroDensityExponent` in `Extension/GafniTao/ZeroEnergy.lean`; `zeroCount` and `zeroCount_eq_weighted_sum` in `SourceConventions.lean` | Kernel-checked definition and upper-bound interface; complete EReal converse/limit interface remains OPEN |
| `N*(sigma,T)` | Ordered four-tuples from `Z(sigma,T)^4`, product multiplicity, `|gamma1+gamma2-gamma3-gamma4|<=1` | `zeroAdditiveEnergyCount`, `resonantZeroQuadruples`, `zeroQuadrupleWeight`; exact membership theorem `mem_resonantZeroQuadruples` | Kernel-checked finite formulation; explicit multiset-equivalence theorem remains OPEN |
| `A*(sigma)` | Least epsilon-loss exponent for `N*` normalized by `1-sigma` | `ZeroAdditiveEnergyEnvelope`, `zeroAdditiveEnergyExponent` | Kernel-checked definition and upper-bound interface; complete EReal converse/limit interface remains OPEN |
| Theorem 1.1 (`folklore`) | Uniform `A(sigma)<=A0`; all intervals for `theta>1-1/A0`; almost all for `theta>1-2/A0` | No public theorem yet | OPEN (GT-20) |
| Theorem 1.2, equation `muth` | `inf_{epsilon>0}` of an empty-supremum-aware constraint using the actual `A`; no continuity assumption | No public theorem yet | OPEN (GT-18--GT-20) |
| Alternate equation `muth-12` | `max(1-theta, ...)`, restricting the inner supremum to `1/2<sigma<1` | No public theorem yet | OPEN (GT-20) |
| Theorem 1.3 (`refined-bound`) | Same mandatory epsilon infimum, with `min(mu_2,mu_4)` using actual `A,A*` | No public theorem yet | OPEN (GT-19) |
| Section 2 local cover | Cover `[X,2X]` by `O_delta(1)` intervals `[Y,(1+delta/J)Y]` | No public theorem yet | OPEN (GT-07) |
| Brun--Titchmarsh replacement | `tau=X^(1-theta)`; replace `x^theta` by `x/tau`, with both length and Mangoldt-sum error `O((delta/J)x^theta)` | No public theorem yet | OPEN (GT-07) |
| Explicit formula before (2.3) | `T=J(log X)^2 tau`; paper prints a positive zero sum. The conventional formula has a negative zero sum. Since (2.3) takes an absolute value, the paper's downstream statement is sign invariant, but Lean must prove and record the sign bridge. Pole, trivial-zero, prime-power, endpoint and truncation errors remain explicit obligations. | `mangoldtIntervalSum_eq_psi_sub` and `mem_mangoldtInterval` provide only the exact arithmetic entry | OPEN (GT-08) |
| Equation (2.3), label `targ` | Exceptional measure reduced to `|S_[0,1](x)| >= delta X/(3 tau)` | No public theorem yet | OPEN (GT-08) |
| Equation (2.4), label `six` | Sum over nontrivial zeros with multiplicity and real part in `I`; coefficient `((x+x/tau)^rho-x^rho)/rho` | No public theorem yet | OPEN (GT-08) |
| Equation (2.6), label `eta-vanish` | VK zero-free region at `T=X^(1-theta+o(1))` | No public theorem yet | OPEN (GT-09) |
| Lemma 2.1 | Uniform exponential right-edge decay; uses a logarithmic near-one density theorem, not a generic `T^epsilon` bound | No public theorem yet | OPEN (GT-10--GT-11) |
| Lemma 2.2 | Exact `L-infinity` exponent with physical `X,T,tau` relations and actual `A(sigma_-)` | No public theorem yet | OPEN (GT-12) |
| Lemma 2.3 | Smoothed log-variable second moment; complex Fourier transform and exact `c_rho` | No public theorem yet | OPEN (GT-13--GT-14) |
| Lemma 2.4 | Smoothed fourth moment; pair-count `F`, Schur test, and actual `N*` | No public theorem yet | OPEN (GT-15--GT-16) |
| Equation (2.7), label `targ-2` | Half-open strips `[j/J,(j+1)/J)`; line `Re rho=1` excluded; right-edge, small-`A`, `L2`, and `L4` branches | No public theorem yet | OPEN (GT-17) |
| Section 3 first sample | `theta=17/30`, limiting `sigma=7/10`, Heath--Brown `A* -> 235/39`, conclusion `mu(17/30)<=7/12` | No public theorem yet | OPEN (GT-22--GT-23) |
| Section 3 second sample | sufficiently small quantified `Delta>0`; Pintz gives cutoff `sigma<=23/24`; conclusion `mu(2/15+Delta)<=1-9Delta/13` | No public theorem yet | OPEN (GT-22--GT-23) |
| Frozen Guth--Maynard input | Published full-range exponent `15/(3+5 sigma)`, and hence uniform `30/13` | `frozen_guthMaynard_zero_density`, `guthMaynard_zeroDensityEnvelope`, `zeroDensityExponent_le_guthMaynard` | Kernel-checked direct consumer; uniform `30/13` and threshold arithmetic remain OPEN |

## Boundary and normalization ledger

- `zeroSet sigma T` is the frozen rectangle `zerosInRect sigma 1 (-T) T`.
  Distinct representatives are weighted by `analyticVanishingOrder`; neither
  `N` nor `N*` is a distinct-zero count.
- The exceptional interval is closed in `x` at both `X` and `2X`, while the
  arithmetic interval is half-open: `x<n<=x+x^theta`. The source proof later
  works on `[X,(1+delta/J)X)`; that is a derived localization, not a change to
  Definition 1.1.
- `mu_delta` uses fixed-power eventual bounds. `A` and `A*` use epsilon-power
  bounds. These notions are deliberately separate in Lean.
- All exponent infima/suprema live in `EReal`, so the paper's empty supremum
  is literally `bot` rather than an arbitrary real default.
- A frozen theorem is credited only where the new proof term consumes it.
  Currently the direct GM density consumer is the only completed post-freeze
  analytic edge in this table.

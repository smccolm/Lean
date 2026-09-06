import GafniTao.HeathBrownTwelfthStatement
import RiemannZeta.GuthMaynard.ArithmeticCoefficients
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# The Atkinson phase and divisor sum in Heath--Brown's twelfth moment proof

This file records the literal oscillatory sum occurring in Heath--Brown
(1978), equations (10)--(11).  The endpoint convention is `K < n <= K+x`;
for real `x` this is represented by `Finset.Ioc K (K + Nat.floor x)`.
The definitions retain the alternating sign, divisor coefficient, and the
complete Atkinson phase.
-/

open Complex Finset Real
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The ordinary divisor coefficient `d(n)` in Heath--Brown's transformed
sum. -/
def heathBrownDivisorCoefficient (n : Nat) : Nat :=
  n.divisors.card

/-- Heath--Brown's phase `f(T,n)` from equation (11). -/
noncomputable def heathBrownAtkinsonPhase (T : Real) (n : Nat) : Real :=
  2 * T * Real.arsinh
      (Real.sqrt (Real.pi * (n : Real) / (2 * T))) +
    Real.sqrt
      (2 * Real.pi * (n : Real) * T +
        Real.pi ^ (2 : Nat) * (n : Real) ^ (2 : Nat)) -
    Real.pi / 4

/-- The exact finite sum `S(x,K,T)` in Heath--Brown's equation (10). -/
noncomputable def heathBrownAtkinsonSum
    (x : Real) (K : Nat) (T : Real) : Complex :=
  ∑ n ∈ Finset.Ioc K (K + Nat.floor x),
    (-1 : Complex) ^ n *
      (heathBrownDivisorCoefficient n : Complex) *
      Complex.exp
        ((heathBrownAtkinsonPhase T n : Complex) * Complex.I)

/-- The source sum has no term at `x=0`. -/
theorem heathBrownAtkinsonSum_zero (K : Nat) (T : Real) :
    heathBrownAtkinsonSum 0 K T = 0 := by
  simp [heathBrownAtkinsonSum]

/-- The terminal value uses exactly the dyadic interval `(K,2K]`. -/
theorem heathBrownAtkinsonSum_nat_terminal (K : Nat) (T : Real) :
    heathBrownAtkinsonSum (K : Real) K T =
      ∑ n ∈ Finset.Ioc K (2 * K),
        (-1 : Complex) ^ n *
          (heathBrownDivisorCoefficient n : Complex) *
          Complex.exp
            ((heathBrownAtkinsonPhase T n : Complex) * Complex.I) := by
  simp [heathBrownAtkinsonSum, two_mul]

/-- The real cutoff enters the source sum only through its floor. -/
theorem heathBrownAtkinsonSum_eq_floor
    (x : Real) (K : Nat) (T : Real) :
    heathBrownAtkinsonSum x K T =
      heathBrownAtkinsonSum (Nat.floor x : Real) K T := by
  unfold heathBrownAtkinsonSum
  rw [Nat.floor_natCast]

/-- Each oscillatory factor in the Atkinson sum has unit norm. -/
theorem norm_heathBrownAtkinsonOscillation
    (T : Real) (n : Nat) :
    ‖(-1 : Complex) ^ n *
        Complex.exp
          ((heathBrownAtkinsonPhase T n : Complex) * Complex.I)‖ = 1 := by
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    Complex.norm_exp]
  norm_num

/-- The norm of a summand is exactly the divisor coefficient. -/
theorem norm_heathBrownAtkinsonSummand
    (T : Real) (n : Nat) :
    ‖(-1 : Complex) ^ n *
        (heathBrownDivisorCoefficient n : Complex) *
      Complex.exp
          ((heathBrownAtkinsonPhase T n : Complex) * Complex.I)‖ =
      (heathBrownDivisorCoefficient n : Real) := by
  rw [show
      (-1 : Complex) ^ n *
          (heathBrownDivisorCoefficient n : Complex) *
          Complex.exp
            ((heathBrownAtkinsonPhase T n : Complex) * Complex.I) =
        ((-1 : Complex) ^ n *
          Complex.exp
            ((heathBrownAtkinsonPhase T n : Complex) * Complex.I)) *
          (heathBrownDivisorCoefficient n : Complex) by ring]
  rw [norm_mul, norm_heathBrownAtkinsonOscillation,
    Complex.norm_natCast, one_mul]

/-- The exact triangle-inequality majorant before any divisor estimate is
applied. -/
theorem norm_heathBrownAtkinsonSum_le_divisorSum
    (x : Real) (K : Nat) (T : Real) :
    ‖heathBrownAtkinsonSum x K T‖ ≤
      ∑ n ∈ Finset.Ioc K (K + Nat.floor x),
        (heathBrownDivisorCoefficient n : Real) := by
  unfold heathBrownAtkinsonSum
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro n hn
  exact (norm_heathBrownAtkinsonSummand T n).le

/-- The elementary coefficient bound `d(n) <= n`, retained separately from
the oscillatory estimate. -/
theorem heathBrownDivisorCoefficient_le_self (n : Nat) :
    heathBrownDivisorCoefficient n ≤ n := by
  exact Nat.card_divisors_le_self n

#print axioms heathBrownAtkinsonSum_zero
#print axioms heathBrownAtkinsonSum_nat_terminal
#print axioms heathBrownAtkinsonSum_eq_floor
#print axioms norm_heathBrownAtkinsonOscillation
#print axioms norm_heathBrownAtkinsonSummand
#print axioms norm_heathBrownAtkinsonSum_le_divisorSum
#print axioms heathBrownDivisorCoefficient_le_self

end

end GafniTao

import Dubon2026.RectangularDualSeries
import Dubon2026.Gamma0CompletedCusp

/-! # Genuine dual cusp coefficients for every divisor of the original level -/

namespace Dubon2026

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- Every actual level divisor leaves a strictly positive complementary factor. -/
theorem levelDivisor_quotient_pos {Q : ℕ} [NeZero Q] (d : Q.divisors) : 0 < Q / d.val := by
  have h := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors d.property)
  have hp : 0 < (Q / d.val) * d.val := by rw [h]; exact Nat.pos_of_neZero Q
  by_contra hn
  have hz : Q / d.val = 0 := Nat.eq_zero_of_not_pos hn
  rw [hz, zero_mul] at hp
  exact (lt_irrefl 0) hp

/-- The original cusp form viewed at the equal product level, with its actual values unchanged. -/
def divisorProductCuspForm {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (d : Q.divisors) :
    CuspForm ((Gamma0 ((Q / d.val) * d.val)).map (mapGL ℝ)) k :=
  cuspRestrictSubgroup (by rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors d.property)]) f

/-- The equal-level adapter preserves the genuine cusp function pointwise. -/
theorem divisorProductCuspForm_apply {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (d : Q.divisors) (z : ℍ) :
    divisorProductCuspForm f d z = f z := rfl

/-- The actual rescaled finite-cusp coefficients attached to a literal divisor of the original level. -/
def divisorRectangularDualCoefficients {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (d : Q.divisors) : ℕ → ℂ :=
  letI : NeZero (Q / d.val) := ⟨(levelDivisor_quotient_pos d).ne'⟩
  letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
  rectangularDualCoefficients (divisorProductCuspForm f d)

/-- Every divisor component consists of real nonnegative actual coefficients and vanishes at zero. -/
theorem divisorRectangularDualCoefficients_positive {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (d : Q.divisors) :
    divisorRectangularDualCoefficients f d 0 = 0 ∧
      (∀ n, 0 ≤ (divisorRectangularDualCoefficients f d n).re) ∧
      (∀ n, (divisorRectangularDualCoefficients f d n).im = 0) := by
  letI : NeZero (Q / d.val) := ⟨(levelDivisor_quotient_pos d).ne'⟩
  letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
  exact rectangularDualCoefficients_positive (divisorProductCuspForm f d)

/-- Each genuine divisor component satisfies the quantitative linear coefficient mean. -/
theorem exists_divisorRectangularDual_sum_upper {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) (d : Q.divisors) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.Icc 1 X, (divisorRectangularDualCoefficients f d n).re) ≤ C * X := by
  letI : NeZero (Q / d.val) := ⟨(levelDivisor_quotient_pos d).ne'⟩
  letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
  exact exists_rectangularDual_sum_upper (divisorProductCuspForm f d) hk

/-- Every actual divisor-component Dirichlet series converges absolutely on Re(s)>1. -/
theorem divisorRectangularDual_lseriesSummable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) (d : Q.divisors)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (divisorRectangularDualCoefficients f d) s := by
  letI : NeZero (Q / d.val) := ⟨(levelDivisor_quotient_pos d).ne'⟩
  letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
  exact rectangularDual_lseriesSummable (divisorProductCuspForm f d) hk hs

/-- Equal-level transport preserves the literal rectangular integral and its genuine fundamental domain. -/
theorem rectangularLatticeCuspCompleted_divisor_adapter {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (d : Q.divisors) (s : ℂ) :
    rectangularLatticeCuspCompleted f Q d.val (Nat.pos_of_neZero Q) (Nat.pos_of_mem_divisors d.property) s =
      rectangularLatticeCuspCompleted (divisorProductCuspForm f d) ((Q / d.val) * d.val) d.val
        (Nat.mul_pos (levelDivisor_quotient_pos d) (Nat.pos_of_mem_divisors d.property))
        (Nat.pos_of_mem_divisors d.property) s := by
  unfold rectangularLatticeCuspCompleted
  change (∫ z : ℍ in gamma0FundamentalDomain Q,
      latticeCompletedMellin (rectangularLatticePoint Q d.val _ _ z) s * petersson k f f z) =
    (∫ z : ℍ in gamma0FundamentalDomain ((Q / d.val) * d.val),
      latticeCompletedMellin (rectangularLatticePoint ((Q / d.val) * d.val) d.val _ _ z) s * petersson k f f z)
  simp only [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors d.property)]

/-- The original divisor lattice integral has the exact genuine dual series on the reflected convergence half-plane. -/
theorem rectangularLatticeCuspCompleted_divisor_reflected {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) (d : Q.divisors)
    {s : ℂ} (hs : s.re < 0) :
    rectangularLatticeCuspCompleted f Q d.val (Nat.pos_of_neZero Q) (Nat.pos_of_mem_divisors d.property) s =
      rectangularDualFactor (Q / d.val) d.val k (1 - s) *
        LSeries (divisorRectangularDualCoefficients f d) (1 - s) := by
  letI : NeZero (Q / d.val) := ⟨(levelDivisor_quotient_pos d).ne'⟩
  letI : NeZero d.val := ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩
  rw [rectangularLatticeCuspCompleted_divisor_adapter f d s]
  exact rectangularLatticeCuspCompleted_reflected_dual (divisorProductCuspForm f d) hk hs

/-- The completed cusp function at every positive level is a finite signed sum of actual convergent dual series, preserving each divisor's exact completion factor. -/
theorem gamma0CompletedCusp_reflected_dual {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ} (hs : s.re < 0) :
    gamma0CompletedCusp f s = ∑ d : Q.divisors,
      (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s) *
        rectangularDualFactor (Q / d.val) d.val k (1 - s) *
          LSeries (divisorRectangularDualCoefficients f d) (1 - s) := by
  rw [gamma0CompletedCusp_eq_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [rectangularLatticeCuspCompleted_divisor_reflected f hk d hs]
  ring

end
end Dubon2026

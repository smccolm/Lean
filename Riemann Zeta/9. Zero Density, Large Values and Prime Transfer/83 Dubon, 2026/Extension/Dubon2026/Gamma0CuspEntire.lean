import Dubon2026.LatticeCuspFunctionalEquation
import Dubon2026.CuspRankinContinuation

/-! # The actual completed Rankin identity and entire finite lattice completion -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The true completed lattice-cusp integral equals the precise principal-character, Gamma and Rankin factors in the convergence half-plane. -/
theorem gamma0CompletedCusp_eq_rankin {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    gamma0CompletedCusp f s = gamma0CompletionFactor Q s * cuspRankinFactor k s * cuspRankinSeries f s := by
  have h := (div_eq_iff (gamma0CompletionFactor_ne_zero Q (by linarith))).mp
    (gamma0CuspEisensteinContinuation_eq_div f s).symm
  rw [gamma0CuspEisensteinContinuation_eq_rankin f hk hs] at h
  rw [h]
  ring

/-- The actual entire finite Möbius lattice completion of the general-level cusp integral. -/
def gamma0CuspEntire {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) : ℂ :=
  ∑ d : Q.divisors, (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s) *
    rectangularLatticeCuspEntire f Q d.val (Nat.pos_of_neZero Q) (Nat.pos_of_mem_divisors d.property) s

/-- The finite completion is entire, with every actual lattice factor and coefficient justified. -/
theorem differentiable_gamma0CuspEntire {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : Differentiable ℂ (gamma0CuspEntire f) := by
  intro s
  apply DifferentiableAt.fun_sum
  intro d hd
  exact (differentiable_gamma0LatticeCoefficient Q (Nat.pos_of_neZero Q) d s).mul
    (differentiable_rectangularLatticeCuspEntire f Q d.val (Nat.pos_of_neZero Q)
      (Nat.pos_of_mem_divisors d.property) s)

/-- The entire finite completion is exactly s(s−1) times the true completed cusp integral away from its possible poles. -/
theorem gamma0CuspEntire_eq {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    gamma0CuspEntire f s = s * (s - 1) * gamma0CompletedCusp f s := by
  rw [gamma0CuspEntire, gamma0CompletedCusp_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [rectangularLatticeCuspEntire_eq f Q d.val (Nat.pos_of_neZero Q)
    (Nat.pos_of_mem_divisors d.property) hs0 hs1]
  ring

/-- The actual completed general-level cusp integral reflects to a finite sum of the genuine self-dual rectangular integrals. -/
theorem gamma0CompletedCusp_reflected_sum {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) :
    gamma0CompletedCusp f (1 - s) =
      ∑ d : Q.divisors, (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (s - 1) *
        rectangularLatticeCuspCompleted f Q d.val (Nat.pos_of_neZero Q)
          (Nat.pos_of_mem_divisors d.property) s := by
  rw [gamma0CompletedCusp_eq_sum]
  simp only [neg_sub, rectangularLatticeCuspCompleted_functional_equation]

end
end Dubon2026

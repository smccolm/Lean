import Dubon2026.AlmostAnalyticRootCount

/-! # Uniform degree bound for the actual vertical phase polynomial -/

namespace Dubon2026

open Polynomial Complex

noncomputable section

theorem realNormPolynomial_natDegree_le (P : ℂ[X]) :
    (realNormPolynomial P).natDegree ≤ 2 * P.natDegree := by
  have he := congrArg Polynomial.natDegree (map_realNormPolynomial P)
  rw [Polynomial.natDegree_map] at he
  rw [he]
  calc
    (P * P.map (starRingEnd ℂ)).natDegree ≤ P.natDegree + (P.map (starRingEnd ℂ)).natDegree :=
      Polynomial.natDegree_mul_le
    _ = 2 * P.natDegree := by rw [Polynomial.natDegree_map]; omega

theorem verticalLinePolynomial_natDegree_le (P : ℂ[X]) (σ : ℝ) :
    (verticalLinePolynomial P σ).natDegree ≤ P.natDegree := by
  have hlin : (C (σ : ℂ) + C I * X).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  exact Polynomial.natDegree_comp_le.trans
    ((Nat.mul_le_mul_left P.natDegree hlin).trans_eq (Nat.mul_one _))

theorem phaseVerticalRealPolynomial_natDegree_le (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u T σ : ℝ) (x : PrimeCoordinate N → ℝ) :
    (phaseVerticalRealPolynomial a N hN ha l u T σ x).natDegree ≤
      2 * twistZeroCount a N hN ha l u T (fun p => (x p : UnitAddCircle)) := by
  unfold phaseVerticalRealPolynomial
  apply (realNormPolynomial_natDegree_le _).trans
  apply (Nat.mul_le_mul_left 2 (verticalLinePolynomial_natDegree_le _ σ)).trans
  unfold complexPhaseZeroPolynomial
  rw [rectangleZeroPolynomial_natDegree]
  have hc : complexPhaseCoefficients a N (complexifyPhase x) =
      twistedCoefficients a N (fun p => (x p : UnitAddCircle)) :=
    complexPhaseCoefficients_real a N x
  simp only [hc, twistZeroCount, le_refl]

theorem exists_uniform_phaseVerticalRealPolynomial_degree_bound (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u T σ : ℝ) :
    ∃ d : ℕ, ∀ x : PrimeCoordinate N → ℝ,
      (phaseVerticalRealPolynomial a N hN ha l u T σ x).natDegree ≤ d := by
  obtain ⟨K, hK⟩ := exists_uniform_twistZeroCount_bound hN ha l u T
  exact ⟨2 * K, fun x => (phaseVerticalRealPolynomial_natDegree_le a N hN ha l u T σ x).trans
    (Nat.mul_le_mul_left 2 (hK _))⟩

end

end Dubon2026

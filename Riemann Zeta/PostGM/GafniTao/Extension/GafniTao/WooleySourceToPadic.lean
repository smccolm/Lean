import GafniTao.WooleyCoefficientBridge
import GafniTao.WooleyPadicConcentration

/-!
# Source Corollary 3.2 implies the monomial p-adic concentration theorem

This is the exact downstream specialization needed by Section 12.  It keeps
the source polynomial theorem stronger than the coefficient-one modular
statement and proves all normalization and conditioning conversions.
-/

namespace GafniTao

noncomputable section

theorem wooleyPadicCount_degree_zero (Q p h : ℕ) :
    wooleyPadicCount (fordVinogradovKappa 0) 0 Q p (0 * h) = 1 := by
  simp [wooleyPadicCount, fordVinogradovKappa, WooleyPadicSolution]

theorem wooley_mul_ceilDiv_self
    {k h : ℕ} (hk : 1 ≤ k) : (k * h) ⌈/⌉ k = h := by
  simpa only [nsmul_eq_mul] using
    (smul_ceilDiv (α := ℕ) (β := ℕ) (a := k) (by omega : 0 < k) h)

/-- The full source-faithful polynomial Corollary 3.2 discharges the exact
coefficient-one p-adic input used by the critical VMVT consumer. -/
theorem wooleyMonomialPadicConcentration_of_polynomialCorollary32
    (hsource : WooleyPolynomialCorollary32) :
    WooleyMonomialPadicConcentration := by
  intro k p hp hkp delta hdelta
  by_cases hkzero : k = 0
  · subst k
    refine ⟨1, by norm_num, 0, ?_⟩
    intro Q h hQ hB hQph
    rw [wooleyPadicCount_degree_zero]
    simp [fordVinogradovKappa]
  · have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hkzero
    letI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨C, hC, B0, hmain⟩ :=
      hsource k p hp hk hkp 1 delta (by norm_num) hdelta
    refine ⟨C, hC, B0, ?_⟩
    intro Q h hQ hB hQph
    let gamma : Fin Q → ℂ := fun _ => 1
    let phi := wooleyMonomialPolynomialSystem k
    have hPhi : phi.InPhiTau p (k * h) 1 := by
      refine ⟨k * h, wooleyMonomialPolynomialSystem_spaced k p (k * h), ?_⟩
      norm_num
    have hadm : (wooleyBoxSourceSequence gamma).Admissible := by
      exact wooleyBoxSourceSequence_one_admissible Q
    have hbound := hmain (k * h) phi (wooleyBoxSourceSequence gamma)
      hB hPhi hadm
    have hceil : (k * h) ⌈/⌉ k = h := wooley_mul_ceilDiv_self hk
    have hs : 1 ≤ wooleyTriangular k := by
      simp only [wooleyTriangular]
      have : 2 ≤ k * (k + 1) := by nlinarith
      omega
    have hconditioned :
        wooleySourcePolynomialConditionedMean
            (wooleyTriangular k) (p ^ (k * h))
              (p ^ ((k * h) ⌈/⌉ k)) phi
              (wooleyBoxSourceSequence gamma) = 1 := by
      rw [hceil]
      rw [wooleySourcePolynomialConditionedMean_box_monomial,
        wooleyWeightedConditionedGridMean_one hQ]
      exact wooley_conditioned_grid_mean_eq_one hs hQ hQph
    have hmean :
        wooleySourcePolynomialMean (wooleyTriangular k) (p ^ (k * h))
            phi (wooleyBoxSourceSequence gamma) =
          (wooleyPadicCount (wooleyTriangular k) k Q p (k * h) : ℝ) /
            ((Q ^ wooleyTriangular k : ℕ) : ℝ) := by
      rw [wooleySourcePolynomialMean_box_monomial,
        wooleyWeightedGridMean_one hQ,
        wooley_equations_3_5_to_3_7 hp hQ]
    rw [hmean, hconditioned, mul_one] at hbound
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    have hQpowPos : (0 : ℝ) < ((Q ^ wooleyTriangular k : ℕ) : ℝ) := by
      positivity
    have hmul := (div_le_iff₀ hQpowPos).mp hbound
    simpa only [Nat.cast_pow, mul_assoc] using hmul

#print axioms wooleyPadicCount_degree_zero
#print axioms wooley_mul_ceilDiv_self
#print axioms wooleyMonomialPadicConcentration_of_polynomialCorollary32

end

end GafniTao

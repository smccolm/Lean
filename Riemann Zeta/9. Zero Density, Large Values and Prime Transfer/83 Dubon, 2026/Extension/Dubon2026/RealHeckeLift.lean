import Dubon2026.RealHeckeRepresentatives
import Dubon2026.PrimitiveFullEigen

/-! # The original real-group lift is a genuine normalized prime Hecke eigenfunction -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm

/-- The actual finite determinant-one Hecke correspondence acting on real-group functions. -/
def realPrimeHecke (Q p : ℕ) [NeZero p] (Φ : SL(2, ℝ) → ℂ) (g : SL(2, ℝ)) : ℂ :=
  (((p : ℝ) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
    ((∑ b ∈ Finset.range p, Φ (realAffineMatrix ((b : ℝ) / p)
      (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_neZero p))) * g)) +
      if Nat.Coprime p Q then
        Φ (realAffineMatrix 0 (Nat.cast_pos.mpr (Nat.pos_of_neZero p)) * g) else 0)

/-- The actual left Hecke correspondence commutes with every right real-group translation. -/
theorem realPrimeHecke_right_translation (Q p : ℕ) [NeZero p]
    (Φ : SL(2, ℝ) → ℂ) (g h : SL(2, ℝ)) :
    realPrimeHecke Q p (fun t => Φ (t * h)) g = realPrimeHecke Q p Φ (g * h) := by
  simp only [realPrimeHecke, mul_assoc]

/-- The literal classical prime operator has its genuine p upper terms and possible lower term. -/
theorem classicalHeckeFunction_prime_point (Q : ℕ) (k : ℤ) {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (f : ℍ → ℂ) (z : ℍ) :
    classicalHeckeFunction Q k p f z =
      (p : ℂ)⁻¹ * (∑ b ∈ Finset.range p, f (heckeUpperPoint p b z)) +
        if Nat.Coprime p Q then (p : ℂ) ^ (k - 1) * f (levelRaiseMatrix p • z) else 0 := by
  rw [classicalHeckeFunction_prime Q k hp]
  simp only [Pi.add_apply, heckeTriangularSum_apply, Nat.cast_one, one_zpow, one_mul]
  have h1 : levelRaiseMatrix 1 • z = z := by
    apply UpperHalfPlane.ext
    simp [coe_levelRaiseMatrix_smul]
  rw [h1, heckeAverage]
  congr 1
  by_cases hc : Nat.Coprime p Q
  · simp only [if_pos hc, heckeTriangular_slash_apply, Nat.cast_one, inv_one, mul_one]
    congr 1
    apply congrArg f
    apply UpperHalfPlane.ext
    simp [heckeUpperPoint]
  · simp [hc]

/-- The actual real-group Hecke correspondence is exactly the classical Hecke operator with its unitary scalar. -/
theorem realPrimeHecke_lift (Q : ℕ) (k : ℤ) {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (f : ℍ → ℂ) (g : SL(2, ℝ)) :
    realPrimeHecke Q p (realWeightLift k f) g =
      (((p : ℝ) ^ (-((k : ℝ) - 1) / 2) : ℝ) : ℂ) *
        realWeightLift k (classicalHeckeFunction Q k p f) g := by
  rw [realPrimeHecke, mul_add, Finset.mul_sum]
  simp_rw [realWeightLift_hecke_upper]
  rw [realWeightLift_apply k (classicalHeckeFunction Q k p f) g,
    classicalHeckeFunction_prime_point Q k hp]
  by_cases hc : Nat.Coprime p Q
  · rw [if_pos hc, if_pos hc, realWeightLift_hecke_lower]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  · rw [if_neg hc, if_neg hc, mul_zero, add_zero, add_zero]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring

/-- For an actual primitive form, this genuine real-group correspondence has the original normalized eigenvalue at every prime. -/
theorem primitive_realPrimeHecke_eigenvalue {Q p : ℕ} [NeZero Q] [NeZero p] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hp : Nat.Prime p) (g : SL(2, ℝ)) :
    realPrimeHecke Q p (realWeightLift k f.toCuspForm) g =
      normalizedCuspCoefficients f.toCuspForm p * realWeightLift k f.toCuspForm g := by
  obtain ⟨e, he⟩ := primitiveCuspForm_isFullEigenform f p hp.pos
  have heval : e = cuspCoefficients f.toCuspForm p :=
    cusp_hecke_eigenvalue_eq_coefficient f.toCuspForm f.normalized hp.ne_zero e he
  rw [heval] at he
  rw [realPrimeHecke_lift Q k hp, realWeightLift_apply, he, realWeightLift_apply,
    normalizedCuspCoefficients, shiftedCoefficients]
  rw [← Complex.ofReal_natCast p, ← Complex.ofReal_cpow (Nat.cast_nonneg p)]
  ring

end
end Dubon2026

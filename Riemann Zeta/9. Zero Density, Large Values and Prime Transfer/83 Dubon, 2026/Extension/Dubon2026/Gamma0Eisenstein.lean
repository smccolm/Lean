import Dubon2026.EisensteinLatticeKernel

/-! # The actual nonholomorphic Eisenstein series at infinity for Γ₀(Q) -/

namespace Dubon2026

open UpperHalfPlane Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- The genuine primitive bottom rows of Γ₀(Q), before dividing by the sign. -/
def gamma0PrimitiveRows (Q : ℕ) : Set (Fin 2 → ℤ) :=
  {v | (v 0).gcd (v 1) = 1 ∧ (Q : ℤ) ∣ v 0}

/-- Every actual primitive row is nonzero. -/
theorem gamma0PrimitiveRow_ne_zero {Q : ℕ} (v : gamma0PrimitiveRows Q) : v.val ≠ 0 := by
  intro hz
  have h := v.property.1
  rw [hz] at h
  norm_num at h

/-- Right multiplication by a Γ₀ matrix preserves the full actual primitive row set. -/
theorem gamma0PrimitiveRows_vecMul {Q : ℕ} (v : gamma0PrimitiveRows Q)
    (A : SL(2, ℤ)) (hA : A ∈ Gamma0 Q) : v.val ᵥ* A.val ∈ gamma0PrimitiveRows Q := by
  refine ⟨EisensteinSeries.vecMulSL_gcd v.property.1 A, ?_⟩
  have hA0 : (Q : ℤ) ∣ A 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hA)
  change (Q : ℤ) ∣ ∑ i : Fin 2, v.val i * A i 0
  rw [Fin.sum_univ_two]
  exact dvd_add (dvd_mul_of_dvd_left v.property.2 _) (dvd_mul_of_dvd_right hA0 _)

/-- The exact row permutation induced by an actual Γ₀ matrix. -/
def gamma0PrimitiveRowsEquiv {Q : ℕ} (A : SL(2, ℤ)) (hA : A ∈ Gamma0 Q) :
    gamma0PrimitiveRows Q ≃ gamma0PrimitiveRows Q where
  toFun v := ⟨v.val ᵥ* A.val, gamma0PrimitiveRows_vecMul v A hA⟩
  invFun v := ⟨v.val ᵥ* A⁻¹.val, gamma0PrimitiveRows_vecMul v A⁻¹ ((Gamma0 Q).inv_mem hA)⟩
  left_inv v := by
    apply Subtype.ext
    simp only [vecMul_vecMul, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
      SpecialLinearGroup.coe_one, vecMul_one]
  right_inv v := by
    apply Subtype.ext
    simp only [vecMul_vecMul, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
      SpecialLinearGroup.coe_one, vecMul_one]

/-- The genuine nonholomorphic Eisenstein series E∞(z,s), with the required division by ±1. -/
def gamma0Eisenstein (Q : ℕ) (s : ℂ) (z : ℍ) : ℂ :=
  (1 / 2 : ℂ) * ∑' v : gamma0PrimitiveRows Q, nonholomorphicEisensteinTerm s v.val z

/-- The actual defining series is absolutely convergent for Re(s)>1. -/
theorem gamma0Eisenstein_summable_norm (Q : ℕ) {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    Summable (fun v : gamma0PrimitiveRows Q => ‖nonholomorphicEisensteinTerm s v.val z‖) :=
  (summable_norm_nonholomorphicEisensteinTerm hs z).subtype _

/-- The defining primitive-row sum has the literal Eisenstein value with its exact normalization. -/
theorem gamma0Eisenstein_hasSum (Q : ℕ) {s : ℂ} (hs : 1 < s.re) (z : ℍ) :
    HasSum (fun v : gamma0PrimitiveRows Q =>
      (1 / 2 : ℂ) * nonholomorphicEisensteinTerm s v.val z) (gamma0Eisenstein Q s z) :=
  ((gamma0Eisenstein_summable_norm Q hs z).of_norm.hasSum).mul_left _

/-- The genuine primitive-row series is invariant under the actual Γ₀ action. -/
theorem gamma0Eisenstein_invariant (Q : ℕ) (s : ℂ) (z : ℍ)
    (A : SL(2, ℤ)) (hA : A ∈ Gamma0 Q) :
    gamma0Eisenstein Q s (A • z) = gamma0Eisenstein Q s z := by
  unfold gamma0Eisenstein
  simp_rw [nonholomorphicEisensteinTerm_SL2]
  congr 1
  exact (gamma0PrimitiveRowsEquiv A hA).tsum_eq
    (fun v : gamma0PrimitiveRows Q => nonholomorphicEisensteinTerm s v.val z)

/-- Both signs of the primitive horizontal row have the required actual height contribution. -/
theorem nonholomorphicEisensteinTerm_horizontal (s : ℂ) (z : ℍ) :
    nonholomorphicEisensteinTerm s ![0, 1] z = (z.im : ℂ) ^ s ∧
      nonholomorphicEisensteinTerm s ![0, -1] z = (z.im : ℂ) ^ s := by
  simp [nonholomorphicEisensteinTerm, eisensteinRowHeight]

end
end Dubon2026

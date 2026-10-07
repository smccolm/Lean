import Dubon2026.Gamma0Eisenstein
import Mathlib.GroupTheory.Coset.Basic

/-! # Primitive rows and actual translation cosets -/

namespace Dubon2026

open UpperHalfPlane Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularGroup
open scoped MatrixGroups

noncomputable section

/-- An integral determinant-one matrix with bottom row (0,1) is an actual integer translation. -/
theorem SL2_eq_translation_of_bottom_row (A : SL(2, ℤ))
    (hc : A 1 0 = 0) (hd : A 1 1 = 1) : A = T ^ (A 0 1) := by
  have ha : A 0 0 = 1 := by
    have h := A.det_coe
    rw [Matrix.det_fin_two] at h
    simpa [hc, hd] using h
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_T_zpow, ha, hc, hd]

/-- Equal primitive bottom rows are precisely left translates by a power of T. -/
theorem SL2_bottom_row_eq_iff (A B : SL(2, ℤ)) :
    A.val 1 = B.val 1 ↔ ∃ n : ℤ, A = T ^ n * B := by
  constructor
  · intro h
    have he : (A * B⁻¹).val 1 = (1 : SL(2, ℤ)).val 1 := by
      calc
        (A * B⁻¹).val 1 = A.val 1 ᵥ* B⁻¹.val := rfl
        _ = B.val 1 ᵥ* B⁻¹.val := by rw [h]
        _ = (1 : SL(2, ℤ)).val 1 := by
          change (B * B⁻¹).val 1 = _
          rw [mul_inv_cancel]
    have hc : (A * B⁻¹) 1 0 = 0 := by simpa using congrFun he 0
    have hd : (A * B⁻¹) 1 1 = 1 := by simpa using congrFun he 1
    have ht := SL2_eq_translation_of_bottom_row (A * B⁻¹) hc hd
    refine ⟨(A * B⁻¹) 0 1, ?_⟩
    rw [← ht, inv_mul_cancel_right]
  · rintro ⟨n, rfl⟩
    exact T_pow_mul_apply_one n B

/-- The subgroup of genuine integral translations inside Γ₀(Q). -/
def gamma0Unipotent (Q : ℕ) : Subgroup (Gamma0 Q) :=
  (Subgroup.zpowers T).comap (Gamma0 Q).subtype

/-- The actual bottom row of a Γ₀ matrix, with its primitive and level conditions. -/
def gamma0BottomRow {Q : ℕ} (A : Gamma0 Q) : gamma0PrimitiveRows Q :=
  ⟨A.val.val 1, Int.isCoprime_iff_gcd_eq_one.mp (A.val.isCoprime_row 1),
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp A.property)⟩

/-- Every admissible primitive row has a determinant-one completion in the actual level subgroup. -/
theorem gamma0BottomRow_surjective (Q : ℕ) : Function.Surjective (@gamma0BottomRow Q) := by
  intro v
  obtain ⟨A, hc, hd⟩ := (Int.isCoprime_iff_gcd_eq_one.mpr v.property.1).exists_SL2_row 1
  have hA : A ∈ Gamma0 Q := by
    rw [Gamma0_mem, hc]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr v.property.2
  refine ⟨⟨A, hA⟩, ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i <;> assumption

/-- The fibers of the bottom-row map are the right cosets of the true unipotent subgroup. -/
theorem gamma0BottomRow_eq_iff {Q : ℕ} (A B : Gamma0 Q) :
    gamma0BottomRow A = gamma0BottomRow B ↔
      (QuotientGroup.rightRel (gamma0Unipotent Q)) A B := by
  rw [QuotientGroup.rightRel_apply]
  change gamma0BottomRow A = gamma0BottomRow B ↔ B.val * A.val⁻¹ ∈ Subgroup.zpowers T
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (SL2_bottom_row_eq_iff B.val A.val).mp
      (congrArg Subtype.val h.symm)
    refine ⟨n, ?_⟩
    rw [hn, mul_inv_cancel_right]
  · rintro ⟨n, hn⟩
    apply Subtype.ext
    apply (SL2_bottom_row_eq_iff A.val B.val).mpr
    refine ⟨-n, ?_⟩
    have he : B.val = T ^ n * A.val := by rw [hn, inv_mul_cancel_right]
    rw [he, zpow_neg, ← mul_assoc, inv_mul_cancel, one_mul]

/-- Exact right-coset to primitive-row identification before dividing by the two signs. -/
def gamma0UnipotentCosetEquiv (Q : ℕ) :
    Quotient (QuotientGroup.rightRel (gamma0Unipotent Q)) ≃ gamma0PrimitiveRows Q :=
  Equiv.ofBijective
    (Quotient.lift gamma0BottomRow (fun A B h => (gamma0BottomRow_eq_iff A B).mpr h))
    ⟨by
      intro x y
      induction x using Quotient.inductionOn with | h A => ?_
      induction y using Quotient.inductionOn with | h B => ?_
      intro h
      exact Quotient.sound ((gamma0BottomRow_eq_iff A B).mp h), by
      intro v
      obtain ⟨A, hA⟩ := gamma0BottomRow_surjective Q v
      exact ⟨Quotient.mk _ A, hA⟩⟩

/-- The exact coset bijection uses the bottom row of its own matrix representative. -/
theorem gamma0UnipotentCosetEquiv_out (Q : ℕ)
    (q : Quotient (QuotientGroup.rightRel (gamma0Unipotent Q))) :
    gamma0UnipotentCosetEquiv Q q = gamma0BottomRow q.out := by
  conv_lhs => rw [← q.out_eq]
  rfl

/-- The primitive-row height is literally the imaginary part of the transformed upper-half-plane point. -/
theorem eisensteinRowHeight_bottom_row (A : SL(2, ℤ)) (z : ℍ) :
    eisensteinRowHeight (A.val 1) z = (A • z).im := by
  rw [ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq, ModularGroup.denom_apply]
  rfl

/-- The defining half-sum is exactly the true translation-coset sum with its two-sign normalization. -/
theorem gamma0Eisenstein_eq_unipotent_coset_sum (Q : ℕ) (s : ℂ) (z : ℍ) :
    gamma0Eisenstein Q s z = (1 / 2 : ℂ) *
      ∑' q : Quotient (QuotientGroup.rightRel (gamma0Unipotent Q)),
        (((q.out.val • z).im : ℝ) : ℂ) ^ s := by
  rw [gamma0Eisenstein, ← (gamma0UnipotentCosetEquiv Q).tsum_eq
    (fun v : gamma0PrimitiveRows Q => nonholomorphicEisensteinTerm s v.val z)]
  congr 1
  apply tsum_congr
  intro q
  rw [gamma0UnipotentCosetEquiv_out]
  exact congrArg (fun y : ℝ => (y : ℂ) ^ s) (eisensteinRowHeight_bottom_row q.out.val z)

end
end Dubon2026

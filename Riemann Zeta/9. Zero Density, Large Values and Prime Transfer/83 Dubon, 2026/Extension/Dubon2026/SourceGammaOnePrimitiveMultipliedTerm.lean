import Dubon2026.SourceGammaOnePrimitiveCuspConjugation
import Dubon2026.SourceGammaOneHeckeSubgroup

/-! DUB-17/18 -> original all-weight association -> exact joint arithmetic
realization -> primitive two-term boundary Hecke formula. Compute the
prime-length orbit contribution using the original integral diagonal
map. The new primitive column and its unchanged width are constructed;
the resulting actual loop has multiplicity one. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup SourceCuspBoundary Matrix.SpecialLinearGroup
open scoped MatrixGroups

private theorem conjugation_entries {M ell : ℕ} [NeZero ell]
    (g : sourceGammaOneHeckeUpper M ell) :
    (sourceGammaOneHeckeConjugation M ell g).val.val =
      !![g.val.val 0 0, g.val.val 0 1 / (ell : ℤ);
        g.val.val 1 0 * (ell : ℤ), g.val.val 1 1] := rfl

/-- The prime-th power of the actual primitive cusp loop lies in the
original upper correspondence subgroup. -/
theorem primitiveCuspTranslation_pow_mem_heckeUpper (M ell : ℕ) (δ : SL(2, ℤ)) :
    primitiveCuspTranslation M δ ^ ell ∈ sourceGammaOneHeckeUpper M ell := by
  change ((((primitiveCuspTranslation M δ) ^ ell).val 0 1 : ℤ) : ZMod ell) = 0
  rw [Subgroup.coe_pow, primitiveCuspTranslation_unipMat, unipMat_pow, unipMat_apply_01]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _

variable (M : ℕ) (ell : sourceBinaryHeckePrime M)
private local instance : NeZero ell.val := ⟨ell.property.1.ne_zero⟩

/-- The nonfixed primitive cusp contribution is exactly the original
primitive value at the column with second coordinate multiplied by the prime. -/
theorem primitiveCuspHecke_multiplied_term {A : Type} [AddCommGroup A]
    (δ : SL(2, ℤ)) (hδ : ¬ (ell.val : ℤ) ∣ δ 0 0)
    (φ : Additive (Gamma1 M) →+ A) :
    ∃ σ : SL(2, ℤ), σ 0 0 = δ 0 0 ∧ σ 1 0 = ell.val * δ 1 0 ∧
      φ (Additive.ofMul (sourceGammaOneHeckeConjugation M ell.val
        ⟨primitiveCuspTranslation M δ ^ ell.val,
          primitiveCuspTranslation_pow_mem_heckeUpper M ell.val δ⟩)) =
        primitiveCuspValue M φ σ := by
  have hell0 : (ell.val : ℤ) ≠ 0 := by exact_mod_cast ell.property.1.ne_zero
  have hp : Prime (ell.val : ℤ) := Nat.prime_iff_prime_int.mp ell.property.1
  have hc : IsCoprime (δ 0 0) ((ell.val : ℤ) * δ 1 0) :=
    IsCoprime.mul_right ((Prime.coprime_iff_not_dvd hp).mpr hδ).symm
      (SourceCuspBoundary.isCoprime_col δ)
  obtain ⟨σ, hσ0, hσ1⟩ := hc.exists_SL2_col (0 : Fin 2)
  let u := ZMod.unitOfCoprime ell.val ell.property.2
  have hu : (u : ZMod M) = ell.val := ZMod.coe_unitOfCoprime _ _
  have hw1 : ((σ 1 0 : ℤ) : ZMod M) = (u : ZMod M) * (δ 1 0 : ℤ) := by
    rw [hu]
    have h := congrArg (fun z : ℤ => (z : ZMod M)) hσ1
    push_cast at h
    exact h
  have hw := primitiveCuspWidth_eq_of_unit_columns M δ σ 1 u
    (by simpa only [Units.val_one, one_mul] using congrArg (fun z : ℤ => (z : ZMod M)) hσ0) hw1
  refine ⟨σ, hσ0, hσ1, ?_⟩
  let m := primitiveCuspWidth M ((δ⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 M)
  let g : sourceGammaOneHeckeUpper M ell.val :=
    ⟨primitiveCuspTranslation M δ ^ ell.val,
      primitiveCuspTranslation_pow_mem_heckeUpper M ell.val δ⟩
  have hg : g.val.val = unipMat (δ 0 0) (δ 1 0) ((m : ℤ) * ell.val) := by
    change (primitiveCuspTranslation M δ).val ^ ell.val = _
    rw [primitiveCuspTranslation_unipMat, unipMat_pow]
  have hkey : sourceGammaOneHeckeConjugation M ell.val g = primitiveCuspTranslation M σ := by
    apply Subtype.ext
    rw [primitiveCuspTranslation_unipMat, ← hw]
    apply Subtype.ext
    rw [conjugation_entries, hg, hσ0, hσ1]
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp [unipMat]
    · ring
    · rw [show (m : ℤ) * ell.val * δ 0 0 * δ 0 0 =
          ell.val * (m * δ 0 0 * δ 0 0) by ring,
        Int.mul_ediv_cancel_left _ hell0]
    · ring
    · ring
  change φ (Additive.ofMul (sourceGammaOneHeckeConjugation M ell.val g)) = _
  rw [hkey]
  rfl

end
end Dubon2026.SourceFunctionField.GammaOne

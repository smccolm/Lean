import Dubon2026.SourceGammaOnePrimitiveCuspConjugation
import Dubon2026.SourceGammaOneHeckeSubgroup
import Dubon2026.SourceCuspHeckeSum

/-! DUB-17/18 -> original all-weight association -> exact joint arithmetic
realization -> primitive boundary Frobenius. Compute the fixed-orbit
contribution of the literal Gamma1 diagonal correspondence. Its divided
column is constructed integrally, its primitive width is preserved by
the good-prime unit, and the actual conjugated loop is the prime-th
power of that primitive loop. Native integral unipotent arithmetic and
prime-unit cancellation are reused; torsion coefficients are retained. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup SourceCuspBoundary Matrix.SpecialLinearGroup
open scoped MatrixGroups

private theorem conjugation_entries {M ell : ℕ} [NeZero ell]
    (g : sourceGammaOneHeckeUpper M ell) :
    (sourceGammaOneHeckeConjugation M ell g).val.val =
      !![g.val.val 0 0, g.val.val 0 1 / (ell : ℤ);
        g.val.val 1 0 * (ell : ℤ), g.val.val 1 1] := rfl

/-- A primitive loop whose first column coordinate is divisible by the
Hecke prime belongs to the actual upper correspondence subgroup. -/
theorem primitiveCuspTranslation_mem_heckeUpper (M ell : ℕ) (δ : SL(2, ℤ))
    (hδ : (ell : ℤ) ∣ δ 0 0) :
    primitiveCuspTranslation M δ ∈ sourceGammaOneHeckeUpper M ell := by
  change (((primitiveCuspTranslation M δ).val 0 1 : ℤ) : ZMod ell) = 0
  rw [primitiveCuspTranslation_unipMat, unipMat_apply_01]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
  exact dvd_mul_of_dvd_right hδ _

variable (M : ℕ) (ell : sourceBinaryHeckePrime M)
private local instance : NeZero ell.val := ⟨ell.property.1.ne_zero⟩

/-- The fixed primitive cusp contribution is exactly the prime times
the primitive value at the constructed divided column. -/
theorem primitiveCuspHecke_divided_term {A : Type} [AddCommGroup A]
    (δ : SL(2, ℤ)) (hδ : (ell.val : ℤ) ∣ δ 0 0)
    (φ : Additive (Gamma1 M) →+ A) :
    ∃ σ : SL(2, ℤ), σ 0 0 * ell.val = δ 0 0 ∧ σ 1 0 = δ 1 0 ∧
      φ (Additive.ofMul (sourceGammaOneHeckeConjugation M ell.val
        ⟨primitiveCuspTranslation M δ, primitiveCuspTranslation_mem_heckeUpper M ell.val δ hδ⟩)) =
          ell.val • primitiveCuspValue M φ σ := by
  have hell0 : (ell.val : ℤ) ≠ 0 := by exact_mod_cast ell.property.1.ne_zero
  have hcol := SourceCuspBoundary.isCoprime_col δ
  obtain ⟨a, ha⟩ := id hδ
  have hac : IsCoprime a (δ 1 0) := by rw [ha] at hcol; exact hcol.of_mul_left_right
  obtain ⟨σ, hσ0, hσ1⟩ := hac.exists_SL2_col (0 : Fin 2)
  have hσ : σ 0 0 * ell.val = δ 0 0 := by rw [hσ0, ha, mul_comm]
  let u := ZMod.unitOfCoprime ell.val ell.property.2
  have hu : (u : ZMod M) = ell.val := ZMod.coe_unitOfCoprime _ _
  have hσcast : ((σ 0 0 : ℤ) : ZMod M) * ell.val = δ 0 0 := by
    have h := congrArg (fun z : ℤ => (z : ZMod M)) hσ
    push_cast at h
    exact h
  have hw0 : ((σ 0 0 : ℤ) : ZMod M) = (u⁻¹ : (ZMod M)ˣ) * (δ 0 0 : ℤ) := by
    apply mul_ell_cancel ell.property.1 (ell.property.1.coprime_iff_not_dvd.mp ell.property.2)
    rw [hσcast, mul_right_comm, ← hu, Units.inv_mul, one_mul]
  have hw := primitiveCuspWidth_eq_of_unit_columns M δ σ u⁻¹ 1 hw0
    (by simpa only [Units.val_one, one_mul] using congrArg (fun z : ℤ => (z : ZMod M)) hσ1)
  refine ⟨σ, hσ, hσ1, ?_⟩
  let m := primitiveCuspWidth M ((δ⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 M)
  let g : sourceGammaOneHeckeUpper M ell.val :=
    ⟨primitiveCuspTranslation M δ, primitiveCuspTranslation_mem_heckeUpper M ell.val δ hδ⟩
  have hg : g.val.val = unipMat (δ 0 0) (δ 1 0) m := primitiveCuspTranslation_unipMat M δ
  have hkey : sourceGammaOneHeckeConjugation M ell.val g = primitiveCuspTranslation M σ ^ ell.val := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, primitiveCuspTranslation_unipMat, unipMat_pow, ← hw]
    apply Subtype.ext
    rw [conjugation_entries, hg, hσ0, hσ1, ha]
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp [unipMat]
    · ring
    · rw [show (m : ℤ) * (ell.val * a) * (ell.val * a) =
          ell.val * (m * a * (ell.val * a)) by ring,
        Int.mul_ediv_cancel_left _ hell0]
      ring
    · ring
    · ring
  change φ (Additive.ofMul (sourceGammaOneHeckeConjugation M ell.val g)) = _
  rw [hkey, ofMul_pow, map_nsmul]
  rfl

end
end Dubon2026.SourceFunctionField.GammaOne

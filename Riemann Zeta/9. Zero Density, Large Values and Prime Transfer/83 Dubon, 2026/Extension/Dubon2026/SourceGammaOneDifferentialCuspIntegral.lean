import Dubon2026.SourceGammaOneCuspAuxiliaryExpansion

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight
Galois association -> original finite Gamma1 character realization ->
actual Picard/H1 comparison -> regular differential/cusp comparison.
The native cusp auxiliary form, existing modular norm and constructed
q-Euler scalar prove the exact inverse-j integral bound. Together with
the finite-coordinate bound this supplies the two integral equations
needed for regularity; the valuation deduction remains separate. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane ModularForm SourceDifferential
open scoped MatrixGroups

theorem isIntegral_cusp_differential_cusp_expression
    (M : ℕ) [NeZero M] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
    [Γ.FiniteIndex] (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) (Y : LaurentSeries ℂ)
    (hY : Y * qEuler ℂ (jqModC ℂ) = (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ)) :
    IsIntegral (Algebra.adjoin ℂ ({(jqModC ℂ)⁻¹} : Set (LaurentSeries ℂ)))
      (Y ^ (2 * M) * (jqModC ℂ) ^ (M + 1) * (jqModC ℂ - 1728) ^ M) := by
  let A := Algebra.adjoin ℂ ({(jqModC ℂ)⁻¹} : Set (LaurentSeries ℂ))
  obtain ⟨c, hc, he⟩ := ModularQDerivative.exists_qEuler_jqModC_formula
  let C := algebraMap ℂ (LaurentSeries ℂ) c
  have hC : C ≠ 0 := by
    intro hz
    apply hc
    apply (algebraMap ℂ (LaurentSeries ℂ)).injective
    simpa only [map_zero] using hz
  have hi : (jqModC ℂ)⁻¹ =
      (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ) /
        (qExpansion 1 (E₄ : ℍ → ℂ) : LaurentSeries ℂ) ^ 3 := by
    rw [jqModC_eq_modular_quotient, inv_div]
  have hI := InverseJIntegral.isIntegral_modular_quotient_E4 (hper hT) M
    (g := CuspAuxiliary.Gform M hΓ f) (by push_cast; ring)
  rw [← hi] at hI
  have hs : IsIntegral A (C⁻¹ ^ (2 * M)) := by
    have hm : C⁻¹ ^ (2 * M) ∈ A := by
      change (algebraMap ℂ (LaurentSeries ℂ) c)⁻¹ ^ (2 * M) ∈ A
      rw [← map_inv₀, ← map_pow]
      exact A.algebraMap_mem _
    exact isIntegral_algebraMap (R := A) (A := LaurentSeries ℂ) (x := ⟨_, hm⟩)
  have hprod := CuspAuxiliary.cusp_expression_identity M
    (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ)
    (qExpansion 1 (E₄ : ℍ → ℂ) : LaurentSeries ℂ)
    (qExpansion 1 (E₆ : ℍ → ℂ) : LaurentSeries ℂ)
    (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ)
    (qEuler ℂ (jqModC ℂ)) Y (jqModC ℂ)
    (qExpansion 1 (CuspAuxiliary.Gform M hΓ f : ℍ → ℂ) : LaurentSeries ℂ) C
    InverseJIntegral.eisenstein_four_expansion_ne_zero discriminant_expansion_ne_zero hC
    he hY jqModC_eq_modular_quotient ModularQDerivative.laurent_discriminant_relation.symm
    (CuspAuxiliary.qExpansion_Gform_mul M hΓ hT f)
  rw [hprod]
  exact hs.mul hI

end
end Dubon2026.SourceFunctionField.GammaOne

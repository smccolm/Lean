import Dubon2026.SourceLaurentAnalyticPolynomial
import Dubon2026.SourceLevelOneJPolynomial
import Dubon2026.SourceJPolynomialDescent
import Dubon2026.SourceAnalyticJTransformation

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
characters -> Picard/H1 and diamond comparison -> differential realization
-> rational Fourier structure -> Fricke level field -> invariant fractions.
Transfer the existing exact Laurent-series level-one polynomial reduction
to the actual analytic functions using already proved convergent Laurent
products. No polynomial representation is assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

theorem realL_jqModC :
    RealL 1 (jqModC ℂ) JMultiplicity.jf := by
  have he : coeffMap (Rat.castHom ℂ) jq = jqModC ℂ := by
    simpa only [jqModC_rat] using map_jqModC (Rat.castHom ℂ)
  rw [← he]
  exact realL_jqC

theorem exists_levelOne_analytic_j_polynomial (m : ℕ)
    (F : ModularForm 𝒮ℒ (12 * (m : ℤ))) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ m ∧
      ∀ τ : ℍ, F τ = P.eval (JMultiplicity.jf τ) * ModularForm.discriminant τ ^ m := by
  obtain ⟨P, hdeg, hP⟩ := exists_levelOne_j_polynomial m F
  rw [← jqModC_eq_modular_quotient] at hP
  have hF := realL_qExpansion one_pos (F : ℍ → ℂ)
    (SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL)
    F.holo' (ModularFormClass.bdd_at_infty F)
  have hD := realL_qExpansion one_pos (ModularForm.discriminant : ℍ → ℂ)
    (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
      one_mem_strictPeriods_SL) CuspForm.discriminant.holo'
    (ModularFormClass.bdd_at_infty CuspForm.discriminant)
  have hEval := (realL_jqModC.aeval one_pos P).mul one_pos (hD.pow one_pos m)
  refine ⟨P, hdeg, fun τ => ?_⟩
  have hFτ := hF τ
  rw [hP] at hFτ
  exact hFτ.unique (hEval τ)

end
end Dubon2026.SourceFunctionField

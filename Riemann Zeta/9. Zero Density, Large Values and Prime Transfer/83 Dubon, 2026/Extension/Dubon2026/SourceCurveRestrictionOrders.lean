import Dubon2026.SourceCurveResidueRestriction
import Dubon2026.SourceCurveLocalDifferentials

/-! DUB-17/18 -> global residue identity -> finite-extension fiber comparison.
Normalized orders under actual place restriction scale by the order of the
mapped base uniformizer. The unit-times-uniformizer decomposition and the
actual local ring inclusion prove this without a supplied ramification law.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [Algebra.IsIntegral F E] (w : Place K E)

theorem ord_algebraMap_restrict (f : F) :
    w.ord (algebraMap F E f) = (w.restrict F).ord f *
      w.ord (algebraMap F E (w.restrict F).uniformizer) := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, w.ord_zero, (w.restrict F).ord_zero, zero_mul]
  let v := w.restrict F
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf
    (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  have hu0 : ((u : v.toValuationSubring) : F) ≠ 0 := by exact_mod_cast u.ne_zero
  have huE : algebraMap F E ((u : v.toValuationSubring) : F) ≠ 0 := by
    simpa only [map_zero] using (algebraMap F E).injective.ne hu0
  have hπE : algebraMap F E v.uniformizer ≠ 0 := by
    simpa only [map_zero] using (algebraMap F E).injective.ne v.uniformizer_ne_zero
  have hunit : w.ord (algebraMap F E ((u : v.toValuationSubring) : F)) = 0 :=
    w.ord_coe_unit (Units.map (w.restrictInclusion F).toMonoidHom u)
  change f = ((u : v.toValuationSubring) : F) * v.uniformizer ^ v.ord f at hu
  conv_lhs => rw [hu, map_mul, map_zpow₀]
  rw [w.ord_mul huE (zpow_ne_zero _ hπE), hunit, zero_add, w.ord_zpow]

theorem ord_restricted_uniformizer_pos :
    0 < w.ord (algebraMap F E (w.restrict F).uniformizer) := by
  let v := w.restrict F
  have hπ : v.uniformizer ∈ v.toValuationSubring :=
    (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose.2
  have hnonneg := w.ord_nonneg_of_mem ((w.mem_restrict_iff).mp hπ)
  by_contra hnot
  change ¬ 0 < w.ord (algebraMap F E v.uniformizer) at hnot
  have hz : w.ord (algebraMap F E v.uniformizer) = 0 := by omega
  have hinv : v.uniformizer⁻¹ ∈ v.toValuationSubring := by
    apply (w.mem_restrict_iff).mpr
    rw [map_inv₀]
    apply w.mem_of_ord_nonneg
    rw [w.ord_inv, hz, neg_zero]
  have hbad := v.ord_nonneg_of_mem hinv
  rw [v.ord_inv, v.ord_uniformizer] at hbad
  omega

end
end Dubon2026.SourceCurve.Place

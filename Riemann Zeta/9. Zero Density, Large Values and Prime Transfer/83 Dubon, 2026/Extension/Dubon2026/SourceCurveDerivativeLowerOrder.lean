import Dubon2026.SourceCurveExactDerivativeOrder

/-! DUB-17/18 -> modular good reduction -> reverse genus inequality ->
ramification contribution to the canonical divisor. Reuse the existing
unit-times-uniformizer derivative formula. In positive characteristic the
integer coefficient may vanish, so only the required lower bound is claimed.
Nonvanishing of the actual differential excludes the zero-coefficient case
from the place-order multiplication formula. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField]

theorem ord_sub_one_le_ordDifferential_D {f : F} (hD : D K F f ≠ 0) :
    v.ord f - 1 ≤ v.ordDifferential (D K F f) := by
  have hf0 : f ≠ 0 := fun h => hD (h ▸ map_zero (D K F))
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 v.irreducible_uniformizerSubring
  change f = ((u : v.toValuationSubring) : F) * v.uniformizer ^ v.ord f at hu
  let a : F := v.differentialCoeff (D K F ((u : v.toValuationSubring) : F))
  let b : F := v.uniformizer * a + (v.ord f : F) * ((u : v.toValuationSubring) : F)
  have ha : a ∈ v.toValuationSubring :=
    v.differentialCoeff_D_mem_of_mem (u : v.toValuationSubring).2
  have hb : b ∈ v.toValuationSubring := by
    apply add_mem
    · apply mul_mem _ ha
      exact v.mem_of_ord_nonneg (by rw [v.ord_uniformizer]; omega)
    · exact mul_mem (intCast_mem _ _) (u : v.toValuationSubring).2
  have he : v.differentialCoeff (D K F f) = v.uniformizer ^ (v.ord f - 1) * b := by
    conv_lhs => rw [hu]
    exact v.differentialCoeff_D_unit_mul_zpow u (v.ord f)
  have hb0 : b ≠ 0 := by
    intro hz
    have hc : v.differentialCoeff (D K F f) = 0 := by rw [he, hz, mul_zero]
    have h := v.differentialCoeff_smul_dCoord (D K F f)
    rw [hc, zero_smul] at h
    exact hD h.symm
  rw [ordDifferential, he, v.ord_mul (zpow_ne_zero _ v.uniformizer_ne_zero) hb0,
    v.ord_zpow, v.ord_uniformizer, mul_one]
  have := v.ord_nonneg_of_mem hb
  omega

end
end Dubon2026.SourceCurve.Place

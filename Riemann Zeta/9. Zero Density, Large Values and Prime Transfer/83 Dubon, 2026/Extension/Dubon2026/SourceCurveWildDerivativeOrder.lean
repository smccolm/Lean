import Dubon2026.SourceCurveDerivativeLowerOrder

/-! DUB-17/18 -> wild modular good reduction -> reverse genus -> local
wild differential contribution. Vanishing of the integer order in the
coefficient field removes the leading derivative term. The existing unit
derivative formula and integral coefficient give the extra order directly. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField]

theorem ord_le_ordDifferential_D_of_cast_eq_zero {f : F}
    (hcast : (v.ord f : K) = 0) (hD : D K F f ≠ 0) :
    v.ord f ≤ v.ordDifferential (D K F f) := by
  have hf0 : f ≠ 0 := fun h => hD (h ▸ map_zero (D K F))
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 v.irreducible_uniformizerSubring
  change f = ((u : v.toValuationSubring) : F) * v.uniformizer ^ v.ord f at hu
  let a : F := v.differentialCoeff (D K F ((u : v.toValuationSubring) : F))
  have ha : a ∈ v.toValuationSubring :=
    v.differentialCoeff_D_mem_of_mem (u : v.toValuationSubring).2
  have hcastF : (v.ord f : F) = 0 := by
    rw [← map_intCast (algebraMap K F), hcast, map_zero]
  have he : v.differentialCoeff (D K F f) =
      v.uniformizer ^ (v.ord f - 1) * (v.uniformizer * a) := by
    conv_lhs => rw [hu]
    rw [v.differentialCoeff_D_unit_mul_zpow, hcastF, zero_mul, add_zero]
  have ha0 : a ≠ 0 := by
    intro hz
    have hc : v.differentialCoeff (D K F f) = 0 := by rw [he, hz, mul_zero, mul_zero]
    have h := v.differentialCoeff_smul_dCoord (D K F f)
    rw [hc, zero_smul] at h
    exact hD h.symm
  rw [ordDifferential, he, v.ord_mul (zpow_ne_zero _ v.uniformizer_ne_zero)
    (mul_ne_zero v.uniformizer_ne_zero ha0), v.ord_zpow,
    v.ord_mul v.uniformizer_ne_zero ha0, v.ord_uniformizer, mul_one]
  have := v.ord_nonneg_of_mem ha
  omega

end
end Dubon2026.SourceCurve.Place

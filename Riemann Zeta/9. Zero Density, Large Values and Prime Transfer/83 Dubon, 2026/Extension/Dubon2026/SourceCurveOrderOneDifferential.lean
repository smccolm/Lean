import Dubon2026.SourceCurveOrderFiltration
import Dubon2026.SourceCurveExactDerivativeOrder

/-! In every characteristic, an actual order-one parameter has
differential order zero. The existing unit-times-uniformizer coefficient
identity and integral derivative theorem suffice. This is the missing
positive-characteristic input in the DUB-17/18 unramified wild transfer. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
variable [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField]

theorem ordDifferential_D_eq_zero_of_ord_one {f : F} (hf : v.ord f = 1) :
    v.ordDifferential (D K F f) = 0 := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 v.irreducible_uniformizerSubring
  change f = ((u : v.toValuationSubring) : F) * v.uniformizer ^ v.ord f at hu
  rw [hf] at hu
  have hu0 : ((u : v.toValuationSubring) : F) ≠ 0 := by exact_mod_cast u.ne_zero
  have hπ : v.OrdGe 1 v.uniformizer := Or.inr v.ord_uniformizer.ge
  have hd : v.OrdGe 0 (v.differentialCoeff (D K F ((u : v.toValuationSubring) : F))) :=
    Or.inr (v.ord_nonneg_of_mem (v.differentialCoeff_D_mem_of_mem (u : v.toValuationSubring).2))
  have htail : v.OrdGe (0 + 1)
      (v.uniformizer * v.differentialCoeff (D K F ((u : v.toValuationSubring) : F))) := by
    simpa only [add_zero, zero_add] using hπ.mul hd
  have he := (ord_add_eq_of_ordGe hu0 (v.ord_coe_unit u) htail).2
  change v.ord (v.differentialCoeff (D K F f)) = 0
  rw [hu, v.differentialCoeff_D_unit_mul_zpow]
  simpa only [sub_self, zpow_zero, one_mul, Int.cast_one, add_comm] using he

end
end Dubon2026.SourceCurve.Place

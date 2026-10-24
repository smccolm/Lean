import Dubon2026.SourceCurveSeparableDifferentialBaseChange
import Dubon2026.SourceCurveExactDerivativeOrder
import Dubon2026.SourceCurveCompletionEmbeddingValuation
import Dubon2026.SourceCurveRegularComparison

/-! DUB-17/18 -> Picard torsion injectivity -> unramified Kummer-cover
genus. At a place of ramification index one, the pulled-back nonzero
differential has exactly its original order. The proved characteristic-zero
derivative-order formula applies to the mapped base uniformizer; native
Kaehler functoriality supplies the actual pullback. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential
variable {K F E : Type*} [Field K] [CharZero K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]
variable (w : Place K E) [(w.restrict F).DCoordGenerates] [w.DCoordGenerates]
  [Nontrivial Ω[F⁄K]] [Nontrivial Ω[E⁄K]]
  [Module.Finite w.toValuationSubring Ω[w.toValuationSubring⁄K]]
  [Algebra.IsSeparable K w.ResidueField]

omit [FiniteDimensional F E] in
theorem ordDifferential_map_of_ramificationIndex_one
    (he : w.ramificationIndex (F := F) = 1) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    w.ordDifferential (KaehlerDifferential.map K K F E ω) =
      (w.restrict F).ordDifferential ω := by
  let v := w.restrict F
  have hu : w.ord (algebraMap F E v.uniformizer) = 1 := by
    rw [← w.ramificationIndex_cast, he, Nat.cast_one]
  have hD : D K E (algebraMap F E v.uniformizer) ≠ 0 :=
    D_algebraMap_ne_zero_of_separable v.dCoord_ne_zero
  have horder : w.ordDifferential (D K E (algebraMap F E v.uniformizer)) = 0 := by
    rw [w.ordDifferential_D_eq_ord_sub_one (by rw [hu]; exact one_ne_zero), hu, sub_self]
  have hc := RegularDifferentialsComparison.differentialCoeff_ne_zero hω v
  have hmap : KaehlerDifferential.map K K F E ω =
      algebraMap F E (v.differentialCoeff ω) • D K E (algebraMap F E v.uniformizer) := by
    calc
      _ = KaehlerDifferential.map K K F E (v.differentialCoeff ω • v.dCoord) :=
        congrArg _ (v.differentialCoeff_smul_dCoord ω).symm
      _ = _ := by
        rw [map_smul]
        change v.differentialCoeff ω • KaehlerDifferential.map K K F E (D K F v.uniformizer) = _
        rw [KaehlerDifferential.map_D, IsScalarTower.algebraMap_smul]
  rw [hmap, w.ordDifferential_smul ((map_ne_zero_iff _ (algebraMap F E).injective).mpr hc)
    (RegularDifferentialsComparison.differentialCoeff_ne_zero hD w), horder, add_zero,
    w.ord_algebraMap_restrict, hu, mul_one]
  rfl

end
end Dubon2026.SourceCurve.Place

import Dubon2026.SourceCurveFiniteEmbeddingRestriction
import Dubon2026.SourceCurveRestrictionOrders

/-! DUB-17/18 -> reverse original genus -> exact wild fiber orders.
The constructed normal field bounds descend through the actual place
restriction formula. This supplies the order upper bound which, together
with the original degree sum and marked fiber count, forces orders twelve
and six in the two wild characteristics. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open SourceCurve

theorem coordinate_order_dvd_of_normal_embedding
    {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra (RatFunc K) L]
    [IsScalarTower K (RatFunc K) L] [FiniteDimensional (RatFunc K) L]
    [IsGalois (RatFunc K) L]
    (x : F) (hx : Transcendental K x) (ι : F →ₐ[K] L)
    (hι : ι x = algebraMap (RatFunc K) L RatFunc.X) (n : ℤ)
    (hdvd : ∀ w : Place K L, 0 < w.ord (algebraMap (RatFunc K) L RatFunc.X) →
      w.ord (algebraMap (RatFunc K) L RatFunc.X) ∣ n)
    (v : Place K F) (hv : 0 < v.ord x) : v.ord x ∣ n := by
  letI := algebraAlong ι
  haveI := scalarTower_along ι
  have hfg := finite_galois_along_coordinate x hx ι hι
  haveI : FiniteDimensional F L := hfg.1
  haveI : IsGalois F L := hfg.2
  have hfinite : ι.toRingHom.Finite := hfg.1
  obtain ⟨w, hw⟩ := Place.restrictAlongFinite_surjective ι hfinite inferInstance v
  change w.restrict F = v at hw
  have hscale : w.ord (algebraMap (RatFunc K) L RatFunc.X) =
      v.ord x * w.ord (algebraMap F L (w.restrict F).uniformizer) := by
    rw [← hι]
    change w.ord (algebraMap F L x) = _
    rw [w.ord_algebraMap_restrict, hw]
  have hwpos : 0 < w.ord (algebraMap (RatFunc K) L RatFunc.X) := by
    rw [hscale]
    exact mul_pos hv (w.ord_restricted_uniformizer_pos (F := F))
  exact dvd_trans ⟨_, hscale⟩ (hdvd w hwpos)

end
end Dubon2026.SourceFunctionField.MarkedChart

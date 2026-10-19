import Dubon2026.FinitePrimaryGroupAlgebraComplete
import Dubon2026.CompleteLocalSpecifiedPowerSeries
import Dubon2026.FinitePowerSeriesPatchingTopology
import Dubon2026.PowerSeriesLocalParameterMap

/-! The fixed variables act on the actual auxiliary group algebra
through its specified original group elements. The local coefficient
map and original finite-module topology give continuity; no new group
generators or continuity certificates are supplied. -/

namespace Dubon2026
noncomputable section
open IsLocalRing
open scoped MvPowerSeries.WithPiTopology

/-- Construct the local continuous common power-series action on
the genuine finite primary group algebra, preserving every specified
original group element as one plus its variable. -/
theorem finitePrimaryGroupAlgebra_exists_powerSeriesMap
    (O D : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [CommGroup D] [Finite D] (q : ℕ) (hq : q.Prime)
    [CharP (ResidueField O) q] (hD : IsPGroup q D)
    {η : Type} [Fintype η] (g : η → D) :
    letI : TopologicalSpace (MonoidAlgebra O D) := moduleTopology O (MonoidAlgebra O D)
    letI := finitePrimaryGroupAlgebra_isLocal O D q hq hD
    ∃ f : MvPowerSeries η O →ₐ[O] MonoidAlgebra O D,
      (∀ i, f (MvPowerSeries.X i) = MonoidAlgebra.of O D (g i) - 1) ∧
        IsLocalHom f.toRingHom ∧ Continuous f := by
  letI : TopologicalSpace (MonoidAlgebra O D) := moduleTopology O (MonoidAlgebra O D)
  letI := finitePrimaryGroupAlgebra_isLocal O D q hq hD
  have hB := finitePrimaryGroupAlgebra_completeData O D q hq hD
  letI := hB.1
  letI := hB.2.1
  letI := hB.2.2.1
  letI := hB.2.2.2.1
  letI := hB.2.2.2.2.1
  letI := hB.2.2.2.2.2
  letI : IsLocalHom (algebraMap O (MonoidAlgebra O D)) := ⟨fun x hx => by
    have h := hx.map (coefficientGroupAlgebraAugmentation O D).toRingHom
    change IsUnit (coefficientGroupAlgebraAugmentation O D (algebraMap O (MonoidAlgebra O D) x)) at h
    simpa only [(coefficientGroupAlgebraAugmentation O D).commutes] using h⟩
  have hvars : ∀ i, MonoidAlgebra.of O D (g i) - 1 ∈ maximalIdeal (MonoidAlgebra O D) := by
    intro i
    rw [finitePrimaryGroupAlgebra_maximalIdeal_eq O D q hq hD (maximalIdeal (MonoidAlgebra O D))]
    change coefficientGroupAlgebraAugmentation O D (MonoidAlgebra.of O D (g i) - 1) ∈ maximalIdeal O
    rw [map_sub, coefficientGroupAlgebraAugmentation_of, map_one, sub_self]
    exact Ideal.zero_mem _
  obtain ⟨f, hf⟩ := completeLocal_exists_specified_powerSeriesMap O _ hvars
  letI := finitePowerSeries_parameterMap_isLocal f (fun i => (hf i) ▸ hvars i)
  letI := finitePowerSeries_compactSpace (O := O) (η := η)
  letI := finiteVariablePowerSeries_isNoetherian (R := O) η
  refine ⟨f, hf, inferInstance, ?_⟩
  exact compactSeparatedLocalRingHom_continuous f.toRingHom

end
end Dubon2026

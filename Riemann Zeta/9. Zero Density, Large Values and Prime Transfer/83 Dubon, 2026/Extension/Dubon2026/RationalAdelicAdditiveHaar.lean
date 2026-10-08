import Dubon2026.RationalAdelicRealDensity
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # Genuine normalized additive Haar measure on the compact rational adele quotient -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain MeasureTheory Set TopologicalSpace

/-- The actual full rational adele ring is Hausdorff in its original product topology. -/
instance rationalAdeleT2Space : T2Space (AdeleRing ℤ ℚ) := by
  letI : T2Space (InfiniteAdeleRing ℚ) := rationalInfiniteAdeleHomeomorph.symm.t2Space
  letI (v : HeightOneSpectrum ℤ) : T2Space (v.adicCompletion ℚ) := by
    unfold HeightOneSpectrum.adicCompletion
    infer_instance
  letI : T2Space (FiniteAdeleRing ℤ ℚ) :=
    T2Space.of_injective_continuous
      (show Function.Injective (fun x : FiniteAdeleRing ℤ ℚ =>
        fun v : HeightOneSpectrum ℤ => x v) from DFunLike.coe_injective)
      RestrictedProduct.continuous_coe
  change T2Space (InfiniteAdeleRing ℚ × FiniteAdeleRing ℤ ℚ)
  infer_instance

/-- Discreteness makes the genuine principal rational subgroup closed. -/
instance rationalAdelePrincipal_isClosed :
    IsClosed (AdeleRing.principalSubgroup ℤ ℚ : Set (AdeleRing ℤ ℚ)) := by
  letI := rationalAdelePrincipal_discreteTopology
  exact AddSubgroup.isClosed_of_discrete

/-- The genuine additive quotient is compact by its proved literal representatives. -/
instance rationalAdelicAdditiveQuotient_instCompactSpace : CompactSpace RationalAdelicAdditiveQuotient :=
  rationalAdelicAdditiveQuotient_compactSpace

/-- The canonical measurable structure is the Borel structure of the actual quotient topology. -/
instance rationalAdelicAdditiveQuotientMeasurableSpace : MeasurableSpace RationalAdelicAdditiveQuotient :=
  borel _

/-- The declared quotient measurable structure is exactly its original Borel structure. -/
instance rationalAdelicAdditiveQuotient_borelSpace : BorelSpace RationalAdelicAdditiveQuotient :=
  ⟨rfl⟩

/-- The actual additive quotient carries its genuine additive Haar measure normalized to total mass one. -/
def rationalAdelicAdditiveHaar : Measure RationalAdelicAdditiveQuotient :=
  Measure.addHaarMeasure (⊤ : PositiveCompacts RationalAdelicAdditiveQuotient)

/-- The original quotient measure is additive Haar, including actual translation invariance and positivity. -/
instance rationalAdelicAdditiveHaar_isAddHaarMeasure : Measure.IsAddHaarMeasure rationalAdelicAdditiveHaar := by
  unfold rationalAdelicAdditiveHaar
  infer_instance

/-- The normalization gives an actual probability measure on the full rational adele quotient. -/
instance rationalAdelicAdditiveHaar_isProbabilityMeasure : IsProbabilityMeasure rationalAdelicAdditiveHaar where
  measure_univ := by
    exact Measure.addHaarMeasure_self (K₀ := (⊤ : PositiveCompacts RationalAdelicAdditiveQuotient))

/-- The full genuine quotient measure has mass precisely one. -/
theorem rationalAdelicAdditiveHaar_univ : rationalAdelicAdditiveHaar Set.univ = 1 :=
  measure_univ

/-- Every actual additive quotient translation preserves the original normalized Haar measure. -/
theorem rationalAdelicAdditiveHaar_translate (a : RationalAdelicAdditiveQuotient) :
    Measure.map (fun x => a + x) rationalAdelicAdditiveHaar = rationalAdelicAdditiveHaar :=
  Measure.IsAddLeftInvariant.map_add_left_eq_self a

end
end Dubon2026

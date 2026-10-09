import Dubon2026.SmoothInducedCompactAverage
import Dubon2026.FinitePlaceSphericalInduced
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # The genuine compact Haar average on the original local induced model -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix MeasureTheory

instance finitePlaceIntegralGL2_compactSpace (v : HeightOneSpectrum ℤ) :
    CompactSpace (finitePlaceGL2Gamma0 1 v) :=
  isCompact_iff_compactSpace.mp (finitePlaceGL2Gamma0_isCompact 1 v)

instance finitePlaceIntegralGL2MeasurableSpace (v : HeightOneSpectrum ℤ) :
    MeasurableSpace (finitePlaceGL2Gamma0 1 v) := borel _

instance finitePlaceIntegralGL2_borelSpace (v : HeightOneSpectrum ℤ) :
    BorelSpace (finitePlaceGL2Gamma0 1 v) := ⟨rfl⟩

/-- Actual Haar probability on the original integral local general-linear group. -/
def finitePlaceIntegralHaar (v : HeightOneSpectrum ℤ) : Measure (finitePlaceGL2Gamma0 1 v) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

instance finitePlaceIntegralHaar_isHaarMeasure (v : HeightOneSpectrum ℤ) :
    (finitePlaceIntegralHaar v).IsHaarMeasure :=
  inferInstanceAs (Measure.IsHaarMeasure (Measure.haarMeasure _))

instance finitePlaceIntegralHaar_isProbabilityMeasure (v : HeightOneSpectrum ℤ) :
    IsProbabilityMeasure (finitePlaceIntegralHaar v) := ⟨Measure.haarMeasure_self⟩

instance finitePlaceIntegralHaar_isMulRightInvariant (v : HeightOneSpectrum ℤ) :
    (finitePlaceIntegralHaar v).IsMulRightInvariant where
  map_mul_right_eq_self k := by
    letI : IsProbabilityMeasure ((finitePlaceIntegralHaar v).map (fun j => j * k)) :=
      Measure.isProbabilityMeasure_map (measurable_mul_const k).aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The literal original compact Haar average of each genuine local induced function. -/
def finitePlaceInducedAverage (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ) :
    FinitePlaceInducedSpace v z₁ z₂ →ₗ[ℂ] ℂ :=
  smoothInducedCompactAverage _ (finitePlaceGL2Gamma0 1 v)
    (finitePlaceLowerCharacter v z₁ z₂) (finitePlaceIntegralHaar v)

/-- The actual compact Haar average is invariant under the original integral local action. -/
theorem finitePlaceInducedAverage_invariant (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ)
    (k : finitePlaceGL2Gamma0 1 v) (f : FinitePlaceInducedSpace v z₁ z₂) :
    finitePlaceInducedAverage v z₁ z₂
      (smoothInducedCharacterRepresentation _ (finitePlaceLowerCharacter v z₁ z₂) k.val f) =
      finitePlaceInducedAverage v z₁ z₂ f :=
  smoothInducedCompactAverage_invariant _ _ _ _ k f

/-- The original spherical section has exactly unit compact Haar average. -/
theorem finitePlaceInducedAverage_spherical (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ) :
    finitePlaceInducedAverage v z₁ z₂ (finitePlaceInducedSpherical v z₁ z₂) = 1 := by
  exact (smoothInducedCompactAverage_fixed _ _ _ _ _
    (finitePlaceInducedSpherical_fixed v z₁ z₂)).trans (finitePlaceInducedSpherical_one v z₁ z₂)

/-- The genuine original compact Haar functional is nonzero. -/
theorem finitePlaceInducedAverage_ne_zero (v : HeightOneSpectrum ℤ) (z₁ z₂ : ℂˣ) :
    finitePlaceInducedAverage v z₁ z₂ ≠ 0 := by
  intro hz
  have he := finitePlaceInducedAverage_spherical v z₁ z₂
  rw [hz, LinearMap.zero_apply] at he
  exact zero_ne_one he

end
end Dubon2026

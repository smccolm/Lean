import Dubon2026.RealIwasawaMeasure
import Dubon2026.ModularGamma0Domain
import Mathlib.MeasureTheory.Integral.Prod

/-! # The genuine lifted Petersson pairing over the original base domain

The integration region is the full compact fiber over the original projective base domain.
No assertion that it is a fundamental domain for the nonprojective real group is made here.
-/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ComplexConjugate

/-- Actual Iwasawa reconstruction preserves the restricted measures over every original base set. -/
theorem realIwasawa_restrict_measurePreserving (S : Set ℍ) :
    MeasurePreserving realIwasawaHomeomorph.symm
      (((volume : Measure ℍ).restrict S).prod realCompactHaar)
      (realGroupMeasure.restrict {g : SL(2, ℝ) | g • I ∈ S}) := by
  have he : realIwasawaHomeomorph.symm ⁻¹' {g : SL(2, ℝ) | g • I ∈ S} =
      S ×ˢ (Set.univ : Set realCompactSubgroup) := by
    ext p
    change (p.1.toSL2R * p.2.val) • I ∈ S ↔ p ∈ S ×ˢ Set.univ
    rw [realIwasawa_orbit]
    simp
  have hh := realIwasawa_measurePreserving.restrict_preimage_emb
    realIwasawaHomeomorph.symm.toMeasurableEquiv.measurableEmbedding
    {g : SL(2, ℝ) | g • I ∈ S}
  rw [he, ← Measure.prod_restrict, Measure.restrict_univ] at hh
  exact hh

/-- The original pointwise real-group pairing is exactly the original Petersson density in Iwasawa coordinates. -/
theorem realWeightLift_pairing_iwasawa (k : ℤ) (f f' : ℍ → ℂ)
    (p : ℍ × realCompactSubgroup) :
    conj (realWeightLift k f (realIwasawaHomeomorph.symm p)) *
      realWeightLift k f' (realIwasawaHomeomorph.symm p) = petersson k f f' p.1 := by
  rw [realWeightLift_pairing]
  change petersson k f f' ((p.1.toSL2R * p.2.val) • I) = _
  rw [realIwasawa_orbit]

/-- Integrability of the actual base Petersson density transfers to the genuine lifted region. -/
theorem realWeightLift_pairing_integrable (k : ℤ) (f f' : ℍ → ℂ) (S : Set ℍ)
    (hS : IntegrableOn (petersson k f f') S (volume : Measure ℍ)) :
    IntegrableOn (fun g : SL(2, ℝ) => conj (realWeightLift k f g) * realWeightLift k f' g)
      {g : SL(2, ℝ) | g • I ∈ S} realGroupMeasure := by
  apply ((realIwasawa_restrict_measurePreserving S).integrable_comp_emb
    realIwasawaHomeomorph.symm.toMeasurableEquiv.measurableEmbedding).mp
  simpa only [Function.comp_def, realWeightLift_pairing_iwasawa] using hS.comp_fst realCompactHaar

/-- Genuine integration over the full compact fiber equals the original base Petersson integral. -/
theorem realWeightLift_pairing_integral (k : ℤ) (f f' : ℍ → ℂ) (S : Set ℍ)
    (hS : IntegrableOn (petersson k f f') S (volume : Measure ℍ)) :
    (∫ g : SL(2, ℝ) in {g | g • I ∈ S},
      conj (realWeightLift k f g) * realWeightLift k f' g ∂realGroupMeasure) =
        ∫ z in S, petersson k f f' z ∂(volume : Measure ℍ) := by
  rw [← (realIwasawa_restrict_measurePreserving S).integral_comp
    realIwasawaHomeomorph.symm.toMeasurableEquiv.measurableEmbedding]
  simp_rw [realWeightLift_pairing_iwasawa]
  rw [integral_prod _ (hS.comp_fst realCompactHaar)]
  simp

/-- The original cusp-form Petersson pairing is exactly the actual real-group integral over the lifted projective base domain. -/
theorem cuspPetersson_eq_realGroup_integral {Q : ℕ} [NeZero Q] {k : ℤ}
    (f f' : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) :
    cuspPetersson f f' = ∫ g : SL(2, ℝ) in {g | g • I ∈ gamma0FundamentalDomain Q},
      conj (realWeightLift k f g) * realWeightLift k f' g ∂realGroupMeasure := by
  rw [realWeightLift_pairing_integral k f f' _ (integrableOn_petersson_gamma0Domain Q f f'),
    cuspPetersson_eq_gamma0Domain_integral Q]

end
end Dubon2026

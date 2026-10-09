import Dubon2026.SmoothInducedContinuity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral

/-! # The genuine compact averaging functional on original smooth induction -/

namespace Dubon2026

noncomputable section
open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (B K : Subgroup G) (χ : B →* ℂ) [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]

/-- Every original smooth induced function is genuinely integrable on the original compact subgroup. -/
theorem smoothInduced_compact_integrable (f : smoothInducedCharacterSpace B χ) :
    Integrable (fun k : K => f.val k.val) μ := by
  have hc : Continuous (fun k : K => f.val k.val) :=
    (smoothInducedCharacter_continuous B χ f).comp continuous_subtype_val
  simpa only [integrableOn_univ] using
    hc.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ

/-- Literal Haar integration on the actual compact subgroup, as a complex linear functional on the original induced space. -/
def smoothInducedCompactAverage : smoothInducedCharacterSpace B χ →ₗ[ℂ] ℂ where
  toFun f := ∫ k : K, f.val k.val ∂μ
  map_add' f j := integral_add (smoothInduced_compact_integrable B K χ μ f)
    (smoothInduced_compact_integrable B K χ μ j)
  map_smul' c f := integral_smul c (fun k : K => f.val k.val)

/-- The actual compact averaging functional uses precisely the original function values and measure. -/
theorem smoothInducedCompactAverage_apply (f : smoothInducedCharacterSpace B χ) :
    smoothInducedCompactAverage B K χ μ f = ∫ k : K, f.val k.val ∂μ := rfl

/-- Original right invariance of the compact measure makes the genuine averaging functional invariant under the actual compact action. -/
theorem smoothInducedCompactAverage_invariant [μ.IsMulRightInvariant]
    (k : K) (f : smoothInducedCharacterSpace B χ) :
    smoothInducedCompactAverage B K χ μ
      (smoothInducedCharacterRepresentation B χ k.val f) =
      smoothInducedCompactAverage B K χ μ f := by
  change (∫ j : K, f.val (j * k).val ∂μ) = ∫ j : K, f.val j.val ∂μ
  exact integral_mul_right_eq_self (fun j : K => f.val j.val) k

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [IsFiniteMeasure μ] in
/-- Genuine compact-fixed induced functions have constant original compact restriction. -/
theorem smoothInduced_fixed_compact_value (f : smoothInducedCharacterSpace B χ)
    (hf : ∀ k : K, smoothInducedCharacterRepresentation B χ k.val f = f) (k : K) :
    f.val k.val = f.val 1 := by
  have he := congrArg (fun j : smoothInducedCharacterSpace B χ => j.val 1) (hf k)
  simpa only [smoothInducedCharacterRepresentation_apply, one_mul] using he

/-- For a genuine compact probability measure, the actual averaging functional recovers the identity value of every original compact-fixed function. -/
theorem smoothInducedCompactAverage_fixed [IsProbabilityMeasure μ]
    (f : smoothInducedCharacterSpace B χ)
    (hf : ∀ k : K, smoothInducedCharacterRepresentation B χ k.val f = f) :
    smoothInducedCompactAverage B K χ μ f = f.val 1 := by
  rw [smoothInducedCompactAverage_apply]
  simp_rw [smoothInduced_fixed_compact_value B K χ f hf]
  simp

end
end Dubon2026

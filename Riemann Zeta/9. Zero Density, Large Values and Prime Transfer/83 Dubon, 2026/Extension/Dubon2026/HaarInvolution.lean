import Dubon2026.FiniteAdelicProjectiveCharacters
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-! # Genuine Haar invariance under involutive continuous group automorphisms -/

namespace Dubon2026

noncomputable section
open MeasureTheory
open scoped NNReal

/-- Every actual involutive continuous group automorphism preserves the original regular Haar measure. -/
theorem continuousMulEquiv_involutive_measurePreserving {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (φ : G ≃ₜ* G) (hφ : Function.Involutive φ) : MeasurePreserving φ μ μ := by
  have he : φ.trans φ = ContinuousMulEquiv.refl G := by ext g; exact hφ g
  have hc : mulEquivHaarChar φ = 1 := by
    apply nnreal_mul_self_eq_one
    rw [← mulEquivHaarChar_trans, he, mulEquivHaarChar_refl]
  refine ⟨φ.continuous.measurable, ?_⟩
  have hm := mulEquivHaarChar_smul_map μ φ
  rwa [hc, one_smul] at hm

end
end Dubon2026

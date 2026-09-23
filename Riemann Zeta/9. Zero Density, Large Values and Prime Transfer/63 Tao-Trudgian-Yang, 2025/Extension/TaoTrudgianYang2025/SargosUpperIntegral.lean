import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Upper nonnegative integral

The infimum over almost-everywhere measurable majorants models the upper
Lebesgue integral even when the integrand itself is not measurable.
It agrees with the ordinary nonnegative integral on measurable functions.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace TaoTrudgianYang2025

def sargosUpperIntegral {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f : A → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (g : A → ℝ≥0∞) (_ : AEMeasurable g μ) (_ : f ≤ᵐ[μ] g), ∫⁻ x, g x ∂μ

theorem sargosUpperIntegral_le {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {f g : A → ℝ≥0∞} (hg : AEMeasurable g μ) (hfg : f ≤ᵐ[μ] g) :
    sargosUpperIntegral μ f ≤ ∫⁻ x, g x ∂μ := by
  exact iInf_le_of_le g (iInf_le_of_le hg (iInf_le _ hfg))

theorem sargosUpperIntegral_eq_lintegral {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {f : A → ℝ≥0∞} (hf : AEMeasurable f μ) :
    sargosUpperIntegral μ f = ∫⁻ x, f x ∂μ := by
  apply le_antisymm (sargosUpperIntegral_le hf (Eventually.of_forall (fun _ => le_rfl)))
  exact le_iInf (fun g => le_iInf (fun _hg => le_iInf (fun hfg => lintegral_mono_ae hfg)))

theorem sargosUpperIntegral_mono_ae {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {f g : A → ℝ≥0∞} (hfg : f ≤ᵐ[μ] g) :
    sargosUpperIntegral μ f ≤ sargosUpperIntegral μ g := by
  refine le_iInf (fun u => le_iInf (fun hu => le_iInf (fun hgu => ?_)))
  exact sargosUpperIntegral_le hu (hfg.trans hgu)

theorem sargosUpperIntegral_ofReal_le_integral {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {f g : A → ℝ} (hg : Integrable g μ)
    (hgn : 0 ≤ᵐ[μ] g) (hfg : f ≤ᵐ[μ] g) :
    sargosUpperIntegral μ (fun x => ENNReal.ofReal (f x)) ≤
      ENNReal.ofReal (∫ x, g x ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hg hgn]
  exact sargosUpperIntegral_le hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (hfg.mono (fun _ h => ENNReal.ofReal_le_ofReal h))

theorem sargosUpperIntegral_ofReal_eq_integral {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {f : A → ℝ} (hf : Integrable f μ) (hfn : 0 ≤ᵐ[μ] f) :
    sargosUpperIntegral μ (fun x => ENNReal.ofReal (f x)) =
      ENNReal.ofReal (∫ x, f x ∂μ) := by
  rw [sargosUpperIntegral_eq_lintegral hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal,
    ofReal_integral_eq_lintegral_ofReal hf hfn]

end TaoTrudgianYang2025

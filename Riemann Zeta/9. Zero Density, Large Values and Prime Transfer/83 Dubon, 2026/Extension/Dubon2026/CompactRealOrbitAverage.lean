import Dubon2026.RationalAdelicAdditiveHaar
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.CompactOpen

/-! # Transfer of a genuine zero real-period average to Haar measure on a compact additive group -/

namespace Dubon2026

noncomputable section
open MeasureTheory Set
open scoped unitInterval

/-- Integration of original continuous functions on the real unit interval is continuous in the genuine supremum norm. -/
theorem continuous_unitInterval_integral :
    Continuous (fun f : C(I, ℂ) => ∫ t : I, f t) := by
  have hi (f : C(I, ℂ)) : Integrable f :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hl : LipschitzWith 1 (fun f : C(I, ℂ) => ∫ t : I, f t) := by
    apply LipschitzWith.of_dist_le_mul
    intro f g
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    rw [← integral_sub (hi f) (hi g)]
    have h := norm_integral_le_of_norm_le_const (μ := (volume : Measure I))
      (Filter.Eventually.of_forall (fun t : I => ContinuousMap.norm_coe_le_norm (f - g) t))
    simpa only [probReal_univ, mul_one, ContinuousMap.sub_apply] using h
  exact hl.continuous

/-- Original interval averaging is continuous in a compact-group translation, without a countability assumption on the group topology. -/
theorem compact_real_orbit_average_continuous {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G]
    (ρ : ℝ →+ G) (hρ : Continuous ρ) (f : G → ℂ) (hf : Continuous f) (h : ℝ) :
    Continuous (fun z : G => ∫ t : I, f (ρ (h * (t : ℝ)) + z)) := by
  let F : C(G × I, ℂ) := ⟨fun p => f (ρ (h * (p.2 : ℝ)) + p.1),
    hf.comp ((hρ.comp (continuous_const.mul
      (continuous_subtype_val.comp continuous_snd))).add continuous_fst)⟩
  exact continuous_unitInterval_integral.comp F.curry.continuous

/-- Density and actual Haar translation invariance transfer a zero real-period average to the original whole compact group integral. -/
theorem compact_additive_integral_zero_of_dense_real_period {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
    [Measure.IsAddLeftInvariant μ] (ρ : ℝ →+ G) (hρ : Continuous ρ)
    (hd : DenseRange ρ) (f : G → ℂ) (hf : Continuous f) (h : ℝ)
    (hz : ∀ a : ℝ, (∫ t : I, f (ρ (h * (t : ℝ)) + ρ a)) = 0) :
    (∫ z, f z ∂μ) = 0 := by
  have havg : ∀ z : G, (∫ t : I, f (ρ (h * (t : ℝ)) + z)) = 0 := by
    intro z
    exact hd.induction_on z
      (isClosed_eq (compact_real_orbit_average_continuous ρ hρ f hf h) continuous_const) hz
  have hc : Continuous (fun p : G × I => f (ρ (h * (p.2 : ℝ)) + p.1)) :=
    hf.comp ((hρ.comp (continuous_const.mul
      (continuous_subtype_val.comp continuous_snd))).add continuous_fst)
  have hi : Integrable (fun p : G × I => f (ρ (h * (p.2 : ℝ)) + p.1)) (μ.prod volume) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs := integral_integral_swap (f := fun (z : G) (t : I) => f (ρ (h * (t : ℝ)) + z)) hi
  simp only [havg, integral_zero, integral_add_left_eq_self, integral_const,
    probReal_univ, one_smul] at hs
  exact hs.symm

end
end Dubon2026

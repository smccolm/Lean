import Dubon2026.RealCyclicRepresentation
import Dubon2026.RealLiftPetersson
import Dubon2026.RealGroupUnimodular
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Actual continuity, boundedness and square integrability of the generated real representation -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups

/-- The actual measure of a full compact fiber over a base set is its original hyperbolic measure. -/
theorem realGroupMeasure_base_fiber (S : Set ℍ) :
    realGroupMeasure {g : SL(2, ℝ) | g • I ∈ S} = (volume : Measure ℍ) S := by
  have he := (realIwasawa_restrict_measurePreserving S).measure_preimage_emb
    realIwasawaHomeomorph.symm.toMeasurableEquiv.measurableEmbedding Set.univ
  simp only [Set.preimage_univ, Measure.restrict_apply_univ] at he
  rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
    measure_univ, mul_one] at he
  exact he.symm

/-- Every original arithmetic cusp lift is globally bounded in its actual real-group norm. -/
theorem realWeightLift_bounded {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (f : CuspForm Γ k) : ∃ C : ℝ, 0 ≤ C ∧ ∀ g : SL(2, ℝ), ‖realWeightLift k f g‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ f f
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC I)
  refine ⟨C + 1, by linarith, fun g => ?_⟩
  have hn : ‖realWeightLift k f g‖ ^ 2 ≤ C := by
    rw [realWeightLift_norm_sq]
    exact hC (g • I)
  nlinarith [sq_nonneg (‖realWeightLift k f g‖ - 1)]

/-- Every vector in the actual algebraic cyclic representation is a continuous original real-group function. -/
theorem realLiftCyclic_continuous {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {v : SL(2, ℝ) → ℂ}
    (hv : v ∈ (realLiftCyclicRepresentation k f).toSubmodule) : Continuous v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    exact (realWeightLift_continuous k (ModularFormClass.continuous f)).comp
      (continuous_id.mul_const h)
  | zero => exact continuous_const
  | add x y hx hy hix hiy => exact hix.add hiy
  | smul c x hx hix => exact hix.const_smul c

/-- Finite linear combinations of actual right translates retain a genuine global bound. -/
theorem realLiftCyclic_bounded {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    (f : CuspForm Γ k) {v : SL(2, ℝ) → ℂ}
    (hv : v ∈ (realLiftCyclicRepresentation k f).toSubmodule) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : SL(2, ℝ), ‖v g‖ ≤ C := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    obtain ⟨C, hC0, hC⟩ := realWeightLift_bounded f
    exact ⟨C, hC0, fun g => hC (g * h)⟩
  | zero => exact ⟨0, le_rfl, fun _ => by simp⟩
  | add x y hx hy hix hiy =>
    obtain ⟨Cx, hx0, hCx⟩ := hix
    obtain ⟨Cy, hy0, hCy⟩ := hiy
    exact ⟨Cx + Cy, add_nonneg hx0 hy0,
      fun g => (norm_add_le (x g) (y g)).trans (add_le_add (hCx g) (hCy g))⟩
  | smul c x hx hix =>
    obtain ⟨C, hC0, hC⟩ := hix
    refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC0, fun g => ?_⟩
    simpa only [Pi.smul_apply, norm_smul] using mul_le_mul_of_nonneg_left (hC g) (norm_nonneg c)

/-- Every actual cyclic cusp vector is square integrable on the full compact fiber over the original finite-volume projective base domain. -/
theorem realLiftCyclic_memLp_two {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k) {v : SL(2, ℝ) → ℂ}
    (hv : v ∈ (realLiftCyclicRepresentation k f).toSubmodule) :
    MemLp v 2 (realGroupMeasure.restrict {g : SL(2, ℝ) | g • I ∈ gamma0FundamentalDomain Q}) := by
  letI : IsFiniteMeasure
      (realGroupMeasure.restrict {g : SL(2, ℝ) | g • I ∈ gamma0FundamentalDomain Q}) := by
    constructor
    simpa only [Measure.restrict_apply_univ, realGroupMeasure_base_fiber] using
      (gamma0FundamentalDomain_volume_lt_top Q)
  obtain ⟨C, _, hC⟩ := realLiftCyclic_bounded f hv
  exact MemLp.of_bound (realLiftCyclic_continuous f hv).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

end
end Dubon2026

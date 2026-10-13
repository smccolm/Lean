/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the Mathlib LICENSE.
Adapted from the pinned Mathlib InfinitePlace.denseRange_algebraMap_pi
(c5ea00351c28e24afc9f0f84379aa41082b1188f); the same proved approximation
argument is applied only to finite sets of actual original finite places.
-/
import Dubon2026.OriginalFinitePlaceIndependence
import Mathlib.Analysis.Normed.Field.WithAbs

/-! # Simultaneous approximation in the original finite completions

This supplies the density input in the original decomposition-group fixed
field comparison. Together with the closed original base-completion map,
that comparison advances the native norm quotient required for DUB-17's
global duality, numerical Selmer and automorphy dependency chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain Filter
open scoped NumberField Topology
variable (K : Type) [Field K] [NumberField K]

/-- The diagonal field is dense for any finite set of original finite-place absolute values. -/
theorem original_finitePlace_withAbs_dense (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (algebraMap K (∀ v : S, WithAbs (NumberField.HeightOneSpectrum.adicAbv K v.1))) := by
  classical
  let abv := fun v : S => NumberField.HeightOneSpectrum.adicAbv K v.1
  refine Metric.denseRange_iff.mpr fun z r hr => ?_
  choose a hx using AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv
    (fun v : S => original_adicAbv_isNontrivial K v.1)
    (fun v w hvw => original_adicAbv_not_isEquiv_of_ne K (Subtype.coe_injective.ne hvw))
  let y := fun n => ∑ v : S, (1 / (1 + (a v)⁻¹ ^ n)) * WithAbs.equiv (abv v) (z v)
  have hy : Tendsto (fun n (v : S) => (WithAbs.equiv (abv v)).symm (y n)) atTop (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun u => ?_
    simp_rw [← Fintype.sum_pi_single u z, y, map_sum, map_mul]
    refine tendsto_finsetSum _ fun w _ => ?_
    by_cases hw : u = w
    · rw [← hw, Pi.single_eq_same]
      have hu : abv u (a u)⁻¹ < 1 := by
        simpa [abv, ← inv_pow, inv_lt_one_iff₀] using Or.inr (a := a u = 0) (hx u).1
      simpa using (WithAbs.tendsto_one_div_one_add_pow_nhds_one hu).mul_const (z u)
    · rw [Pi.single_eq_of_ne (M := fun v => WithAbs (abv v)) hw (z w)]
      have ha0 : a w ≠ 0 := by
        intro hzero
        have hgt := (hx w).1
        rw [hzero, map_zero] at hgt
        exact (not_lt_of_ge (zero_le_one : (0 : ℝ) ≤ 1)) hgt
      have hu : 1 < abv u (a w)⁻¹ := by
        simpa [one_lt_inv_iff₀] using And.intro ((abv u).pos_iff.mpr ha0) ((hx w).2 u hw)
      have ht := (abv u).tendsto_div_one_add_pow_nhds_zero hu
      simp_rw [← WithAbs.norm_toAbs_eq] at ht
      simpa using (tendsto_zero_iff_norm_tendsto_zero.mpr ht).mul_const
        ((WithAbs.equiv (abv u)).symm (WithAbs.equiv (abv w) (z w)))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hy r hr
  exact ⟨y N, dist_comm z (algebraMap K _ (y N)) ▸ hN N le_rfl⟩

/-- The original number field is dense diagonally in any finite product of its original finite completions. -/
theorem original_finiteCompletions_dense (S : Finset (HeightOneSpectrum (𝓞 K))) :
    DenseRange (fun x : K => fun v : S => algebraMap K (v.1.adicCompletion K) x) := by
  let abv := fun v : S => NumberField.HeightOneSpectrum.adicAbv K v.1
  let f := fun v : S => (algebraMap K (v.1.adicCompletion K)).comp (WithAbs.equiv (abv v)).toRingHom
  have hf (v : S) : Isometry (f v) := by
    apply AddMonoidHomClass.isometry_of_norm
    intro x
    change ‖NumberField.FinitePlace.embedding v.1 (WithAbs.equiv (abv v) x)‖ = ‖x‖
    rw [NumberField.FinitePlace.norm_embedding]
    rfl
  have hd (v : S) : DenseRange (f v) := by
    have h := v.1.denseRange_algebraMap K
    intro x
    apply h.mono
    rintro y ⟨r, rfl⟩
    exact ⟨(WithAbs.equiv (abv v)).symm r, rfl⟩
  exact (DenseRange.piMap hd).comp (original_finitePlace_withAbs_dense K S)
    (continuous_pi fun v => (hf v).continuous.comp (continuous_apply v))

end
end Dubon2026

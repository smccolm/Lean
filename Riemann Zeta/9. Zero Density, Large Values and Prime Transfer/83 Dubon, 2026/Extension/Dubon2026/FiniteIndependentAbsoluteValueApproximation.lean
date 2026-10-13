/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the Mathlib LICENSE.
Adapted from pinned Mathlib InfinitePlace.denseRange_algebraMap_pi,
c5ea00351c28e24afc9f0f84379aa41082b1188f.
-/
import Dubon2026.OriginalFinitePlaceWeakApproximation

/-! # Approximation for the finite family needed by original norm correction

The same proved finite-place approximation argument applies to the combined
finite and archimedean family. This is used to construct a principal norm
correction, hence prime selection for the DUB-17 global norm-index bound.
-/
namespace Dubon2026
noncomputable section
open Filter
open scoped Topology
variable (K : Type) [Field K] {ι : Type} [Fintype ι]

/-- A finite independent nontrivial absolute-value family admits diagonal approximation. -/
theorem finite_independent_absoluteValues_dense (abv : ι → AbsoluteValue K ℝ)
    (hNontrivial : ∀ i, (abv i).IsNontrivial)
    (hIndependent : Pairwise fun i j => ¬ (abv i).IsEquiv (abv j)) :
    DenseRange (algebraMap K (∀ i, WithAbs (abv i))) := by
  classical
  refine Metric.denseRange_iff.mpr fun z r hr => ?_
  choose a hx using AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv
    hNontrivial hIndependent
  let y := fun n => ∑ v : ι, (1 / (1 + (a v)⁻¹ ^ n)) * WithAbs.equiv (abv v) (z v)
  have hy : Tendsto (fun n (v : ι) => (WithAbs.equiv (abv v)).symm (y n)) atTop (𝓝 z) := by
    refine tendsto_pi_nhds.mpr fun u => ?_
    simp_rw [← Fintype.sum_pi_single u z, y, map_sum, map_mul]
    refine tendsto_finsetSum _ fun w _ => ?_
    by_cases hw : u = w
    · rw [← hw, Pi.single_eq_same]
      have hu : abv u (a u)⁻¹ < 1 := by
        simpa [← inv_pow, inv_lt_one_iff₀] using Or.inr (a := a u = 0) (hx u).1
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

end
end Dubon2026

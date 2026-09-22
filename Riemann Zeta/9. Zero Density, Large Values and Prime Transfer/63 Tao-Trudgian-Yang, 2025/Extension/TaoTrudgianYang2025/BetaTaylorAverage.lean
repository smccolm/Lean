import TaoTrudgianYang2025.BetaMorseCriticalPoint
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smooth Taylor averages along an actual real segment

The averaging interval is fixed. Every derivative is justified by a
locally uniform integrable bound on the original function's next jet.
These averages will remove the stationary deficit's apparent singularity.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def segmentTaylorAverage (f : ℝ → ℝ) (a : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1, (1-t)*t^k*iteratedDeriv k f (a+t*(x-a))

theorem affineSegment_mem_Icc {b c a x t : ℝ}
    (ha : a ∈ Icc b c) (hx : x ∈ Icc b c) (ht : t ∈ Icc (0 : ℝ) 1) :
    a+t*(x-a) ∈ Icc b c := by
  simpa only [smul_eq_mul] using
    (convex_Icc b c).add_smul_mem ha (by simpa using hx) ht

theorem affineSegment_mem_Ioo {b c a x t : ℝ}
    (ha : a ∈ Ioo b c) (hx : x ∈ Ioo b c) (ht : t ∈ Icc (0 : ℝ) 1) :
    a+t*(x-a) ∈ Ioo b c := by
  simpa only [smul_eq_mul] using
    (convex_Ioo b c).add_smul_mem ha (by simpa using hx) ht

theorem segmentTaylorAverage_integrable
    {f : ℝ → ℝ} {l r a x : ℝ}
    (hf : ∀ u ∈ Ioo l r, ContDiffAt ℝ ∞ f u)
    (ha : a ∈ Ioo l r) (hx : x ∈ Ioo l r) (k : ℕ) :
    IntegrableOn (fun t : ℝ => (1-t)*t^k*iteratedDeriv k f (a+t*(x-a)))
      (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.integrableOn_Icc
  intro t ht
  have hc := (contDiffAt_iteratedDeriv_infty
    (hf _ (affineSegment_mem_Ioo ha hx ht)) k).continuousAt
  exact ((continuousWithinAt_const.sub continuousWithinAt_id).mul
    (continuousWithinAt_id.pow k)).mul
      (hc.comp_continuousWithinAt (f := fun t : ℝ => a+t*(x-a)) (by
        fun_prop : ContinuousWithinAt (fun t : ℝ => a+t*(x-a)) (Icc (0 : ℝ) 1) t))

theorem segmentTaylorAverage_hasDerivAt
    {f : ℝ → ℝ} {l r a x : ℝ}
    (hf : ∀ u ∈ Ioo l r, ContDiffAt ℝ ∞ f u)
    (ha : a ∈ Ioo l r) (hx : x ∈ Ioo l r) (k : ℕ) :
    HasDerivAt (segmentTaylorAverage f a k)
      (segmentTaylorAverage f a (k+1) x) x := by
  obtain ⟨b,hlb,hb⟩ := exists_between (lt_min ha.1 hx.1)
  obtain ⟨c,hc,hcr⟩ := exists_between (max_lt ha.2 hx.2)
  have ha' : a ∈ Icc b c :=
    ⟨(hb.trans_le (min_le_left _ _)).le,((le_max_left _ _).trans_lt hc).le⟩
  have hx' : x ∈ Ioo b c :=
    ⟨hb.trans_le (min_le_right _ _),(le_max_right _ _).trans_lt hc⟩
  have hsub : Icc b c ⊆ Ioo l r := fun u hu =>
    ⟨hlb.trans_le hu.1,hu.2.trans_lt hcr⟩
  have hj : ContinuousOn (iteratedDeriv (k+1) f) (Icc b c) := by
    intro u hu
    exact (contDiffAt_iteratedDeriv_infty (hf u (hsub hu)) (k+1)).continuousAt.continuousWithinAt
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hj
  have hbound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ∀ z ∈ Ioo b c,
        ‖(1-t)*t^(k+1)*iteratedDeriv (k+1) f (a+t*(z-a))‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht z hz
    have hfactor : 0 ≤ (1-t)*t^(k+1) := mul_nonneg (by linarith [ht.2])
      (pow_nonneg ht.1 _)
    have hfactor' : (1-t)*t^(k+1) ≤ 1 := by
      have hp : t^(k+1) ≤ 1 := pow_le_one₀ ht.1 ht.2
      nlinarith [mul_nonneg ht.1 (pow_nonneg ht.1 (k+1))]
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hfactor]
    exact (mul_le_of_le_one_left (norm_nonneg _) hfactor').trans
      (hM _ (affineSegment_mem_Icc ha' (Ioo_subset_Icc_self hz) ht))
  have hdiff : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ∀ z ∈ Ioo b c,
        HasDerivAt (fun y : ℝ => (1-t)*t^k*iteratedDeriv k f (a+t*(y-a)))
          ((1-t)*t^(k+1)*iteratedDeriv (k+1) f (a+t*(z-a))) z := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht z hz
    have hu := hsub (affineSegment_mem_Icc ha' (Ioo_subset_Icc_self hz) ht)
    have hd := (contDiffAt_iteratedDeriv_infty (hf _ hu) k).differentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hh := (hd.hasDerivAt.comp z
      ((((hasDerivAt_id z).sub_const a).const_mul t).const_add a)).const_mul ((1-t)*t^k)
    convert hh using 1
    rw [iteratedDeriv_succ]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t : ℝ => (1-t)*t^k*iteratedDeriv k f (a+t*(z-a)))
    (F' := fun z t : ℝ => (1-t)*t^(k+1)*iteratedDeriv (k+1) f (a+t*(z-a)))
    (bound := fun _ : ℝ => M)
    (Ioo_mem_nhds hx'.1 hx'.2)
    (by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with z hz
      exact (segmentTaylorAverage_integrable hf ha hz k).aestronglyMeasurable)
    (segmentTaylorAverage_integrable hf ha hx k)
    (segmentTaylorAverage_integrable hf ha hx (k+1)).aestronglyMeasurable
    hbound (integrable_const M) hdiff).2

theorem segmentTaylorAverage_contDiffOn
    {f : ℝ → ℝ} {l r a : ℝ}
    (hf : ∀ u ∈ Ioo l r, ContDiffAt ℝ ∞ f u)
    (ha : a ∈ Ioo l r) (k : ℕ) :
    ContDiffOn ℝ ∞ (segmentTaylorAverage f a k) (Ioo l r) := by
  apply contDiffOn_infty.mpr
  intro n
  induction n generalizing k with
  | zero =>
      rw [Nat.cast_zero,contDiffOn_zero]
      exact fun x hx => (segmentTaylorAverage_hasDerivAt hf ha hx k).continuousAt.continuousWithinAt
  | succ n ih =>
      rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨fun x hx => (segmentTaylorAverage_hasDerivAt hf ha hx k).differentiableAt.differentiableWithinAt,
        by simp,?_⟩
      exact (ih (k+1)).congr (fun x hx => (segmentTaylorAverage_hasDerivAt hf ha hx k).deriv)

end TaoTrudgianYang2025

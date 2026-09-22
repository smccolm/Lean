import TaoTrudgianYang2025.BetaLegendreAnchoring
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Smooth cutoffs on retained real intervals

The plateau and support are constructed from strict endpoint buffers.
Multiplication by the cutoff turns a function smooth near its support
into a globally smooth correction, without extending the original function.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025

theorem exists_smooth_interval_cutoff {l a b r : ℝ}
    (hla : l < a) (hab : a ≤ b) (hbr : b < r) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
      (∀ x ∈ Icc a b, χ x = 1) ∧ tsupport χ ⊆ Ioo l r ∧
      HasCompactSupport χ ∧ ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := by
  let m := min (a-l) (r-b)
  have hm : 0 < m := lt_min (sub_pos.mpr hla) (sub_pos.mpr hbr)
  let c := (a+b)/2
  let f : ContDiffBump c :=
    ⟨(b-a)/2+m/3, (b-a)/2+2*m/3, by linarith,
      by linarith⟩
  refine ⟨f,f.contDiff,?_,?_,f.hasCompactSupport,fun x => ⟨f.nonneg,f.le_one⟩⟩
  · intro x hx
    apply f.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    dsimp [f,c]
    constructor <;> linarith [hx.1,hx.2]
  · intro x hx
    rw [f.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    have hm₁ : m ≤ a-l := min_le_left _ _
    have hm₂ : m ≤ r-b := min_le_right _ _
    dsimp [f,c] at hx
    constructor <;> linarith [hx.1,hx.2]

theorem smoothCutoff_mul_contDiff {χ H : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hH : ∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ H x) :
    ContDiff ℝ ∞ (fun x => χ x * H x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hH x hx)
  · have he : (fun y => χ y * H y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [hy, zero_mul, Pi.zero_apply]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem smoothCutoff_mul_iteratedDeriv_zero {χ H : ℝ → ℝ}
    {x : ℝ} (hx : x ∉ tsupport χ) (n : ℕ) :
    iteratedDeriv n (fun y => χ y * H y) x = 0 := by
  have he : (fun y => χ y * H y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [hy, zero_mul, Pi.zero_apply]
  rw [he.iteratedDeriv_eq n]
  simp

end TaoTrudgianYang2025

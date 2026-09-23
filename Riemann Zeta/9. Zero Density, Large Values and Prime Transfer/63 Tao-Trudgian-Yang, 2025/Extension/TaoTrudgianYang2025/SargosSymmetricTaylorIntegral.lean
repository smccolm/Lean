import TaoTrudgianYang2025.SargosTaylorIntegral

/-! The source symmetric sixth-derivative integral formula, on its actual segment. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem sargosSymmetricRemainder_eq_integral {f : ℝ → ℝ} {m n : ℝ}
    (hn : 0 ≤ n)
    (hf : ∀ x ∈ Icc (m-n) (m+n), ContDiffAt ℝ ∞ f x) :
    sargosSymmetricRemainder f n m =
      (1/120:ℝ)*∫ t in (0:ℝ)..n,
        (iteratedDeriv 6 f (m+t)+iteratedDeriv 6 f (m-t))*(n-t)^5 := by
  have hmem (t : ℝ) (ht : t ∈ uIcc (0:ℝ) n) :
      m+t ∈ Icc (m-n) (m+n) ∧ m-t ∈ Icc (m-n) (m+n) := by
    rw [uIcc_of_le hn] at ht
    constructor <;> constructor <;> linarith [ht.1,ht.2]
  have hplus : ∀ t ∈ uIcc (0:ℝ) n, ContDiffAt ℝ ∞ (fun x => f (m+x)) t := by
    intro t ht
    exact (hf _ (hmem t ht).1).comp t (contDiffAt_const.add contDiffAt_id)
  have hminus : ∀ t ∈ uIcc (0:ℝ) n, ContDiffAt ℝ ∞ (fun x => f (m-x)) t := by
    intro t ht
    exact (hf _ (hmem t ht).2).comp t (contDiffAt_const.sub contDiffAt_id)
  have hp := sargos_taylor_integral_remainder hplus 5
  have hm := sargos_taylor_integral_remainder hminus 5
  rw [sargos_taylor_polynomial_shift] at hp
  rw [sargos_taylor_polynomial_reflect] at hm
  simp only [Nat.reduceAdd,iteratedDeriv_comp_const_add] at hp
  simp only [Nat.reduceAdd,iteratedDeriv_comp_const_sub] at hm
  norm_num at hp hm
  have hip : IntervalIntegrable
      (fun t => ((n-t)^5/120)*iteratedDeriv 6 f (m+t)) volume 0 n := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hc := (contDiffAt_iteratedDeriv_infty (hf _ (hmem t ht).1) 6).continuousAt
    exact (by fun_prop : ContinuousWithinAt (fun t : ℝ => (n-t)^5/120) (uIcc 0 n) t).mul
      (hc.comp_continuousWithinAt (f := fun t : ℝ => m+t) (by fun_prop))
  have him : IntervalIntegrable
      (fun t => ((n-t)^5/120)*iteratedDeriv 6 f (m-t)) volume 0 n := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hc := (contDiffAt_iteratedDeriv_infty (hf _ (hmem t ht).2) 6).continuousAt
    exact (by fun_prop : ContinuousWithinAt (fun t : ℝ => (n-t)^5/120) (uIcc 0 n) t).mul
      (hc.comp_continuousWithinAt (f := fun t : ℝ => m-t) (by fun_prop))
  rw [sargosSymmetricRemainder_eq_errors,hp,hm,
    ← intervalIntegral.integral_add hip him,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  ring

end TaoTrudgianYang2025

import TaoTrudgianYang2025.ExponentPairShiftJets

/-!
# Quantitative model errors for an actual difference segment

Mean value is applied to the original phase jet plus a linear reference
correction. Every intermediate point stays inside the original model
interval; no exterior smoothness or assumed difference model is used.
-/

noncomputable section

open Set Expdb

open scoped ContDiff

namespace TaoTrudgianYang2025

theorem modelPhase_jet_difference_error
    {F : ℝ → ℝ} {σ δ η u v w : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hu : u ∈ Ioo (1 : ℝ) 2) (hv : v ∈ Ioo (1 : ℝ) 2)
    (hw : w ∈ Ioo (1 : ℝ) 2) (hvw : v ≤ w)
    (hvu : |v-u| ≤ η) (hwu : |w-u| ≤ η) (p : ℕ) (hp : p+1 ≤ P) :
    |iteratedDeriv (p+1) F v-iteratedDeriv (p+1) F w-
      σ*(w-v)*iteratedDeriv p (modelPhase (σ+1)) u| ≤
      (δ+σ*modelPhaseJetCoefficient (σ+1) (p+1)*η)*(w-v) := by
  let R := iteratedDeriv p (modelPhase (σ+1)) u
  let f : ℝ → ℝ := fun x => iteratedDeriv (p+1) F x+σ*x*R
  have hxI {x : ℝ} (hx : x ∈ Icc v w) : x ∈ Ioo (1 : ℝ) 2 :=
    ⟨hv.1.trans_le hx.1,hx.2.trans_lt hw.2⟩
  have hxU {x : ℝ} (hx : x ∈ Icc v w) : |x-u| ≤ η := by
    have hl := (abs_le.mp hvu).1
    have hr := (abs_le.mp hwu).2
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  have hd (x : ℝ) (hx : x ∈ Icc v w) :
      HasDerivAt f (iteratedDeriv (p+2) F x+σ*R) x := by
    have hdF := (contDiffAt_iteratedDeriv_infty
      (approximateModelPhase_contDiffAt hF (hxI hx)) (p+1)).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hj : HasDerivAt (iteratedDeriv (p+1) F) (iteratedDeriv (p+2) F x) x := by
      simpa only [iteratedDeriv_succ] using hdF.hasDerivAt
    convert hj.add (((hasDerivAt_id x).const_mul σ).mul_const R) using 1
    simp only [mul_one]
  have hb (x : ℝ) (hx : x ∈ Icc v w) :
      ‖deriv f x‖ ≤ δ+σ*modelPhaseJetCoefficient (σ+1) (p+1)*η := by
    rw [(hd x hx).deriv,Real.norm_eq_abs]
    have he := approximateModelPhase_iteratedDeriv_error hF (hxI hx) (p+1) hp
    have hl := iteratedDeriv_modelPhase_lipschitz (show 0 ≤ σ+1 by linarith)
      hu (hxI hx) p
    have hl' : |R-iteratedDeriv p (modelPhase (σ+1)) x| ≤
        modelPhaseJetCoefficient (σ+1) (p+1)*η := by
      exact hl.trans (mul_le_mul_of_nonneg_left
        (by simpa only [abs_sub_comm] using hxU hx)
        (modelPhaseJetCoefficient_nonneg _ _))
    calc
      _ = |(iteratedDeriv (p+2) F x-iteratedDeriv (p+1) (modelPhase σ) x)+
          σ*(R-iteratedDeriv p (modelPhase (σ+1)) x)| := by
        rw [modelPhase_iteratedDeriv_succ_parameter σ (zero_lt_one.trans (hxI hx).1) p]
        congr 1
        ring
      _ ≤ |iteratedDeriv (p+2) F x-iteratedDeriv (p+1) (modelPhase σ) x|+
          |σ*(R-iteratedDeriv p (modelPhase (σ+1)) x)| := abs_add_le _ _
      _ ≤ δ+σ*(modelPhaseJetCoefficient (σ+1) (p+1)*η) := by
        rw [abs_mul,abs_of_pos hσ]
        exact add_le_add he (mul_le_mul_of_nonneg_left hl' hσ.le)
      _ = _ := by ring
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hd x hx).differentiableAt) hb (convex_Icc v w)
    (right_mem_Icc.mpr hvw) (left_mem_Icc.mpr hvw)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hvw)] at hm
  convert hm using 1 <;> dsimp [f,R] <;> congr 1 <;> ring

end TaoTrudgianYang2025

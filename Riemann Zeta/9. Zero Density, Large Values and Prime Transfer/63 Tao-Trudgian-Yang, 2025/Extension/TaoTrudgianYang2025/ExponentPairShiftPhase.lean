import TaoTrudgianYang2025.BetaModelJetEstimates
import Expdb.Mathlib.IteratedDeriv

/-!
# Domain-preserving phases for the analytic A-process

The affine compression keeps every shifted argument inside the original
closed model interval. Its physical coordinates are N-r and m-r, not an
independently supplied dual scale.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def aProcessShiftPoint (η t u : ℝ) : ℝ :=
  (1-η)*u+(1+t)*η

theorem aProcessShiftPoint_mem_Icc {η t u : ℝ}
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (1 : ℝ) 2) :
    aProcessShiftPoint η t u ∈ Icc (1 : ℝ) 2 := by
  have hleft := mul_nonneg (by linarith : 0 ≤ 1-η) (by linarith [hu.1] : 0 ≤ u-1)
  have hright := mul_nonneg (by linarith : 0 ≤ 1-η) (by linarith [hu.2] : 0 ≤ 2-u)
  have htη := mul_nonneg ht.1 hη
  have htcη := mul_nonneg (by linarith [ht.2] : 0 ≤ 1-t) hη
  constructor <;> dsimp [aProcessShiftPoint] <;> nlinarith

theorem aProcessShiftPoint_mem_Ioo {η t u : ℝ}
    (hη : 0 ≤ η) (hη₁ : η < 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Ioo (1 : ℝ) 2) :
    aProcessShiftPoint η t u ∈ Ioo (1 : ℝ) 2 := by
  have hleft := mul_pos (by linarith : 0 < 1-η) (by linarith [hu.1] : 0 < u-1)
  have hright := mul_pos (by linarith : 0 < 1-η) (by linarith [hu.2] : 0 < 2-u)
  have htη := mul_nonneg ht.1 hη
  have htcη := mul_nonneg (by linarith [ht.2] : 0 ≤ 1-t) hη
  constructor <;> dsimp [aProcessShiftPoint] <;> nlinarith

theorem aProcessShiftPoint_distance {η t u : ℝ}
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (1 : ℝ) 2) :
    |aProcessShiftPoint η t u-u| ≤ η := by
  have hlo := mul_nonneg (by linarith [ht.1,hu.2] : 0 ≤ 2+t-u) hη
  have hhi := mul_nonneg (by linarith [ht.2,hu.1] : 0 ≤ u-t) hη
  rw [abs_le]
  constructor <;> dsimp [aProcessShiftPoint] <;> nlinarith

def aProcessShiftPhase (F : ℝ → ℝ) (σ η u : ℝ) : ℝ :=
  (F (aProcessShiftPoint η 0 u)-F (aProcessShiftPoint η 1 u))/(σ*η)

theorem aProcessShiftPhase_contDiffOn {F : ℝ → ℝ} {η : ℝ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (σ : ℝ) : ContDiffOn ℝ ∞ (aProcessShiftPhase F σ η) phaseInterval := by
  have hc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffOn ℝ ∞ (fun u => F (aProcessShiftPoint η t u)) phaseInterval := by
    apply hF.comp (by unfold aProcessShiftPoint; fun_prop)
    intro u hu
    exact aProcessShiftPoint_mem_Icc hη hη₁ ht hu
  exact ((hc 0 (by norm_num)).sub (hc 1 (by norm_num))).div_const (σ*η)

theorem aProcessShiftPhase_iteratedDerivWithin {F : ℝ → ℝ} {η u : ℝ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hu : u ∈ phaseInterval) (σ : ℝ) (n : ℕ) :
    iteratedDerivWithin n (aProcessShiftPhase F σ η) phaseInterval u =
      (1-η)^n/(σ*η) *
        (iteratedDerivWithin n F phaseInterval (aProcessShiftPoint η 0 u)-
         iteratedDerivWithin n F phaseInterval (aProcessShiftPoint η 1 u)) := by
  have hf : ContDiffOn ℝ n F phaseInterval :=
    hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)
  have hc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffOn ℝ n (fun u => F (aProcessShiftPoint η t u)) phaseInterval := by
    apply hf.comp (by unfold aProcessShiftPoint; fun_prop)
    intro v hv
    exact aProcessShiftPoint_mem_Icc hη hη₁ ht hv
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin n (fun u => F (aProcessShiftPoint η t u)) phaseInterval u =
        (1-η)^n*iteratedDerivWithin n F phaseInterval (aProcessShiftPoint η t u) :=
    iteratedDerivWithin_comp_affine_of_mapsTo hf uniqueDiffOn_phaseInterval
      uniqueDiffOn_phaseInterval hu (fun _ hv => aProcessShiftPoint_mem_Icc hη hη₁ ht hv)
  unfold aProcessShiftPhase
  simp only [div_eq_mul_inv]
  have hs := iteratedDerivWithin_sub hu uniqueDiffOn_phaseInterval
    (hc 0 (by norm_num) u hu) (hc 1 (by norm_num) u hu)
  simp only [Pi.sub_def] at hs
  rw [iteratedDerivWithin_mul_const_field,hs,
    hd 0 (by norm_num),hd 1 (by norm_num)]
  ring

theorem aProcessShiftPoint_physical {N r m : ℝ}
    (hN : N ≠ 0) (hNr : N-r ≠ 0) :
    aProcessShiftPoint (r/N) 0 ((m-r)/(N-r)) = m/N ∧
    aProcessShiftPoint (r/N) 1 ((m-r)/(N-r)) = (m+r)/N := by
  constructor <;> dsimp [aProcessShiftPoint] <;> field_simp <;> ring

theorem aProcessShiftPhase_physical {F : ℝ → ℝ} {σ T N r m : ℝ}
    (hN : N ≠ 0) (hNr : N-r ≠ 0) (hσ : σ ≠ 0) (hr : r ≠ 0) :
    (σ*T*r/N)*aProcessShiftPhase F σ (r/N) ((m-r)/(N-r)) =
      T*(F (m/N)-F ((m+r)/N)) := by
  unfold aProcessShiftPhase
  rw [(aProcessShiftPoint_physical (m := m) hN hNr).1,
    (aProcessShiftPoint_physical (m := m) hN hNr).2]
  field_simp

end TaoTrudgianYang2025

import TaoTrudgianYang2025.ExponentPairDifferenceError
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Finite-jet bounds for the compressed A-process model

The error is delta/sigma plus a fixed coefficient times the shift ratio.
It is uniform in the original source phase and includes the actual
closed model interval through the endpoint bridge.
-/

noncomputable section

open Set Expdb
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

theorem abs_compression_pow_sub_one {η : ℝ}
    (hη : 0 ≤ η) (hη₁ : η ≤ 1) (n : ℕ) :
    |(1-η)^n-1| ≤ (n : ℝ)*η := by
  have hp : (1-η)^n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hl := one_add_mul_sub_le_pow (a := 1-η) (by linarith) n
  rw [abs_of_nonpos (sub_nonpos.mpr hp)]
  nlinarith

theorem aProcessShiftPhase_jet_error
    {F : ℝ → ℝ} {σ δ η u : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hη : 0 < η) (hη₁ : η < 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hu : u ∈ Ioo (1 : ℝ) 2) (p : ℕ) (hp : p+1 ≤ P) :
    |iteratedDeriv (p+1) (aProcessShiftPhase F σ η) u-
      iteratedDeriv p (modelPhase (σ+1)) u| ≤
      δ/σ+(modelPhaseJetCoefficient (σ+1) (p+1)+
        (p+1 : ℕ)*modelPhaseJetCoefficient (σ+1) p)*η := by
  let v := aProcessShiftPoint η 0 u
  let w := aProcessShiftPoint η 1 u
  let R := iteratedDeriv p (modelPhase (σ+1)) u
  let D := iteratedDeriv (p+1) F v-iteratedDeriv (p+1) F w
  let C := modelPhaseJetCoefficient (σ+1) (p+1)
  let J := modelPhaseJetCoefficient (σ+1) p
  let a := (1-η)^(p+1)
  have hv : v ∈ Ioo (1 : ℝ) 2 :=
    aProcessShiftPoint_mem_Ioo hη.le hη₁ (by norm_num) hu
  have hw : w ∈ Ioo (1 : ℝ) 2 :=
    aProcessShiftPoint_mem_Ioo hη.le hη₁ (by norm_num) hu
  have hdiff : w-v = η := by dsimp [v,w,aProcessShiftPoint]; ring
  have hle : v ≤ w := by linarith
  have he := modelPhase_jet_difference_error hσ hF hu hv hw hle
    (aProcessShiftPoint_distance hη.le (by norm_num) ⟨hu.1.le,hu.2.le⟩)
    (aProcessShiftPoint_distance hη.le (by norm_num) ⟨hu.1.le,hu.2.le⟩) p hp
  rw [hdiff] at he
  have hden : 0 < σ*η := mul_pos hσ hη
  have hquot : |D/(σ*η)-R| ≤ δ/σ+C*η := by
    have hq := div_le_div_of_nonneg_right he hden.le
    have hleft : D/(σ*η)-R = (D-σ*η*R)/(σ*η) := by field_simp
    rw [hleft,abs_div,abs_of_pos hden]
    convert hq using 1
    dsimp [C]
    field_simp
  have ha0 : 0 ≤ a := pow_nonneg (by linarith) _
  have ha1 : a ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hscale : |a-1| ≤ (p+1 : ℕ)*η := abs_compression_pow_sub_one hη.le hη₁.le _
  have hR : |R| ≤ J := iteratedDeriv_modelPhase_abs_le (by linarith) hu p
  rw [aProcessShiftPhase_iteratedDeriv hF.1 hη.le hη₁ hu σ (p+1)]
  change |a/(σ*η)*D-R| ≤ _
  calc
    _ = |a*(D/(σ*η)-R)+(a-1)*R| := by congr 1; ring
    _ ≤ |a*(D/(σ*η)-R)|+|(a-1)*R| := abs_add_le _ _
    _ = a*|D/(σ*η)-R|+|a-1| *|R| := by rw [abs_mul,abs_mul,abs_of_nonneg ha0]
    _ ≤ (δ/σ+C*η)+((p+1 : ℕ)*η)*J := by
      apply add_le_add
      · exact (mul_le_of_le_one_left (abs_nonneg _) ha1).trans hquot
      · exact mul_le_mul hscale hR (abs_nonneg _) (by positivity)
    _ = _ := by dsimp [C,J]; ring

end TaoTrudgianYang2025

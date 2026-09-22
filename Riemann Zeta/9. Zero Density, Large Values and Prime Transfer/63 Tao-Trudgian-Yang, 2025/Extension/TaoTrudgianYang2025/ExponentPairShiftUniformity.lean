import TaoTrudgianYang2025.ExponentPairShiftModel

/-!
# One finite-order tolerance for every small A-process shift

The tolerance and maximum shift ratio are chosen before the original
phase. The conclusion is the actual ANTEDB closed-interval model
predicate with parameter sigma+1, not an interior approximation.
-/

noncomputable section

open Set Expdb
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

def aProcessShiftJetBudget (σ : ℝ) (P : ℕ) : ℝ :=
  1+∑ p ∈ Finset.range (P+1),
    (modelPhaseJetCoefficient (σ+1) (p+1)+
      (p+1 : ℕ)*modelPhaseJetCoefficient (σ+1) p)

theorem aProcessShiftJetBudget_ge_one (σ : ℝ) (P : ℕ) :
    1 ≤ aProcessShiftJetBudget σ P := by
  have hs : 0 ≤ ∑ p ∈ Finset.range (P+1),
      (modelPhaseJetCoefficient (σ+1) (p+1)+
        (p+1 : ℕ)*modelPhaseJetCoefficient (σ+1) p) := by
    apply Finset.sum_nonneg
    intro p _
    exact add_nonneg (modelPhaseJetCoefficient_nonneg _ _)
      (mul_nonneg (Nat.cast_nonneg _) (modelPhaseJetCoefficient_nonneg _ _))
  dsimp [aProcessShiftJetBudget]
  linarith

theorem aProcessShiftJetCoefficient_le_budget (σ : ℝ) {P p : ℕ} (hp : p ≤ P) :
    modelPhaseJetCoefficient (σ+1) (p+1)+
      (p+1 : ℕ)*modelPhaseJetCoefficient (σ+1) p ≤ aProcessShiftJetBudget σ P := by
  have hs := Finset.single_le_sum
    (s := Finset.range (P+1))
    (f := fun j => modelPhaseJetCoefficient (σ+1) (j+1)+
      (j+1 : ℕ)*modelPhaseJetCoefficient (σ+1) j)
    (fun j _ => add_nonneg (modelPhaseJetCoefficient_nonneg _ _)
      (mul_nonneg (Nat.cast_nonneg _) (modelPhaseJetCoefficient_nonneg _ _)))
    (Finset.mem_range.mpr (by omega : p < P+1))
  exact hs.trans (by dsimp [aProcessShiftJetBudget]; linarith)

theorem aProcessShiftPhase_uniform_model {σ : ℝ}
    (hσ : 0 < σ) (P : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∀ (F : ℝ → ℝ) (η : ℝ),
        IsApproximateModelPhaseFunction F σ (P+1) δ →
        0 < η → η ≤ η₀ →
        IsApproximateModelPhaseFunction (aProcessShiftPhase F σ η) (σ+1) P ε := by
  let B := aProcessShiftJetBudget σ P
  have hB : 0 < B := zero_lt_one.trans_le (aProcessShiftJetBudget_ge_one σ P)
  let δ := σ*ε/2
  let η₀ := min (1/2 : ℝ) (ε/(2*B))
  have hd : 0 < δ := by dsimp [δ]; positivity
  have he : 0 < η₀ := by dsimp [η₀]; exact lt_min (by norm_num) (by positivity)
  have hehalf : η₀ ≤ (1/2 : ℝ) := min_le_left _ _
  refine ⟨δ,η₀,hd,he,hehalf,?_⟩
  intro F η hF hη hη₀
  have hη₁ : η < 1 := by linarith
  apply approximateModelPhase_of_interior_bounds
    (aProcessShiftPhase_contDiffOn hF.1 hη.le hη₁.le σ)
  intro u hu p hp
  have hb := aProcessShiftPhase_jet_error hσ hη hη₁ hF hu p (by omega)
  have hcap : η ≤ ε/(2*B) := hη₀.trans (min_le_right _ _)
  have hprod : B*η ≤ ε/2 := by
    have hi := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hB)).mp hcap
    nlinarith
  have hδeq : δ/σ = ε/2 := by dsimp [δ]; field_simp
  have hcoef := mul_le_mul_of_nonneg_right
    (aProcessShiftJetCoefficient_le_budget σ hp) hη.le
  rw [hδeq] at hb
  exact hb.trans (by dsimp [B] at hprod; linarith)

end TaoTrudgianYang2025

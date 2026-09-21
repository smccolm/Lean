import TaoTrudgianYang2025.AtkinsonPhysicalTerm

/-!
# Physical cutoff optimization of the closed packet budget

The actual ceiling, dyadic logarithm, harmonic loss and arithmetic
epsilon are all linked to H and G. The resulting constant is uniform
in the localization interval and the number of heights.
-/

noncomputable section

open Filter

namespace TaoTrudgianYang2025

theorem atkinsonPhysical_gap_budget_log_le {H G η : ℝ} {N : ℕ} (L : ℝ) (R : ℕ)
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hη : 0 ≤ η) (hN0 : 0 < N)
    (hlog : 1 ≤ Real.log (2*H)) (hN : (N:ℝ) ≤ H)
    (hcut : (N:ℝ) ≤ 74*H*(Real.log (2*H))^2/G^2) :
    G^2*H^(-(1/2:ℝ))*atkinsonPowerGapBudget η H G L N R ≤
      (148000*(1/Real.log 2+1)^2)*H^η*(Real.log (2*H))^5*
        ((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)) := by
  have hH0 : 0 < H := by linarith
  have hG0 : 0 < G := by linarith
  have hlog0 : 0 < Real.log (2*H) := by linarith
  have hterm := atkinsonPhysical_gap_term_zero_le L R hH hG hlog hN hcut
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg N) hN hη
  have hJ := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.clog 2 N) : (0:ℝ) ≤ _)
    (atkinson_clog_le_height_log hH hlog hN) 2
  have ht : G^2*H^(-(1/2:ℝ))*atkinsonPowerGapTerm η H G L N R ≤
      H^η*(148000*(Real.log (2*H))^3*
        ((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L))) := by
    rw [atkinsonPowerGapTerm_epsilon_factor hN0]
    calc
      _ = (N:ℝ)^η*(G^2*H^(-(1/2:ℝ))*atkinsonPowerGapTerm 0 H G L N R) := by ring
      _ ≤ (N:ℝ)^η*(148000*(Real.log (2*H))^3*
          ((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L))) :=
        mul_le_mul_of_nonneg_left hterm (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity)
  unfold atkinsonPowerGapBudget
  calc
    _ = (Nat.clog 2 N:ℝ)^2*
      (G^2*H^(-(1/2:ℝ))*atkinsonPowerGapTerm η H G L N R) := by ring
    _ ≤ (Nat.clog 2 N:ℝ)^2*
      (H^η*(148000*(Real.log (2*H))^3*
        ((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)))) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg _)
    _ ≤ ((1/Real.log 2+1)*Real.log (2*H))^2*
      (H^η*(148000*(Real.log (2*H))^3*
        ((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)))) :=
      mul_le_mul_of_nonneg_right hJ (by positivity)
    _ = _ := by ring

theorem exists_atkinsonPhysicalGapBudget_le_twoTerm {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G L : ℝ, ∀ R : ℕ, H₀ ≤ H → H^δ ≤ G → G ≤ Real.sqrt (2*H) →
        G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget (ν/2) H G L
            (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) R ≤
          C*H^ν*((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)) := by
  obtain ⟨A,hA,hgeometry⟩ := exists_atkinsonPhysicalCutoff_prefix_geometry hδ
  obtain ⟨B,hB⟩ := eventually_atTop.mp
    (eventually_atkinson_height_log_pow_le_rpow 5 (show 0 < ν/2 by linarith))
  obtain ⟨D,hD⟩ := eventually_atTop.mp (Real.tendsto_log_atTop.eventually_ge_atTop 1)
  let C : ℝ := 148000*(1/Real.log 2+1)^2
  have hC : 0 < C := by
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [C]
    positivity
  refine ⟨C,hC,max A (max B D),(hA.trans (le_max_left _ _)),?_⟩
  intro H G L R hH hwidth hupper
  have hAH : A ≤ H := (le_max_left _ _).trans hH
  have hBH : B ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hDH : D ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hH1 : 1 ≤ H := by linarith [hA.trans hAH]
  have hH0 : 0 < H := by linarith
  have hG1 : 1 ≤ G := (Real.one_le_rpow hH1 hδ.le).trans hwidth
  have hG0 : 0 < G := by linarith
  have hl : 1 ≤ Real.log (2*H) :=
    (hD H hDH).trans (Real.log_le_log hH0 (by linarith))
  have hn : (atkinsonSourceCutoff (2*H) G (Real.log (2*H)):ℝ) ≤ H := by
    have hg := hgeometry H G hAH hwidth
    have hn0 := Nat.cast_nonneg (α := ℝ) (atkinsonSourceCutoff (2*H) G (Real.log (2*H)))
    linarith
  have hn0 := atkinsonSourceCutoff_pos (by positivity : 0 < 2*H) hG0
    (by linarith : 0 < Real.log (2*H))
  have hp := atkinsonPhysical_gap_budget_log_le L R hH1 hG1
    (show 0 ≤ ν/2 by linarith) hn0 hl hn
    (atkinsonPhysicalCutoff_le_natural hH1 hG0 hupper hl)
  have hh : H^(ν/2)*H^(ν/2) = H^ν := by
    rw [← Real.rpow_add hH0]; congr 1; ring
  apply hp.trans
  change C*H^(ν/2)*(Real.log (2*H))^5*_ ≤ _
  calc
    _ ≤ C*H^(ν/2)*H^(ν/2)*
        ((R:ℝ)*H/G+(R:ℝ)^2*Real.sqrt (G*L)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (hB H hBH) (by positivity)
    _ = _ := by rw [mul_assoc C,hh]

end TaoTrudgianYang2025

import TaoTrudgianYang2025.AtkinsonPrefixGapBound

/-!
# Analytic prefix geometry derived from the actual physical cutoff

Every enlarged full phase block has its two extra mean-value endpoints
below every physical height. The proof uses the source ceiling at 2H,
with the width lower bound derived at H, not a freely chosen index scale.
-/

noncomputable section

open Filter

namespace TaoTrudgianYang2025

theorem atkinson_doubled_height_half_power {H δ : ℝ} (hH : 2 ≤ H) (hδ : 0 < δ) :
    (2*H)^(δ/2) ≤ H^δ := by
  have hH0 : 0 < H := by linarith
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hH0.le]
  calc
    (2:ℝ)^(δ/2)*H^(δ/2) ≤ H^(δ/2)*H^(δ/2) :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by norm_num) hH (by linarith)) (Real.rpow_nonneg hH0.le _)
    _ = H^δ := by rw [← Real.rpow_add hH0]; congr 1; ring

theorem exists_atkinsonPhysicalCutoff_prefix_geometry {δ : ℝ} (hδ : 0 < δ) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, H₀ ≤ H → H^δ ≤ G →
      2*(atkinsonSourceCutoff (2*H) G (Real.log (2*H)):ℝ)+2 ≤ H := by
  obtain ⟨A,hA⟩ := eventually_atTop.mp
    (eventually_atkinsonSourceCutoff_small (show 0 < δ/2 by linarith))
  refine ⟨max 40000 A,le_max_left _ _,?_⟩
  intro H G hH hG
  have hlarge : 40000 ≤ H := (le_max_left _ _).trans hH
  have hAH : A ≤ H := (le_max_right _ _).trans hH
  have hwidth := (atkinson_doubled_height_half_power (by linarith : 2 ≤ H) hδ).trans hG
  have hcut := hA (2*H) (by linarith) G hwidth
  linarith

theorem atkinson_dyadic_prefix_geometry {H G : ℝ} {j : ℕ}
    (hcut : 2*(atkinsonSourceCutoff (2*H) G (Real.log (2*H)):ℝ)+2 ≤ H)
    (hj : j < Nat.clog 2 (atkinsonSourceCutoff (2*H) G (Real.log (2*H)))) :
    (((2^j)+(2^j)+2:ℕ):ℝ) ≤ H := by
  have hjN := truncatedDyadic_start_lt hj
  have hcast : (((2^j):ℕ):ℝ) ≤
      (atkinsonSourceCutoff (2*H) G (Real.log (2*H)):ℝ) := by exact_mod_cast hjN.le
  push_cast at hcast ⊢
  linarith

theorem exists_atkinsonPhysicalPrefixGramMax_le_gap {δ : ℝ} (hδ : 0 < δ) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, H₀ ≤ H → H^δ ≤ G →
      ∀ j : ℕ, j < Nat.clog 2 (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) →
      ∀ t u : ℝ, H ≤ t → t ≤ 2*H → H ≤ u → u ≤ 2*H →
        atkinsonPrefixGramMax (2^j) (2^j) t u ≤ atkinsonPrefixGapMajorant (2^j) (2^j) t u := by
  obtain ⟨A,hA,hcut⟩ := exists_atkinsonPhysicalCutoff_prefix_geometry hδ
  refine ⟨A,hA,?_⟩
  intro H G hH hG j hj t u ht htU hu huU
  have hH0 : 0 < H := by linarith [hA.trans hH]
  have hend := atkinson_dyadic_prefix_geometry (hcut H G hH hG) hj
  exact atkinsonPrefixGramMax_le_gap (lt_min (hH0.trans_le ht) (hH0.trans_le hu))
    (pow_pos (by norm_num) _) (le_min (hend.trans ht) (hend.trans hu))
    (max_le (by linarith [le_min ht hu]) (by linarith [le_min ht hu]))

end TaoTrudgianYang2025

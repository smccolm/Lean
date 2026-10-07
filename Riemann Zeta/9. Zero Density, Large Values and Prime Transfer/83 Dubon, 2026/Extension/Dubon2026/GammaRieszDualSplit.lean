import Dubon2026.GammaRieszDualDifference

/-! # The justified low/high split of the actual dual Riesz Gamma series -/

namespace Dubon2026

open Set

noncomputable section

/-- Absolute convergence and the actual kernel bounds give the genuine dual-series second-difference split. -/
theorem exists_gammaRieszDualSeries_split_bound {k A : ℝ} (hk : 2 ≤ k) (hA : 0 < A) :
    ∃ C₀ C₂ : ℝ, 0 < C₀ ∧ 0 < C₂ ∧ ∀ (a : ℕ → ℝ) (B : ℝ),
      (∀ n, 0 ≤ a n) → 0 ≤ B → (∀ N : ℕ, (∑ n ∈ Finset.Icc 0 N, a n) ≤ B * N) →
      ∀ (x h : ℝ) (N : ℕ), 0 < x → 0 ≤ h → h ≤ x → 1 ≤ N →
        ‖gammaRieszDualSeries a k A (x + 2 * h) - 2 * gammaRieszDualSeries a k A (x + h) +
          gammaRieszDualSeries a k A x‖ ≤
          C₀ * h ^ 2 * x ^ (3 / 8 : ℝ) *
            (∑ n ∈ Finset.Icc 1 N, a n * (n : ℝ) ^ (-(5 / 8 : ℝ))) +
          C₂ * x ^ (15 / 8 : ℝ) *
            (∑' n : ℕ, if N < n then a n * (n : ℝ) ^ (-(9 / 8 : ℝ)) else 0) := by
  obtain ⟨C₀, C₂, hC₀, hC₂, hterm⟩ := exists_gammaRieszDualDifference_term_bounds hk hA
  refine ⟨C₀, C₂, hC₀, hC₂, ?_⟩
  intro a B ha hB hb x h N hx hh hhx hN
  rw [gammaRieszDualSeries_difference hk hA ha hB hb hx hh]
  have hlo : HasSum (fun n : ℕ => if n ∈ Finset.Icc 1 N then a n * (n : ℝ) ^ (-(5 / 8 : ℝ)) else 0)
      (∑ n ∈ Finset.Icc 1 N, a n * (n : ℝ) ^ (-(5 / 8 : ℝ))) := by
    convert (hasSum_subtype_iff_indicator).mp ((Finset.Icc 1 N).hasSum
      (fun n : ℕ => a n * (n : ℝ) ^ (-(5 / 8 : ℝ)))) using 1
    funext n
    simp only [Set.indicator_apply, Finset.mem_coe]
  have hhi := (linearPowerTail_summable_bound ha hB hb (by norm_num : (1 : ℝ) < 9 / 8) hN).1.hasSum
  have hmajor := (hlo.mul_left (C₀ * h ^ 2 * x ^ (3 / 8 : ℝ))).add
    (hhi.mul_left (C₂ * x ^ (15 / 8 : ℝ)))
  apply tsum_of_norm_bounded hmajor
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hn : 1 ≤ n := by omega
    have ht := hterm a x h n (ha n) hx hh hhx hn
    by_cases hnN : n ≤ N
    · have hmem : n ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hn, hnN⟩
      simpa only [if_pos hmem, if_neg (not_lt.mpr hnN), mul_zero, add_zero] using ht.1
    · have hmem : n ∉ Finset.Icc 1 N := by simp only [Finset.mem_Icc]; omega
      simpa only [if_neg hmem, if_pos (by omega : N < n), mul_zero, zero_add] using ht.2

end
end Dubon2026

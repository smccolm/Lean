import Dubon2026.VerticalZeroTranslation

/-! # Uniform multiplicity bounds in every translated unit-height window -/

namespace Dubon2026

open Set Complex Metric
open scoped BigOperators

theorem exists_uniform_translated_ball_zero_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    ∃ c : ℝ, ∀ r : ℝ, 0 < r → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (τ : ℝ) (S : Finset ℂ),
        (∀ s ∈ S, s ∈ closedBall ((c : ℂ) + Complex.I * τ) r ∧ dirichletSum a N s = 0) →
        (∑ s ∈ S, (zeroMultiplicity a N s : ℝ)) ≤ C := by
  classical
  obtain ⟨c, hc⟩ := exists_uniform_twist_ball_zero_bound hN ha
  refine ⟨c, ?_⟩
  intro r hr
  obtain ⟨C, hC, hb⟩ := hc r hr
  refine ⟨C, hC, ?_⟩
  intro τ S hS
  let S' := S.image (fun s => s - Complex.I * τ)
  have hS' : ∀ s ∈ S', s ∈ closedBall (c : ℂ) r ∧
      dirichletSum (twistedCoefficients a N (primeTorusFlow N τ)) N s = 0 := by
    intro s hs
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hd, hz⟩ := hS w hw
    constructor
    · rw [mem_closedBall, dist_eq_norm] at hd ⊢
      have he : w - Complex.I * τ - (c : ℂ) = w - ((c : ℂ) + Complex.I * τ) := by ring
      rwa [he]
    · rw [dirichletSum_twist_height, sub_add_cancel]
      exact hz
  have hsum := hb (primeTorusFlow N τ) S' hS'
  rw [Finset.sum_image] at hsum
  · simpa only [zeroMultiplicity_twist_height, sub_add_cancel] using hsum
  · intro s _ w _ he
    simpa only [sub_add_cancel] using congrArg (fun z : ℂ => z + Complex.I * τ) he

theorem exists_uniform_unit_strip_zero_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (S : Finset ℂ),
      (∀ s ∈ S, l ≤ s.re ∧ s.re ≤ u ∧ |s.im - τ| ≤ 1 ∧ dirichletSum a N s = 0) →
        (∑ s ∈ S, (zeroMultiplicity a N s : ℝ)) ≤ C := by
  obtain ⟨c, hc⟩ := exists_uniform_translated_ball_zero_bound hN ha
  let r := |l - c| + |u - c| + 1
  have hr : 0 < r := by dsimp only [r]; positivity
  obtain ⟨C, hC, hb⟩ := hc r hr
  refine ⟨C, hC, ?_⟩
  intro τ S hS
  apply hb τ S
  intro s hs
  obtain ⟨hl, hu, ht, hz⟩ := hS s hs
  refine ⟨?_, hz⟩
  rw [mem_closedBall, dist_eq_norm]
  have hre : |s.re - c| ≤ |l - c| + |u - c| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (l - c), abs_nonneg (u - c)]
    · linarith [le_abs_self (u - c), abs_nonneg (l - c)]
  have hn := (s - ((c : ℂ) + Complex.I * τ)).norm_le_abs_re_add_abs_im
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero,
    add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add] at hn
  exact hn.trans (add_le_add hre ht)

end Dubon2026

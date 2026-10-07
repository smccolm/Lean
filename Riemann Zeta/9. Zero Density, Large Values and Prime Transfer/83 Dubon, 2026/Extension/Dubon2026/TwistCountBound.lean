import Dubon2026.UniformTwistZeroBound
import Dubon2026.TorusDiscreteAverage

/-! # The actual bounded zero-count observable on the prime torus

Each value counts analytic multiplicity in a fixed open rectangle. The uniform
bound is derived from the proved compact-family Jensen bound, for all phases.
No phase measurability or almost-everywhere continuity is asserted here.
-/

namespace Dubon2026

open Set Complex Metric
open scoped BigOperators

noncomputable section

theorem continuous_twisted_dirichletSum (a : ℕ → ℂ) (N : ℕ) :
    Continuous (fun zs : PrimeTorus N × ℂ =>
      dirichletSum (twistedCoefficients a N zs.1) N zs.2) := by
  simp only [dirichletSum_eq_sum_exp, twistedCoefficients, bohrMonomial]
  fun_prop

/-- The actual multiplicity-weighted count for a torus twist in a fixed rectangle. -/
def twistZeroCount (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u H : ℝ) (z : PrimeTorus N) : ℕ :=
  verticalZeroCount (twistedCoefficients a N z) N hN
    (by rwa [twistedCoefficients_one]) l u H

theorem exists_uniform_twistZeroCount_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u H : ℝ) :
    ∃ K : ℕ, ∀ z, twistZeroCount a N hN ha l u H z ≤ K := by
  obtain ⟨c, hc⟩ := exists_uniform_twist_ball_zero_bound hN ha
  let r := |l - c| + |u - c| + |H| + 1
  have hr : 0 < r := by dsimp only [r]; positivity
  obtain ⟨C, _, hC⟩ := hc r hr
  refine ⟨⌈C⌉₊, ?_⟩
  intro z
  have ha' : twistedCoefficients a N z 1 ≠ 0 := by rwa [twistedCoefficients_one]
  let S := zerosInOpenRectangleFinset (twistedCoefficients a N z) N hN ha' l u H
  have hb : (∑ s ∈ S, (zeroMultiplicity (twistedCoefficients a N z) N s : ℝ)) ≤ C := by
    apply hC z S
    intro s hs
    obtain ⟨hl, hu, ht, hz⟩ := (mem_zerosInOpenRectangleFinset
      (twistedCoefficients a N z) N hN ha' l u H s).mp hs
    refine ⟨?_, hz⟩
    rw [mem_closedBall, dist_eq_norm]
    have hre : |s.re - c| ≤ |l - c| + |u - c| := by
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le (l - c), abs_nonneg (u - c)]
      · linarith [le_abs_self (u - c), abs_nonneg (l - c)]
    have him : |s.im| ≤ |H| := ht.le.trans (le_abs_self H)
    have hn := (s - (c : ℂ)).norm_le_abs_re_add_abs_im
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, sub_zero] at hn
    dsimp only [r]
    linarith
  have hn : (twistZeroCount a N hN ha l u H z : ℝ) ≤ C := by
    simpa only [twistZeroCount, verticalZeroCount, Nat.cast_sum, S] using hb
  exact_mod_cast hn.trans (Nat.le_ceil C)

theorem tendsto_twistZeroCount_average {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u H : ℝ)
    (hm : Measurable (twistZeroCount a N hN ha l u H))
    (hc : ∀ᵐ z ∂torusHaar N, ContinuousAt (twistZeroCount a N hN ha l u H) z) :
    Filter.Tendsto (fun T : ℝ => (2 * T)⁻¹ * ∫ t in -T..T,
      (twistZeroCount a N hN ha l u H (primeTorusFlow N t) : ℝ))
      Filter.atTop (nhds (∫ z, (twistZeroCount a N hN ha l u H z : ℝ) ∂torusHaar N)) := by
  obtain ⟨K, hK⟩ := exists_uniform_twistZeroCount_bound hN ha l u H
  exact tendsto_torusAverage_bounded_nat N hm hc K hK

end

end Dubon2026

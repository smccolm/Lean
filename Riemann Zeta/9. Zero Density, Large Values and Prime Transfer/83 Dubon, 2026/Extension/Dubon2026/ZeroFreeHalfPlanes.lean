import Dubon2026.LeadingBohrTerm

/-! # Uniform zero-free half-planes for the actual finite Dirichlet polynomial -/

namespace Dubon2026

open Filter
open scoped Topology BigOperators

theorem eventually_ne_zero_of_constant_modulus_limit
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {ι : Type*} {l : Filter ι} {F : ι → C(X, ℂ)} {g : C(X, ℂ)} {c : ℝ}
    (hc : 0 < c) (hg : ∀ x, ‖g x‖ = c) (hF : Tendsto F l (𝓝 g)) :
    ∀ᶠ i in l, ∀ x, F i x ≠ 0 := by
  filter_upwards [(Metric.tendsto_nhds.mp hF) c hc] with i hi
  intro x hx
  have hp := ((F i - g).norm_coe_le_norm x).trans_lt
    (show ‖F i - g‖ < c by simpa only [dist_eq_norm] using hi)
  have he : ‖(F i - g) x‖ = c := by
    simp only [ContinuousMap.sub_apply, hx, zero_sub, norm_neg, hg]
  exact (ne_of_lt hp) he

theorem tendsto_bohrOnTorus_atTop (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (bohrOnTorus a N) atTop
      (𝓝 (a 1 • UnitAddTorus.mFourier (primeExponent N 1))) := by
  classical
  have he (σ : ℝ) : bohrOnTorus a N σ = ∑ n ∈ Finset.Icc 1 N,
      (a n * (n : ℂ) ^ (-(σ : ℂ))) • UnitAddTorus.mFourier (primeExponent N n) := by
    ext z
    simp only [bohrOnTorus_eq_fourier_sum, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
  have ht (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      Tendsto (fun σ : ℝ => (a n * (n : ℂ) ^ (-(σ : ℂ))) •
        UnitAddTorus.mFourier (primeExponent N n)) atTop
        (𝓝 (if n = 1 then a n • UnitAddTorus.mFourier (primeExponent N n) else 0)) := by
    by_cases h : n = 1
    · subst n
      simp only [Nat.cast_one, Complex.one_cpow, mul_one, ite_true]
      exact tendsto_const_nhds
    · have hn' : 1 < n := by have := (Finset.mem_Icc.mp hn).1; omega
      have hzero : (0 : ℂ) • UnitAddTorus.mFourier (primeExponent N n) =
          (0 : C(PrimeTorus N, ℂ)) := by
        ext z
        simp only [ContinuousMap.smul_apply, smul_eq_mul, zero_mul, ContinuousMap.zero_apply]
      simpa only [mul_zero, hzero, if_neg h] using
        ((tendsto_nat_cpow_neg_real hn').const_mul (a n)).smul_const
          (UnitAddTorus.mFourier (primeExponent N n))
  change Tendsto (fun σ => bohrOnTorus a N σ) _ _
  simpa only [he, Finset.sum_ite_eq', Finset.mem_Icc, le_refl, hN, and_self, if_pos] using
    tendsto_finsetSum (Finset.Icc 1 N) ht

theorem eventually_bohrOnTorus_ne_zero_atTop {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    ∀ᶠ σ : ℝ in atTop, ∀ z, bohrOnTorus a N σ z ≠ 0 := by
  apply eventually_ne_zero_of_constant_modulus_limit (norm_pos_iff.mpr ha) _
    (tendsto_bohrOnTorus_atTop a hN)
  intro z
  simp only [ContinuousMap.smul_apply, smul_eq_mul, norm_mul, norm_mFourier_apply, mul_one]

theorem eventually_bohrOnTorus_ne_zero_atBot {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    ∀ᶠ σ : ℝ in atBot, ∀ z, bohrOnTorus a N σ z ≠ 0 := by
  have h := eventually_ne_zero_of_constant_modulus_limit
    (norm_pos_iff.mpr (coefficient_lastIndex_ne_zero hN ha))
    (norm_terminal_bohr_term a N) (tendsto_scaledBohr_atBot hN ha)
  filter_upwards [h] with σ hσ
  intro z hz
  apply hσ z
  simp only [scaledBohr_eq_smul, ContinuousMap.smul_apply, hz, smul_zero]

theorem exists_zero_containing_vertical_strip {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    ∃ l u : ℝ, l < u ∧ ∀ s : ℂ, dirichletSum a N s = 0 → l < s.re ∧ s.re < u := by
  obtain ⟨L, hL⟩ := eventually_atBot.mp (eventually_bohrOnTorus_ne_zero_atBot hN ha)
  obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_bohrOnTorus_ne_zero_atTop hN ha)
  refine ⟨min L (R - 1), R, lt_of_le_of_lt (min_le_right _ _) (by linarith), ?_⟩
  intro s hs
  have hflow : bohrOnTorus a N s.re (primeTorusFlow N s.im) = 0 := by
    rw [bohrOnTorus_verticalFlow, mul_comm Complex.I]
    simpa only [Complex.re_add_im] using hs
  constructor
  · by_contra h
    exact hL s.re ((not_lt.mp h).trans (min_le_left _ _)) _ hflow
  · by_contra h
    exact hR s.re (not_lt.mp h) _ hflow

end Dubon2026

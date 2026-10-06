import Dubon2026.DirichletPolynomial
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Nontriviality and genuine analytic zero multiplicities

The fixed finite truncation tends to its first coefficient on the positive real
axis. A nonzero first coefficient therefore excludes the identically zero
entire function. The analytic identity principle then makes every local order
finite, so the natural-valued multiplicity retains the actual analytic order.
-/

namespace Dubon2026

open Filter
open scoped BigOperators Topology

noncomputable section

theorem tendsto_nat_cpow_neg_real {n : ℕ} (hn : 1 < n) :
    Tendsto (fun σ : ℝ => (n : ℂ) ^ (-(σ : ℂ))) atTop (𝓝 0) := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hr := (tendsto_rpow_atBot_of_base_gt_one (n : ℝ) hnR).comp
    tendsto_neg_atTop_atBot
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  simpa only [Function.comp_def, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_neg,
    Complex.ofReal_natCast, Complex.ofReal_zero] using hc

theorem tendsto_dirichletSum_real (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun σ : ℝ => dirichletSum a N σ) atTop (𝓝 (a 1)) := by
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      Tendsto (fun σ : ℝ => a n * (n : ℂ) ^ (-(σ : ℂ))) atTop
        (𝓝 (if n = 1 then a n else 0)) := by
    by_cases h : n = 1
    · subst n
      simp only [Nat.cast_one, Complex.one_cpow, mul_one, ite_true]
      exact tendsto_const_nhds
    · have hn' : 1 < n := by have := (Finset.mem_Icc.mp hn).1; omega
      simpa only [if_neg h, mul_zero] using
        (tendsto_const_nhds (x := a n)).mul (tendsto_nat_cpow_neg_real hn')
  simpa [dirichletSum, hN] using tendsto_finsetSum (Finset.Icc 1 N) hterm

theorem dirichletSum_ne_zero_function {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) : dirichletSum a N ≠ 0 := by
  intro h
  have hlim := tendsto_dirichletSum_real a hN
  have hz : Tendsto (fun σ : ℝ => dirichletSum a N σ) atTop (𝓝 (0 : ℂ)) := by
    simp only [h, Pi.zero_apply]
    exact tendsto_const_nhds
  exact ha (tendsto_nhds_unique hlim hz)

theorem analyticOrderAt_dirichletSum_ne_top {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (s : ℂ) :
    analyticOrderAt (dirichletSum a N) s ≠ ⊤ := by
  intro h
  have hz := (analyticOnNhd_dirichletSum a N).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ s) (analyticOrderAt_eq_top.mp h)
  exact dirichletSum_ne_zero_function hN ha (funext fun z => hz (Set.mem_univ z))

/-- The actual analytic vanishing order of the finite Dirichlet polynomial. -/
def zeroMultiplicity (a : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℕ :=
  analyticOrderNatAt (dirichletSum a N) s

theorem zeroMultiplicity_cast {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (s : ℂ) :
    (zeroMultiplicity a N s : ℕ∞) = analyticOrderAt (dirichletSum a N) s :=
  Nat.cast_analyticOrderNatAt (analyticOrderAt_dirichletSum_ne_top hN ha s)

theorem zeroMultiplicity_pos_iff {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (s : ℂ) :
    0 < zeroMultiplicity a N s ↔ dirichletSum a N s = 0 := by
  rw [Nat.pos_iff_ne_zero]
  constructor
  · exact apply_eq_zero_of_analyticOrderNatAt_ne_zero
  · intro hz hm
    have ho : analyticOrderAt (dirichletSum a N) s = 0 := by
      rw [← zeroMultiplicity_cast hN ha s, hm]
      rfl
    exact (analyticAt_dirichletSum a N s).analyticOrderAt_ne_zero.mpr hz ho

theorem zeroMultiplicity_local_factorization {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (s : ℂ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ g s ≠ 0 ∧
      ∀ᶠ z in 𝓝 s, dirichletSum a N z = (z - s) ^ zeroMultiplicity a N s * g z := by
  obtain ⟨g,hg,hgn,hfactor⟩ := (analyticAt_dirichletSum a N s).analyticOrderAt_ne_top.mp
    (analyticOrderAt_dirichletSum_ne_top hN ha s)
  exact ⟨g,hg,hgn,by simpa only [zeroMultiplicity, smul_eq_mul] using hfactor⟩

theorem dirichletSum_eventually_ne_zero_codiscrete {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) :
    ∀ᶠ s in codiscreteWithin (Set.univ : Set ℂ), dirichletSum a N s ≠ 0 := by
  rcases (analyticOnNhd_dirichletSum a N).eqOn_zero_or_eventually_ne_zero_of_preconnected
    isPreconnected_univ with h | h
  · exact (dirichletSum_ne_zero_function hN ha (funext fun z => h (Set.mem_univ z))).elim
  · exact h

theorem finite_dirichletZeros_in_compact {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {K : Set ℂ} (hK : IsCompact K) :
    {s ∈ K | dirichletSum a N s = 0}.Finite := by
  have hd := Filter.codiscreteWithin_mono (Set.subset_univ K)
    (dirichletSum_eventually_ne_zero_codiscrete hN ha)
  convert hK.finite_diff_of_mem_codiscreteWithin hd using 1
  ext s
  simp

/-- The source's open real-part interval and symmetric open height cutoff. -/
def zerosInOpenRectangle (a : ℕ → ℂ) (N : ℕ) (left right T : ℝ) : Set ℂ :=
  {s | left < s.re ∧ s.re < right ∧ |s.im| < T ∧ dirichletSum a N s = 0}

theorem finite_zerosInOpenRectangle {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (left right T : ℝ) :
    (zerosInOpenRectangle a N left right T).Finite := by
  apply (finite_dirichletZeros_in_compact hN ha
    (isCompact_closedBall (0 : ℂ) (|left| + |right| + |T|))).subset
  intro s hs
  rcases hs with ⟨hl, hr, hi, hz⟩
  refine ⟨?_, hz⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hre : |s.re| ≤ |left| + |right| := by
    apply abs_le.mpr
    constructor
    · have := neg_abs_le left; have := abs_nonneg right; linarith
    · have := le_abs_self right; have := abs_nonneg left; linarith
  have him : |s.im| ≤ |T| := hi.le.trans (le_abs_self T)
  exact s.norm_le_abs_re_add_abs_im.trans (add_le_add hre him)

/-- A finite set of the actual zeros; the proof of finiteness is derived above. -/
def zerosInOpenRectangleFinset (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (left right T : ℝ) : Finset ℂ :=
  (finite_zerosInOpenRectangle hN ha left right T).toFinset

theorem mem_zerosInOpenRectangleFinset (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (left right T : ℝ) (s : ℂ) :
    s ∈ zerosInOpenRectangleFinset a N hN ha left right T ↔
      left < s.re ∧ s.re < right ∧ |s.im| < T ∧ dirichletSum a N s = 0 := by
  simp only [zerosInOpenRectangleFinset, Set.Finite.mem_toFinset, zerosInOpenRectangle,
    Set.mem_setOf_eq]

/-- The literal finite-height count with analytic multiplicity; not yet a density limit. -/
def verticalZeroCount (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (left right T : ℝ) : ℕ :=
  ∑ s ∈ zerosInOpenRectangleFinset a N hN ha left right T, zeroMultiplicity a N s

theorem card_zeros_le_verticalZeroCount (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (left right T : ℝ) :
    (zerosInOpenRectangleFinset a N hN ha left right T).card ≤
      verticalZeroCount a N hN ha left right T := by
  classical
  change _ ≤ ∑ s ∈ zerosInOpenRectangleFinset a N hN ha left right T,
    zeroMultiplicity a N s
  calc
    _ = ∑ _s ∈ zerosInOpenRectangleFinset a N hN ha left right T, 1 := by simp
    _ ≤ _ := ?_
  apply Finset.sum_le_sum
  intro s hs
  exact (zeroMultiplicity_pos_iff hN ha s).mpr
    ((mem_zerosInOpenRectangleFinset a N hN ha left right T s).mp hs).2.2.2

end

end Dubon2026

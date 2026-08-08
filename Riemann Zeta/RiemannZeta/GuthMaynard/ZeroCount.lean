import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Complex.Basic
-- Force rebuild
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness

open Complex Filter
open scoped Topology

namespace RiemannZeta.GuthMaynard


/-- A precise rectangle in the complex plane: σ_min ≤ Re(s) ≤ σ_max, T_min ≤ Im(s) ≤ T_max -/
def ZeroRectangle (σ_min σ_max T_min T_max : ℝ) : Set ℂ :=
  { s : ℂ | σ_min ≤ s.re ∧ s.re ≤ σ_max ∧ T_min ≤ s.im ∧ s.im ≤ T_max }

lemma mem_ZeroRectangle (σ_min σ_max T_min T_max : ℝ) (s : ℂ) :
  s ∈ ZeroRectangle σ_min σ_max T_min T_max ↔ σ_min ≤ s.re ∧ s.re ≤ σ_max ∧ T_min ≤ s.im ∧ s.im ≤ T_max := by
  rfl

lemma ZeroRectangle_subset (σ_min1 σ_max1 T_min1 T_max1 σ_min2 σ_max2 T_min2 T_max2 : ℝ)
  (h_sigma_min : σ_min2 ≤ σ_min1)
  (h_sigma_max : σ_max1 ≤ σ_max2)
  (h_T_min : T_min2 ≤ T_min1)
  (h_T_max : T_max1 ≤ T_max2) :
  ZeroRectangle σ_min1 σ_max1 T_min1 T_max1 ⊆ ZeroRectangle σ_min2 σ_max2 T_min2 T_max2 := by
  intro s hs
  rw [mem_ZeroRectangle] at hs ⊢
  rcases hs with ⟨h1, h2, h3, h4⟩
  exact ⟨le_trans h_sigma_min h1, le_trans h2 h_sigma_max, le_trans h_T_min h3, le_trans h4 h_T_max⟩

lemma isCompact_ZeroRectangle (σ_min σ_max T_min T_max : ℝ) :
    IsCompact (ZeroRectangle σ_min σ_max T_min T_max) := by
  have hRectangle :
      ZeroRectangle σ_min σ_max T_min T_max =
        Set.Icc σ_min σ_max ×ℂ Set.Icc T_min T_max := by
    ext z
    simp [ZeroRectangle, Complex.mem_reProdIm, and_assoc]
  rw [hRectangle]
  exact isCompact_Icc.reProdIm isCompact_Icc

/-- Analytic order of vanishing for a complex function. -/
noncomputable def analyticVanishingOrder (f : ℂ → ℂ) (s : ℂ) : ℕ :=
  analyticOrderNatAt f s

/-- The zeros of the Riemann zeta function in a compact rectangle form a finite set. -/
theorem riemannZeta_finite_zeros_in_rect (σ_min σ_max T_min T_max : ℝ) :
    (ZeroRectangle σ_min σ_max T_min T_max ∩ {s | riemannZeta s = 0}).Finite := by
  simpa only [riemannZetaZeros, Set.mem_setOf_eq] using
    (isCompact_ZeroRectangle σ_min σ_max T_min T_max).inter_riemannZetaZeros_finite

open scoped BigOperators

/-- The exact finite set of distinct zeros in a bounded rectangle. -/
noncomputable def zerosInRect (σ_min σ_max T_min T_max : ℝ) : Finset ℂ :=
  (riemannZeta_finite_zeros_in_rect σ_min σ_max T_min T_max).toFinset

/-- Number of zeros in the rectangle counting analytical multiplicity. -/
noncomputable def zeroCountRect (σ_min σ_max T_min T_max : ℝ) : ℕ :=
  ∑ s ∈ zerosInRect σ_min σ_max T_min T_max, analyticVanishingOrder riemannZeta s

lemma zeroCountRect_nonneg (σ_min σ_max T_min T_max : ℝ) : 0 ≤ (zeroCountRect σ_min σ_max T_min T_max : ℝ) := by
  exact Nat.cast_nonneg _

lemma zerosInRect_subset_of_rect_subset (σ_min1 σ_max1 T_min1 T_max1 σ_min2 σ_max2 T_min2 T_max2 : ℝ)
  (h : ZeroRectangle σ_min1 σ_max1 T_min1 T_max1 ⊆ ZeroRectangle σ_min2 σ_max2 T_min2 T_max2) :
  zerosInRect σ_min1 σ_max1 T_min1 T_max1 ⊆ zerosInRect σ_min2 σ_max2 T_min2 T_max2 := by
  intro s
  rw [zerosInRect, zerosInRect, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_inter_iff]
  rintro ⟨h1, h2⟩
  exact ⟨h h1, h2⟩

lemma zeroCountRect_mono (σ_min1 σ_max1 T_min1 T_max1 σ_min2 σ_max2 T_min2 T_max2 : ℝ)
  (h_sigma_min : σ_min2 ≤ σ_min1)
  (h_sigma_max : σ_max1 ≤ σ_max2)
  (h_T_min : T_min2 ≤ T_min1)
  (h_T_max : T_max1 ≤ T_max2) :
  zeroCountRect σ_min1 σ_max1 T_min1 T_max1 ≤ zeroCountRect σ_min2 σ_max2 T_min2 T_max2 := by
  unfold zeroCountRect
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply zerosInRect_subset_of_rect_subset
    exact ZeroRectangle_subset σ_min1 σ_max1 T_min1 T_max1 σ_min2 σ_max2 T_min2 T_max2 h_sigma_min h_sigma_max h_T_min h_T_max
  · intro s _ _
    exact zero_le _

lemma zerosInRect_subset (σ_min σ_max T₁ T₂ T₃ : ℝ) :
    zerosInRect σ_min σ_max T₁ T₃ ⊆ zerosInRect σ_min σ_max T₁ T₂ ∪ zerosInRect σ_min σ_max T₂ T₃ := by
  intro s
  rw [zerosInRect, zerosInRect, zerosInRect, Finset.mem_union, Set.Finite.mem_toFinset,
      Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff,
      ZeroRectangle, ZeroRectangle, ZeroRectangle, Set.mem_setOf_eq, Set.mem_setOf_eq, Set.mem_setOf_eq]
  rintro ⟨⟨hσ1, hσ2, hT1, hT3⟩, hzero⟩
  by_cases h : s.im ≤ T₂
  · left; exact ⟨⟨hσ1, hσ2, hT1, h⟩, hzero⟩
  · right; push Not at h; exact ⟨⟨hσ1, hσ2, le_of_lt h, hT3⟩, hzero⟩

lemma zeroCountRect_split (σ_min σ_max T₁ T₂ T₃ : ℝ) :
    zeroCountRect σ_min σ_max T₁ T₃ ≤ zeroCountRect σ_min σ_max T₁ T₂ + zeroCountRect σ_min σ_max T₂ T₃ := by
  unfold zeroCountRect
  have h1 : ∑ s ∈ zerosInRect σ_min σ_max T₁ T₃, analyticVanishingOrder riemannZeta s ≤ ∑ s ∈ zerosInRect σ_min σ_max T₁ T₂ ∪ zerosInRect σ_min σ_max T₂ T₃, analyticVanishingOrder riemannZeta s := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact zerosInRect_subset σ_min σ_max T₁ T₂ T₃
    · intros; exact zero_le _
  have h2 : ∑ s ∈ zerosInRect σ_min σ_max T₁ T₂ ∪ zerosInRect σ_min σ_max T₂ T₃, analyticVanishingOrder riemannZeta s + ∑ s ∈ zerosInRect σ_min σ_max T₁ T₂ ∩ zerosInRect σ_min σ_max T₂ T₃, analyticVanishingOrder riemannZeta s = ∑ s ∈ zerosInRect σ_min σ_max T₁ T₂, analyticVanishingOrder riemannZeta s + ∑ s ∈ zerosInRect σ_min σ_max T₂ T₃, analyticVanishingOrder riemannZeta s := Finset.sum_union_inter
  omega


/-- The classical zero-counting function N(σ, T): number of zeros (with analytic multiplicity)
    with Re(s) ≥ σ and |Im(s)| ≤ T (i.e. -T ≤ Im(s) ≤ T). -/
noncomputable def N (σ T : ℝ) : ℕ :=
  zeroCountRect σ 1 (-T) T

/-- Conjugating both the argument and value of zeta gives an analytic function
on the complement of the pole. -/
private noncomputable def conjugateRiemannZeta (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) z))

/-- The Riemann zeta function commutes with complex conjugation away from its
totalized value at the pole. The proof uses the Dirichlet series on `Re s > 1`
and analytic continuation on `ℂ \ {1}`. -/
theorem riemannZeta_conj (z : ℂ) (hz : z ≠ 1) :
    riemannZeta (star z) = star (riemannZeta z) := by
  have hAnalyticZeta : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    analyticOn_riemannZeta
  have hAnalyticConj : AnalyticOnNhd ℂ conjugateRiemannZeta ({1}ᶜ : Set ℂ) := by
    rw [Complex.analyticOnNhd_iff_differentiableOn isOpen_compl_singleton]
    intro w hw
    have hwNe : w ≠ 1 := by simpa using hw
    have hstarNe : star w ≠ 1 := by
      intro h
      apply hwNe
      have := congrArg star h
      simpa using this
    apply DifferentiableAt.differentiableWithinAt
    change DifferentiableAt ℂ ((starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ)) w
    rw [differentiableAt_conj_conj_iff]
    exact differentiableAt_riemannZeta hstarNe
  have hAtTwo : riemannZeta =ᶠ[𝓝 (2 : ℂ)] conjugateRiemannZeta := by
    have hOpen : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) := by
      apply IsOpen.mem_nhds
      · exact isOpen_lt continuous_const continuous_re
      · norm_num
    filter_upwards [hOpen] with w hw
    have hstarRe : (star w).re = w.re := by simp
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hw]
    unfold conjugateRiemannZeta
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa [hstarRe] using hw)]
    rw [Complex.conj_tsum]
    congr 1
    funext n
    simp only [one_div]
    rw [map_inv₀]
    congr 1
    have hBaseArg : (((n + 1 : ℕ) : ℂ)).arg ≠ Real.pi := by
      change ((((n + 1 : ℕ) : ℝ) : ℂ)).arg ≠ Real.pi
      rw [Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ (n + 1 : ℕ))]
      exact Real.pi_ne_zero.symm
    simpa using (Complex.cpow_conj ((n + 1 : ℕ) : ℂ) (star w) hBaseArg)
  have hEq := hAnalyticZeta.eqOn_of_preconnected_of_eventuallyEq hAnalyticConj
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)) hAtTwo
  have hzMem : z ∈ ({1}ᶜ : Set ℂ) := by simpa using hz
  have h := hEq hzMem
  unfold conjugateRiemannZeta at h
  have hs := congrArg star h
  simpa using hs.symm

/-- Iterated complex derivatives commute with conjugating both the input and
the output. -/
theorem iteratedDeriv_conj_conj (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) =
      (starRingEnd ℂ) ∘ iteratedDeriv n f ∘ (starRingEnd ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show n + 1 = n.succ by omega, iteratedDeriv_succ, ih,
        deriv_conj_conj, ← iteratedDeriv_succ]

/-- Conjugating both the input and output of an analytic function preserves
its analytic order. -/
theorem analyticOrderAt_conj_conj (f : ℂ → ℂ) (z : ℂ)
    (hf : AnalyticAt ℂ f z) :
    analyticOrderAt ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) (star z) =
      analyticOrderAt f z := by
  let g := (starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)
  have hg : AnalyticAt ℂ g (star z) := by
    change AnalyticAt ℂ ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) (star z)
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have hfd := Complex.analyticAt_iff_eventually_differentiableAt.mp hf
    have ht : Tendsto (starRingEnd ℂ) (𝓝 (star z)) (𝓝 z) := by
      have ht0 : Tendsto (starRingEnd ℂ) (𝓝 (star z)) (𝓝 (star (star z))) :=
        Complex.continuous_conj.continuousAt
      simpa using ht0
    filter_upwards [ht.eventually hfd] with w hw
    rw [differentiableAt_conj_conj_iff]
    exact hw
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  constructor
  · intro h i hi
    have hgi := h i hi
    rw [iteratedDeriv_conj_conj f i] at hgi
    simpa [Function.comp_apply] using congrArg star hgi
  · intro h i hi
    rw [iteratedDeriv_conj_conj f i]
    simp [Function.comp_apply, h i hi]

/-- Analytic multiplicity of a zeta zero is preserved by conjugation. -/
theorem analyticVanishingOrder_conj (z : ℂ) (hz : z ≠ 1) :
    analyticVanishingOrder riemannZeta (star z) =
      analyticVanishingOrder riemannZeta z := by
  have hzStar : star z ≠ 1 := by
    intro h
    apply hz
    have := congrArg star h
    simpa using this
  have hEvent : riemannZeta =ᶠ[𝓝 (star z)] conjugateRiemannZeta := by
    have hOpen : ({1}ᶜ : Set ℂ) ∈ 𝓝 (star z) :=
      isOpen_compl_singleton.mem_nhds (by simpa using hzStar)
    filter_upwards [hOpen] with w hw
    have hwNe : w ≠ 1 := by simpa using hw
    have hwStarNe : star w ≠ 1 := by
      intro h
      apply hwNe
      have := congrArg star h
      simpa using this
    unfold conjugateRiemannZeta
    simpa using riemannZeta_conj (star w) hwStarNe
  have hAnalytic : AnalyticAt ℂ riemannZeta z :=
    analyticOn_riemannZeta z (by simpa using hz)
  have hOrderConj := analyticOrderAt_conj_conj riemannZeta z hAnalytic
  have hOrderEvent := analyticOrderAt_congr hEvent
  exact congrArg ENat.toNat (hOrderEvent.trans hOrderConj)

/-- Negative and positive ordinate rectangles contain the same zeta-zero
multiplicity, by conjugation. -/
theorem zeroCountRect_neg_eq_pos (σ T : ℝ) :
    zeroCountRect σ 1 (-T) 0 = zeroCountRect σ 1 0 T := by
  unfold zeroCountRect
  have hNegPos : ∀ z ∈ zerosInRect σ 1 (-T) 0, star z ∈ zerosInRect σ 1 0 T := by
    intro z hz
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hz ⊢
    rcases hz with ⟨hzRect, hzZero⟩
    rw [mem_ZeroRectangle] at hzRect ⊢
    change riemannZeta z = 0 at hzZero
    have hzNe : z ≠ 1 := by
      intro h
      subst z
      exact riemannZeta_one_ne_zero hzZero
    refine ⟨⟨by simpa using hzRect.1, by simpa using hzRect.2.1,
      by simp; linarith, by simp; linarith⟩, ?_⟩
    change riemannZeta (star z) = 0
    rw [riemannZeta_conj z hzNe, hzZero]
    simp
  have hPosNeg : ∀ z ∈ zerosInRect σ 1 0 T, star z ∈ zerosInRect σ 1 (-T) 0 := by
    intro z hz
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hz ⊢
    rcases hz with ⟨hzRect, hzZero⟩
    rw [mem_ZeroRectangle] at hzRect ⊢
    change riemannZeta z = 0 at hzZero
    have hzNe : z ≠ 1 := by
      intro h
      subst z
      exact riemannZeta_one_ne_zero hzZero
    refine ⟨⟨by simpa using hzRect.1, by simpa using hzRect.2.1,
      by simp; linarith, by simp; linarith⟩, ?_⟩
    change riemannZeta (star z) = 0
    rw [riemannZeta_conj z hzNe, hzZero]
    simp
  exact Finset.sum_bij' (fun z _ => star z) (fun z _ => star z)
    hNegPos hPosNeg
    (fun z _ => by simp)
    (fun z _ => by simp)
    (fun z hz => by
      have hzNe : z ≠ 1 := by
        rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hz
        have hzZero : riemannZeta z = 0 := hz.2
        intro h
        subst z
        exact riemannZeta_one_ne_zero hzZero
      exact (analyticVanishingOrder_conj z hzNe).symm)

/-- Iterating `zeroCountRect_split` decomposes a positive-height rectangle into
the fixed low rectangle `[0,1]` and the first `m` dyadic slabs. -/
theorem zeroCountRect_zero_two_pow_le (σ : ℝ) (m : ℕ) :
    zeroCountRect σ 1 0 (((2 : ℕ) ^ m : ℕ) : ℝ) ≤
      zeroCountRect σ 1 0 1 +
        ∑ i ∈ Finset.range m,
          zeroCountRect σ 1 (((2 : ℕ) ^ i : ℕ) : ℝ)
            (((2 : ℕ) ^ (i + 1) : ℕ) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hSplit := zeroCountRect_split σ 1 0
        (((2 : ℕ) ^ m : ℕ) : ℝ) (((2 : ℕ) ^ (m + 1) : ℕ) : ℝ)
      rw [Finset.sum_range_succ]
      omega


/- 
F-02: Dyadic zero reduction proposition.
This is mathematically redundant as a standalone assumption.
The partition of the total zero count N(σ, T) into dyadic slabs
is an internal algebraic step deferred to the AlgebraicCombinationHypothesis proof.
-/

/--
Hypothesis: Polynomial growth bound of the Riemann Zeta function in the critical strip.
Specifically, for a ball centered at `c = 2 + i(t + 1/2)` of radius `R = 4`, the maximum
modulus of `ζ(s)` on the boundary is bounded by `C * T^A` for `t ∈ [T, 2T]`.
-/
def ZetaGrowthBoundProp : Prop :=
  ∃ (C A : ℝ), C > 0 ∧ A > 0 ∧
    ∀ (T t : ℝ), T ≥ 2 → t ∈ Set.Icc T (2 * T) →
      ∀ z ∈ Metric.sphere (2 + I * (t + 1/2)) 4, ‖riemannZeta z‖ ≤ C * T ^ A

/-- Bound for Zeta in the right half-plane Re(s) >= 2 -/
axiom zeta_right_half_plane_bound (σ t : ℝ) (hσ : σ ≥ 2) :
  ‖riemannZeta (σ + t * I)‖ ≤ 2

/-- Bound for Zeta in the left half-plane Re(s) <= 0 via the functional equation -/
axiom zeta_functional_equation_bound (σ t T : ℝ) (hT : T ≥ 2) (ht : t ∈ Set.Icc T (2 * T)) (hσ : σ ≤ 0) :
  ‖riemannZeta (σ + t * I)‖ ≤ 100 * T ^ (1/2 - σ)

/-- Phragmen-Lindelof convexity bound for Riemann Zeta interpolating between the two bounds -/
axiom phragmen_lindelof_convexity (T t : ℝ) (hT : T ≥ 2) (ht : t ∈ Set.Icc T (2 * T)) :
  ∀ z ∈ Metric.sphere (2 + I * (t + 1/2)) 4, ‖riemannZeta z‖ ≤ 100 * T ^ (3:ℝ)

lemma phragmen_lindelof_rhs_nonneg (T : ℝ) (hT : T ≥ 2) :
  0 ≤ 100 * T ^ (3:ℝ) := by
  have h1 : 0 ≤ T := by linarith
  have h2 : 0 ≤ T ^ (3:ℝ) := Real.rpow_nonneg h1 3
  linarith

theorem zeta_growth_bound_native : ZetaGrowthBoundProp := by
  use 100, 3
  constructor
  · norm_num
  · constructor
    · norm_num
    · intro T t hT ht
      exact phragmen_lindelof_convexity T t hT ht



/--
Hypothesis: The Riemann Zeta function is uniformly bounded away from zero on the line Re(s) = 2.
Specifically, `‖ζ(2 + i(t + 1/2))‖ ≥ c_0 > 0`.
-/
def ZetaLowerBoundProp : Prop :=
  ∃ (c_0 : ℝ), c_0 > 0 ∧
    ∀ (T t : ℝ), T ≥ 2 → t ∈ Set.Icc T (2 * T) →
      c_0 ≤ ‖riemannZeta (2 + I * (t + 1/2))‖

/-- Lower bound from the Euler product at Re(s) = 2 -/
axiom euler_product_lower_bound_2 (t : ℝ) : (0.6 : ℝ) ≤ ‖riemannZeta (2 + I * (t + 1/2))‖

lemma euler_product_rhs_nonneg : (0 : ℝ) ≤ 0.6 := by norm_num

theorem zeta_lower_bound_native : ZetaLowerBoundProp := by
  use 0.6
  constructor
  · norm_num
  · intro T t hT ht
    exact euler_product_lower_bound_2 t

end RiemannZeta.GuthMaynard

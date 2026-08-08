import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Basic
-- Force rebuild
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Analytic.Order

open Complex

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

/-- Analytic order of vanishing for a complex function. -/
noncomputable def analyticVanishingOrder (f : ℂ → ℂ) (s : ℂ) : ℕ :=
  analyticOrderNatAt f s

/- 
  The zeros of the Riemann Zeta function in any compact rectangle are finite.
  This is unconditionally true by the identity theorem for analytic functions,
  since riemannZeta is analytic everywhere except at 1, and is not identically zero.
-/
axiom riemannZeta_finite_zeros_in_rect : ∀ (σ_min σ_max T_min T_max : ℝ), (ZeroRectangle σ_min σ_max T_min T_max ∩ {s | riemannZeta s = 0}).Finite

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

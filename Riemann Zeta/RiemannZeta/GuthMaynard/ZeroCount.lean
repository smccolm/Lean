import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Data.Real.Basic

open Complex

namespace RiemannZeta.GuthMaynard

/-- A precise rectangle in the complex plane: σ_min ≤ Re(s) ≤ σ_max, T_min ≤ Im(s) ≤ T_max -/
def ZeroRectangle (σ_min σ_max T_min T_max : ℝ) : Set ℂ :=
  { s : ℂ | σ_min ≤ s.re ∧ s.re ≤ σ_max ∧ T_min ≤ s.im ∧ s.im ≤ T_max }

/-- An interface for counting zeros of the Riemann Zeta function with analytic multiplicity.
    This serves as the canonical description of the zeros used throughout the proof. -/
structure ZetaZeroCountModel where
  /-- Analytic multiplicity of a zero. -/
  multiplicity : ℂ → ℕ
  /-- A point has positive multiplicity if and only if it is a zero of riemannZeta. -/
  zero_iff : ∀ s : ℂ, multiplicity s > 0 ↔ riemannZeta s = 0
  /-- The zeros are isolated, so they are finite in any compact rectangle. -/
  finite_zeros : ∀ σ_min σ_max T_min T_max,
    (ZeroRectangle σ_min σ_max T_min T_max ∩ {s | riemannZeta s = 0}).Finite

open scoped BigOperators

/-- The exact finite set of distinct zeros in a bounded rectangle.
    This connects the analytical zeros to finite collections used in combinatorial extraction arguments. -/
noncomputable def zerosInRect (model : ZetaZeroCountModel) (σ_min σ_max T_min T_max : ℝ) : Finset ℂ :=
  (model.finite_zeros σ_min σ_max T_min T_max).toFinset

/-- Cardinality of the set of distinct zeros in the rectangle. -/
noncomputable def distinctZeroCountRect (model : ZetaZeroCountModel) (σ_min σ_max T_min T_max : ℝ) : ℕ :=
  (zerosInRect model σ_min σ_max T_min T_max).card

/-- Number of zeros in the rectangle counting analytical multiplicity. -/
noncomputable def zeroCountRect (model : ZetaZeroCountModel) (σ_min σ_max T_min T_max : ℝ) : ℕ :=
  ∑ s ∈ zerosInRect model σ_min σ_max T_min T_max, model.multiplicity s

lemma zerosInRect_subset (model : ZetaZeroCountModel) (σ_min σ_max T₁ T₂ T₃ : ℝ) :
    zerosInRect model σ_min σ_max T₁ T₃ ⊆ zerosInRect model σ_min σ_max T₁ T₂ ∪ zerosInRect model σ_min σ_max T₂ T₃ := by
  intro s
  rw [zerosInRect, zerosInRect, zerosInRect, Finset.mem_union, Set.Finite.mem_toFinset,
      Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff,
      ZeroRectangle, ZeroRectangle, ZeroRectangle, Set.mem_setOf_eq, Set.mem_setOf_eq, Set.mem_setOf_eq]
  rintro ⟨⟨hσ1, hσ2, hT1, hT3⟩, hzero⟩
  by_cases h : s.im ≤ T₂
  · left
    exact ⟨⟨hσ1, hσ2, hT1, h⟩, hzero⟩
  · right
    push Not at h
    exact ⟨⟨hσ1, hσ2, le_of_lt h, hT3⟩, hzero⟩

lemma zeroCountRect_split (model : ZetaZeroCountModel) (σ_min σ_max T₁ T₂ T₃ : ℝ) :
    zeroCountRect model σ_min σ_max T₁ T₃ ≤ zeroCountRect model σ_min σ_max T₁ T₂ + zeroCountRect model σ_min σ_max T₂ T₃ := by
  unfold zeroCountRect
  have h1 : ∑ s ∈ zerosInRect model σ_min σ_max T₁ T₃, model.multiplicity s ≤ ∑ s ∈ zerosInRect model σ_min σ_max T₁ T₂ ∪ zerosInRect model σ_min σ_max T₂ T₃, model.multiplicity s := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact zerosInRect_subset model σ_min σ_max T₁ T₂ T₃
    · intros; exact zero_le _
  have h2 : ∑ s ∈ zerosInRect model σ_min σ_max T₁ T₂ ∪ zerosInRect model σ_min σ_max T₂ T₃, model.multiplicity s + ∑ s ∈ zerosInRect model σ_min σ_max T₁ T₂ ∩ zerosInRect model σ_min σ_max T₂ T₃, model.multiplicity s = ∑ s ∈ zerosInRect model σ_min σ_max T₁ T₂, model.multiplicity s + ∑ s ∈ zerosInRect model σ_min σ_max T₂ T₃, model.multiplicity s := Finset.sum_union_inter
  omega

/-- The classical zero-counting function N(σ, T): number of zeros (with multiplicity)
    with Re(s) ≥ σ and -T ≤ Im(s) ≤ T. -/
noncomputable def N (model : ZetaZeroCountModel) (σ T : ℝ) : ℕ :=
  zeroCountRect model σ 1 (-T) T

/-- The dyadic zero reduction proposition.
    This states that the global zero count N(σ, T) can be bounded by a finite sum
    of counts in dyadic slabs, plus a bounded low-height remainder. 
    (Considering just positive heights for the dyadic split, symmetry handles negative). -/
def DyadicReductionProp (model : ZetaZeroCountModel) (σ T : ℝ) : Prop :=
  ∃ k : ℕ, zeroCountRect model σ 1 0 T ≤ zeroCountRect model σ 1 0 (T / 2^(k:ℝ)) + ∑ j ∈ Finset.range k,
    zeroCountRect model σ 1 (T / 2^((j:ℝ)+1)) (T / 2^(j:ℝ))

theorem dyadic_reduction_all (model : ZetaZeroCountModel) (σ T : ℝ) (k : ℕ) : 
  zeroCountRect model σ 1 0 T ≤ zeroCountRect model σ 1 0 (T / 2^(k:ℝ)) + ∑ j ∈ Finset.range k,
    zeroCountRect model σ 1 (T / 2^((j:ℝ)+1)) (T / 2^(j:ℝ)) := by
  induction k with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, Nat.cast_zero]
    have h_pow : (2 : ℝ) ^ (0 : ℝ) = 1 := by norm_num
    rw [h_pow, div_one]
  | succ k ih =>
    have hk : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hk]
    have h_split := zeroCountRect_split model σ 1 0 (T / 2^((k:ℝ)+1)) (T / 2^(k:ℝ))
    have h_sum : ∑ j ∈ Finset.range (k + 1), zeroCountRect model σ 1 (T / 2^((j:ℝ)+1)) (T / 2^(j:ℝ)) =
      (∑ j ∈ Finset.range k, zeroCountRect model σ 1 (T / 2^((j:ℝ)+1)) (T / 2^(j:ℝ))) + zeroCountRect model σ 1 (T / 2^((k:ℝ)+1)) (T / 2^(k:ℝ)) := by
      exact Finset.sum_range_succ _ k
    rw [h_sum]
    omega

theorem dyadic_reduction (model : ZetaZeroCountModel) (σ T : ℝ) : DyadicReductionProp model σ T :=
  ⟨0, dyadic_reduction_all model σ T 0⟩

end RiemannZeta.GuthMaynard

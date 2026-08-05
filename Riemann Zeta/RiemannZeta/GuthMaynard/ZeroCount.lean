import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Data.Real.Basic
-- Would import complex analysis tools for `orderOf` if available, 
-- but we specify the property via axioms if missing.

open Complex

namespace RiemannZeta.GuthMaynard

/-- A precise rectangle in the complex plane: σ_min ≤ Re(s) ≤ σ_max, T_min ≤ Im(s) ≤ T_max -/
def ZeroRectangle (σ_min σ_max T_min T_max : ℝ) : Set ℂ :=
  { s : ℂ | σ_min ≤ s.re ∧ s.re ≤ σ_max ∧ T_min ≤ s.im ∧ s.im ≤ T_max }

/-- An interface for counting zeros of the Riemann Zeta function with analytic multiplicity.
    This serves as the canonical description of the zeros used throughout the proof. -/
structure ZetaZeroCountModel where
  /-- Analytic multiplicity of a zero. This must correspond to the analytic vanishing order. -/
  multiplicity : ℂ → ℕ
  /-- A point has positive multiplicity if and only if it is a zero of riemannZeta. -/
  zero_iff : ∀ s : ℂ, multiplicity s > 0 ↔ riemannZeta s = 0
  /-- The zeros are isolated, so they are finite in any compact rectangle. -/
  finite_zeros : ∀ σ_min σ_max T_min T_max,
    (ZeroRectangle σ_min σ_max T_min T_max ∩ {s | riemannZeta s = 0}).Finite
  /-- The multiplicity function respects conjugate symmetry of the zeta function. -/
  conjugate_symmetry : ∀ s : ℂ, multiplicity s = multiplicity (conj s)

open scoped BigOperators

/-- The exact finite set of distinct zeros in a bounded rectangle. -/
noncomputable def zerosInRect (model : ZetaZeroCountModel) (σ_min σ_max T_min T_max : ℝ) : Finset ℂ :=
  (model.finite_zeros σ_min σ_max T_min T_max).toFinset

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
  · left; exact ⟨⟨hσ1, hσ2, hT1, h⟩, hzero⟩
  · right; push Not at h; exact ⟨⟨hσ1, hσ2, le_of_lt h, hT3⟩, hzero⟩

lemma zeroCountRect_split (model : ZetaZeroCountModel) (σ_min σ_max T₁ T₂ T₃ : ℝ) :
    zeroCountRect model σ_min σ_max T₁ T₃ ≤ zeroCountRect model σ_min σ_max T₁ T₂ + zeroCountRect model σ_min σ_max T₂ T₃ := by
  unfold zeroCountRect
  have h1 : ∑ s ∈ zerosInRect model σ_min σ_max T₁ T₃, model.multiplicity s ≤ ∑ s ∈ zerosInRect model σ_min σ_max T₁ T₂ ∪ zerosInRect model σ_min σ_max T₂ T₃, model.multiplicity s := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact zerosInRect_subset model σ_min σ_max T₁ T₂ T₃
    · intros; exact zero_le _
  have h2 : ∑ s ∈ zerosInRect model σ_min σ_max T₁ T₂ ∪ zerosInRect model σ_min σ_max T₂ T₃, model.multiplicity s + ∑ s ∈ zerosInRect model σ_min σ_max T₁ T₂ ∩ zerosInRect model σ_min σ_max T₂ T₃, model.multiplicity s = ∑ s ∈ zerosInRect model σ_min σ_max T₁ T₂, model.multiplicity s + ∑ s ∈ zerosInRect model σ_min σ_max T₂ T₃, model.multiplicity s := Finset.sum_union_inter
  omega

/-- The classical zero-counting function N(σ, T): number of zeros (with analytic multiplicity)
    with Re(s) ≥ σ and |Im(s)| ≤ T (i.e. -T ≤ Im(s) ≤ T). -/
noncomputable def N (model : ZetaZeroCountModel) (σ T : ℝ) : ℕ :=
  zeroCountRect model σ 1 (-T) T

/-- The dyadic zero reduction proposition.
    Bounds the global zero count N(σ, T) by a finite sum of dyadic slabs
    and a low-height remainder on the full [-T, T] interval using symmetry. -/
def DyadicReductionProp (model : ZetaZeroCountModel) (σ T : ℝ) : Prop :=
  ∃ k : ℕ, N model σ T ≤ 2 * (zeroCountRect model σ 1 0 (T / 2^(k:ℝ)) + ∑ j ∈ Finset.range k,
    zeroCountRect model σ 1 (T / 2^((j:ℝ)+1)) (T / 2^(j:ℝ)))

end RiemannZeta.GuthMaynard

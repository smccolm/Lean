import Mathlib

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
sum-of-genera inequality -> the common residue chart has only constants.
These algebraic ingredients support that exact chart-intersection argument;
the actual joint chart consumer remains to be assembled. Adapted from the
frozen Apache-2.0 FLT source, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial

variable {L : Type*} [Field L] (A : ValuationSubring L)

/-- A polynomial reducing to a nonzero constant. -/
def IsGood (t : L[X]) : Prop :=
  A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1

theorem IsGood.valuation_le {t : L[X]} (ht : IsGood A t) (j : ℕ) :
    A.valuation (t.coeff j) ≤ 1 := by
  by_cases hj : j = 0
  · rw [hj, ht.1]
  · exact (ht.2 j hj).le

theorem IsGood.coeff_zero_ne {t : L[X]} (ht : IsGood A t) : t.coeff 0 ≠ 0 := by
  intro h; have := ht.1; rw [h, map_zero] at this; exact zero_ne_one this

theorem IsGood.ne_zero {t : L[X]} (ht : IsGood A t) : t ≠ 0 := fun h =>
  ht.coeff_zero_ne A (by rw [h, coeff_zero])

theorem IsGood.valuation_eval_eq_one {t : L[X]} (ht : IsGood A t) {c : L}
    (hc : A.valuation c < 1) : A.valuation (t.eval c) = 1 := by
  rw [eval_eq_sum_range, Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  rw [Valuation.map_add_eq_of_lt_right]
  · exact ht.1
  · rw [ht.1]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j _
    rw [map_mul, map_pow]
    calc A.valuation (t.coeff (j + 1)) * A.valuation c ^ (j + 1)
        ≤ 1 * A.valuation c ^ (j + 1) := by gcongr; exact ht.valuation_le A _
      _ < 1 := by rw [one_mul]; exact pow_lt_one₀ zero_le' hc (Nat.succ_ne_zero j)

theorem IsGood.one_lt_valuation_of_isRoot {t : L[X]} (ht : IsGood A t) {ρ : L}
    (hρ : t.IsRoot ρ) : 1 < A.valuation ρ := by
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · have h1 := ht.valuation_eval_eq_one A hlt
    rw [show t.eval ρ = 0 from hρ, map_zero] at h1
    exact zero_ne_one h1
  · have hev : t.eval ρ = 0 := hρ
    rw [eval_eq_sum_range, Finset.sum_range_succ'] at hev
    simp only [pow_zero, mul_one] at hev
    have h0 : t.coeff 0 = -∑ j ∈ Finset.range t.natDegree, t.coeff (j + 1) * ρ ^ (j + 1) := by
      linear_combination hev
    have hlt : A.valuation (∑ j ∈ Finset.range t.natDegree, t.coeff (j + 1) * ρ ^ (j + 1)) < 1 := by
      apply Valuation.map_sum_lt _ one_ne_zero
      intro j _
      rw [map_mul, map_pow, heq, one_pow, mul_one]
      exact ht.2 (j + 1) (Nat.succ_ne_zero j)
    have h1 := ht.1
    rw [h0, Valuation.map_neg] at h1
    exact absurd h1 (ne_of_lt hlt)

theorem prod_X_sub_C_eq_C_mul_prod_one_sub (s : Multiset L) (hs : ∀ ρ ∈ s, ρ ≠ 0) :
    (s.map fun ρ => (X - C ρ : L[X])).prod =
      C (s.map fun ρ => -ρ).prod *
        ((s.map fun ρ => ρ⁻¹).map fun r => (1 - C r * X : L[X])).prod := by
  rw [map_multiset_prod C, Multiset.map_map, Multiset.map_map, ← Multiset.prod_map_mul]
  refine congr_arg _ (Multiset.map_congr rfl fun ρ hρ => ?_)
  simp only [Function.comp_apply]
  have hρ0 : ρ ≠ 0 := hs ρ hρ
  have : C (-ρ) * (1 - C ρ⁻¹ * X) = X - C ρ := by
    have h1 : C ρ * C ρ⁻¹ = (1 : L[X]) := by rw [← C_mul, mul_inv_cancel₀ hρ0, C_1]
    rw [C_neg]
    linear_combination X * h1
  exact this.symm

theorem IsGood.exists_eq_C_mul_prod [IsAlgClosed L] {t : L[X]} (ht : IsGood A t) :
    ∃ (u : L) (cs : Multiset L), u ≠ 0 ∧ (∀ c ∈ cs, A.valuation c < 1) ∧
      t = C u * (cs.map fun c => (1 - C c * X : L[X])).prod := by
  classical
  have ht0 := ht.ne_zero A
  have hsplit : C t.leadingCoeff * (t.roots.map fun a => X - C a).prod = t :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree
  have hroots : ∀ ρ ∈ t.roots, 1 < A.valuation ρ := fun ρ hρ =>
    ht.one_lt_valuation_of_isRoot A ((mem_roots ht0).mp hρ)
  have hroots0 : ∀ ρ ∈ t.roots, ρ ≠ 0 := by
    intro ρ hρ h; have := hroots ρ hρ; rw [h, map_zero] at this
    exact absurd this (not_lt.mpr zero_le')
  refine ⟨t.leadingCoeff * (t.roots.map fun ρ => -ρ).prod, t.roots.map fun ρ => ρ⁻¹, ?_, ?_, ?_⟩
  · refine mul_ne_zero (leadingCoeff_ne_zero.mpr ht0) ?_
    rw [ne_eq, Multiset.prod_eq_zero_iff, Multiset.mem_map]
    rintro ⟨ρ, hρ, h⟩
    exact hroots0 ρ hρ (neg_eq_zero.mp h)
  · intro r hr
    rw [Multiset.mem_map] at hr
    obtain ⟨ρ, hρ, rfl⟩ := hr
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ (hroots ρ hρ)
  · conv_lhs => rw [← hsplit, prod_X_sub_C_eq_C_mul_prod_one_sub t.roots hroots0]
    rw [C_mul, mul_assoc]


end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants

import GafniTao.FordExponentialSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Ford's zero-representation domination principle

This is Proposition ZRD in Section 2 of Ford's source.  For a finite family
of integer-valued functions, the number of ordered pairs whose value vectors
have a prescribed difference is at most the number whose difference is zero.

The theorem is stated for an arbitrary additive commutative group.  Ford's
literal application is obtained by taking the codomain to be a finite vector
of integers.  The proof is the source Cauchy--Schwarz argument on the exact
fiber-count function; no Fourier integral or unproved moment estimate enters.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

variable {β Γ : Type*} [DecidableEq β] [AddCommGroup Γ] [DecidableEq Γ]

/-- The number of points of `B` on which `F` takes the value `v`. -/
def fordRepresentationFiberCount (B : Finset β) (F : β → Γ) (v : Γ) : ℕ :=
  (B.filter fun x => F x = v).card

/-- The exact ordered-pair representation count at displacement `w`. -/
def fordRepresentationCount (B : Finset β) (F : β → Γ) (w : Γ) : ℕ :=
  ((B ×ˢ B).filter fun xy => F xy.1 - F xy.2 = w).card

omit [DecidableEq β] [AddCommGroup Γ] in
theorem fordRepresentationFiberCount_eq_zero_of_not_mem_image
    {B : Finset β} {F : β → Γ} {v : Γ} (hv : v ∉ B.image F) :
    fordRepresentationFiberCount B F v = 0 := by
  unfold fordRepresentationFiberCount
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro x hx hFx
  exact hv (mem_image.mpr ⟨x, hx, hFx⟩)

omit [DecidableEq β] [AddCommGroup Γ] in
theorem summable_fordRepresentationFiberCount_sq
    (B : Finset β) (F : β → Γ) :
    Summable (fun v : Γ => (fordRepresentationFiberCount B F v : ℝ) ^ 2) := by
  apply summable_of_ne_finset_zero (s := B.image F)
  intro v hv
  rw [fordRepresentationFiberCount_eq_zero_of_not_mem_image hv]
  norm_num

omit [DecidableEq β] in
private theorem fordRepresentationFiber_product
    (B : Finset β) (F : β → Γ) (w v : Γ) :
    ((B ×ˢ B).filter fun xy =>
        F xy.1 - F xy.2 = w ∧ F xy.1 = v) =
      (B.filter fun x => F x = v) ×ˢ
        (B.filter fun y => F y = v - w) := by
  ext xy
  simp only [mem_filter, mem_product]
  constructor
  · rintro ⟨⟨hx, hy⟩, hdiff, hxv⟩
    refine ⟨⟨hx, hxv⟩, hy, ?_⟩
    rw [← hxv, ← hdiff]
    abel
  · rintro ⟨⟨hx, hxv⟩, hy, hyv⟩
    refine ⟨⟨hx, hy⟩, ?_, hxv⟩
    rw [hxv, hyv]
    abel

omit [DecidableEq β] in
/-- Exact fiber expansion of the displaced representation count. -/
theorem fordRepresentationCount_eq_sum_fibers
    (B : Finset β) (F : β → Γ) (w : Γ) :
    fordRepresentationCount B F w =
      ∑ v ∈ B.image F,
        fordRepresentationFiberCount B F v *
          fordRepresentationFiberCount B F (v - w) := by
  classical
  let P := (B ×ˢ B).filter fun xy => F xy.1 - F xy.2 = w
  calc
    fordRepresentationCount B F w = P.card := rfl
    _ = ∑ v ∈ B.image F, (P.filter fun xy => F xy.1 = v).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro xy hxy
      have hxy' : xy ∈ (B ×ˢ B).filter (fun xy => F xy.1 - F xy.2 = w) := by
        simpa only [P] using hxy
      exact mem_image.mpr ⟨xy.1, (mem_product.mp (mem_filter.mp hxy').1).1, rfl⟩
    _ = ∑ v ∈ B.image F,
          fordRepresentationFiberCount B F v *
            fordRepresentationFiberCount B F (v - w) := by
      apply sum_congr rfl
      intro v hv
      have hset :
          P.filter (fun xy => F xy.1 = v) =
            (B.filter fun x => F x = v) ×ˢ
              (B.filter fun y => F y = v - w) := by
        simpa only [P, filter_filter, and_assoc] using
          fordRepresentationFiber_product B F w v
      rw [hset, card_product]
      rfl

omit [DecidableEq β] in
/-- The fiber square sum is exactly the zero-displacement representation
count. -/
theorem fordRepresentationCount_zero_eq_sum_fiber_sq
    (B : Finset β) (F : β → Γ) :
    fordRepresentationCount B F 0 =
      ∑ v ∈ B.image F, fordRepresentationFiberCount B F v ^ 2 := by
  rw [fordRepresentationCount_eq_sum_fibers]
  simp only [sub_zero, pow_two]

omit [DecidableEq β] in
/-- Proposition ZRD (Zero Representation Dominates), in source-faithful
ordered-pair form. -/
theorem ford_zeroRepresentationDominates
    (B : Finset β) (F : β → Γ) (w : Γ) :
    fordRepresentationCount B F w ≤ fordRepresentationCount B F 0 := by
  classical
  let n : Γ → ℝ := fun v => fordRepresentationFiberCount B F v
  let S : Finset Γ := B.image F
  have hSq : Summable (fun v : Γ => n v ^ 2) := by
    simpa [n] using summable_fordRepresentationFiberCount_sq B F
  have hShiftSq : Summable (fun v : Γ => n (v - w) ^ 2) := by
    have hcomp := hSq.comp_injective (Equiv.subRight w).injective
    simpa [Function.comp_def] using hcomp
  have hShiftTsum :
      ∑' v : Γ, n (v - w) ^ 2 = ∑' v : Γ, n v ^ 2 := by
    simpa using (Equiv.subRight w).tsum_eq (fun v : Γ => n v ^ 2)
  have hShiftFinite :
      (∑ v ∈ S, n (v - w) ^ 2) ≤ ∑' v : Γ, n v ^ 2 := by
    calc
      (∑ v ∈ S, n (v - w) ^ 2) ≤ ∑' v : Γ, n (v - w) ^ 2 :=
        hShiftSq.sum_le_tsum S (fun _ _ => sq_nonneg _)
      _ = ∑' v : Γ, n v ^ 2 := hShiftTsum
  have hUnshifted :
      ∑ v ∈ S, n v ^ 2 = ∑' v : Γ, n v ^ 2 := by
    symm
    apply tsum_eq_sum
    intro v hv
    rw [show n v = 0 by
      simpa [n, S] using
        fordRepresentationFiberCount_eq_zero_of_not_mem_image
          (B := B) (F := F) hv]
    norm_num
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S n (fun v => n (v - w))
  have hSumNonneg : 0 ≤ ∑ v ∈ S, n v * n (v - w) := by
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hEnergyNonneg : 0 ≤ ∑' v : Γ, n v ^ 2 := by
    exact tsum_nonneg fun _ => sq_nonneg _
  have hSquare :
      (∑ v ∈ S, n v * n (v - w)) ^ 2 ≤
        (∑' v : Γ, n v ^ 2) ^ 2 := by
    calc
      (∑ v ∈ S, n v * n (v - w)) ^ 2 ≤
          (∑ v ∈ S, n v ^ 2) * (∑ v ∈ S, n (v - w) ^ 2) := hCS
      _ ≤ (∑' v : Γ, n v ^ 2) * (∑' v : Γ, n v ^ 2) := by
        rw [hUnshifted]
        exact mul_le_mul_of_nonneg_left hShiftFinite hEnergyNonneg
      _ = (∑' v : Γ, n v ^ 2) ^ 2 := by ring
  have hCorr :
      (∑ v ∈ S, n v * n (v - w)) ≤ ∑' v : Γ, n v ^ 2 := by
    nlinarith
  have hCorrFinite :
      (∑ v ∈ S, n v * n (v - w)) ≤ ∑ v ∈ S, n v ^ 2 := by
    rw [hUnshifted]
    exact hCorr
  rw [fordRepresentationCount_eq_sum_fibers,
    fordRepresentationCount_zero_eq_sum_fiber_sq]
  have hCorr' :
      ((∑ v ∈ B.image F,
          fordRepresentationFiberCount B F v *
            fordRepresentationFiberCount B F (v - w) : ℕ) : ℝ) ≤
        ((∑ v ∈ B.image F,
          fordRepresentationFiberCount B F v ^ 2 : ℕ) : ℝ) := by
    simpa [n, S, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using hCorrFinite
  exact_mod_cast hCorr'

omit [DecidableEq β] in
/-- Ford's literal finite vector specialization: a family `f j` of
integer-valued functions is bundled into its value vector. -/
theorem ford_zeroRepresentationDominates_integerFamily
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Finset β) (f : ι → β → ℤ) (w : ι → ℤ) :
    fordRepresentationCount B (fun x j => f j x) w ≤
      fordRepresentationCount B (fun x j => f j x) 0 := by
  exact ford_zeroRepresentationDominates B (fun x j => f j x) w

#print axioms fordRepresentationCount_eq_sum_fibers
#print axioms ford_zeroRepresentationDominates
#print axioms ford_zeroRepresentationDominates_integerFamily

end

end GafniTao

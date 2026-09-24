import TaoTrudgianYang2025.ZetaReflectionConvolutionEntry
import TaoTrudgianYang2025.BourgainDyadicBands

/-! Finite amplitude selection retains the exact value-times-cardinality loss. -/

noncomputable section
open Complex MeasureTheory Set
open scoped Classical
namespace TaoTrudgianYang2025

def reflectionValueBand (W : Finset ℝ) (f : ℝ → ℝ) (a : ℝ) (j : ℕ) : Finset ℝ :=
  W.filter (fun t => a*(2 : ℝ)^j ≤ f t ∧ f t < 2*(a*(2 : ℝ)^j))

theorem reflectionValueBand_subset (W : Finset ℝ) (f : ℝ → ℝ) (a : ℝ) (j : ℕ) :
    reflectionValueBand W f a j ⊆ W := Finset.filter_subset _ _

theorem reflectionValueBand_values {W : Finset ℝ} {f : ℝ → ℝ} {a t : ℝ} {j : ℕ}
    (ht : t ∈ reflectionValueBand W f a j) :
    a*(2 : ℝ)^j ≤ f t ∧ f t < 2*(a*(2 : ℝ)^j) :=
  (Finset.mem_filter.mp ht).2

theorem reflection_sum_le_low_and_bands (W : Finset ℝ) (f : ℝ → ℝ)
    {a : ℝ} (ha : 0 < a) (J : ℕ) (hterminal : ∀ t ∈ W, f t < a*(2 : ℝ)^J) :
    (∑ t ∈ W, f t) ≤ a*(W.card : ℝ)+
      ∑ j ∈ Finset.range J, 2*(a*(2 : ℝ)^j)*((reflectionValueBand W f a j).card : ℝ) := by
  have hpoint (t : ℝ) (ht : t ∈ W) :
      f t ≤ a+∑ j ∈ Finset.range J,
        2*(a*(2 : ℝ)^j)*(if a*(2 : ℝ)^j ≤ f t ∧ f t < 2*(a*(2 : ℝ)^j) then 1 else 0) := by
    have hnonneg (j : ℕ) (_hj : j ∈ Finset.range J) : 0 ≤
        2*(a*(2 : ℝ)^j)*(if a*(2 : ℝ)^j ≤ f t ∧ f t < 2*(a*(2 : ℝ)^j) then 1 else 0) := by
      split_ifs <;> positivity
    by_cases hlow : f t < a
    · linarith [Finset.sum_nonneg hnonneg]
    · obtain ⟨j,hj,hlo,hhi⟩ := exists_bourgain_dyadic_amplitude (le_of_not_gt hlow) (hterminal t ht)
      have hsingle := Finset.single_le_sum hnonneg hj
      rw [if_pos ⟨hlo,hhi⟩,mul_one] at hsingle
      linarith
  calc
    _ ≤ ∑ t ∈ W, (a+∑ j ∈ Finset.range J,
        2*(a*(2 : ℝ)^j)*(if a*(2 : ℝ)^j ≤ f t ∧ f t < 2*(a*(2 : ℝ)^j) then 1 else 0)) :=
      Finset.sum_le_sum hpoint
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [mul_comm (W.card : ℝ) a]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum]
      simp only [Finset.sum_boole,reflectionValueBand]

theorem exists_reflectionValueBand_mass (W : Finset ℝ) (f : ℝ → ℝ)
    {a R : ℝ} (ha : 0 < a) (hR : 0 < R) {J : ℕ} (hJ : 0 < J)
    (hterminal : ∀ t ∈ W, f t < a*(2 : ℝ)^J)
    (hlow : 2*a*(W.card : ℝ) ≤ R) (hsum : R ≤ ∑ t ∈ W, f t) :
    ∃ j ∈ Finset.range J, (reflectionValueBand W f a j).Nonempty ∧
      R/(4*(J : ℝ)) ≤ a*(2 : ℝ)^j*((reflectionValueBand W f a j).card : ℝ) := by
  have hpart := reflection_sum_le_low_and_bands W f ha J hterminal
  have hmass : R/4 ≤ ∑ j ∈ Finset.range J,
      a*(2 : ℝ)^j*((reflectionValueBand W f a j).card : ℝ) := by
    have he : (∑ j ∈ Finset.range J, 2*(a*(2 : ℝ)^j)*
        ((reflectionValueBand W f a j).card : ℝ)) =
      2*∑ j ∈ Finset.range J, a*(2 : ℝ)^j*((reflectionValueBand W f a j).card : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he] at hpart
    linarith
  have haverage : (∑ _j ∈ Finset.range J, R/(4*(J : ℝ))) = R/4 := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    field_simp
  obtain ⟨j,hj,hbound⟩ := Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hJ))
    (show (∑ _j ∈ Finset.range J, R/(4*(J : ℝ))) ≤
      ∑ j ∈ Finset.range J, a*(2 : ℝ)^j*((reflectionValueBand W f a j).card : ℝ) by
        rw [haverage]
        exact hmass)
  refine ⟨j,hj,?_,hbound⟩
  by_contra hne
  have he := Finset.not_nonempty_iff_eq_empty.mp hne
  rw [he,Finset.card_empty,Nat.cast_zero,mul_zero] at hbound
  exact (not_le_of_gt (div_pos hR (by positivity))) hbound

theorem reflectionValueBand_shift_card (W : Finset ℝ) (f : ℝ → ℝ) (a u : ℝ) (j : ℕ) :
    ((reflectionValueBand W f a j).image (fun t => t+u)).card =
      (reflectionValueBand W f a j).card := by
  exact Finset.card_image_of_injective _ (fun x y h => by linarith)

theorem reflectionValueBand_shift_oneSeparated {W : Finset ℝ}
    (hW : IsOneSeparated W) (f : ℝ → ℝ) (a u : ℝ) (j : ℕ) :
    IsOneSeparated ((reflectionValueBand W f a j).image (fun t => t+u)) := by
  intro x hx y hy hxy
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hy
  have hst : s ≠ t := by intro h; exact hxy (congrArg (fun v => v+u) h)
  have h := hW s (reflectionValueBand_subset W f a j hs)
    t (reflectionValueBand_subset W f a j ht) hst
  simpa only [add_sub_add_right_eq_sub] using h

end TaoTrudgianYang2025

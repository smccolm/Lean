import GafniTao.WooleyFiniteMean

/-!
# Redundant finite Fourier constraints

Equation (7.17) inserts a second finite Fourier average whose congruences are
already forced by the first average.  This file proves that operation once
for arbitrary finite weighted families.  No analytic integral or informal
"orthogonality" step remains hidden in the later use.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The normalized character average is the indicator of zero frequency. -/
theorem wooley_normalized_grid_character
    (q k : ℕ) [NeZero q] (d : Fin k → ZMod q) :
    ((((q ^ k : ℕ) : ℂ))⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          ∏ j, ZMod.stdAddChar (alpha j * d j) =
      if d = 0 then 1 else 0 := by
  rw [wooley_sum_grid_character]
  split_ifs with hd
  · have hq : (((q ^ k : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast pow_ne_zero k (NeZero.ne q)
    field_simp
  · simp

private theorem finite_weighted_filter
    {I Ω : Type*} [Fintype I] [Fintype Ω]
    (A : ℂ) (weight : Ω → ℂ) (character : I → Ω → ℂ)
    (P : Ω → Prop) [DecidablePred P]
    (hcharacter : ∀ omega,
      A * ∑ i : I, character i omega = if P omega then 1 else 0) :
    A * ∑ i : I, ∑ omega : Ω, weight omega * character i omega =
      ∑ omega : Ω, if P omega then weight omega else 0 := by
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega homega
  calc
    (∑ i : I, A * (weight omega * character i omega)) =
        weight omega * (A * ∑ i : I, character i omega) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = if P omega then weight omega else 0 := by
      rw [hcharacter]
      split_ifs <;> simp

/-- Weighted orthogonality: a normalized Fourier grid average retains
exactly those terms whose complete displacement is zero. -/
theorem wooley_weighted_grid_average_eq_filter
    {Ω : Type*} [Fintype Ω] (q k : ℕ) [NeZero q]
    (weight : Ω → ℂ) (disp : Ω → Fin k → ZMod q) :
    ((((q ^ k : ℕ) : ℂ))⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          ∑ omega : Ω, weight omega *
            ∏ j, ZMod.stdAddChar (alpha j * disp omega j) =
      ∑ omega : Ω, if disp omega = 0 then weight omega else 0 := by
  apply finite_weighted_filter
  intro omega
  exact wooley_normalized_grid_character q k (disp omega)

private theorem finite_insert_redundant_average
    {I J Ω : Type*} [Fintype I] [Fintype J] [Fintype Ω]
    (A E : ℂ) (weight : Ω → ℂ)
    (first : I → Ω → ℂ) (second : J → Ω → ℂ)
    (P Q : Ω → Prop) [DecidablePred P] [DecidablePred Q]
    (hfirst : ∀ omega,
      A * ∑ i : I, first i omega = if P omega then 1 else 0)
    (hsecond : ∀ omega,
      E * ∑ j : J, second j omega = if Q omega then 1 else 0)
    (hforced : ∀ omega, P omega → Q omega) :
    A * ∑ i : I, ∑ omega : Ω, weight omega * first i omega =
      A * (E * ∑ i : I, ∑ j : J, ∑ omega : Ω,
        weight omega * first i omega * second j omega) := by
  have hleft :
      A * ∑ i : I, ∑ omega : Ω, weight omega * first i omega =
        ∑ omega : Ω, if P omega then weight omega else 0 :=
    finite_weighted_filter A weight first P hfirst
  have hinner (i : I) :
      E * ∑ j : J, ∑ omega : Ω,
          (weight omega * first i omega) * second j omega =
        ∑ omega : Ω,
          if Q omega then weight omega * first i omega else 0 :=
    finite_weighted_filter E (fun omega => weight omega * first i omega)
      second Q hsecond
  have hright :
      A * (E * ∑ i : I, ∑ j : J, ∑ omega : Ω,
          weight omega * first i omega * second j omega) =
        ∑ omega : Ω,
          if P omega then (if Q omega then weight omega else 0) else 0 := by
    calc
      A * (E * ∑ i : I, ∑ j : J, ∑ omega : Ω,
          weight omega * first i omega * second j omega) =
        A * ∑ i : I, E * ∑ j : J, ∑ omega : Ω,
          weight omega * first i omega * second j omega := by
            rw [Finset.mul_sum]
      _ = A * ∑ i : I, ∑ omega : Ω,
          if Q omega then weight omega * first i omega else 0 := by
            apply congrArg (A * ·)
            apply Finset.sum_congr rfl
            intro i hi
            exact hinner i
      _ = A * ∑ i : I, ∑ omega : Ω,
          (if Q omega then weight omega else 0) * first i omega := by
            apply congrArg (A * ·)
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro omega homega
            by_cases hQ : Q omega
            · simp only [if_pos hQ]
            · simp only [if_neg hQ, zero_mul]
      _ = ∑ omega : Ω,
          if P omega then (if Q omega then weight omega else 0) else 0 :=
            finite_weighted_filter A
              (fun omega => if Q omega then weight omega else 0)
              first P hfirst
  calc
    A * ∑ i : I, ∑ omega : Ω, weight omega * first i omega =
        ∑ omega : Ω, if P omega then weight omega else 0 := hleft
    _ = ∑ omega : Ω,
        if P omega then (if Q omega then weight omega else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro omega homega
          by_cases hP : P omega
          · rw [if_pos hP, if_pos hP, if_pos (hforced omega hP)]
          · rw [if_neg hP, if_neg hP]
    _ = A * (E * ∑ i : I, ∑ j : J, ∑ omega : Ω,
        weight omega * first i omega * second j omega) := hright.symm

/-- A second normalized Fourier grid may be inserted without changing a
weighted average when its zero condition is implied by the first grid's
zero condition.  This is the abstract, exact form of Wooley (7.17). -/
theorem wooley_insert_redundant_grid_average
    {Ω : Type*} [Fintype Ω]
    (q k qPrime r : ℕ) [NeZero q] [NeZero qPrime]
    (weight : Ω → ℂ)
    (disp : Ω → Fin k → ZMod q)
    (extra : Ω → Fin r → ZMod qPrime)
    (hforced : ∀ omega, disp omega = 0 → extra omega = 0) :
    ((((q ^ k : ℕ) : ℂ))⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          ∑ omega : Ω, weight omega *
            ∏ j, ZMod.stdAddChar (alpha j * disp omega j) =
      ((((q ^ k : ℕ) : ℂ))⁻¹) *
        ((((qPrime ^ r : ℕ) : ℂ))⁻¹) *
          ∑ alpha : Fin k → ZMod q,
            ∑ beta : Fin r → ZMod qPrime,
              ∑ omega : Ω, weight omega *
                (∏ j, ZMod.stdAddChar (alpha j * disp omega j)) *
                ∏ l, ZMod.stdAddChar (beta l * extra omega l) := by
  let A : ℂ := (((q ^ k : ℕ) : ℂ))⁻¹
  let E : ℂ := (((qPrime ^ r : ℕ) : ℂ))⁻¹
  let first : (Fin k → ZMod q) → Ω → ℂ := fun alpha omega =>
    ∏ j, ZMod.stdAddChar (alpha j * disp omega j)
  let second : (Fin r → ZMod qPrime) → Ω → ℂ := fun beta omega =>
    ∏ l, ZMod.stdAddChar (beta l * extra omega l)
  have hfirst : ∀ omega,
      A * ∑ alpha, first alpha omega = if disp omega = 0 then 1 else 0 := by
    intro omega
    exact wooley_normalized_grid_character q k (disp omega)
  have hsecond : ∀ omega,
      E * ∑ beta, second beta omega = if extra omega = 0 then 1 else 0 := by
    intro omega
    exact wooley_normalized_grid_character qPrime r (extra omega)
  change A * ∑ alpha, ∑ omega, weight omega * first alpha omega =
    A * E * ∑ alpha, ∑ beta, ∑ omega,
      weight omega * first alpha omega * second beta omega
  rw [mul_assoc]
  exact finite_insert_redundant_average A E weight first second
    (fun omega => disp omega = 0) (fun omega => extra omega = 0)
    hfirst hsecond hforced

#print axioms wooley_normalized_grid_character
#print axioms wooley_weighted_grid_average_eq_filter
#print axioms wooley_insert_redundant_grid_average

end

end GafniTao

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

/-- Weighted orthogonality: a normalized Fourier grid average retains
exactly those terms whose complete displacement is zero. -/
set_option maxHeartbeats 800000 in
theorem wooley_weighted_grid_average_eq_filter
    {Ω : Type*} [Fintype Ω] (q k : ℕ) [NeZero q]
    (weight : Ω → ℂ) (disp : Ω → Fin k → ZMod q) :
    ((((q ^ k : ℕ) : ℂ))⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          ∑ omega : Ω, weight omega *
            ∏ j, ZMod.stdAddChar (alpha j * disp omega j) =
      ∑ omega : Ω, if disp omega = 0 then weight omega else 0 := by
  let A : ℂ := (((q ^ k : ℕ) : ℂ))⁻¹
  change A * (∑ alpha, ∑ omega, weight omega *
    ∏ j, ZMod.stdAddChar (alpha j * disp omega j)) = _
  calc
    A * (∑ alpha : Fin k → ZMod q,
        ∑ omega : Ω, weight omega *
          ∏ j, ZMod.stdAddChar (alpha j * disp omega j)) =
        ∑ alpha : Fin k → ZMod q,
          ∑ omega : Ω, A * (weight omega *
            ∏ j, ZMod.stdAddChar (alpha j * disp omega j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro alpha halpha
      rw [Finset.mul_sum]
    _ = ∑ omega : Ω,
        ∑ alpha : Fin k → ZMod q,
          A * (weight omega *
            ∏ j, ZMod.stdAddChar (alpha j * disp omega j)) :=
      Finset.sum_comm
    _ = ∑ omega : Ω,
          weight omega *
            (A * ∑ alpha : Fin k → ZMod q,
              ∏ j, ZMod.stdAddChar
                (alpha j * disp omega j)) := by
      apply Finset.sum_congr rfl
      intro omega homega
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro alpha halpha
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro omega homega
      change weight omega *
        (((((q ^ k : ℕ) : ℂ))⁻¹) * ∑ alpha,
          ∏ j, ZMod.stdAddChar (alpha j * disp omega j)) = _
      rw [wooley_normalized_grid_character]
      split_ifs <;> simp_all

/-- A second normalized Fourier grid may be inserted without changing a
weighted average when its zero condition is implied by the first grid's
zero condition.  This is the abstract, exact form of Wooley (7.17). -/
set_option maxHeartbeats 1200000 in
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
  change A * (∑ alpha, ∑ omega, weight omega *
      ∏ j, ZMod.stdAddChar (alpha j * disp omega j)) =
    A * (E * ∑ alpha, ∑ beta, ∑ omega,
      weight omega *
        (∏ j, ZMod.stdAddChar (alpha j * disp omega j)) *
        ∏ l, ZMod.stdAddChar (beta l * extra omega l))
  rw [wooley_weighted_grid_average_eq_filter]
  symm
  calc
    A * (E *
        ∑ alpha : Fin k → ZMod q,
          ∑ beta : Fin r → ZMod qPrime,
            ∑ omega : Ω, weight omega *
              (∏ j, ZMod.stdAddChar (alpha j * disp omega j)) *
              ∏ l, ZMod.stdAddChar (beta l * extra omega l)) =
      A *
        ∑ alpha : Fin k → ZMod q,
          E *
            ∑ beta : Fin r → ZMod qPrime,
              ∑ omega : Ω, weight omega *
                (∏ j, ZMod.stdAddChar (alpha j * disp omega j)) *
                ∏ l, ZMod.stdAddChar (beta l * extra omega l) := by
      rw [Finset.mul_sum]
    _ = A *
        ∑ alpha : Fin k → ZMod q,
          ∑ omega : Ω,
            if extra omega = 0 then
              weight omega *
                ∏ j, ZMod.stdAddChar (alpha j * disp omega j)
            else 0 := by
      apply congrArg (A * ·)
      apply Finset.sum_congr rfl
      intro alpha halpha
      change ((((qPrime ^ r : ℕ) : ℂ))⁻¹) * _ = _
      simpa only [mul_assoc] using
        wooley_weighted_grid_average_eq_filter qPrime r
          (fun omega => weight omega *
            ∏ j, ZMod.stdAddChar (alpha j * disp omega j)) extra
    _ = ∑ omega : Ω,
        if disp omega = 0 then
          (if extra omega = 0 then weight omega else 0)
        else 0 := by
      change ((((q ^ k : ℕ) : ℂ))⁻¹) * _ = _
      simpa only [ite_mul, zero_mul] using
        wooley_weighted_grid_average_eq_filter q k
          (fun omega => if extra omega = 0 then weight omega else 0) disp
    _ = ∑ omega : Ω,
        if disp omega = 0 then weight omega else 0 := by
      apply Finset.sum_congr rfl
      intro omega homega
      by_cases hdisp : disp omega = 0
      · rw [if_pos hdisp, if_pos (hforced omega hdisp)]
      · rw [if_neg hdisp, if_neg hdisp]

#print axioms wooley_normalized_grid_character
#print axioms wooley_weighted_grid_average_eq_filter
#print axioms wooley_insert_redundant_grid_average

end

end GafniTao

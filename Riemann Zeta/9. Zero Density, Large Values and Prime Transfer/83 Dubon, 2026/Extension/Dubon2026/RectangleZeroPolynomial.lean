import Dubon2026.PhaseZeroMoments
import Mathlib.RingTheory.Polynomial.Vieta

/-! # The genuine local zero polynomial, retaining every analytic multiplicity -/

namespace Dubon2026

open Polynomial
open scoped BigOperators

noncomputable section

/-- The actual zeros in the open rectangle, repeated according to analytic multiplicity. -/
def rectangleZeroMultiset (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u T : ℝ) : Multiset ℂ :=
  ∑ s ∈ zerosInOpenRectangleFinset a N hN ha l u T,
    Multiset.replicate (zeroMultiplicity a N s) s

/-- The monic polynomial whose roots are precisely these zeros with their multiplicities. -/
def rectangleZeroPolynomial (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u T : ℝ) : ℂ[X] :=
  ((rectangleZeroMultiset a N hN ha l u T).map (fun s => X - C s)).prod

theorem rectangleZeroMultiset_card (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u T : ℝ) :
    (rectangleZeroMultiset a N hN ha l u T).card = verticalZeroCount a N hN ha l u T := by
  simp [rectangleZeroMultiset, verticalZeroCount]

theorem rectangleZeroMultiset_power_sum (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u T : ℝ) (k : ℕ) :
    ((rectangleZeroMultiset a N hN ha l u T).map (fun s => s ^ k)).sum =
      ∑ s ∈ zerosInOpenRectangleFinset a N hN ha l u T, s ^ k * (zeroMultiplicity a N s : ℂ) := by
  classical
  unfold rectangleZeroMultiset
  generalize zerosInOpenRectangleFinset a N hN ha l u T = S
  induction S using Finset.induction with
  | empty => simp
  | @insert b S hb ih =>
    simp [Finset.sum_insert hb, Multiset.map_add, ih, mul_comm]

theorem rectangleZeroPolynomial_monic (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u T : ℝ) : (rectangleZeroPolynomial a N hN ha l u T).Monic := by
  exact monic_multisetProd_X_sub_C _

theorem rectangleZeroPolynomial_roots (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u T : ℝ) :
    (rectangleZeroPolynomial a N hN ha l u T).roots = rectangleZeroMultiset a N hN ha l u T :=
  roots_multiset_prod_X_sub_C _

theorem rectangleZeroPolynomial_natDegree (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u T : ℝ) :
    (rectangleZeroPolynomial a N hN ha l u T).natDegree = verticalZeroCount a N hN ha l u T := by
  rw [rectangleZeroPolynomial, natDegree_multiset_prod_X_sub_C_eq_card, rectangleZeroMultiset_card]

theorem rectangleZeroMultiset_count (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (ha : a 1 ≠ 0)
    (l u T : ℝ) (s : ℂ) :
    (rectangleZeroMultiset a N hN ha l u T).count s =
      if s ∈ zerosInOpenRectangleFinset a N hN ha l u T then zeroMultiplicity a N s else 0 := by
  classical
  unfold rectangleZeroMultiset
  generalize zerosInOpenRectangleFinset a N hN ha l u T = S
  induction S using Finset.induction with
  | empty => simp
  | @insert b S hb ih =>
    by_cases hsb : s = b
    · subst b
      simp [Finset.sum_insert hb, ih, hb]
    · simp [Finset.sum_insert hb, ih, hsb, Multiset.mem_replicate]

theorem rectangleZeroPolynomial_rootMultiplicity (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u T : ℝ) (s : ℂ) :
    (rectangleZeroPolynomial a N hN ha l u T).rootMultiplicity s =
      if s ∈ zerosInOpenRectangleFinset a N hN ha l u T then zeroMultiplicity a N s else 0 := by
  rw [← Polynomial.count_roots, rectangleZeroPolynomial_roots, rectangleZeroMultiset_count]

end

end Dubon2026

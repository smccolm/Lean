import GafniTao.HeathBrownAtkinsonPhase
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The divisor-square mean needed in Heath--Brown's Lemma 7.1

This file proves the elementary estimate behind
`sum d(n)^2 \ll X log(X)^3`.  A pair of divisors `d,e | n` is sent to

`(gcd(d,e), d / gcd(d,e), e / gcd(d,e))`.

The product of these three positive integers is `lcm(d,e)` and therefore
divides `n`; the map is injective because it recovers `d` and `e`.  Summing
over `n <= X` and using the exact count of multiples gives the finite bound
`X * harmonic(X)^3`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The ambient three-factor box used to majorize a pair of divisors. -/
def heathBrownThreeFactorBox (X : Nat) : Finset ((Nat × Nat) × Nat) :=
  (Finset.Ioc 0 X ×ˢ Finset.Ioc 0 X) ×ˢ Finset.Ioc 0 X

/-- Three positive factors in the box whose product divides `n`. -/
def heathBrownThreeFactorDivisorFiber (X n : Nat) : Finset ((Nat × Nat) × Nat) :=
  (heathBrownThreeFactorBox X).filter
    (fun p => p.1.1 * p.1.2 * p.2 ∣ n)

/-- The gcd parametrization of a pair of positive divisors. -/
def heathBrownDivisorPairToThreeFactors (p : Nat × Nat) : (Nat × Nat) × Nat :=
  let g := Nat.gcd p.1 p.2
  ((g, p.1 / g), p.2 / g)

theorem heathBrownDivisorPairToThreeFactors_recover_left
    {d e : Nat} :
    (heathBrownDivisorPairToThreeFactors (d, e)).1.1 *
        (heathBrownDivisorPairToThreeFactors (d, e)).1.2 = d := by
  simp only [heathBrownDivisorPairToThreeFactors]
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)

theorem heathBrownDivisorPairToThreeFactors_recover_right
    {d e : Nat} :
    (heathBrownDivisorPairToThreeFactors (d, e)).1.1 *
        (heathBrownDivisorPairToThreeFactors (d, e)).2 = e := by
  simp only [heathBrownDivisorPairToThreeFactors]
  exact Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)

theorem heathBrownDivisorPairToThreeFactors_injectiveOn
    (n : Nat) :
    Set.InjOn heathBrownDivisorPairToThreeFactors
      (n.divisors ×ˢ n.divisors : Finset (Nat × Nat)) := by
  intro p hp q hq hpq
  have hpMem := Finset.mem_product.mp hp
  have hqMem := Finset.mem_product.mp hq
  have hn : n ≠ 0 := by
    intro hn0
    simp [hn0] at hpMem
  have hpd : 0 < p.1 := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hpMem.1)
    (Nat.pos_of_ne_zero hn)
  have hpe : 0 < p.2 := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hpMem.2)
    (Nat.pos_of_ne_zero hn)
  have hqd : 0 < q.1 := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hqMem.1)
    (Nat.pos_of_ne_zero hn)
  have hqe : 0 < q.2 := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hqMem.2)
    (Nat.pos_of_ne_zero hn)
  apply Prod.ext
  · calc
      p.1 = (heathBrownDivisorPairToThreeFactors p).1.1 *
          (heathBrownDivisorPairToThreeFactors p).1.2 :=
        heathBrownDivisorPairToThreeFactors_recover_left.symm
      _ = (heathBrownDivisorPairToThreeFactors q).1.1 *
          (heathBrownDivisorPairToThreeFactors q).1.2 := by rw [hpq]
      _ = q.1 := heathBrownDivisorPairToThreeFactors_recover_left
  · calc
      p.2 = (heathBrownDivisorPairToThreeFactors p).1.1 *
          (heathBrownDivisorPairToThreeFactors p).2 :=
        heathBrownDivisorPairToThreeFactors_recover_right.symm
      _ = (heathBrownDivisorPairToThreeFactors q).1.1 *
          (heathBrownDivisorPairToThreeFactors q).2 := by rw [hpq]
      _ = q.2 := heathBrownDivisorPairToThreeFactors_recover_right

theorem heathBrownDivisorPairToThreeFactors_mapsTo
    {X n : Nat} (hn : 0 < n) (hnX : n ≤ X) :
    Set.MapsTo heathBrownDivisorPairToThreeFactors
      (n.divisors ×ˢ n.divisors : Finset (Nat × Nat))
      (heathBrownThreeFactorDivisorFiber X n : Finset ((Nat × Nat) × Nat)) := by
  intro p hp
  have hpMem := Finset.mem_product.mp hp
  have hdDvd : p.1 ∣ n := Nat.dvd_of_mem_divisors hpMem.1
  have heDvd : p.2 ∣ n := Nat.dvd_of_mem_divisors hpMem.2
  have hdPos : 0 < p.1 := Nat.pos_of_dvd_of_pos hdDvd hn
  have hePos : 0 < p.2 := Nat.pos_of_dvd_of_pos heDvd hn
  have hgPos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ hdPos
  have hgLe : Nat.gcd p.1 p.2 ≤ X :=
    (Nat.gcd_le_left p.2 hdPos).trans (Nat.le_of_dvd hn hdDvd) |>.trans hnX
  have hdgPos : 0 < p.1 / Nat.gcd p.1 p.2 := Nat.div_pos
    (Nat.gcd_le_left p.2 hdPos) hgPos
  have hegPos : 0 < p.2 / Nat.gcd p.1 p.2 := Nat.div_pos
    (Nat.gcd_le_right p.1 hePos) hgPos
  have hdgLe : p.1 / Nat.gcd p.1 p.2 ≤ X :=
    (Nat.div_le_self _ _).trans ((Nat.le_of_dvd hn hdDvd).trans hnX)
  have hegLe : p.2 / Nat.gcd p.1 p.2 ≤ X :=
    (Nat.div_le_self _ _).trans ((Nat.le_of_dvd hn heDvd).trans hnX)
  change heathBrownDivisorPairToThreeFactors p ∈
    heathBrownThreeFactorDivisorFiber X n
  simp only [heathBrownThreeFactorDivisorFiber,
    heathBrownThreeFactorBox, heathBrownDivisorPairToThreeFactors,
    Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact Finset.mem_Ioc.mpr ⟨hgPos, hgLe⟩
  · exact Finset.mem_Ioc.mpr ⟨hdgPos, hdgLe⟩
  · exact Finset.mem_Ioc.mpr ⟨hegPos, hegLe⟩
  · change Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) *
      (p.2 / Nat.gcd p.1 p.2) ∣ n
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)]
    have hlcm : Nat.lcm p.1 p.2 = p.1 * (p.2 / Nat.gcd p.1 p.2) := by
      apply Nat.eq_of_mul_eq_mul_left hgPos
      rw [Nat.gcd_mul_lcm]
      calc
        p.1 * p.2 = p.1 *
            (Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2)) := by
          rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)]
        _ = Nat.gcd p.1 p.2 *
            (p.1 * (p.2 / Nat.gcd p.1 p.2)) := by ac_rfl
    rw [← hlcm]
    exact Nat.lcm_dvd hdDvd heDvd

/-- A divisor-pair square is bounded by the three-factor divisor fiber. -/
theorem heathBrown_divisorCoefficient_sq_le_threeFactorFiber
    {X n : Nat} (hn : 0 < n) (hnX : n ≤ X) :
    heathBrownDivisorCoefficient n ^ 2 ≤
      (heathBrownThreeFactorDivisorFiber X n).card := by
  rw [pow_two, heathBrownDivisorCoefficient, ← Finset.card_product]
  exact Finset.card_le_card_of_injOn heathBrownDivisorPairToThreeFactors
    (heathBrownDivisorPairToThreeFactors_mapsTo hn hnX)
    (heathBrownDivisorPairToThreeFactors_injectiveOn n)

/-- Exact interchange of the integer and three-factor sums. -/
theorem sum_threeFactorFiber_card_eq_divisionSum (X : Nat) :
    ∑ n ∈ Finset.Ioc 0 X, (heathBrownThreeFactorDivisorFiber X n).card =
      ∑ p ∈ heathBrownThreeFactorBox X,
        (X / (p.1.1 * p.1.2 * p.2) : Nat) := by
  calc
    ∑ n ∈ Finset.Ioc 0 X, (heathBrownThreeFactorDivisorFiber X n).card =
        ∑ n ∈ Finset.Ioc 0 X,
          ∑ p ∈ heathBrownThreeFactorBox X,
            if p.1.1 * p.1.2 * p.2 ∣ n then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact Finset.card_filter _ _
    _ = ∑ p ∈ heathBrownThreeFactorBox X,
          ∑ n ∈ Finset.Ioc 0 X,
            (if p.1.1 * p.1.2 * p.2 ∣ n then (1 : Nat) else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ heathBrownThreeFactorBox X,
          (X / (p.1.1 * p.1.2 * p.2) : Nat) := by
      apply Finset.sum_congr rfl
      intro p hp
      calc
        ∑ n ∈ Finset.Ioc 0 X,
            (if p.1.1 * p.1.2 * p.2 ∣ n then (1 : Nat) else 0) =
            ((Finset.Ioc 0 X).filter
              (fun n => p.1.1 * p.1.2 * p.2 ∣ n)).card := by
          symm
          exact Finset.card_filter _ _
        _ = X / (p.1.1 * p.1.2 * p.2) :=
          Nat.Ioc_filter_dvd_card_eq_div X _

/-- The reciprocal mass of the three-factor box is exactly the cube of the
harmonic number. -/
theorem sum_threeFactorBox_reciprocal_eq_harmonic_cube (X : Nat) :
    ∑ p ∈ heathBrownThreeFactorBox X,
        (1 / (p.1.1 * p.1.2 * p.2 : Real)) =
      ((harmonic X : Rat) : Real) ^ (3 : Nat) := by
  have hIoc : Finset.Ioc 0 X = Finset.Icc 1 X := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  simp only [heathBrownThreeFactorBox, Finset.sum_product]
  rw [hIoc, harmonic_eq_sum_Icc]
  push_cast
  simp only [one_div, mul_inv_rev]
  rw [pow_three]
  simp_rw [← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]

/-- The exact finite divisor-square mean bound used for the coefficient norm
in Heath--Brown's Lemma 7.1. -/
theorem sum_heathBrownDivisorCoefficient_sq_le_harmonic_cube (X : Nat) :
    ∑ n ∈ Finset.Ioc 0 X,
        (heathBrownDivisorCoefficient n : Real) ^ (2 : Nat) ≤
      (X : Real) * ((harmonic X : Rat) : Real) ^ (3 : Nat) := by
  have hpoint : ∀ n ∈ Finset.Ioc 0 X,
      (heathBrownDivisorCoefficient n : Real) ^ (2 : Nat) ≤
        ((heathBrownThreeFactorDivisorFiber X n).card : Real) := by
    intro n hn
    exact_mod_cast heathBrown_divisorCoefficient_sq_le_threeFactorFiber
      (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hn).2
  calc
    ∑ n ∈ Finset.Ioc 0 X,
        (heathBrownDivisorCoefficient n : Real) ^ (2 : Nat) ≤
        ∑ n ∈ Finset.Ioc 0 X,
          ((heathBrownThreeFactorDivisorFiber X n).card : Real) := by
      exact Finset.sum_le_sum fun n hn => hpoint n hn
    _ = ((∑ n ∈ Finset.Ioc 0 X,
          (heathBrownThreeFactorDivisorFiber X n).card : Nat) : Real) := by
      push_cast
      rfl
    _ = ((∑ p ∈ heathBrownThreeFactorBox X,
          (X / (p.1.1 * p.1.2 * p.2) : Nat) : Nat) : Real) := by
      rw [sum_threeFactorFiber_card_eq_divisionSum]
    _ = ∑ p ∈ heathBrownThreeFactorBox X,
          ((X / (p.1.1 * p.1.2 * p.2) : Nat) : Real) := by
      push_cast
      rfl
    _ ≤ ∑ p ∈ heathBrownThreeFactorBox X,
          (X : Real) / (p.1.1 * p.1.2 * p.2 : Real) := by
      apply Finset.sum_le_sum
      intro p hp
      have hdiv :
          ((X / (p.1.1 * p.1.2 * p.2) : Nat) : Real) ≤
            (X : Real) / ((p.1.1 * p.1.2 * p.2 : Nat) : Real) :=
        Nat.cast_div_le
      simpa only [Nat.cast_mul] using hdiv
    _ = (X : Real) * ∑ p ∈ heathBrownThreeFactorBox X,
          (1 / (p.1.1 * p.1.2 * p.2 : Real)) := by
      simp only [div_eq_mul_inv, one_mul, Finset.mul_sum]
    _ = (X : Real) * ((harmonic X : Rat) : Real) ^ (3 : Nat) := by
      rw [sum_threeFactorBox_reciprocal_eq_harmonic_cube]

/-- The dyadic coefficient norm in Heath--Brown's equation (7.16), before
replacing the harmonic number by a logarithm. -/
theorem sum_Ioc_heathBrownDivisorCoefficient_sq_le_harmonic_cube (K : Nat) :
    ∑ n ∈ Finset.Ioc K (2 * K),
        (heathBrownDivisorCoefficient n : Real) ^ (2 : Nat) ≤
      ((2 * K : Nat) : Real) *
        ((harmonic (2 * K) : Rat) : Real) ^ (3 : Nat) := by
  calc
    ∑ n ∈ Finset.Ioc K (2 * K),
        (heathBrownDivisorCoefficient n : Real) ^ (2 : Nat) ≤
        ∑ n ∈ Finset.Ioc 0 (2 * K),
          (heathBrownDivisorCoefficient n : Real) ^ (2 : Nat) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_Ioc.mpr ⟨Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1,
          (Finset.mem_Ioc.mp hn).2⟩
      · intro n hn hnot
        positivity
    _ ≤ ((2 * K : Nat) : Real) *
          ((harmonic (2 * K) : Rat) : Real) ^ (3 : Nat) :=
      sum_heathBrownDivisorCoefficient_sq_le_harmonic_cube (2 * K)

/-- Fully explicit logarithmic form of the dyadic coefficient norm. -/
theorem sum_Ioc_heathBrownDivisorCoefficient_sq_le_log_cube
    {K : Nat} (hK : 1 ≤ K) :
    ∑ n ∈ Finset.Ioc K (2 * K),
        (heathBrownDivisorCoefficient n : Real) ^ (2 : Nat) ≤
      ((2 * K : Nat) : Real) *
        (1 + Real.log (2 * K : Nat)) ^ (3 : Nat) := by
  have hTwoK : 1 ≤ 2 * K := by omega
  have hHarm : ((harmonic (2 * K) : Rat) : Real) ≤
      1 + Real.log (2 * K : Nat) := harmonic_le_one_add_log (2 * K)
  have hHarmNonneg : 0 ≤ ((harmonic (2 * K) : Rat) : Real) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hLogNonneg : 0 ≤ 1 + Real.log (2 * K : Nat) := by
    have hcast : (1 : Real) ≤ (2 * K : Nat) := by exact_mod_cast hTwoK
    have := Real.log_nonneg hcast
    linarith
  calc
    ∑ n ∈ Finset.Ioc K (2 * K),
        (heathBrownDivisorCoefficient n : Real) ^ (2 : Nat) ≤
        ((2 * K : Nat) : Real) *
          ((harmonic (2 * K) : Rat) : Real) ^ (3 : Nat) :=
      sum_Ioc_heathBrownDivisorCoefficient_sq_le_harmonic_cube K
    _ ≤ ((2 * K : Nat) : Real) *
          (1 + Real.log (2 * K : Nat)) ^ (3 : Nat) := by
      gcongr


end

end GafniTao

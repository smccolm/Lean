import GafniTao.WooleyPadicSetup
import Mathlib.Analysis.Fourier.ZMod

/-!
# Wooley's finite grid mean

This file gives the coefficient-one monomial instance of equations (3.5)--
(3.7) in Wooley's nested efficient congruencing paper.  The average is over
the literal grid `(ZMod q)^k`; no continuous-torus or asymptotic
orthogonality is used.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

/-- Orthogonality of the standard additive character on a nonzero residue
ring.  This is the one-coordinate calculation in Wooley (3.5). -/
theorem wooley_sum_stdAddChar_mul (q : ℕ) [NeZero q] (t : ZMod q) :
    ∑ u : ZMod q, ZMod.stdAddChar (t * u) =
      if t = 0 then (q : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht]
  · exact AddChar.sum_eq_zero_of_ne_one
      (ZMod.isPrimitive_stdAddChar q ht)

/-- The product-grid version of additive-character orthogonality. -/
theorem wooley_sum_grid_character (q k : ℕ) [NeZero q]
    (d : Fin k → ZMod q) :
    ∑ alpha : Fin k → ZMod q,
        ∏ j, ZMod.stdAddChar (alpha j * d j) =
      if d = 0 then ((q ^ k : ℕ) : ℂ) else 0 := by
  rw [← Fintype.prod_sum
    (fun j : Fin k => fun u : ZMod q =>
      ZMod.stdAddChar (u * d j))]
  have hcoord (j : Fin k) :
      ∑ u : ZMod q, ZMod.stdAddChar (u * d j) =
        if d j = 0 then (q : ℂ) else 0 := by
    simpa only [mul_comm] using wooley_sum_stdAddChar_mul q (d j)
  simp_rw [hcoord]
  by_cases hd : d = 0
  · subst d
    simp
  · rw [if_neg hd]
    obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
      simpa only [Function.ne_iff] using hd
    rw [prod_eq_zero (mem_univ j)]
    simp [hj]

theorem wooley_addChar_sum_eq_prod
    {A M I : Type*} [AddCommMonoid A] [CommMonoid M] [Fintype I]
    (chi : AddChar A M) (f : I → A) :
    chi (∑ i, f i) = ∏ i, chi (f i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
      rw [sum_insert ha, prod_insert ha, chi.map_add_eq_mul, ih]

/-- The monomial phase on Wooley's finite residue grid.  A value `n : Fin Q`
represents the source integer `n+1`. -/
def wooleyMonomialGridPhase (q k Q : ℕ) [NeZero q]
    (alpha : Fin k → ZMod q) (n : Fin Q) : ℂ :=
  ZMod.stdAddChar
    (∑ j : Fin k,
      alpha j * (((n : ℕ) + 1 : ℕ) : ZMod q) ^ ((j : ℕ) + 1))

/-- The coefficient-one Weyl sum on the finite grid in (3.5). -/
def wooleyMonomialGridSum (q k Q : ℕ) [NeZero q]
    (alpha : Fin k → ZMod q) : ℂ :=
  ∑ n : Fin Q, wooleyMonomialGridPhase q k Q alpha n

theorem wooleyMonomialTuplePhase_eq (q s k Q : ℕ) [NeZero q]
    (alpha : Fin k → ZMod q) (x : FordVinogradovTuple s Q) :
    ∏ i : Fin s, wooleyMonomialGridPhase q k Q alpha (x i) =
      ZMod.stdAddChar
        (∑ j : Fin k,
          alpha j * (fordVinogradovPowerVector s k Q x j : ZMod q)) := by
  simp only [wooleyMonomialGridPhase]
  rw [← wooley_addChar_sum_eq_prod]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum]
  congr 1
  simp [fordVinogradovPowerVector]

theorem wooleyMonomialGridSum_pow (q s k Q : ℕ) [NeZero q]
    (alpha : Fin k → ZMod q) :
    wooleyMonomialGridSum q k Q alpha ^ s =
      ∑ x : FordVinogradovTuple s Q,
        ZMod.stdAddChar
          (∑ j : Fin k,
            alpha j * (fordVinogradovPowerVector s k Q x j : ZMod q)) := by
  rw [wooleyMonomialGridSum, Fintype.sum_pow]
  apply sum_congr rfl
  intro x hx
  exact wooleyMonomialTuplePhase_eq q s k Q alpha x

theorem wooley_conj_monomialGridSum_pow (q s k Q : ℕ) [NeZero q]
    (alpha : Fin k → ZMod q) :
    conj (wooleyMonomialGridSum q k Q alpha) ^ s =
      ∑ y : FordVinogradovTuple s Q,
        ZMod.stdAddChar
          (-∑ j : Fin k,
            alpha j * (fordVinogradovPowerVector s k Q y j : ZMod q)) := by
  have h := congrArg conj (wooleyMonomialGridSum_pow q s k Q alpha)
  simpa only [map_pow, map_sum, AddChar.map_neg_eq_conj] using h

/-- The degree-by-degree displacement in the residue ring. -/
def wooleyModularDisplacement (q s k Q : ℕ)
    (xy : FordVinogradovTuple s Q × FordVinogradovTuple s Q) :
    Fin k → ZMod q :=
  fun j => (fordVinogradovPowerVector s k Q xy.1 j : ZMod q) -
    (fordVinogradovPowerVector s k Q xy.2 j : ZMod q)

theorem wooley_pair_grid_character (q s k Q : ℕ) [NeZero q]
    (alpha : Fin k → ZMod q)
    (xy : FordVinogradovTuple s Q × FordVinogradovTuple s Q) :
    ZMod.stdAddChar
          (∑ j : Fin k,
            alpha j * (fordVinogradovPowerVector s k Q xy.1 j : ZMod q)) *
        ZMod.stdAddChar
          (-∑ j : Fin k,
            alpha j * (fordVinogradovPowerVector s k Q xy.2 j : ZMod q)) =
      ∏ j : Fin k,
        ZMod.stdAddChar (alpha j * wooleyModularDisplacement q s k Q xy j) := by
  rw [← AddChar.map_add_eq_mul, ← wooley_addChar_sum_eq_prod]
  congr 1
  simp only [wooleyModularDisplacement]
  rw [← sub_eq_add_neg, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  ring

/-- A modulus-generic version of the congruence system (3.7). -/
abbrev WooleyModularSolution (s k Q q : ℕ) :=
  {xy : FordVinogradovTuple s Q × FordVinogradovTuple s Q //
    ∀ j : Fin k,
      Int.ModEq (q : ℤ)
        (fordVinogradovPowerVector s k Q xy.1 j)
        (fordVinogradovPowerVector s k Q xy.2 j)}

def wooleyModularCount (s k Q q : ℕ) : ℕ :=
  Nat.card (WooleyModularSolution s k Q q)

/-- Complex form of the unnormalised grid moment. -/
def wooleyMonomialComplexGridMoment (s k Q q : ℕ) [NeZero q] : ℂ :=
  ∑ alpha : Fin k → ZMod q,
    wooleyMonomialGridSum q k Q alpha ^ s *
      conj (wooleyMonomialGridSum q k Q alpha) ^ s

theorem wooleyModularDisplacement_eq_zero_iff
    (q s k Q : ℕ)
    (xy : FordVinogradovTuple s Q × FordVinogradovTuple s Q) :
    wooleyModularDisplacement q s k Q xy = 0 ↔
      ∀ j : Fin k,
        Int.ModEq (q : ℤ)
          (fordVinogradovPowerVector s k Q xy.1 j)
          (fordVinogradovPowerVector s k Q xy.2 j) := by
  constructor
  · intro h j
    have hj := congrFun h j
    simp only [wooleyModularDisplacement, Pi.zero_apply, sub_eq_zero] at hj
    exact (ZMod.intCast_eq_intCast_iff _ _ q).mp hj
  · intro h
    funext j
    simp only [wooleyModularDisplacement, Pi.zero_apply, sub_eq_zero]
    exact (ZMod.intCast_eq_intCast_iff _ _ q).mpr (h j)

theorem wooleyModularCount_cast_complex (q s k Q : ℕ) :
    (wooleyModularCount s k Q q : ℂ) =
      ∑ xy : FordVinogradovTuple s Q × FordVinogradovTuple s Q,
        if wooleyModularDisplacement q s k Q xy = 0 then 1 else 0 := by
  letI : Fintype (WooleyModularSolution s k Q q) := Fintype.ofFinite _
  rw [wooleyModularCount, Nat.card_eq_fintype_card]
  unfold WooleyModularSolution
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  apply sum_congr rfl
  intro xy hxy
  simp only [wooleyModularDisplacement_eq_zero_iff]

theorem wooleyMonomialComplexGridMoment_eq_count
    (q s k Q : ℕ) [NeZero q] :
    wooleyMonomialComplexGridMoment s k Q q =
      ((q ^ k : ℕ) : ℂ) * (wooleyModularCount s k Q q : ℂ) := by
  unfold wooleyMonomialComplexGridMoment
  simp_rw [wooleyMonomialGridSum_pow, wooley_conj_monomialGridSum_pow,
    Finset.sum_mul_sum]
  calc
    (∑ alpha : Fin k → ZMod q,
        ∑ x : FordVinogradovTuple s Q,
          ∑ y : FordVinogradovTuple s Q,
            ZMod.stdAddChar
                (∑ j : Fin k,
                  alpha j * (fordVinogradovPowerVector s k Q x j : ZMod q)) *
              ZMod.stdAddChar
                (-∑ j : Fin k,
                  alpha j * (fordVinogradovPowerVector s k Q y j : ZMod q))) =
        ∑ x : FordVinogradovTuple s Q,
          ∑ y : FordVinogradovTuple s Q,
            ∑ alpha : Fin k → ZMod q,
              ZMod.stdAddChar
                  (∑ j : Fin k,
                    alpha j * (fordVinogradovPowerVector s k Q x j : ZMod q)) *
                ZMod.stdAddChar
                  (-∑ j : Fin k,
                    alpha j * (fordVinogradovPowerVector s k Q y j : ZMod q)) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro x hx
      rw [sum_comm]
    _ = ∑ x : FordVinogradovTuple s Q,
          ∑ y : FordVinogradovTuple s Q,
            if wooleyModularDisplacement q s k Q (x, y) = 0
              then ((q ^ k : ℕ) : ℂ) else 0 := by
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      calc
        (∑ alpha : Fin k → ZMod q,
            ZMod.stdAddChar
                (∑ j : Fin k,
                  alpha j * (fordVinogradovPowerVector s k Q x j : ZMod q)) *
              ZMod.stdAddChar
                (-∑ j : Fin k,
                  alpha j * (fordVinogradovPowerVector s k Q y j : ZMod q))) =
            ∑ alpha : Fin k → ZMod q,
              ∏ j : Fin k,
                ZMod.stdAddChar
                  (alpha j * wooleyModularDisplacement q s k Q (x, y) j) := by
          apply sum_congr rfl
          intro alpha halpha
          exact wooley_pair_grid_character q s k Q alpha (x, y)
        _ = _ := wooley_sum_grid_character q k
          (wooleyModularDisplacement q s k Q (x, y))
    _ = ((q ^ k : ℕ) : ℂ) * (wooleyModularCount s k Q q : ℂ) := by
      rw [wooleyModularCount_cast_complex]
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro y hy
      split_ifs <;> simp

/-- The unnormalised finite grid moment.  Division by `q^k` and `Q^s`
produces Wooley's normalized `U^B_{s,k}` for the coefficient-one sequence. -/
def wooleyMonomialRawGridMoment (s k Q q : ℕ) [NeZero q] : ℝ :=
  ∑ alpha : Fin k → ZMod q,
    ‖wooleyMonomialGridSum q k Q alpha‖ ^ (2 * s)

theorem wooleyMonomialComplexGridMoment_eq_ofReal_raw
    (q s k Q : ℕ) [NeZero q] :
    wooleyMonomialComplexGridMoment s k Q q =
      (wooleyMonomialRawGridMoment s k Q q : ℂ) := by
  unfold wooleyMonomialComplexGridMoment wooleyMonomialRawGridMoment
  simp_rw [ford_pow_mul_conj_pow]
  norm_cast

theorem wooleyMonomialRawGridMoment_eq_count
    (q s k Q : ℕ) [NeZero q] :
    wooleyMonomialRawGridMoment s k Q q =
      ((q ^ k : ℕ) : ℝ) * (wooleyModularCount s k Q q : ℝ) := by
  apply Complex.ofReal_injective
  rw [← wooleyMonomialComplexGridMoment_eq_ofReal_raw]
  simpa using wooleyMonomialComplexGridMoment_eq_count q s k Q

theorem wooleyModularCount_primePower_eq_padic
    (s k Q p B : ℕ) :
    wooleyModularCount s k Q (p ^ B) = wooleyPadicCount s k Q p B := by
  rfl

/-- Wooley's normalized coefficient-one mean `U^B_{s,k}` on a grid of
modulus `q`. -/
def wooleyMonomialNormalizedGridMean
    (s k Q q : ℕ) [NeZero q] : ℝ :=
  wooleyMonomialRawGridMoment s k Q q /
    (((q ^ k : ℕ) : ℝ) * ((Q ^ s : ℕ) : ℝ))

theorem wooleyMonomialNormalizedGridMean_eq_count
    {q s k Q : ℕ} [NeZero q] (hQ : 1 ≤ Q) :
    wooleyMonomialNormalizedGridMean s k Q q =
      (wooleyModularCount s k Q q : ℝ) / ((Q ^ s : ℕ) : ℝ) := by
  rw [wooleyMonomialNormalizedGridMean,
    wooleyMonomialRawGridMoment_eq_count]
  have hq : 0 < q := NeZero.pos q
  have hqpow : (((q ^ k : ℕ) : ℝ)) ≠ 0 := by positivity
  have hQpow : (((Q ^ s : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

/-- Equations (3.5)--(3.7) at Wooley's literal prime-power modulus. -/
theorem wooley_equations_3_5_to_3_7
    {p B s k Q : ℕ} (hp : Nat.Prime p) (hQ : 1 ≤ Q) :
    letI : NeZero (p ^ B) := ⟨pow_ne_zero B hp.ne_zero⟩
    wooleyMonomialNormalizedGridMean s k Q (p ^ B) =
      (wooleyPadicCount s k Q p B : ℝ) / ((Q ^ s : ℕ) : ℝ) := by
  letI : NeZero (p ^ B) := ⟨pow_ne_zero B hp.ne_zero⟩
  rw [wooleyMonomialNormalizedGridMean_eq_count hQ,
    wooleyModularCount_primePower_eq_padic]

#print axioms wooley_sum_stdAddChar_mul
#print axioms wooley_sum_grid_character
#print axioms wooleyMonomialTuplePhase_eq
#print axioms wooleyMonomialGridSum_pow
#print axioms wooley_conj_monomialGridSum_pow
#print axioms wooley_pair_grid_character
#print axioms wooleyModularDisplacement_eq_zero_iff
#print axioms wooleyModularCount_cast_complex
#print axioms wooleyMonomialComplexGridMoment_eq_count
#print axioms wooleyMonomialRawGridMoment_eq_count
#print axioms wooleyMonomialNormalizedGridMean_eq_count
#print axioms wooley_equations_3_5_to_3_7

end

end GafniTao

import GafniTao.FordEquation54Setup

/-!
# Ford Lemma 5.1: tuple expansion and displacement vectors for (5.4)

The `2s`-th power in Ford's weighted lattice moment is expanded over two
literal `B^s` tuples.  Their signed degree sums are retained as an integer
vector `d`; the accompanying complex coefficient and the phase
`sum_j gamma_j d_j c_j` are both exposed.  This is the finite algebraic
expansion preceding the tent-series evaluation in equation (5.4).
-/

open Finset
open scoped BigOperators NNReal ComplexConjugate

namespace GafniTao

noncomputable section

/-- One of the two ordered `s`-tuples from Ford's expansion of `|sum_b|^(2s)`. -/
abbrev FordLemma51BTuple (s : ℕ) (B : Finset ℕ) := Fin s → B

/-- One summand in the oscillatory fiber sum, indexed by the attached
subtype of the literal finite set `B`. -/
def fordLemma51OscillatoryTerm
    (k M r : ℕ) (B : Finset ℕ) (t z : ℝ)
    (c : Fin k → ℤ) (b : B) : ℂ :=
  fordLemma51Epsilon k M r t z b *
    fordAdditiveCharacter (fordLemma51FiberPhase k t z b c)

theorem fordLemma51FiberOscillatorySum_eq_subtypeSum
    (k M r : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ) :
    fordLemma51FiberOscillatorySum k M r B t z c =
      ∑ b : B, fordLemma51OscillatoryTerm k M r B t z c b := by
  unfold fordLemma51FiberOscillatorySum fordLemma51OscillatoryTerm
  exact (Finset.sum_attach B (fun b =>
    fordLemma51Epsilon k M r t z b *
      fordAdditiveCharacter (fordLemma51FiberPhase k t z b c))).symm

/-- Complex conjugation reverses Ford's additive character. -/
theorem conj_fordAdditiveCharacter (x : ℝ) :
    conj (fordAdditiveCharacter x) = fordAdditiveCharacter (-x) := by
  unfold fordAdditiveCharacter
  calc
    conj (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) =
        Complex.exp (conj (2 * Real.pi * Complex.I * (x : ℂ))) :=
      (Complex.exp_conj (2 * Real.pi * Complex.I * (x : ℂ))).symm
    _ = Complex.exp (2 * Real.pi * Complex.I * ((-x : ℝ) : ℂ)) := by
      congr 1
      rw [map_mul, map_mul, map_mul]
      simp only [map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring

/-- The product of the `epsilon_b` factors attached to an ordered pair of
source tuples. -/
def fordLemma51TupleCoefficient
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ)
    (x y : FordLemma51BTuple s B) : ℂ :=
  (∏ i : Fin s, fordLemma51Epsilon k M r t z (x i)) *
    conj (∏ i : Fin s, fordLemma51Epsilon k M r t z (y i))

/-- The phase difference before it is regrouped degree by degree. -/
def fordLemma51TuplePhase
    (k s : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ)
    (x y : FordLemma51BTuple s B) : ℝ :=
  (∑ i : Fin s, fordLemma51FiberPhase k t z (x i) c) -
    ∑ i : Fin s, fordLemma51FiberPhase k t z (y i) c

/-- Ford's exact signed power differences
`d_j = sum_{i≤s} b_i^j - sum_{i>s} b_i^j`, with source degree `j+1`. -/
def fordLemma51DifferenceVector
    (k s : ℕ) (B : Finset ℕ)
    (x y : FordLemma51BTuple s B) : Fin k → ℤ :=
  fun j =>
    (∑ i : Fin s, ((x i : ℕ) : ℤ) ^ ((j : ℕ) + 1)) -
      ∑ i : Fin s, ((y i : ℕ) : ℤ) ^ ((j : ℕ) + 1)

/-- The degree-grouped phase `sum_j gamma_j d_j c_j`. -/
def fordLemma51DifferencePhase
    (k : ℕ) (t z : ℝ) (d c : Fin k → ℤ) : ℝ :=
  ∑ j : Fin k,
    fordTaylorGamma t z (j : ℕ) * (d j : ℝ) * (c j : ℝ)

theorem fordLemma51TuplePhase_eq_differencePhase
    (k s : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ)
    (x y : FordLemma51BTuple s B) :
    fordLemma51TuplePhase k s B t z c x y =
      fordLemma51DifferencePhase k t z
        (fordLemma51DifferenceVector k s B x y) c := by
  unfold fordLemma51TuplePhase fordLemma51DifferencePhase
    fordLemma51FiberPhase
  rw [Finset.sum_comm]
  rw [show (∑ i : Fin s, ∑ j : Fin k,
      fordTaylorGamma t z (j : ℕ) * (y i : ℝ) ^ ((j : ℕ) + 1) * (c j : ℝ)) =
      ∑ j : Fin k, ∑ i : Fin s,
        fordTaylorGamma t z (j : ℕ) * (y i : ℝ) ^ ((j : ℕ) + 1) * (c j : ℝ) by
    rw [Finset.sum_comm]]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  unfold fordLemma51DifferenceVector
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  push_cast
  ring

theorem fordLemma51_prod_oscillatoryTerm
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ)
    (x : FordLemma51BTuple s B) :
    (∏ i : Fin s, fordLemma51OscillatoryTerm k M r B t z c (x i)) =
      (∏ i : Fin s, fordLemma51Epsilon k M r t z (x i)) *
        fordAdditiveCharacter
          (∑ i : Fin s, fordLemma51FiberPhase k t z (x i) c) := by
  unfold fordLemma51OscillatoryTerm
  rw [Finset.prod_mul_distrib]
  rw [← fordAdditiveCharacter_sum Finset.univ]

theorem fordLemma51_conj_prod_oscillatoryTerm
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ)
    (y : FordLemma51BTuple s B) :
    conj (∏ i : Fin s, fordLemma51OscillatoryTerm k M r B t z c (y i)) =
      conj (∏ i : Fin s, fordLemma51Epsilon k M r t z (y i)) *
        fordAdditiveCharacter
          (-(∑ i : Fin s, fordLemma51FiberPhase k t z (y i) c)) := by
  rw [fordLemma51_prod_oscillatoryTerm]
  rw [map_mul, conj_fordAdditiveCharacter]

theorem fordLemma51_pair_oscillatoryTerm
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ)
    (x y : FordLemma51BTuple s B) :
    (∏ i : Fin s, fordLemma51OscillatoryTerm k M r B t z c (x i)) *
        conj (∏ i : Fin s,
          fordLemma51OscillatoryTerm k M r B t z c (y i)) =
      fordLemma51TupleCoefficient k M r s B t z x y *
        fordAdditiveCharacter
          (fordLemma51DifferencePhase k t z
            (fordLemma51DifferenceVector k s B x y) c) := by
  rw [fordLemma51_prod_oscillatoryTerm,
    fordLemma51_conj_prod_oscillatoryTerm]
  unfold fordLemma51TupleCoefficient
  rw [← fordLemma51TuplePhase_eq_differencePhase]
  unfold fordLemma51TuplePhase
  let A := ∑ i : Fin s, fordLemma51FiberPhase k t z (x i) c
  let D := ∑ i : Fin s, fordLemma51FiberPhase k t z (y i) c
  have hchar : fordAdditiveCharacter A * fordAdditiveCharacter (-D) =
      fordAdditiveCharacter (A - D) := by
    rw [← fordAdditiveCharacter_add]
    congr 1
  change
    ((∏ i : Fin s, fordLemma51Epsilon k M r t z (x i)) *
        fordAdditiveCharacter A) *
      (conj (∏ i : Fin s, fordLemma51Epsilon k M r t z (y i)) *
        fordAdditiveCharacter (-D)) =
      ((∏ i : Fin s, fordLemma51Epsilon k M r t z (x i)) *
        conj (∏ i : Fin s, fordLemma51Epsilon k M r t z (y i))) *
          fordAdditiveCharacter (A - D)
  rw [show
    ((∏ i : Fin s, fordLemma51Epsilon k M r t z (x i)) *
        fordAdditiveCharacter A) *
      (conj (∏ i : Fin s, fordLemma51Epsilon k M r t z (y i)) *
        fordAdditiveCharacter (-D)) =
      ((∏ i : Fin s, fordLemma51Epsilon k M r t z (x i)) *
        conj (∏ i : Fin s, fordLemma51Epsilon k M r t z (y i))) *
          (fordAdditiveCharacter A * fordAdditiveCharacter (-D)) by ring]
  rw [hchar]

/-- Exact expansion of the `2s`-th norm power over two source tuples, with
Ford's integer difference vector exposed in every term. -/
theorem fordLemma51_nnnorm_pow_eq_differenceTupleSum
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ) :
    ((‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^
        (2 * s) : ℝ≥0) : ℂ) =
      ∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
        fordLemma51TupleCoefficient k M r s B t z x y *
          fordAdditiveCharacter
            (fordLemma51DifferencePhase k t z
              (fordLemma51DifferenceVector k s B x y) c) := by
  let Z := fordLemma51FiberOscillatorySum k M r B t z c
  have hZ : Z = ∑ b : B,
      fordLemma51OscillatoryTerm k M r B t z c b :=
    fordLemma51FiberOscillatorySum_eq_subtypeSum k M r B t z c
  have hpowZ : Z ^ s = ∑ x : FordLemma51BTuple s B,
      ∏ i : Fin s, fordLemma51OscillatoryTerm k M r B t z c (x i) := by
    rw [hZ]
    exact Fintype.sum_pow _ s
  have hpowConj : conj Z ^ s = ∑ y : FordLemma51BTuple s B,
      conj (∏ i : Fin s,
        fordLemma51OscillatoryTerm k M r B t z c (y i)) := by
    rw [← map_pow, hpowZ, map_sum]
  calc
    ((‖Z‖₊ ^ (2 * s) : ℝ≥0) : ℂ) = Z ^ s * conj Z ^ s := by
      rw [ford_pow_mul_conj_pow]
      push_cast
      rfl
    _ = (∑ x : FordLemma51BTuple s B,
          ∏ i : Fin s, fordLemma51OscillatoryTerm k M r B t z c (x i)) *
        (∑ y : FordLemma51BTuple s B,
          conj (∏ i : Fin s,
            fordLemma51OscillatoryTerm k M r B t z c (y i))) := by
      rw [hpowZ, hpowConj]
    _ = ∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
        (∏ i : Fin s, fordLemma51OscillatoryTerm k M r B t z c (x i)) *
          conj (∏ i : Fin s,
            fordLemma51OscillatoryTerm k M r B t z c (y i)) := by
      rw [Finset.sum_mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      exact fordLemma51_pair_oscillatoryTerm k M r s B t z c x y

#print axioms fordLemma51FiberOscillatorySum_eq_subtypeSum
#print axioms conj_fordAdditiveCharacter
#print axioms fordLemma51TuplePhase_eq_differencePhase
#print axioms fordLemma51_pair_oscillatoryTerm
#print axioms fordLemma51_nnnorm_pow_eq_differenceTupleSum

end

end GafniTao

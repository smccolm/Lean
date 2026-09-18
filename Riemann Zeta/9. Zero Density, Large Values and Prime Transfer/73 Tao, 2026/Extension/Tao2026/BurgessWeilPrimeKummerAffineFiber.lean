import Tao2026.BurgessWeilPrimeKummerPowerFiber
import Mathlib.Algebra.GroupWithZero.Units.Equiv

/-!
# Exact affine fibers of the prime Kummer cover

For a multiplicative character `χ` on a finite field, this file counts every
fiber of the equation

`y ^ orderOf χ = a`.

The zero fiber has one point.  A nonzero fiber has `orderOf χ` points exactly
when `χ a = 1`, and is empty otherwise.  Summing the fiber count over the
values of a polynomial gives the exact affine point count for the associated
Kummer cover.  No Weil estimate or projective completion is used here.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The affine `orderOf χ`-power fiber above `a`. -/
def primeKummerPowerFiber
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (a : F) : Finset F :=
  Finset.univ.filter fun y => y ^ orderOf χ = a

/-- The kernel of the `orderOf χ`-power map on the unit group has precisely
`orderOf χ` elements. -/
theorem natCard_powMonoidHom_orderOf_ker
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) :
    Nat.card (powMonoidHom (orderOf χ) : Fˣ →* Fˣ).ker = orderOf χ := by
  have hdiv0 : orderOf χ ∣ Fintype.card F - 1 :=
    MulChar.orderOf_dvd_card_sub_one F χ
  rw [← Fintype.card_units] at hdiv0
  have hdiv : orderOf χ ∣ Nat.card Fˣ := by
    simpa [Nat.card_eq_fintype_card] using hdiv0
  rw [IsCyclic.card_powMonoidHom_ker,
    Nat.gcd_eq_right_iff_dvd.mpr hdiv]

/-- A nonzero power fiber has `orderOf χ` elements when its value lies in the
character kernel. -/
theorem card_primeKummerPowerFiber_of_ne_zero_of_apply_eq_one
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (a : F) (ha0 : a ≠ 0) (haχ : χ a = 1) :
    (primeKummerPowerFiber F χ a).card = orderOf χ := by
  classical
  let d := orderOf χ
  let f : Fˣ →* Fˣ := powMonoidHom d
  let u : Fˣ := Units.mk0 a ha0
  have hpow : ∃ y : F, y ≠ 0 ∧ y ^ d = a :=
    (mulChar_apply_eq_one_iff_exists_nonzero_pow_eq F χ a).mp haχ
  have hu : u ∈ Set.range f := by
    rcases hpow with ⟨y, hy0, hy⟩
    refine ⟨Units.mk0 y hy0, ?_⟩
    apply Units.ext
    simpa [f, u, d, powMonoidHom_apply] using hy
  have hone : (1 : Fˣ) ∈ Set.range f := ⟨1, by simp [f]⟩
  let e : {y : F // y ^ d = a} ≃ {v : Fˣ // f v = u} :=
    { toFun := fun y => by
        have hy0 : (y : F) ≠ 0 := by
          intro hy
          have := y.property
          rw [hy, zero_pow χ.orderOf_pos.ne'] at this
          exact ha0 this.symm
        refine ⟨Units.mk0 y hy0, ?_⟩
        apply Units.ext
        simpa [f, u, d, powMonoidHom_apply] using y.property
      invFun := fun v => ⟨((v : Fˣ) : F), by
        have hv := congrArg Units.val v.property
        simpa [f, u, d, powMonoidHom_apply] using hv⟩
      left_inv := fun y => Subtype.ext rfl
      right_inv := fun v => Subtype.ext (Units.ext rfl) }
  have hker : #{v : Fˣ | f v = 1} = Nat.card f.ker := by
    symm
    simpa only [Nat.card_eq_fintype_card, MonoidHom.mem_ker] using
      (Fintype.card_subtype (fun v : Fˣ => f v = 1))
  calc
    (primeKummerPowerFiber F χ a).card =
        Fintype.card {y : F // y ^ d = a} := by
      rw [Fintype.card_subtype]
      rfl
    _ = Fintype.card {v : Fˣ // f v = u} := Fintype.card_congr e
    _ = #{v : Fˣ | f v = u} := Fintype.card_subtype _
    _ = #{v : Fˣ | f v = 1} :=
      MonoidHom.card_fiber_eq_of_mem_range f hu hone
    _ = Nat.card f.ker := hker
    _ = orderOf χ := by
      exact natCard_powMonoidHom_orderOf_ker F χ

/-- A nonzero power fiber is empty when its value is outside the character
kernel. -/
theorem card_primeKummerPowerFiber_of_ne_zero_of_apply_ne_one
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (a : F) (ha0 : a ≠ 0) (haχ : χ a ≠ 1) :
    (primeKummerPowerFiber F χ a).card = 0 := by
  classical
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hypow : y ^ orderOf χ = a :=
    by
      change y ∈ Finset.univ.filter
        (fun z : F => z ^ orderOf χ = a) at hy
      exact (Finset.mem_filter.mp hy).2
  have hy0 : y ≠ 0 := by
    intro hzero
    subst y
    rw [zero_pow χ.orderOf_pos.ne'] at hypow
    exact ha0 hypow.symm
  exact haχ <|
    (mulChar_apply_eq_one_iff_exists_nonzero_pow_eq F χ a).mpr
      ⟨y, hy0, hypow⟩

/-- The zero fiber of the positive power map is the singleton `{0}`. -/
theorem card_primeKummerPowerFiber_zero
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) :
    (primeKummerPowerFiber F χ 0).card = 1 := by
  classical
  have hfiber : primeKummerPowerFiber F χ 0 = {0} := by
    ext y
    simp only [primeKummerPowerFiber, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hy
      by_contra hy0
      exact (pow_ne_zero (orderOf χ) hy0) hy
    · rintro rfl
      exact zero_pow χ.orderOf_pos.ne'
  rw [hfiber, Finset.card_singleton]

/-- Complete exact formula for an affine power fiber. -/
theorem card_primeKummerPowerFiber
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (a : F) :
    (primeKummerPowerFiber F χ a).card =
      if a = 0 then 1 else if χ a = 1 then orderOf χ else 0 := by
  by_cases ha0 : a = 0
  · subst a
    simp [card_primeKummerPowerFiber_zero]
  · rw [if_neg ha0]
    by_cases haχ : χ a = 1
    · rw [if_pos haχ]
      exact card_primeKummerPowerFiber_of_ne_zero_of_apply_eq_one
        F χ a ha0 haχ
    · rw [if_neg haχ]
      exact card_primeKummerPowerFiber_of_ne_zero_of_apply_ne_one
        F χ a ha0 haχ

/-- Affine points on the Kummer cover `y ^ orderOf χ = P(x)`. -/
def primeKummerAffineCurvePoints
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    Finset (ZMod p × ZMod p) :=
  (Finset.univ ×ˢ Finset.univ).filter fun q =>
    q.2 ^ orderOf χ = P.eval q.1

/-- Inputs at which the polynomial value is zero. -/
def primePolynomialZeroFiber
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) : Finset (ZMod p) :=
  Finset.univ.filter fun x => P.eval x = 0

/-- For a nonzero polynomial, the zero-value fiber is its finset of distinct
roots in the prime field. -/
theorem primePolynomialZeroFiber_eq_roots_toFinset
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (hP0 : P ≠ 0) :
    primePolynomialZeroFiber p P = P.roots.toFinset := by
  classical
  ext x
  simp [primePolynomialZeroFiber, Polynomial.mem_roots hP0,
    Polynomial.IsRoot]

/-- Counting the affine curve by its vertical fibers. -/
theorem card_primeKummerAffineCurvePoints_eq_sum_fibers
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    (primeKummerAffineCurvePoints p χ P).card =
      ∑ x : ZMod p, (primeKummerPowerFiber (ZMod p) χ (P.eval x)).card := by
  classical
  rw [primeKummerAffineCurvePoints]
  simp_rw [primeKummerPowerFiber, Finset.card_filter]
  rw [Finset.sum_product]

/-- Exact affine point count for the prime Kummer cover.  Zero polynomial
values contribute one point; nonzero values in the character kernel
contribute `orderOf χ` points. -/
theorem card_primeKummerAffineCurvePoints
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    (primeKummerAffineCurvePoints p χ P).card =
      (primePolynomialZeroFiber p P).card +
        orderOf χ * (primeKummerKernelFiber p χ P).card := by
  classical
  rw [card_primeKummerAffineCurvePoints_eq_sum_fibers]
  simp_rw [card_primeKummerPowerFiber]
  have hzeroχ : ∀ x : ZMod p, P.eval x = 0 → χ (P.eval x) ≠ 1 := by
    intro x hx
    rw [hx, χ.map_zero]
    exact zero_ne_one
  calc
    (∑ x : ZMod p,
        if P.eval x = 0 then 1
        else if χ (P.eval x) = 1 then orderOf χ else 0) =
        ∑ x : ZMod p,
          ((if P.eval x = 0 then 1 else 0) +
            orderOf χ * (if χ (P.eval x) = 1 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx0 : P.eval x = 0
      · have hxχ := hzeroχ x hx0
        simp only [if_pos hx0, if_neg hxχ, mul_zero, add_zero]
      · by_cases hxχ : χ (P.eval x) = 1 <;> simp [hx0, hxχ]
    _ = (∑ x : ZMod p, if P.eval x = 0 then 1 else 0) +
          orderOf χ *
            ∑ x : ZMod p, if χ (P.eval x) = 1 then 1 else 0 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (primePolynomialZeroFiber p P).card +
          orderOf χ * (primeKummerKernelFiber p χ P).card := by
      simp [primePolynomialZeroFiber, primeKummerKernelFiber,
        Finset.sum_boole]

/-- Root-set form of the exact affine point count for a nonzero polynomial. -/
theorem card_primeKummerAffineCurvePoints_eq_roots
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) (hP0 : P ≠ 0) :
    (primeKummerAffineCurvePoints p χ P).card =
      P.roots.toFinset.card +
        orderOf χ * (primeKummerKernelFiber p χ P).card := by
  rw [card_primeKummerAffineCurvePoints,
    primePolynomialZeroFiber_eq_roots_toFinset p P hP0]

end

end Tao2026

import Tao2026.BurgessWeilIteration
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots

/-!
# Prime-square fibers for the Burgess complete correlation

This file begins the elementary local analysis at a prime-square modulus.
It gives the exact finite equivalence which writes every residue modulo
`p^2` uniquely as `a + p * t`, with `a,t : Fin p`, and uses it to split a
complete sum into its `p` residue fibers.
-/

namespace Tao2026

open Finset Complex
open Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

@[simp]
theorem zmod_finEquiv_apply (n : ℕ) [NeZero n] (a : Fin n) :
    ZMod.finEquiv n a = (a.1 : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      change (show ZMod (n + 1) from a) = (a.val : ZMod (n + 1))
      exact (ZMod.natCast_zmod_val
        (n := n + 1) (show ZMod (n + 1) from a)).symm

/-- The canonical base-`p` equivalence `(t,a) ↦ a + p*t` between two
prime-sized coordinates and residues modulo `p^2`.  Primality is not needed
for this finite arithmetic equivalence. -/
def burgessPrimeSquareEquiv (p : ℕ) [NeZero p] :
    Fin p × Fin p ≃ ZMod (p ^ 2) := by
  letI : NeZero (p * p) := ⟨mul_ne_zero (NeZero.ne p) (NeZero.ne p)⟩
  exact finProdFinEquiv.trans
    ((ZMod.finEquiv (p * p)).toEquiv.trans
      (ZMod.ringEquivCongr (pow_two p).symm).toEquiv)

@[simp]
theorem burgessPrimeSquareEquiv_apply (p : ℕ) [NeZero p]
    (t a : Fin p) :
    burgessPrimeSquareEquiv p (t, a) =
      ((a.1 + p * t.1 : ℕ) : ZMod (p ^ 2)) := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p =>
      have hlt : a.1 + (p + 1) * t.1 < (p + 1) ^ 2 := by
        nlinarith [a.isLt, t.isLt]
      apply ZMod.val_injective
      rw [ZMod.val_natCast_of_lt hlt]
      change ((ZMod.ringEquivCongr (pow_two (p + 1)).symm)
        ((ZMod.finEquiv ((p + 1) * (p + 1)))
          (finProdFinEquiv (t, a)))).val = _
      rw [ZMod.ringEquivCongr_val, zmod_finEquiv_apply]
      rw [ZMod.val_natCast_of_lt]
      · simp [finProdFinEquiv]
      · simpa [finProdFinEquiv, pow_two] using hlt

/-- Reduction of a base-`p` fiber representative modulo `p` forgets the
fiber coordinate. -/
theorem zmod_cast_burgessPrimeSquareEquiv_apply
    (p : ℕ) [NeZero p] (t a : Fin p) :
    (ZMod.cast (burgessPrimeSquareEquiv p (t, a)) : ZMod p) =
      (a.1 : ZMod p) := by
  rw [burgessPrimeSquareEquiv_apply]
  rw [ZMod.cast_natCast (dvd_pow_self p (by norm_num))]
  simp

/-- The tuple numerator commutes with reduction from a multiple modulus. -/
theorem zmod_cast_burgessTupleNumerator
    {m n B r : ℕ} (h : m ∣ n)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (x : ZMod n) :
    (ZMod.cast (burgessTupleNumerator uv x) : ZMod m) =
      burgessTupleNumerator uv (ZMod.cast x : ZMod m) := by
  unfold burgessTupleNumerator
  change ZMod.castHom h (ZMod m) (Finset.univ.prod
      (fun i : Fin r => x + (((uv.1 i).1 + 1 : ℕ) : ZMod n))) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp [ZMod.castHom_apply, ZMod.cast_add h, ZMod.cast_natCast h,
    ZMod.cast_one h]

/-- The tuple denominator commutes with reduction from a multiple modulus. -/
theorem zmod_cast_burgessTupleDenominator
    {m n B r : ℕ} (h : m ∣ n)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (x : ZMod n) :
    (ZMod.cast (burgessTupleDenominator uv x) : ZMod m) =
      burgessTupleDenominator uv (ZMod.cast x : ZMod m) := by
  unfold burgessTupleDenominator
  change ZMod.castHom h (ZMod m) (Finset.univ.prod
      (fun i : Fin r => x + (((uv.2 i).1 + 1 : ℕ) : ZMod n))) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp [ZMod.castHom_apply, ZMod.cast_add h, ZMod.cast_natCast h,
    ZMod.cast_one h]

/-- On a prime-square fiber, the numerator reduces to the numerator of the
base residue modulo `p`. -/
theorem zmod_cast_burgessTupleNumerator_primeSquare_fiber
    (p B r : ℕ) [NeZero p]
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (t a : Fin p) :
    (ZMod.cast
        (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (t, a))) :
          ZMod p) =
      burgessTupleNumerator uv (a.1 : ZMod p) := by
  rw [zmod_cast_burgessTupleNumerator (dvd_pow_self p (by norm_num)),
    zmod_cast_burgessPrimeSquareEquiv_apply]

/-- On a prime-square fiber, the denominator likewise reduces to its base
residue modulo `p`. -/
theorem zmod_cast_burgessTupleDenominator_primeSquare_fiber
    (p B r : ℕ) [NeZero p]
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (t a : Fin p) :
    (ZMod.cast
        (burgessTupleDenominator uv (burgessPrimeSquareEquiv p (t, a))) :
          ZMod p) =
      burgessTupleDenominator uv (a.1 : ZMod p) := by
  rw [zmod_cast_burgessTupleDenominator (dvd_pow_self p (by norm_num)),
    zmod_cast_burgessPrimeSquareEquiv_apply]

/-- For a prime square, an element is a unit exactly when its reduction
modulo the underlying prime is nonzero. -/
theorem isUnit_zmod_primeSquare_iff_cast_ne_zero
    (p : ℕ) [NeZero p] (hp : p.Prime) (x : ZMod (p ^ 2)) :
    IsUnit x ↔ (ZMod.cast x : ZMod p) ≠ 0 := by
  calc
    IsUnit x ↔ x.val.Coprime (p ^ 2) := by
      rw [← ZMod.isUnit_iff_coprime x.val (p ^ 2),
        ZMod.natCast_zmod_val]
    _ ↔ x.val.Coprime p :=
      Nat.coprime_pow_right_iff (by norm_num : 0 < (2 : ℕ)) x.val p
    _ ↔ ¬p ∣ x.val := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    _ ↔ (x.val : ZMod p) ≠ 0 :=
      (not_congr (ZMod.natCast_eq_zero_iff x.val p)).symm
    _ ↔ (ZMod.cast x : ZMod p) ≠ 0 := by
      rw [ZMod.cast_eq_val x]

/-- Unit status of a prime-square fiber numerator depends only on its base
residue modulo `p`. -/
theorem isUnit_burgessTupleNumerator_primeSquare_fiber_iff
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (t a : Fin p) :
    IsUnit (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (t, a))) ↔
      burgessTupleNumerator uv (a.1 : ZMod p) ≠ 0 := by
  rw [isUnit_zmod_primeSquare_iff_cast_ne_zero p hp,
    zmod_cast_burgessTupleNumerator_primeSquare_fiber]

/-- Unit status of a prime-square fiber denominator also depends only on its
base residue modulo `p`. -/
theorem isUnit_burgessTupleDenominator_primeSquare_fiber_iff
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (t a : Fin p) :
    IsUnit (burgessTupleDenominator uv (burgessPrimeSquareEquiv p (t, a))) ↔
      burgessTupleDenominator uv (a.1 : ZMod p) ≠ 0 := by
  rw [isUnit_zmod_primeSquare_iff_cast_ne_zero p hp,
    zmod_cast_burgessTupleDenominator_primeSquare_fiber]

/-- The base residues modulo `p` at which one of the `2r` linear tuple
factors vanishes. -/
def burgessPrimeSingularBases (p B r : ℕ)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) : Finset (ZMod p) :=
  Finset.univ.image (fun j : Fin r ⊕ Fin r =>
    -((((burgessTupleFlatten uv j).1 + 1 : ℕ)) : ZMod p))

/-- There are at most `2r` singular base residues. -/
theorem card_burgessPrimeSingularBases_le
    (p B r : ℕ) (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    (burgessPrimeSingularBases p B r uv).card ≤ 2 * r := by
  unfold burgessPrimeSingularBases
  calc
    (Finset.univ.image (fun j : Fin r ⊕ Fin r =>
        -((((burgessTupleFlatten uv j).1 + 1 : ℕ)) : ZMod p))).card ≤
        (Finset.univ : Finset (Fin r ⊕ Fin r)).card :=
      Finset.card_image_le
    _ = 2 * r := by simp [two_mul]

/-- A zero numerator marks a singular base residue. -/
theorem mem_burgessPrimeSingularBases_of_numerator_eq_zero
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (a : ZMod p)
    (hzero : burgessTupleNumerator uv a = 0) :
    a ∈ burgessPrimeSingularBases p B r uv := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold burgessTupleNumerator at hzero
  obtain ⟨i, hi, hfactor⟩ := Finset.prod_eq_zero_iff.mp hzero
  unfold burgessPrimeSingularBases
  rw [Finset.mem_image]
  refine ⟨Sum.inl i, Finset.mem_univ _, ?_⟩
  change -((((uv.1 i).1 + 1 : ℕ) : ZMod p)) = a
  exact ((eq_neg_iff_add_eq_zero).2 hfactor).symm

/-- A zero denominator also marks a singular base residue. -/
theorem mem_burgessPrimeSingularBases_of_denominator_eq_zero
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (a : ZMod p)
    (hzero : burgessTupleDenominator uv a = 0) :
    a ∈ burgessPrimeSingularBases p B r uv := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold burgessTupleDenominator at hzero
  obtain ⟨i, hi, hfactor⟩ := Finset.prod_eq_zero_iff.mp hzero
  unfold burgessPrimeSingularBases
  rw [Finset.mem_image]
  refine ⟨Sum.inr i, Finset.mem_univ _, ?_⟩
  change -((((uv.2 i).1 + 1 : ℕ) : ZMod p)) = a
  exact ((eq_neg_iff_add_eq_zero).2 hfactor).symm

/-- The singular-base finset is exactly the zero set of the tuple numerator
or denominator modulo `p`. -/
theorem mem_burgessPrimeSingularBases_iff
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (a : ZMod p) :
    a ∈ burgessPrimeSingularBases p B r uv ↔
      burgessTupleNumerator uv a = 0 ∨
        burgessTupleDenominator uv a = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  constructor
  · intro ha
    unfold burgessPrimeSingularBases at ha
    rw [Finset.mem_image] at ha
    obtain ⟨j, hj, hja⟩ := ha
    rcases j with i | i
    · left
      unfold burgessTupleNumerator
      apply Finset.prod_eq_zero_iff.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      change a + ((((uv.1 i).1 + 1 : ℕ) : ZMod p)) = 0
      rw [← hja]
      simp [burgessTupleFlatten]
    · right
      unfold burgessTupleDenominator
      apply Finset.prod_eq_zero_iff.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      change a + ((((uv.2 i).1 + 1 : ℕ) : ZMod p)) = 0
      rw [← hja]
      simp [burgessTupleFlatten]
  · rintro (hnum | hden)
    · exact mem_burgessPrimeSingularBases_of_numerator_eq_zero
        p B r hp uv a hnum
    · exact mem_burgessPrimeSingularBases_of_denominator_eq_zero
        p B r hp uv a hden

/-- Every summand above a singular base residue vanishes identically. -/
theorem burgess_primeSquare_fiber_term_eq_zero_of_singular
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ (p ^ 2))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (a t : Fin p)
    (ha : (a.1 : ZMod p) ∈ burgessPrimeSingularBases p B r uv) :
    χ (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (t, a))) *
        χ⁻¹ (burgessTupleDenominator uv
          (burgessPrimeSquareEquiv p (t, a))) = 0 := by
  rcases (mem_burgessPrimeSingularBases_iff
    p B r hp uv (a.1 : ZMod p)).mp ha with hnum | hden
  · have hnonunit : ¬IsUnit
        (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (t, a))) := by
      rw [isUnit_burgessTupleNumerator_primeSquare_fiber_iff p B r hp]
      exact not_ne_iff.mpr hnum
    rw [MulChar.map_nonunit χ hnonunit, zero_mul]
  · have hnonunit : ¬IsUnit
        (burgessTupleDenominator uv (burgessPrimeSquareEquiv p (t, a))) := by
      rw [isUnit_burgessTupleDenominator_primeSquare_fiber_iff p B r hp]
      exact not_ne_iff.mpr hden
    rw [MulChar.map_nonunit χ⁻¹ hnonunit, mul_zero]

/-- The full inner fiber sum at a singular base residue is zero. -/
theorem sum_burgess_primeSquare_fiber_eq_zero_of_singular
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ (p ^ 2))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (a : Fin p)
    (ha : (a.1 : ZMod p) ∈ burgessPrimeSingularBases p B r uv) :
    (∑ t : Fin p,
      χ (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (t, a))) *
        χ⁻¹ (burgessTupleDenominator uv
          (burgessPrimeSquareEquiv p (t, a)))) = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  exact burgess_primeSquare_fiber_term_eq_zero_of_singular
    p B r hp χ uv a t ha

/-- Away from the finite singular set, every numerator and denominator in
the entire prime-square fiber is a unit. -/
theorem burgess_primeSquare_fiber_units_of_not_singular
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (a : Fin p) (ha : (a.1 : ZMod p) ∉ burgessPrimeSingularBases p B r uv) :
    ∀ t : Fin p,
      IsUnit (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (t, a))) ∧
      IsUnit (burgessTupleDenominator uv
        (burgessPrimeSquareEquiv p (t, a))) := by
  intro t
  rw [isUnit_burgessTupleNumerator_primeSquare_fiber_iff p B r hp,
    isUnit_burgessTupleDenominator_primeSquare_fiber_iff p B r hp]
  constructor
  · intro hzero
    exact ha (mem_burgessPrimeSingularBases_of_numerator_eq_zero
      p B r hp uv (a.1 : ZMod p) hzero)
  · intro hzero
    exact ha (mem_burgessPrimeSingularBases_of_denominator_eq_zero
      p B r hp uv (a.1 : ZMod p) hzero)

/-- The principal-unit value `1 + p*t` modulo `p^2`, using the canonical
representative of `t : ZMod p`. -/
def burgessPrimeSquarePrincipalUnitValue
    (p : ℕ) (t : ZMod p) : ZMod (p ^ 2) :=
  1 + (p : ZMod (p ^ 2)) * (t.val : ZMod (p ^ 2))

/-- Principal-unit values reduce to one modulo `p`. -/
theorem zmod_cast_burgessPrimeSquarePrincipalUnitValue
    (p : ℕ) (t : ZMod p) :
    (ZMod.cast (burgessPrimeSquarePrincipalUnitValue p t) : ZMod p) = 1 := by
  unfold burgessPrimeSquarePrincipalUnitValue
  rw [ZMod.cast_add (dvd_pow_self p (by norm_num)),
    ZMod.cast_mul (dvd_pow_self p (by norm_num)),
    ZMod.cast_one (dvd_pow_self p (by norm_num)),
    ZMod.cast_natCast (dvd_pow_self p (by norm_num))]
  simp

/-- The base-`p` representative of a sum is congruent to the sum of the two
representatives. -/
theorem zmod_val_add_modEq (p : ℕ) [NeZero p] (s t : ZMod p) :
    (s + t).val ≡ s.val + t.val [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp

/-- The principal-unit parametrization converts addition modulo `p` into
multiplication modulo `p^2`. -/
theorem burgessPrimeSquarePrincipalUnitValue_add
    (p : ℕ) [NeZero p] (s t : ZMod p) :
    burgessPrimeSquarePrincipalUnitValue p (s + t) =
      burgessPrimeSquarePrincipalUnitValue p s *
        burgessPrimeSquarePrincipalUnitValue p t := by
  have hmod := (zmod_val_add_modEq p s t).mul_left' p
  have hcast :
      ((p * (s + t).val : ℕ) : ZMod (p ^ 2)) =
        ((p * (s.val + t.val) : ℕ) : ZMod (p ^ 2)) := by
    rw [ZMod.natCast_eq_natCast_iff]
    simpa [pow_two] using hmod
  have hlinear :
      (p : ZMod (p ^ 2)) * ((s + t).val : ZMod (p ^ 2)) =
        (p : ZMod (p ^ 2)) *
          ((s.val + t.val : ℕ) : ZMod (p ^ 2)) := by
    simpa only [Nat.cast_mul] using hcast
  have hpSq : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
    rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]
  unfold burgessPrimeSquarePrincipalUnitValue
  rw [hlinear, Nat.cast_add]
  linear_combination -hpSq * ((s.val : ZMod (p ^ 2)) * t.val)

/-- Multiplication by `p` modulo `p^2` depends only on reduction modulo
`p`.  This is the elementary congruence used in every first-order fiber
calculation below. -/
theorem zmod_prime_mul_eq_of_cast_eq
    (p : ℕ) [NeZero p] (x y : ZMod (p ^ 2))
    (hxy : (ZMod.cast x : ZMod p) = ZMod.cast y) :
    (p : ZMod (p ^ 2)) * x = (p : ZMod (p ^ 2)) * y := by
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y,
    ← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  have hval : (x.val : ZMod p) = (y.val : ZMod p) := by
    simpa only [ZMod.cast_eq_val] using hxy
  have hmod := (ZMod.natCast_eq_natCast_iff x.val y.val p).mp hval
  simpa [pow_two] using hmod.mul_left' p

/-- Multiplying by a principal unit is exactly a first-order displacement;
the coefficient is computed after reduction modulo `p`. -/
theorem mul_burgessPrimeSquarePrincipalUnitValue
    (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) (s : ZMod p) :
    x * burgessPrimeSquarePrincipalUnitValue p s =
      x + (p : ZMod (p ^ 2)) *
        ((((ZMod.cast x : ZMod p) * s).val : ℕ) : ZMod (p ^ 2)) := by
  unfold burgessPrimeSquarePrincipalUnitValue
  have hcast :
      (ZMod.cast (x * (s.val : ZMod (p ^ 2))) : ZMod p) =
        ZMod.cast
          (((((ZMod.cast x : ZMod p) * s).val : ℕ) : ZMod (p ^ 2))) := by
    rw [ZMod.cast_mul (dvd_pow_self p (by norm_num)),
      ZMod.cast_natCast (dvd_pow_self p (by norm_num)),
      ZMod.cast_natCast (dvd_pow_self p (by norm_num))]
    simp
  have hp := zmod_prime_mul_eq_of_cast_eq p
    (x * (s.val : ZMod (p ^ 2)))
    (((((ZMod.cast x : ZMod p) * s).val : ℕ) : ZMod (p ^ 2))) hcast
  rw [mul_add, mul_one]
  simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z => x + z) hp

/-- If the base reduction of `x` is nonzero, displacement by `p*t` is
multiplication by the principal unit with logarithmic coefficient `x⁻¹`. -/
theorem mul_burgessPrimeSquarePrincipalUnitValue_inv_cast
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (x : ZMod (p ^ 2)) (t : ZMod p)
    (hx : (ZMod.cast x : ZMod p) ≠ 0) :
    x * burgessPrimeSquarePrincipalUnitValue p
        ((ZMod.cast x : ZMod p)⁻¹ * t) =
      x + (p : ZMod (p ^ 2)) * (t.val : ZMod (p ^ 2)) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [mul_burgessPrimeSquarePrincipalUnitValue]
  have hcancel :
      (ZMod.cast x : ZMod p) * ((ZMod.cast x : ZMod p)⁻¹ * t) = t := by
    rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  rw [hcancel]

/-- A nonsingular linear factor on the fiber `a+p*t` is its base value
times an explicitly parametrized principal unit. -/
theorem burgessPrimeSquare_linearFactor_eq_mul_principalUnit
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (a t : Fin p) (b : ℕ)
    (hb : (a.1 : ZMod p) + (b : ZMod p) ≠ 0) :
    burgessPrimeSquareEquiv p (t, a) + (b : ZMod (p ^ 2)) =
      (burgessPrimeSquareEquiv p (0, a) + (b : ZMod (p ^ 2))) *
        burgessPrimeSquarePrincipalUnitValue p
          (((a.1 : ZMod p) + b)⁻¹ * (t.1 : ZMod p)) := by
  have hxcast :
      (ZMod.cast
          (burgessPrimeSquareEquiv p (0, a) + (b : ZMod (p ^ 2))) : ZMod p) =
        (a.1 : ZMod p) + b := by
    rw [ZMod.cast_add (dvd_pow_self p (by norm_num)),
      zmod_cast_burgessPrimeSquareEquiv_apply,
      ZMod.cast_natCast (dvd_pow_self p (by norm_num))]
  have hxne :
      (ZMod.cast
          (burgessPrimeSquareEquiv p (0, a) + (b : ZMod (p ^ 2))) : ZMod p) ≠
        0 := by
    rw [hxcast]
    exact hb
  calc
    burgessPrimeSquareEquiv p (t, a) + (b : ZMod (p ^ 2)) =
        (burgessPrimeSquareEquiv p (0, a) + (b : ZMod (p ^ 2))) +
          (p : ZMod (p ^ 2)) * (t.1 : ZMod (p ^ 2)) := by
      simp only [burgessPrimeSquareEquiv_apply]
      push_cast
      simp
      ring
    _ = (burgessPrimeSquareEquiv p (0, a) + (b : ZMod (p ^ 2))) *
          burgessPrimeSquarePrincipalUnitValue p
            ((ZMod.cast
                (burgessPrimeSquareEquiv p (0, a) + (b : ZMod (p ^ 2))) :
                  ZMod p)⁻¹ * (t.1 : ZMod p)) :=
      by
        simpa [ZMod.val_natCast_of_lt t.isLt] using
          (mul_burgessPrimeSquarePrincipalUnitValue_inv_cast p hp _
            (t.1 : ZMod p) hxne).symm
    _ = _ := by rw [hxcast]

/-- Principal-unit parametrization carries a finite sum to the corresponding
finite product. -/
theorem burgessPrimeSquarePrincipalUnitValue_sum
    {ι : Type*} [DecidableEq ι] (p : ℕ) [NeZero p]
    (s : Finset ι) (f : ι → ZMod p) :
    burgessPrimeSquarePrincipalUnitValue p (∑ i ∈ s, f i) =
      ∏ i ∈ s, burgessPrimeSquarePrincipalUnitValue p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [burgessPrimeSquarePrincipalUnitValue]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Finset.prod_insert hi]
      rw [burgessPrimeSquarePrincipalUnitValue_add, ih]

/-- The logarithmic first-order coefficient of the numerator product at a
base residue modulo `p`. -/
def burgessPrimeNumeratorLogDerivative
    (p B r : ℕ) (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (a : ZMod p) : ZMod p :=
  ∑ i : Fin r, (a + ((((uv.1 i).1 + 1 : ℕ)) : ZMod p))⁻¹

/-- The logarithmic first-order coefficient of the denominator product. -/
def burgessPrimeDenominatorLogDerivative
    (p B r : ℕ) (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (a : ZMod p) : ZMod p :=
  ∑ i : Fin r, (a + ((((uv.2 i).1 + 1 : ℕ)) : ZMod p))⁻¹

/-- The logarithmic first-order coefficient of the Burgess quotient. -/
def burgessPrimeStationaryCoefficient
    (p B r : ℕ) (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (a : ZMod p) : ZMod p :=
  burgessPrimeNumeratorLogDerivative p B r uv a -
    burgessPrimeDenominatorLogDerivative p B r uv a

/-- Exact first-order expansion of the numerator product on a nonsingular
prime-square fiber. -/
theorem burgessTupleNumerator_primeSquare_fiber_eq_mul_principalUnit
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (a t : Fin p)
    (hN : burgessTupleNumerator uv (a.1 : ZMod p) ≠ 0) :
    burgessTupleNumerator uv (burgessPrimeSquareEquiv p (t, a)) =
      burgessTupleNumerator uv (burgessPrimeSquareEquiv p (0, a)) *
        burgessPrimeSquarePrincipalUnitValue p
          (burgessPrimeNumeratorLogDerivative p B r uv (a.1 : ZMod p) *
            (t.1 : ZMod p)) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hfactor : ∀ i : Fin r,
      (a.1 : ZMod p) + ((((uv.1 i).1 + 1 : ℕ)) : ZMod p) ≠ 0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp hN i (Finset.mem_univ i))
  unfold burgessTupleNumerator
  calc
    (∏ i : Fin r,
        (burgessPrimeSquareEquiv p (t, a) +
          ((((uv.1 i).1 + 1 : ℕ)) : ZMod (p ^ 2)))) =
        ∏ i : Fin r,
          (burgessPrimeSquareEquiv p (0, a) +
              ((((uv.1 i).1 + 1 : ℕ)) : ZMod (p ^ 2))) *
            burgessPrimeSquarePrincipalUnitValue p
              (((a.1 : ZMod p) +
                  ((((uv.1 i).1 + 1 : ℕ)) : ZMod p))⁻¹ *
                (t.1 : ZMod p)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact burgessPrimeSquare_linearFactor_eq_mul_principalUnit
        p hp a t ((uv.1 i).1 + 1) (hfactor i)
    _ = (∏ i : Fin r,
          (burgessPrimeSquareEquiv p (0, a) +
            ((((uv.1 i).1 + 1 : ℕ)) : ZMod (p ^ 2)))) *
        ∏ i : Fin r, burgessPrimeSquarePrincipalUnitValue p
          (((a.1 : ZMod p) +
              ((((uv.1 i).1 + 1 : ℕ)) : ZMod p))⁻¹ *
            (t.1 : ZMod p)) := Finset.prod_mul_distrib
    _ = _ := by
      rw [← burgessPrimeSquarePrincipalUnitValue_sum]
      unfold burgessPrimeNumeratorLogDerivative
      rw [Finset.sum_mul]

/-- Exact first-order expansion of the denominator product on a nonsingular
prime-square fiber. -/
theorem burgessTupleDenominator_primeSquare_fiber_eq_mul_principalUnit
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (a t : Fin p)
    (hD : burgessTupleDenominator uv (a.1 : ZMod p) ≠ 0) :
    burgessTupleDenominator uv (burgessPrimeSquareEquiv p (t, a)) =
      burgessTupleDenominator uv (burgessPrimeSquareEquiv p (0, a)) *
        burgessPrimeSquarePrincipalUnitValue p
          (burgessPrimeDenominatorLogDerivative p B r uv (a.1 : ZMod p) *
            (t.1 : ZMod p)) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hfactor : ∀ i : Fin r,
      (a.1 : ZMod p) + ((((uv.2 i).1 + 1 : ℕ)) : ZMod p) ≠ 0 := by
    intro i
    exact (Finset.prod_ne_zero_iff.mp hD i (Finset.mem_univ i))
  unfold burgessTupleDenominator
  calc
    (∏ i : Fin r,
        (burgessPrimeSquareEquiv p (t, a) +
          ((((uv.2 i).1 + 1 : ℕ)) : ZMod (p ^ 2)))) =
        ∏ i : Fin r,
          (burgessPrimeSquareEquiv p (0, a) +
              ((((uv.2 i).1 + 1 : ℕ)) : ZMod (p ^ 2))) *
            burgessPrimeSquarePrincipalUnitValue p
              (((a.1 : ZMod p) +
                  ((((uv.2 i).1 + 1 : ℕ)) : ZMod p))⁻¹ *
                (t.1 : ZMod p)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact burgessPrimeSquare_linearFactor_eq_mul_principalUnit
        p hp a t ((uv.2 i).1 + 1) (hfactor i)
    _ = (∏ i : Fin r,
          (burgessPrimeSquareEquiv p (0, a) +
            ((((uv.2 i).1 + 1 : ℕ)) : ZMod (p ^ 2)))) *
        ∏ i : Fin r, burgessPrimeSquarePrincipalUnitValue p
          (((a.1 : ZMod p) +
              ((((uv.2 i).1 + 1 : ℕ)) : ZMod p))⁻¹ *
            (t.1 : ZMod p)) := Finset.prod_mul_distrib
    _ = _ := by
      rw [← burgessPrimeSquarePrincipalUnitValue_sum]
      unfold burgessPrimeDenominatorLogDerivative
      rw [Finset.sum_mul]

/-- Every principal-unit value is a unit at a prime-square modulus. -/
theorem isUnit_burgessPrimeSquarePrincipalUnitValue
    (p : ℕ) [NeZero p] (hp : p.Prime) (t : ZMod p) :
    IsUnit (burgessPrimeSquarePrincipalUnitValue p t) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [isUnit_zmod_primeSquare_iff_cast_ne_zero p hp,
    zmod_cast_burgessPrimeSquarePrincipalUnitValue]
  exact one_ne_zero

/-- Restriction of a Dirichlet character modulo `p^2` to the principal-unit
subgroup, expressed as an additive character modulo `p`. -/
def burgessPrimeSquarePrincipalAddChar
    (p : ℕ) [NeZero p] (χ : DirichletCharacter ℂ (p ^ 2)) :
    AddChar (ZMod p) ℂ where
  toFun t := χ (burgessPrimeSquarePrincipalUnitValue p t)
  map_zero_eq_one' := by
    simp [burgessPrimeSquarePrincipalUnitValue]
  map_add_eq_mul' s t := by
    rw [burgessPrimeSquarePrincipalUnitValue_add]
    exact χ.map_mul _ _

@[simp]
theorem burgessPrimeSquarePrincipalAddChar_apply
    (p : ℕ) [NeZero p] (χ : DirichletCharacter ℂ (p ^ 2))
    (t : ZMod p) :
    burgessPrimeSquarePrincipalAddChar p χ t =
      χ (burgessPrimeSquarePrincipalUnitValue p t) := rfl

/-- Any nontrivial principal-unit restriction has zero complete additive
sum. -/
theorem sum_burgessPrimeSquarePrincipalAddChar_eq_zero
    (p : ℕ) [NeZero p] (χ : DirichletCharacter ℂ (p ^ 2))
    (hχ : burgessPrimeSquarePrincipalAddChar p χ ≠ 0) :
    ∑ t : ZMod p, burgessPrimeSquarePrincipalAddChar p χ t = 0 :=
  AddChar.sum_eq_zero_iff_ne_zero.mpr hχ

/-- A nonzero frequency preserves nontriviality of an additive character
over the prime field. -/
theorem burgessPrimeSquarePrincipalAddChar_mulShift_ne_zero
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ (p ^ 2))
    (hχ : burgessPrimeSquarePrincipalAddChar p χ ≠ 0)
    (c : ZMod p) (hc : c ≠ 0) :
    AddChar.mulShift (burgessPrimeSquarePrincipalAddChar p χ) c ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  intro hzero
  have hcUnit : IsUnit c := isUnit_iff_ne_zero.mpr hc
  have hone : AddChar.mulShift
      (burgessPrimeSquarePrincipalAddChar p χ) c = 1 := by
    simpa using hzero
  have hbase := (AddChar.mulShift_unit_eq_one_iff
    (burgessPrimeSquarePrincipalAddChar p χ) hcUnit).mp hone
  exact hχ (by simpa using hbase)

/-- The complete principal additive-character sum at a nonzero frequency,
written over the canonical `Fin p` representatives, vanishes. -/
theorem sum_fin_burgessPrimeSquarePrincipalAddChar_mul_eq_zero
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ (p ^ 2))
    (hχ : burgessPrimeSquarePrincipalAddChar p χ ≠ 0)
    (c : ZMod p) (hc : c ≠ 0) :
    ∑ t : Fin p, burgessPrimeSquarePrincipalAddChar p χ
      (c * (t.1 : ZMod p)) = 0 := by
  have hshift : AddChar.mulShift
      (burgessPrimeSquarePrincipalAddChar p χ) c ≠ 0 :=
    burgessPrimeSquarePrincipalAddChar_mulShift_ne_zero p hp χ hχ c hc
  have hsum : ∑ z : ZMod p,
      AddChar.mulShift (burgessPrimeSquarePrincipalAddChar p χ) c z = 0 :=
    AddChar.sum_eq_zero_iff_ne_zero.mpr hshift
  calc
    (∑ t : Fin p, burgessPrimeSquarePrincipalAddChar p χ
        (c * (t.1 : ZMod p))) =
        ∑ z : ZMod p, AddChar.mulShift
          (burgessPrimeSquarePrincipalAddChar p χ) c z := by
      rw [← (ZMod.finEquiv p).sum_comp]
      simp only [AddChar.mulShift_apply]
      apply Finset.sum_congr rfl
      intro t ht
      congr 2
      exact (zmod_finEquiv_apply p t).symm
    _ = 0 := hsum

/-- Every unit in the kernel of reduction from `p^2` to `p` has the form
`1 + p*t`. -/
theorem exists_burgessPrimeSquarePrincipalUnitValue_eq_of_unitsMap_eq_one
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (u : (ZMod (p ^ 2))ˣ)
    (hu : ZMod.unitsMap (dvd_pow_self p (by norm_num)) u = 1) :
    ∃ t : ZMod p,
      burgessPrimeSquarePrincipalUnitValue p t = (u : ZMod (p ^ 2)) := by
  have hcast : (ZMod.cast (u : ZMod (p ^ 2)) : ZMod p) = 1 := by
    have h := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) hu
    simpa [ZMod.unitsMap_val] using h
  have hmod : (u : ZMod (p ^ 2)).val % p = 1 := by
    have hcastVal : (ZMod.cast (u : ZMod (p ^ 2)) : ZMod p) =
        ((u : ZMod (p ^ 2)).val : ZMod p) :=
      ZMod.cast_eq_val (u : ZMod (p ^ 2))
    have hnatcast : ((u : ZMod (p ^ 2)).val : ZMod p) = 1 :=
      hcastVal.symm.trans hcast
    have h := (ZMod.natCast_eq_natCast_iff
      (u : ZMod (p ^ 2)).val 1 p).mp (by simpa using hnatcast)
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] using h
  have hquot : (u : ZMod (p ^ 2)).val / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.pos]
    simpa [pow_two] using ZMod.val_lt (u : ZMod (p ^ 2))
  have hdecomp :
      1 + p * ((u : ZMod (p ^ 2)).val / p) =
        (u : ZMod (p ^ 2)).val := by
    simpa [hmod] using Nat.mod_add_div (u : ZMod (p ^ 2)).val p
  refine ⟨(((u : ZMod (p ^ 2)).val / p : ℕ) : ZMod p), ?_⟩
  calc
    burgessPrimeSquarePrincipalUnitValue p
        (((u : ZMod (p ^ 2)).val / p : ℕ) : ZMod p) =
        ((1 + p * ((u : ZMod (p ^ 2)).val / p) : ℕ) :
          ZMod (p ^ 2)) := by
      unfold burgessPrimeSquarePrincipalUnitValue
      rw [ZMod.val_natCast_of_lt hquot]
      push_cast
      rfl
    _ = ((u : ZMod (p ^ 2)).val : ZMod (p ^ 2)) := by
      exact congrArg (fun n : ℕ => (n : ZMod (p ^ 2))) hdecomp
    _ = (u : ZMod (p ^ 2)) := ZMod.natCast_zmod_val _

/-- Primitivity at level `p^2` forces a nontrivial character on the
principal-unit subgroup. -/
theorem burgessPrimeSquarePrincipalAddChar_ne_zero_of_isPrimitive
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ (p ^ 2))
    (hχ : DirichletCharacter.IsPrimitive χ) :
    burgessPrimeSquarePrincipalAddChar p χ ≠ 0 := by
  intro hzero
  have hfactor : χ.FactorsThrough p := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap
      (dvd_pow_self p (by norm_num))]
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    obtain ⟨t, ht⟩ :=
      exists_burgessPrimeSquarePrincipalUnitValue_eq_of_unitsMap_eq_one
        p hp u hu
    rw [Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
    rw [← ht]
    exact AddChar.eq_zero_iff.mp hzero t
  have hcond : χ.conductor ≤ p := Nat.sInf_le hfactor
  rw [hχ] at hcond
  nlinarith [hp.one_lt]

/-- On a nonsingular base fiber, the Burgess quotient character is a fixed
base value times the principal additive character evaluated at the
stationary coefficient times the fiber coordinate. -/
theorem burgess_primeSquare_fiber_term_eq_base_mul_addChar
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ (p ^ 2))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (a t : Fin p)
    (ha : (a.1 : ZMod p) ∉ burgessPrimeSingularBases p B r uv) :
    χ (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (t, a))) *
        χ⁻¹ (burgessTupleDenominator uv
          (burgessPrimeSquareEquiv p (t, a))) =
      (χ (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (0, a))) *
        χ⁻¹ (burgessTupleDenominator uv
          (burgessPrimeSquareEquiv p (0, a)))) *
        burgessPrimeSquarePrincipalAddChar p χ
          (burgessPrimeStationaryCoefficient p B r uv (a.1 : ZMod p) *
            (t.1 : ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hN : burgessTupleNumerator uv (a.1 : ZMod p) ≠ 0 := by
    intro hzero
    exact ha ((mem_burgessPrimeSingularBases_iff p B r hp uv
      (a.1 : ZMod p)).2 (Or.inl hzero))
  have hD : burgessTupleDenominator uv (a.1 : ZMod p) ≠ 0 := by
    intro hzero
    exact ha ((mem_burgessPrimeSingularBases_iff p B r hp uv
      (a.1 : ZMod p)).2 (Or.inr hzero))
  rw [burgessTupleNumerator_primeSquare_fiber_eq_mul_principalUnit
      p B r hp uv a t hN,
    burgessTupleDenominator_primeSquare_fiber_eq_mul_principalUnit
      p B r hp uv a t hD]
  simp only [map_mul, MulChar.inv_apply_eq_inv']
  let u := burgessPrimeNumeratorLogDerivative p B r uv (a.1 : ZMod p)
  let v := burgessPrimeDenominatorLogDerivative p B r uv (a.1 : ZMod p)
  let C := χ (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (0, a)))
  let D := (χ (burgessTupleDenominator uv
    (burgessPrimeSquareEquiv p (0, a))))⁻¹
  calc
    (C * χ (burgessPrimeSquarePrincipalUnitValue p
          (u * (t.1 : ZMod p)))) *
        (D * (χ (burgessPrimeSquarePrincipalUnitValue p
          (v * (t.1 : ZMod p))))⁻¹) =
        (C * D) *
          (burgessPrimeSquarePrincipalAddChar p χ
              (u * (t.1 : ZMod p)) /
            burgessPrimeSquarePrincipalAddChar p χ
              (v * (t.1 : ZMod p))) := by
      simp only [burgessPrimeSquarePrincipalAddChar_apply, div_eq_mul_inv]
      ring
    _ = (C * D) * burgessPrimeSquarePrincipalAddChar p χ
          (u * (t.1 : ZMod p) - v * (t.1 : ZMod p)) := by
      rw [AddChar.map_sub_eq_div]
    _ = _ := by
      unfold C D u v burgessPrimeStationaryCoefficient
      congr 2
      ring

/-- The inner complete correlation over the fiber above `a mod p`. -/
def burgessPrimeSquareFiberCorrelation
    (p B r : ℕ) [NeZero p] (χ : DirichletCharacter ℂ (p ^ 2))
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (a : Fin p) : ℂ :=
  ∑ t : Fin p,
    χ (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (t, a))) *
      χ⁻¹ (burgessTupleDenominator uv
        (burgessPrimeSquareEquiv p (t, a)))

/-- Every nonsingular fiber with nonzero stationary coefficient cancels
exactly by additive-character orthogonality. -/
theorem burgessPrimeSquareFiberCorrelation_eq_zero_of_not_singular_of_coefficient_ne_zero
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ (p ^ 2))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (a : Fin p)
    (hχ : DirichletCharacter.IsPrimitive χ)
    (ha : (a.1 : ZMod p) ∉ burgessPrimeSingularBases p B r uv)
    (hc : burgessPrimeStationaryCoefficient p B r uv
      (a.1 : ZMod p) ≠ 0) :
    burgessPrimeSquareFiberCorrelation p B r χ uv a = 0 := by
  let C :=
    χ (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (0, a))) *
      χ⁻¹ (burgessTupleDenominator uv
        (burgessPrimeSquareEquiv p (0, a)))
  have hphase : ∀ t : Fin p,
      χ (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (t, a))) *
          χ⁻¹ (burgessTupleDenominator uv
            (burgessPrimeSquareEquiv p (t, a))) =
        C * burgessPrimeSquarePrincipalAddChar p χ
          (burgessPrimeStationaryCoefficient p B r uv (a.1 : ZMod p) *
            (t.1 : ZMod p)) := by
    intro t
    exact burgess_primeSquare_fiber_term_eq_base_mul_addChar
      p B r hp χ uv a t ha
  have hnontrivial : burgessPrimeSquarePrincipalAddChar p χ ≠ 0 :=
    burgessPrimeSquarePrincipalAddChar_ne_zero_of_isPrimitive p hp χ hχ
  have hsum := sum_fin_burgessPrimeSquarePrincipalAddChar_mul_eq_zero
    p hp χ hnontrivial
      (burgessPrimeStationaryCoefficient p B r uv (a.1 : ZMod p)) hc
  unfold burgessPrimeSquareFiberCorrelation
  calc
    (∑ t : Fin p,
        χ (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (t, a))) *
          χ⁻¹ (burgessTupleDenominator uv
            (burgessPrimeSquareEquiv p (t, a)))) =
        ∑ t : Fin p, C * burgessPrimeSquarePrincipalAddChar p χ
          (burgessPrimeStationaryCoefficient p B r uv (a.1 : ZMod p) *
            (t.1 : ZMod p)) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hphase t
    _ = C * ∑ t : Fin p, burgessPrimeSquarePrincipalAddChar p χ
          (burgessPrimeStationaryCoefficient p B r uv (a.1 : ZMod p) *
            (t.1 : ZMod p)) := by rw [Finset.mul_sum]
    _ = 0 := by rw [hsum, mul_zero]

/-- Exact decomposition of a complete prime-square sum into the `p` fibers
`a + p*t`. -/
theorem sum_zmod_primeSquare_eq_sum_fibers
    {M : Type*} [AddCommMonoid M] (p : ℕ) [NeZero p]
    (f : ZMod (p ^ 2) → M) :
    ∑ x : ZMod (p ^ 2), f x =
      ∑ t : Fin p, ∑ a : Fin p,
        f ((a.1 + p * t.1 : ℕ) : ZMod (p ^ 2)) := by
  rw [← (burgessPrimeSquareEquiv p).sum_comp f,
    Fintype.sum_prod_type]
  simp

/-- The Burgess complete correlation at `p^2` is the corresponding iterated
sum over residue fibers. -/
theorem burgessCompleteCorrelation_primeSquare_eq_sum_fibers
    (p B r : ℕ) [NeZero p]
    (χ : DirichletCharacter ℂ (p ^ 2))
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    burgessCompleteCorrelation χ uv =
      ∑ t : Fin p, ∑ a : Fin p,
        χ (burgessTupleNumerator uv
            ((a.1 + p * t.1 : ℕ) : ZMod (p ^ 2))) *
          χ⁻¹ (burgessTupleDenominator uv
            ((a.1 + p * t.1 : ℕ) : ZMod (p ^ 2))) := by
  unfold burgessCompleteCorrelation
  exact sum_zmod_primeSquare_eq_sum_fibers p _

/-- Reordered form of the exact decomposition, with base residues outside
and the fiber correlation inside. -/
theorem burgessCompleteCorrelation_primeSquare_eq_sum_fiberCorrelations
    (p B r : ℕ) [NeZero p]
    (χ : DirichletCharacter ℂ (p ^ 2))
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    burgessCompleteCorrelation χ uv =
      ∑ a : Fin p, burgessPrimeSquareFiberCorrelation p B r χ uv a := by
  rw [burgessCompleteCorrelation_primeSquare_eq_sum_fibers]
  unfold burgessPrimeSquareFiberCorrelation
  rw [Finset.sum_comm]
  simp only [burgessPrimeSquareEquiv_apply]

/-- Every prime-square fiber correlation has the trivial norm bound `p`. -/
theorem norm_burgessPrimeSquareFiberCorrelation_le
    (p B r : ℕ) [NeZero p]
    (χ : DirichletCharacter ℂ (p ^ 2))
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (a : Fin p) :
    ‖burgessPrimeSquareFiberCorrelation p B r χ uv a‖ ≤ (p : ℝ) := by
  unfold burgessPrimeSquareFiberCorrelation
  calc
    ‖∑ t : Fin p,
        χ (burgessTupleNumerator uv (burgessPrimeSquareEquiv p (t, a))) *
          χ⁻¹ (burgessTupleDenominator uv
            (burgessPrimeSquareEquiv p (t, a)))‖ ≤
        ∑ _t : Fin p, (1 : ℝ) := by
      calc
        _ ≤ ∑ t : Fin p,
            ‖χ (burgessTupleNumerator uv
                (burgessPrimeSquareEquiv p (t, a))) *
              χ⁻¹ (burgessTupleDenominator uv
                (burgessPrimeSquareEquiv p (t, a)))‖ := norm_sum_le _ _
        _ ≤ ∑ _t : Fin p, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro t ht
          rw [norm_mul]
          exact mul_le_one₀ (DirichletCharacter.norm_le_one χ _)
            (norm_nonneg _) (DirichletCharacter.norm_le_one χ⁻¹ _)
    _ = (p : ℝ) := by simp

/-- A finite support of fiber correlations bounds the entire prime-square
complete correlation by its cardinality times `p`. -/
theorem norm_burgessCompleteCorrelation_primeSquare_le_card_mul
    (p B r : ℕ) [NeZero p]
    (χ : DirichletCharacter ℂ (p ^ 2))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (S : Finset (Fin p))
    (hsupport : ∀ a : Fin p, a ∉ S →
      burgessPrimeSquareFiberCorrelation p B r χ uv a = 0) :
    ‖burgessCompleteCorrelation χ uv‖ ≤ (S.card : ℝ) * p := by
  rw [burgessCompleteCorrelation_primeSquare_eq_sum_fiberCorrelations]
  have hsum :
      (∑ a : Fin p, burgessPrimeSquareFiberCorrelation p B r χ uv a) =
        ∑ a ∈ S, burgessPrimeSquareFiberCorrelation p B r χ uv a := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro a haUniv haS
    exact hsupport a haS
  rw [hsum]
  calc
    ‖∑ a ∈ S, burgessPrimeSquareFiberCorrelation p B r χ uv a‖ ≤
        ∑ a ∈ S, ‖burgessPrimeSquareFiberCorrelation p B r χ uv a‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _a ∈ S, (p : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact norm_burgessPrimeSquareFiberCorrelation_le p B r χ uv a
    _ = (S.card : ℝ) * p := by simp

/-- The exact remaining stationary-phase support statement at prime-square
level.  It asks that at most `2r` base residues have a nonzero fiber sum. -/
def TaoPrimitivePrimeSquareFiberSupportBound : Prop :=
  ∀ (p B r : ℕ) [NeZero p]
    (χ : DirichletCharacter ℂ (p ^ 2))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r),
    p.Prime → 2 ≤ r → DirichletCharacter.IsPrimitive χ →
    burgessTupleDifferenceProduct uv j ≠ 0 →
    (burgessTupleDifferenceProduct uv j).natAbs.Coprime p →
    ∃ S : Finset (Fin p), S.card ≤ 2 * r ∧
      ∀ a : Fin p, a ∉ S →
        burgessPrimeSquareFiberCorrelation p B r χ uv a = 0

/-- The finite stationary-phase support bound implies the full normalized
prime-square coprime-coefficient Weil predicate. -/
theorem TaoPrimitivePrimeSquareFiberSupportBound.toPrimeSquareWeil
    (hsupport : TaoPrimitivePrimeSquareFiberSupportBound) :
    TaoPrimitivePrimeSquareCoprimeCoefficientWeilBound := by
  intro p B r _ χ uv j hp hr hχ hAj hcop
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨S, hScard, hS⟩ :=
    hsupport p B r χ uv j hp hr hχ hAj hcop
  calc
    ‖burgessCompleteCorrelation χ uv‖ ≤ (S.card : ℝ) * p :=
      norm_burgessCompleteCorrelation_primeSquare_le_card_mul
        p B r χ uv S hS
    _ ≤ ((2 * r : ℕ) : ℝ) * p := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hScard) (by positivity)
    _ ≤ ((4 * r : ℕ) : ℝ) * p := by
      gcongr
      omega

/-- Numerator polynomial of the Burgess quotient over `ZMod p`. -/
def burgessPrimeNumeratorPolynomial
    (p B r : ℕ) (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    Polynomial (ZMod p) :=
  ∏ i : Fin r,
    (Polynomial.X + Polynomial.C
      ((((uv.1 i).1 + 1 : ℕ)) : ZMod p))

/-- Denominator polynomial of the Burgess quotient over `ZMod p`. -/
def burgessPrimeDenominatorPolynomial
    (p B r : ℕ) (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    Polynomial (ZMod p) :=
  ∏ i : Fin r,
    (Polynomial.X + Polynomial.C
      ((((uv.2 i).1 + 1 : ℕ)) : ZMod p))

/-- Polynomial numerator of the logarithmic derivative `F'/F-G'/G`. -/
def burgessPrimeStationaryPolynomial
    (p B r : ℕ) (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    Polynomial (ZMod p) :=
  (burgessPrimeNumeratorPolynomial p B r uv).derivative *
      burgessPrimeDenominatorPolynomial p B r uv -
    burgessPrimeNumeratorPolynomial p B r uv *
      (burgessPrimeDenominatorPolynomial p B r uv).derivative

/-- Coprimality of the selected source coefficient with `p` says that its
integer value remains nonzero modulo `p`. -/
theorem intCast_burgessTupleDifferenceProduct_ne_zero_of_coprime
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r)
    (hcop : (burgessTupleDifferenceProduct uv j).natAbs.Coprime p) :
    ((burgessTupleDifferenceProduct uv j : ℤ) : ZMod p) ≠ 0 := by
  intro hzero
  have hdvdInt : (p : ℤ) ∣ burgessTupleDifferenceProduct uv j :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  have hdvdNat : p ∣ (burgessTupleDifferenceProduct uv j).natAbs := by
    simpa using Int.natAbs_dvd_natAbs.mpr hdvdInt
  have hnot : ¬p ∣ (burgessTupleDifferenceProduct uv j).natAbs :=
    (hp.coprime_iff_not_dvd).mp hcop.symm
  exact hnot hdvdNat

/-- Every individual tagged shift difference occurring in a coefficient
coprime to `p` is nonzero modulo `p`. -/
theorem intCast_burgessTupleShiftInt_sub_ne_zero_of_coprime
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j i : Fin r ⊕ Fin r) (hij : i ≠ j)
    (hcop : (burgessTupleDifferenceProduct uv j).natAbs.Coprime p) :
    ((burgessTupleShiftInt uv i - burgessTupleShiftInt uv j : ℤ) :
      ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hprod := intCast_burgessTupleDifferenceProduct_ne_zero_of_coprime
    p B r hp uv j hcop
  unfold burgessTupleDifferenceProduct at hprod
  push_cast at hprod
  have hi := Finset.prod_ne_zero_iff.mp hprod i
    (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  simpa only [Int.cast_sub] using hi

/-- Evaluation of a tagged linear factor at the root belonging to `j` is
the corresponding integer shift difference modulo `p`. -/
theorem burgessPrime_linearFactor_at_taggedRoot
    (p B r : ℕ)
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j i : Fin r ⊕ Fin r) :
    -((((burgessTupleFlatten uv j).1 + 1 : ℕ)) : ZMod p) +
        ((((burgessTupleFlatten uv i).1 + 1 : ℕ)) : ZMod p) =
      ((burgessTupleShiftInt uv i - burgessTupleShiftInt uv j : ℤ) :
        ZMod p) := by
  unfold burgessTupleShiftInt
  push_cast
  ring

/-- Formal differentiation of a product of monic linear factors, evaluated
at one selected root. -/
theorem eval_derivative_prod_X_add_C_at_root
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (c : ι → R) (j : ι) :
    (∏ i : ι, (Polynomial.X + Polynomial.C (c i))).derivative.eval (-c j) =
      ∏ i ∈ (Finset.univ : Finset ι).erase j, (-c j + c i) := by
  rw [show (∏ i : ι, (Polynomial.X + Polynomial.C (c i))) =
      ∏ i ∈ (Finset.univ : Finset ι),
        (Polynomial.X + Polynomial.C (c i)) by simp]
  rw [Polynomial.derivative_prod_finset]
  change (Polynomial.evalRingHom (-c j)) _ = _
  rw [map_sum]
  simp
  rw [Finset.sum_eq_single j]
  · intro i hi hij
    apply Finset.prod_eq_zero
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
    simp
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Evaluation of the numerator polynomial is the tuple numerator. -/
theorem eval_burgessPrimeNumeratorPolynomial
    (p B r : ℕ) (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (a : ZMod p) :
    (burgessPrimeNumeratorPolynomial p B r uv).eval a =
      burgessTupleNumerator uv a := by
  unfold burgessPrimeNumeratorPolynomial burgessTupleNumerator
  rw [Polynomial.eval_prod]
  simp

/-- Evaluation of the denominator polynomial is the tuple denominator. -/
theorem eval_burgessPrimeDenominatorPolynomial
    (p B r : ℕ) (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (a : ZMod p) :
    (burgessPrimeDenominatorPolynomial p B r uv).eval a =
      burgessTupleDenominator uv a := by
  unfold burgessPrimeDenominatorPolynomial burgessTupleDenominator
  rw [Polynomial.eval_prod]
  simp

/-- At a nonsingular point, the derivative of the numerator polynomial is
the numerator value times its logarithmic coefficient. -/
theorem eval_derivative_burgessPrimeNumeratorPolynomial
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (a : ZMod p)
    (hN : burgessTupleNumerator uv a ≠ 0) :
    (burgessPrimeNumeratorPolynomial p B r uv).derivative.eval a =
      burgessTupleNumerator uv a *
        burgessPrimeNumeratorLogDerivative p B r uv a := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let f : Fin r → ZMod p := fun i =>
    a + ((((uv.1 i).1 + 1 : ℕ)) : ZMod p)
  have hf : ∀ i : Fin r, f i ≠ 0 := by
    intro i
    exact Finset.prod_ne_zero_iff.mp hN i (Finset.mem_univ i)
  have herase : ∀ i : Fin r,
      (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i, f k) =
        (∏ k : Fin r, f k) * (f i)⁻¹ := by
    intro i
    have hprod := Finset.prod_erase_mul (Finset.univ : Finset (Fin r))
      f (Finset.mem_univ i)
    calc
      (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i, f k) =
          ((∏ k ∈ (Finset.univ : Finset (Fin r)).erase i, f k) * f i) *
            (f i)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ (hf i), mul_one]
      _ = (∏ k : Fin r, f k) * (f i)⁻¹ := by rw [hprod]
  unfold burgessPrimeNumeratorPolynomial
  rw [show (∏ i : Fin r,
      (Polynomial.X + Polynomial.C
        ((((uv.1 i).1 + 1 : ℕ)) : ZMod p))) =
      ∏ i ∈ (Finset.univ : Finset (Fin r)),
        (Polynomial.X + Polynomial.C
          ((((uv.1 i).1 + 1 : ℕ)) : ZMod p)) by simp]
  rw [Polynomial.derivative_prod_finset]
  change (Polynomial.evalRingHom a) _ = _
  rw [map_sum]
  simp
  unfold burgessTupleNumerator burgessPrimeNumeratorLogDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa [f, Nat.cast_add, Nat.cast_one] using herase i

/-- Denominator analogue of the logarithmic derivative identity. -/
theorem eval_derivative_burgessPrimeDenominatorPolynomial
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (a : ZMod p)
    (hD : burgessTupleDenominator uv a ≠ 0) :
    (burgessPrimeDenominatorPolynomial p B r uv).derivative.eval a =
      burgessTupleDenominator uv a *
        burgessPrimeDenominatorLogDerivative p B r uv a := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let f : Fin r → ZMod p := fun i =>
    a + ((((uv.2 i).1 + 1 : ℕ)) : ZMod p)
  have hf : ∀ i : Fin r, f i ≠ 0 := by
    intro i
    exact Finset.prod_ne_zero_iff.mp hD i (Finset.mem_univ i)
  have herase : ∀ i : Fin r,
      (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i, f k) =
        (∏ k : Fin r, f k) * (f i)⁻¹ := by
    intro i
    have hprod := Finset.prod_erase_mul (Finset.univ : Finset (Fin r))
      f (Finset.mem_univ i)
    calc
      (∏ k ∈ (Finset.univ : Finset (Fin r)).erase i, f k) =
          ((∏ k ∈ (Finset.univ : Finset (Fin r)).erase i, f k) * f i) *
            (f i)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ (hf i), mul_one]
      _ = (∏ k : Fin r, f k) * (f i)⁻¹ := by rw [hprod]
  unfold burgessPrimeDenominatorPolynomial
  rw [show (∏ i : Fin r,
      (Polynomial.X + Polynomial.C
        ((((uv.2 i).1 + 1 : ℕ)) : ZMod p))) =
      ∏ i ∈ (Finset.univ : Finset (Fin r)),
        (Polynomial.X + Polynomial.C
          ((((uv.2 i).1 + 1 : ℕ)) : ZMod p)) by simp]
  rw [Polynomial.derivative_prod_finset]
  change (Polynomial.evalRingHom a) _ = _
  rw [map_sum]
  simp
  unfold burgessTupleDenominator burgessPrimeDenominatorLogDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa [f, Nat.cast_add, Nat.cast_one] using herase i

/-- Away from singular bases, evaluation of `F'G-FG'` is exactly
`F(a)G(a)` times the stationary coefficient. -/
theorem eval_burgessPrimeStationaryPolynomial_eq_mul_coefficient
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (a : ZMod p)
    (hN : burgessTupleNumerator uv a ≠ 0)
    (hD : burgessTupleDenominator uv a ≠ 0) :
    (burgessPrimeStationaryPolynomial p B r uv).eval a =
      burgessTupleNumerator uv a * burgessTupleDenominator uv a *
        burgessPrimeStationaryCoefficient p B r uv a := by
  unfold burgessPrimeStationaryPolynomial
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
    eval_derivative_burgessPrimeNumeratorPolynomial p B r hp uv a hN,
    eval_derivative_burgessPrimeDenominatorPolynomial p B r hp uv a hD,
    eval_burgessPrimeNumeratorPolynomial,
    eval_burgessPrimeDenominatorPolynomial]
  unfold burgessPrimeStationaryCoefficient
  ring

/-- A tagged coefficient coprime to `p` supplies a simple zero in exactly one
of `F` and `G`; evaluating `F'G-FG'` there proves that the stationary
polynomial is nonzero. -/
theorem burgessPrimeStationaryPolynomial_ne_zero_of_coefficient_coprime
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r)
    (hcop : (burgessTupleDifferenceProduct uv j).natAbs.Coprime p) :
    burgessPrimeStationaryPolynomial p B r uv ≠ 0 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  cases j with
  | inl j =>
      let z : ZMod p :=
        -((((uv.1 j).1 + 1 : ℕ)) : ZMod p)
      have hFzero : burgessTupleNumerator uv z = 0 := by
        unfold burgessTupleNumerator
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [z]
      have hGne : burgessTupleDenominator uv z ≠ 0 := by
        unfold burgessTupleDenominator
        apply Finset.prod_ne_zero_iff.mpr
        intro i hi
        have hdiff :=
          intCast_burgessTupleShiftInt_sub_ne_zero_of_coprime
            p B r hp uv (Sum.inl j) (Sum.inr i) (by simp) hcop
        change -((((burgessTupleFlatten uv (Sum.inl j)).1 + 1 : ℕ)) :
              ZMod p) +
            ((((burgessTupleFlatten uv (Sum.inr i)).1 + 1 : ℕ)) :
              ZMod p) ≠ 0
        rw [burgessPrime_linearFactor_at_taggedRoot]
        exact hdiff
      have hFderiv :
          (burgessPrimeNumeratorPolynomial p B r uv).derivative.eval z ≠ 0 := by
        have hderiv := eval_derivative_prod_X_add_C_at_root
          (R := ZMod p)
          (c := fun i : Fin r =>
            ((((uv.1 i).1 + 1 : ℕ)) : ZMod p)) j
        change (∏ i : Fin r,
          (Polynomial.X + Polynomial.C
            ((((uv.1 i).1 + 1 : ℕ)) : ZMod p))).derivative.eval
              (-((((uv.1 j).1 + 1 : ℕ)) : ZMod p)) ≠ 0
        rw [hderiv]
        apply Finset.prod_ne_zero_iff.mpr
        intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        have hdiff :=
          intCast_burgessTupleShiftInt_sub_ne_zero_of_coprime
            p B r hp uv (Sum.inl j) (Sum.inl i)
              (by exact fun h => hij (Sum.inl_injective h)) hcop
        change -((((burgessTupleFlatten uv (Sum.inl j)).1 + 1 : ℕ)) :
              ZMod p) +
            ((((burgessTupleFlatten uv (Sum.inl i)).1 + 1 : ℕ)) :
              ZMod p) ≠ 0
        rw [burgessPrime_linearFactor_at_taggedRoot]
        exact hdiff
      have hEval :
          (burgessPrimeStationaryPolynomial p B r uv).eval z ≠ 0 := by
        unfold burgessPrimeStationaryPolynomial
        rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
          eval_burgessPrimeNumeratorPolynomial,
          eval_burgessPrimeDenominatorPolynomial, hFzero, zero_mul, sub_zero]
        exact mul_ne_zero hFderiv hGne
      intro hzero
      apply hEval
      rw [hzero, Polynomial.eval_zero]
  | inr j =>
      let z : ZMod p :=
        -((((uv.2 j).1 + 1 : ℕ)) : ZMod p)
      have hGzero : burgessTupleDenominator uv z = 0 := by
        unfold burgessTupleDenominator
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [z]
      have hFne : burgessTupleNumerator uv z ≠ 0 := by
        unfold burgessTupleNumerator
        apply Finset.prod_ne_zero_iff.mpr
        intro i hi
        have hdiff :=
          intCast_burgessTupleShiftInt_sub_ne_zero_of_coprime
            p B r hp uv (Sum.inr j) (Sum.inl i) (by simp) hcop
        change -((((burgessTupleFlatten uv (Sum.inr j)).1 + 1 : ℕ)) :
              ZMod p) +
            ((((burgessTupleFlatten uv (Sum.inl i)).1 + 1 : ℕ)) :
              ZMod p) ≠ 0
        rw [burgessPrime_linearFactor_at_taggedRoot]
        exact hdiff
      have hGderiv :
          (burgessPrimeDenominatorPolynomial p B r uv).derivative.eval z ≠ 0 := by
        have hderiv := eval_derivative_prod_X_add_C_at_root
          (R := ZMod p)
          (c := fun i : Fin r =>
            ((((uv.2 i).1 + 1 : ℕ)) : ZMod p)) j
        change (∏ i : Fin r,
          (Polynomial.X + Polynomial.C
            ((((uv.2 i).1 + 1 : ℕ)) : ZMod p))).derivative.eval
              (-((((uv.2 j).1 + 1 : ℕ)) : ZMod p)) ≠ 0
        rw [hderiv]
        apply Finset.prod_ne_zero_iff.mpr
        intro i hi
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        have hdiff :=
          intCast_burgessTupleShiftInt_sub_ne_zero_of_coprime
            p B r hp uv (Sum.inr j) (Sum.inr i)
              (by exact fun h => hij (Sum.inr_injective h)) hcop
        change -((((burgessTupleFlatten uv (Sum.inr j)).1 + 1 : ℕ)) :
              ZMod p) +
            ((((burgessTupleFlatten uv (Sum.inr i)).1 + 1 : ℕ)) :
              ZMod p) ≠ 0
        rw [burgessPrime_linearFactor_at_taggedRoot]
        exact hdiff
      have hEval :
          (burgessPrimeStationaryPolynomial p B r uv).eval z ≠ 0 := by
        unfold burgessPrimeStationaryPolynomial
        rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
          eval_burgessPrimeNumeratorPolynomial,
          eval_burgessPrimeDenominatorPolynomial, hGzero, mul_zero, zero_sub]
        exact neg_ne_zero.mpr (mul_ne_zero hFne hGderiv)
      intro hzero
      apply hEval
      rw [hzero, Polynomial.eval_zero]

/-- Each tuple polynomial has degree at most `r`. -/
theorem natDegree_burgessPrimeNumeratorPolynomial_le
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    (burgessPrimeNumeratorPolynomial p B r uv).natDegree ≤ r := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold burgessPrimeNumeratorPolynomial
  calc
    (∏ i : Fin r, (Polynomial.X + Polynomial.C
        ((((uv.1 i).1 + 1 : ℕ)) : ZMod p))).natDegree ≤
        ∑ i : Fin r, (Polynomial.X + Polynomial.C
          ((((uv.1 i).1 + 1 : ℕ)) : ZMod p)).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ = r := by
      simp only [Polynomial.natDegree_X_add_C, sum_const,
        card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      norm_num

/-- The denominator polynomial likewise has degree at most `r`. -/
theorem natDegree_burgessPrimeDenominatorPolynomial_le
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    (burgessPrimeDenominatorPolynomial p B r uv).natDegree ≤ r := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold burgessPrimeDenominatorPolynomial
  calc
    (∏ i : Fin r, (Polynomial.X + Polynomial.C
        ((((uv.2 i).1 + 1 : ℕ)) : ZMod p))).natDegree ≤
        ∑ i : Fin r, (Polynomial.X + Polynomial.C
          ((((uv.2 i).1 + 1 : ℕ)) : ZMod p)).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ = r := by
      simp only [Polynomial.natDegree_X_add_C, sum_const,
        card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      norm_num

/-- The stationary polynomial has degree at most `2r`; this coarse bound is
already sufficient for the target constant. -/
theorem natDegree_burgessPrimeStationaryPolynomial_le
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    (burgessPrimeStationaryPolynomial p B r uv).natDegree ≤ 2 * r := by
  let F := burgessPrimeNumeratorPolynomial p B r uv
  let G := burgessPrimeDenominatorPolynomial p B r uv
  have hF : F.natDegree ≤ r :=
    natDegree_burgessPrimeNumeratorPolynomial_le p B r hp uv
  have hG : G.natDegree ≤ r :=
    natDegree_burgessPrimeDenominatorPolynomial_le p B r hp uv
  have hFd : F.derivative.natDegree ≤ r := by
    exact (Polynomial.natDegree_derivative_le F).trans
      ((Nat.sub_le _ _).trans hF)
  have hGd : G.derivative.natDegree ≤ r := by
    exact (Polynomial.natDegree_derivative_le G).trans
      ((Nat.sub_le _ _).trans hG)
  change (F.derivative * G - F * G.derivative).natDegree ≤ 2 * r
  have hbound := Polynomial.natDegree_sub_le_of_le
    (Polynomial.natDegree_mul_le_of_le hFd hG)
    (Polynomial.natDegree_mul_le_of_le hF hGd)
  simpa [two_mul] using hbound

/-- The finite root set of the stationary polynomial. -/
def burgessPrimeStationaryRoots
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) : Finset (ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact (burgessPrimeStationaryPolynomial p B r uv).roots.toFinset

/-- A nonzero stationary polynomial has at most `2r` distinct roots. -/
theorem card_burgessPrimeStationaryRoots_le
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    (burgessPrimeStationaryRoots p B r hp uv).card ≤ 2 * r := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold burgessPrimeStationaryRoots
  calc
    (burgessPrimeStationaryPolynomial p B r uv).roots.toFinset.card ≤
        (burgessPrimeStationaryPolynomial p B r uv).roots.card :=
      Multiset.toFinset_card_le _
    _ ≤ (burgessPrimeStationaryPolynomial p B r uv).natDegree :=
      Polynomial.card_roots' _
    _ ≤ 2 * r :=
      natDegree_burgessPrimeStationaryPolynomial_le p B r hp uv

/-- The stationary roots, transported to the canonical `Fin p` base-fiber
coordinates. -/
def burgessPrimeStationaryRootFibers
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) : Finset (Fin p) :=
  (burgessPrimeStationaryRoots p B r hp uv).image
    (ZMod.finEquiv p).symm

/-- Transport to canonical fibers does not increase the stationary root
count. -/
theorem card_burgessPrimeStationaryRootFibers_le
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    (burgessPrimeStationaryRootFibers p B r hp uv).card ≤ 2 * r := by
  unfold burgessPrimeStationaryRootFibers
  exact (Finset.card_image_le.trans
    (card_burgessPrimeStationaryRoots_le p B r hp uv))

/-- For a nonzero stationary polynomial, membership in the transported root
set is exactly vanishing at the represented base residue. -/
theorem mem_burgessPrimeStationaryRootFibers_iff
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (hP : burgessPrimeStationaryPolynomial p B r uv ≠ 0)
    (a : Fin p) :
    a ∈ burgessPrimeStationaryRootFibers p B r hp uv ↔
      (burgessPrimeStationaryPolynomial p B r uv).eval
        (a.1 : ZMod p) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold burgessPrimeStationaryRootFibers burgessPrimeStationaryRoots
  rw [Finset.mem_image]
  constructor
  · rintro ⟨z, hz, hza⟩
    have hzEval : (burgessPrimeStationaryPolynomial p B r uv).eval z = 0 := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP] at hz
      exact hz
    have hza' : z = (a.1 : ZMod p) := by
      have := congrArg (ZMod.finEquiv p) hza
      simpa [zmod_finEquiv_apply] using this
    simpa [hza'] using hzEval
  · intro ha
    refine ⟨(a.1 : ZMod p), ?_, ?_⟩
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
      exact ha
    · apply (ZMod.finEquiv p).injective
      simp [zmod_finEquiv_apply]

/-- Once the stationary polynomial is known to be nonzero, its root fibers
support every nonvanishing prime-square correlation fiber. -/
theorem exists_burgessPrimeSquareFiberSupport_of_stationaryPolynomial_ne_zero
    (p B r : ℕ) [NeZero p] (hp : p.Prime)
    (χ : DirichletCharacter ℂ (p ^ 2))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (hχ : DirichletCharacter.IsPrimitive χ)
    (hP : burgessPrimeStationaryPolynomial p B r uv ≠ 0) :
    ∃ S : Finset (Fin p), S.card ≤ 2 * r ∧
      ∀ a : Fin p, a ∉ S →
        burgessPrimeSquareFiberCorrelation p B r χ uv a = 0 := by
  refine ⟨burgessPrimeStationaryRootFibers p B r hp uv,
    card_burgessPrimeStationaryRootFibers_le p B r hp uv, ?_⟩
  intro a haRoot
  by_cases haSingular :
      (a.1 : ZMod p) ∈ burgessPrimeSingularBases p B r uv
  · simpa [burgessPrimeSquareFiberCorrelation] using
      sum_burgess_primeSquare_fiber_eq_zero_of_singular
        p B r hp χ uv a haSingular
  · have hN : burgessTupleNumerator uv (a.1 : ZMod p) ≠ 0 := by
      intro hzero
      exact haSingular ((mem_burgessPrimeSingularBases_iff p B r hp uv
        (a.1 : ZMod p)).2 (Or.inl hzero))
    have hD : burgessTupleDenominator uv (a.1 : ZMod p) ≠ 0 := by
      intro hzero
      exact haSingular ((mem_burgessPrimeSingularBases_iff p B r hp uv
        (a.1 : ZMod p)).2 (Or.inr hzero))
    have hEval : (burgessPrimeStationaryPolynomial p B r uv).eval
        (a.1 : ZMod p) ≠ 0 := by
      intro hzero
      exact haRoot ((mem_burgessPrimeStationaryRootFibers_iff
        p B r hp uv hP a).2 hzero)
    have hCoeff : burgessPrimeStationaryCoefficient p B r uv
        (a.1 : ZMod p) ≠ 0 := by
      intro hzero
      apply hEval
      rw [eval_burgessPrimeStationaryPolynomial_eq_mul_coefficient
        p B r hp uv (a.1 : ZMod p) hN hD, hzero, mul_zero]
    exact
      burgessPrimeSquareFiberCorrelation_eq_zero_of_not_singular_of_coefficient_ne_zero
        p B r hp χ uv a hχ haSingular hCoeff

/-- The prime-square stationary-phase support theorem is unconditional: the
selected coefficient coprime to `p` makes `F'G-FG'` nonzero, and its at most
`2r` roots support every nonvanishing fiber. -/
theorem taoPrimitivePrimeSquareFiberSupportBound :
    TaoPrimitivePrimeSquareFiberSupportBound := by
  intro p B r _ χ uv j hp hr hχ hAj hcop
  exact exists_burgessPrimeSquareFiberSupport_of_stationaryPolynomial_ne_zero
    p B r hp χ uv hχ
      (burgessPrimeStationaryPolynomial_ne_zero_of_coefficient_coprime
        p B r hp uv j hcop)

/-- The primitive prime-square coprime-coefficient Weil estimate, with no
remaining analytic hypothesis. -/
theorem taoPrimitivePrimeSquareCoprimeCoefficientWeilBound :
    TaoPrimitivePrimeSquareCoprimeCoefficientWeilBound :=
  TaoPrimitivePrimeSquareFiberSupportBound.toPrimeSquareWeil
    taoPrimitivePrimeSquareFiberSupportBound

/-- After the prime-square proof, the full cube-free composite Weil boundary
depends only on the genuinely prime-modulus Weil estimate. -/
theorem TaoPrimitivePrimeCoprimeCoefficientWeilBound.toComposite
    (hprime : TaoPrimitivePrimeCoprimeCoefficientWeilBound) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (TaoPrimitivePrimePowerCoprimeCoefficientWeilBound.ofPrimeAndPrimeSquare
    hprime taoPrimitivePrimeSquareCoprimeCoefficientWeilBound).toComposite

end

end Tao2026

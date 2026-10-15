import Dubon2026.PrimitiveRootCyclotomicContinuity
import Mathlib.NumberTheory.Cyclotomic.Gal

/-! # The real-sign action on an actual rational cyclotomic field

Over `ℚ`, irreducibility of the cyclotomic polynomial makes the power
character an equivalence from the actual Galois group to `(ZMod n)ˣ`.
The inverse image of `-1` is therefore an actual field automorphism and acts
on every primitive root by the inverse power.  Selecting it exactly for a
negative rational unit constructs the real-sign factor required by the
cyclotomic principal-product assembly.
-/
namespace Dubon2026
noncomputable section

open Polynomial IsCyclotomicExtension
open scoped Cyclotomic

/-- The actual rational cyclotomic automorphism with power character `-1`. -/
def rationalCyclotomicConjugation
    (n : ℕ) [NeZero n] (F : Type*) [Field F] [Algebra ℚ F]
    [IsCyclotomicExtension {n} ℚ F] : Gal(F/ℚ) :=
  (IsCyclotomicExtension.autEquivPow F
    (cyclotomic.irreducible_rat (NeZero.pos n))).symm (-1)

/-- The power character of the constructed conjugation is exactly `-1`,
independently of the chosen primitive root. -/
theorem rationalCyclotomicConjugation_autToPow
    (n : ℕ) [NeZero n] (F : Type*) [Field F] [Algebra ℚ F]
    [IsCyclotomicExtension {n} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    hζ.autToPow ℚ (rationalCyclotomicConjugation n F) = -1 := by
  have hc : hζ.autToPow ℚ (rationalCyclotomicConjugation n F) =
      (IsCyclotomicExtension.zeta_spec n ℚ F).autToPow ℚ
        (rationalCyclotomicConjugation n F) := by
    rw [hζ.autToPow_eq_modularCyclotomicCharacter n ℚ,
      (IsCyclotomicExtension.zeta_spec n ℚ F).autToPow_eq_modularCyclotomicCharacter n ℚ]
  rw [hc]
  change IsCyclotomicExtension.autEquivPow F
      (cyclotomic.irreducible_rat (NeZero.pos n))
        ((IsCyclotomicExtension.autEquivPow F
          (cyclotomic.irreducible_rat (NeZero.pos n))).symm (-1)) = -1
  exact MulEquiv.apply_symm_apply _ _

/-- The constructed conjugation acts on every actual primitive root by the
`-1` residue-class exponent. -/
theorem rationalCyclotomicConjugation_apply_root
    (n : ℕ) [NeZero n] (F : Type*) [Field F] [Algebra ℚ F]
    [IsCyclotomicExtension {n} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    rationalCyclotomicConjugation n F ζ =
      ζ ^ ((-1 : (ZMod n)ˣ) : ZMod n).val := by
  rw [← hζ.autToPow_spec ℚ, rationalCyclotomicConjugation_autToPow n F hζ]

/-- The unit power character selected by the actual sign of a rational unit. -/
def rationalCyclotomicRealSignUnit (n : ℕ) (q : ℚˣ) : (ZMod n)ˣ :=
  if 0 < q.val then 1 else -1

/-- The actual rational cyclotomic automorphism selected by the real sign of
a rational unit. -/
def rationalCyclotomicRealSignAut
    (n : ℕ) [NeZero n] (F : Type*) [Field F] [Algebra ℚ F]
    [IsCyclotomicExtension {n} ℚ F] (q : ℚˣ) : Gal(F/ℚ) :=
  if 0 < q.val then 1 else rationalCyclotomicConjugation n F

/-- The power character of the real-sign automorphism is exactly the sign
unit selected from the original rational value. -/
theorem rationalCyclotomicRealSignAut_autToPow
    (n : ℕ) [NeZero n] (F : Type*) [Field F] [Algebra ℚ F]
    [IsCyclotomicExtension {n} ℚ F] (q : ℚˣ)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    hζ.autToPow ℚ (rationalCyclotomicRealSignAut n F q) =
      rationalCyclotomicRealSignUnit n q := by
  by_cases hq : 0 < q.val
  · simp [rationalCyclotomicRealSignAut, rationalCyclotomicRealSignUnit, hq]
  · simp [rationalCyclotomicRealSignAut, rationalCyclotomicRealSignUnit, hq,
      rationalCyclotomicConjugation_autToPow n F hζ]

/-- The actual real-sign automorphism acts on every chosen primitive root by
the corresponding sign exponent. -/
theorem rationalCyclotomicRealSignAut_apply_root
    (n : ℕ) [NeZero n] (F : Type*) [Field F] [Algebra ℚ F]
    [IsCyclotomicExtension {n} ℚ F] (q : ℚˣ)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) :
    rationalCyclotomicRealSignAut n F q ζ =
      ζ ^ ((rationalCyclotomicRealSignUnit n q : (ZMod n)ˣ) : ZMod n).val := by
  rw [← hζ.autToPow_spec ℚ, rationalCyclotomicRealSignAut_autToPow n F q hζ]

end
end Dubon2026

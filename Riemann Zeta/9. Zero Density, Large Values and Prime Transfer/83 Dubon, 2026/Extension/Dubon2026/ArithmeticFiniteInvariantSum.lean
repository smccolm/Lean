import Dubon2026.ArithmeticPrimeInvariantSupport
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The actual finite-prime invariant sum of original arithmetic H2

Proved finite support, rather than an assumed summability condition, defines
the coherent family and its sum. The exact finite-sum evaluation below is the
map whose zero value remains the global reciprocity obligation for DUB-17.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (ha : a ≠ 0)

/-- Bundle the actual original coherent prime invariants as a finitely
supported linear family, using the proved support of each original class. -/
def rationalArithmeticPrimeH2InvariantFamily :
    ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous) →ₗ[ZMod q]
      (Nat.Primes →₀ ZMod q) where
  toFun x := Finsupp.ofSupportFinite
    (fun p => rationalArithmeticPrimeH2Invariant a q hqa p.val p.property x)
    (rationalArithmeticPrimeH2Invariant_finite_support a q hqa ha x)
  map_add' x y := by
    apply Finsupp.ext
    intro p
    exact map_add (rationalArithmeticPrimeH2Invariant a q hqa p.val p.property) x y
  map_smul' r x := by
    apply Finsupp.ext
    intro p
    exact map_smul (rationalArithmeticPrimeH2Invariant a q hqa p.val p.property) r x

/-- Sum the original coherent invariant family over its proved finite support.
This defines the genuine finite-prime sum; it does not assert reciprocity. -/
def rationalArithmeticFiniteH2InvariantSum :
    ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous) →ₗ[ZMod q] ZMod q :=
  (Finsupp.linearCombination (ZMod q) (fun _ : Nat.Primes => (1 : ZMod q))).comp
    (rationalArithmeticPrimeH2InvariantFamily a q hqa ha)

/-- The constructed sum evaluates to the sum of the literal original local
invariants over the actual support, with no unproved support premise. -/
theorem rationalArithmeticFiniteH2InvariantSum_apply
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalArithmeticFiniteH2InvariantSum a q hqa ha x =
      ∑ p ∈ (rationalArithmeticPrimeH2InvariantFamily a q hqa ha x).support,
        rationalArithmeticPrimeH2Invariant a q hqa p.val p.property x := by
  change (rationalArithmeticPrimeH2InvariantFamily a q hqa ha x).sum (fun _ t => t • (1 : ZMod q)) = _
  simp only [Finsupp.sum, smul_eq_mul, mul_one]
  rfl

end
end Dubon2026

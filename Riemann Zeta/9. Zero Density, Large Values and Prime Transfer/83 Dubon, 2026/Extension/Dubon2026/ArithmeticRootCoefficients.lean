import Dubon2026.ArithmeticCompatibleRootCoefficients

/-! # The original global cyclotomic coefficient and its compatible local values

The global scalar coefficient is identified with genuine roots in the same
unramified extension. Its action and every local image are proved compatible.
This discharges coefficient normalization before the global reciprocity and
Selmer duality step serving DUB-17; it does not assert global reciprocity.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)

/-- Use the original intermediate-field rational algebra structure. -/
local instance arithmeticRootAlgebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'

/-- Use the actual arithmetic Galois action on the original root subgroup. -/
local instance arithmeticRootAction :
    MulDistribMulAction (rationalArithmeticGaloisGroup a)
      (rootsOfUnity q (rationalUnramifiedExtension a)) :=
  galoisRootOfUnityMulDistribMulAction (K := ℚ) (Ω := rationalUnramifiedExtension a) q

/-- The genuine root representation of the original arithmetic Galois group. -/
def rationalArithmeticRootRepresentation : Rep ℤ (rationalArithmeticGaloisGroup a) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  exact galoisRootOfUnityRepresentation (K := ℚ) (Ω := U) q

/-- The original global scalar coefficient is the actual root group through
the single primitive root used to normalize all of its local images. -/
def rationalArithmeticRootCoefficientEquiv :
    coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom ≃+
    rationalArithmeticRootRepresentation a q :=
  (primitiveRootAdditiveEquiv (rationalArithmeticPrimitiveRoot_isPrimitive a q hqa)).trans
    Rep.toAdditive.symm

/-- The global coefficient identification preserves the original arithmetic
action, derived from the actual primitive-root exponent. -/
theorem rationalArithmeticRootCoefficientEquiv_equivariant
    (g : rationalArithmeticGaloisGroup a) (x : ZMod q) :
    rationalArithmeticRootCoefficientEquiv a q hqa
      ((coefficientCharacterRep
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom).ρ g x) =
      (rationalArithmeticRootRepresentation a q).ρ g
        (rationalArithmeticRootCoefficientEquiv a q hqa x) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  let hζ := rationalArithmeticPrimitiveRoot_isPrimitive a q hqa
  have hc : rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q) g =
      (hζ.autToPow ℚ g : ZMod q) := by
    have he : (rationalArithmeticCyclotomicCharacter a q hqa g : ZMod q) =
        (hζ.autToPow ℚ g : ZMod q) := by
      apply ZMod.val_injective
      apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
      exact (rationalArithmeticCyclotomicCharacter_apply_root a q hqa g hζ).symm.trans
        (hζ.autToPow_spec ℚ g).symm
    change ZMod.castHom (dvd_refl q) (ZMod q)
      (rationalArithmeticCyclotomicCharacter a q hqa g : ZMod q) = _
    simpa only [ZMod.castHom_self, RingHom.id_apply] using he
  apply Rep.toAdditive.injective
  change primitiveRootAdditiveEquiv hζ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q) g * x) =
    Additive.ofMul (g • Additive.toMul (primitiveRootAdditiveEquiv hζ x))
  rw [hc]
  exact (congrArg Additive.ofMul (primitiveRootAdditiveEquiv_galois hζ g x)).symm

/-- The same coefficient scalar has literally compatible root values under
each actual embedding used to define arithmetic restriction. -/
theorem rationalArithmeticRootCoefficientEquiv_local
    (p : ℕ) (hp : p.Prime) (x : ZMod q) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    rationalArithmeticLocalEmbedding a
      (((Additive.toMul (Rep.toAdditive
        (rationalArithmeticRootCoefficientEquiv a q hqa x)) : rootsOfUnity q U) : Uˣ) : U) =
      (((Additive.toMul (Rep.toAdditive
        (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp x)) :
          rootsOfUnity q (rationalPrimeLocalClosure p hp)) :
            (rationalPrimeLocalClosure p hp)ˣ) : rationalPrimeLocalClosure p hp) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  exact (congrArg (rationalArithmeticLocalEmbedding a)
    (primitiveRootAdditiveEquiv_apply
      (rationalArithmeticPrimitiveRoot_isPrimitive a q hqa) x)).trans
        (rationalArithmeticLocalRootCoefficientEquiv_compatible a q hqa p hp x).symm

end
end Dubon2026

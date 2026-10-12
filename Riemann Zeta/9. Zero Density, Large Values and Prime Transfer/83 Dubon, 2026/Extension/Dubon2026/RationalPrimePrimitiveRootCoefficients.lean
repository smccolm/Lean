import Dubon2026.RationalPrimeCyclotomicH2Scalar

/-! # Actual local cyclotomic coefficients with a specified genuine primitive root

Local perfectness allows any genuine root identification. Global reciprocity
requires the image of the same global root at every place. This original-object
coefficient construction supplies that choice without replacing the arithmetic
character, and is used in DUB-17's coherent global-local invariant maps.
-/

namespace Dubon2026
noncomputable section

variable (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  {ζ : rationalPrimeLocalClosure p hp} (hζ : IsPrimitiveRoot ζ q)

/-- The actual local cyclotomic coefficient character gives the exponent
on every original primitive root, including a transported global root. -/
theorem rationalPrimeCyclotomicCoefficientCharacter_primitive
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) :
    rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q) g =
      (hζ.autToPow (rationalPrimeLocalField p hp) g : ZMod q) := by
  have hc : (rationalPrimeCyclotomicCharacter p hp q g : ZMod q) =
      (hζ.autToPow (rationalPrimeLocalField p hp) g : ZMod q) := by
    apply ZMod.val_injective
    apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    exact (rationalPrimeCyclotomicCharacter_apply_root p hp q g hζ).symm.trans
      (hζ.autToPow_spec (rationalPrimeLocalField p hp) g).symm
  change ZMod.castHom (dvd_refl q) (ZMod q)
    (rationalPrimeCyclotomicCharacter p hp q g : ZMod q) = _
  simpa only [ZMod.castHom_self, RingHom.id_apply] using hc

/-- Identify the original scalar cyclotomic coefficient with its genuine
root-of-unity representation using the specified actual primitive root. -/
def rationalPrimePrimitiveRootCoefficientEquiv :
    coefficientCharacterRep
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom ≃+
    galoisRootOfUnityRepresentation
      (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q :=
  (primitiveRootAdditiveEquiv hζ).trans Rep.toAdditive.symm

/-- The specified root identification keeps the original arithmetic Galois
action; no independently supplied equivariance condition is retained. -/
theorem rationalPrimePrimitiveRootCoefficientEquiv_equivariant
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) (x : ZMod q) :
    rationalPrimePrimitiveRootCoefficientEquiv p hp q hζ
      ((coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom).ρ g x) =
      (galoisRootOfUnityRepresentation
        (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q).ρ g
        (rationalPrimePrimitiveRootCoefficientEquiv p hp q hζ x) := by
  apply Rep.toAdditive.injective
  change primitiveRootAdditiveEquiv hζ
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q) g * x) =
    Additive.ofMul (g • Additive.toMul (primitiveRootAdditiveEquiv hζ x))
  rw [rationalPrimeCyclotomicCoefficientCharacter_primitive p hp q hζ]
  exact (congrArg Additive.ofMul (primitiveRootAdditiveEquiv_galois hζ g x)).symm

/-- On the original coefficient value, the specified identification is the
literal power of that same primitive root, retaining normalization data. -/
theorem rationalPrimePrimitiveRootCoefficientEquiv_apply (x : ZMod q) :
    (((Additive.toMul (Rep.toAdditive
      (rationalPrimePrimitiveRootCoefficientEquiv p hp q hζ x)) :
        rootsOfUnity q (rationalPrimeLocalClosure p hp)) : (rationalPrimeLocalClosure p hp)ˣ) :
        rationalPrimeLocalClosure p hp) = ζ ^ x.val :=
  primitiveRootAdditiveEquiv_apply hζ x

end
end Dubon2026

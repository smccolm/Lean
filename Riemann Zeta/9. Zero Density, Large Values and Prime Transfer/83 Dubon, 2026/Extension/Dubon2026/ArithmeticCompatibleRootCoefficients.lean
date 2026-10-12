import Dubon2026.RationalPrimePrimitiveRootCoefficients
import Dubon2026.ArithmeticCyclotomicRestriction

/-! # One original global primitive root and its actual local coefficient maps

Choose the root already proved to lie in the original arithmetic extension,
then use the exact embedding defining arithmetic restriction at every prime.
The resulting local coefficient identifications have proved arithmetic action
and literal compatible values. This is the normalization dependency before
the global sum-of-local-invariants theorem in DUB-17's Selmer route.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)

/-- The actual primitive root in the original arithmetic extension supplied
by the proved unramified-union cyclotomic inclusion. -/
def rationalArithmeticPrimitiveRoot : rationalUnramifiedExtension a :=
  Classical.choose (originalQUnramifiedUnion_exists_primitiveRoot
    (Ω := AlgebraicClosure ℚ) a q hqa)

/-- The chosen original arithmetic root is primitive of the required order. -/
theorem rationalArithmeticPrimitiveRoot_isPrimitive :
    IsPrimitiveRoot (rationalArithmeticPrimitiveRoot a q hqa) q :=
  Classical.choose_spec (originalQUnramifiedUnion_exists_primitiveRoot
    (Ω := AlgebraicClosure ℚ) a q hqa)

variable (p : ℕ) (hp : p.Prime)

/-- The local root is the image of that same global root under the exact
embedding used by the original arithmetic restriction, at this actual prime. -/
def rationalArithmeticLocalPrimitiveRoot : rationalPrimeLocalClosure p hp := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  exact rationalArithmeticLocalEmbedding a (rationalArithmeticPrimitiveRoot a q hqa)

/-- Injectivity of the actual arithmetic embedding proves the local image
is primitive; no local root compatibility hypothesis is introduced. -/
theorem rationalArithmeticLocalPrimitiveRoot_isPrimitive :
    IsPrimitiveRoot (rationalArithmeticLocalPrimitiveRoot a q hqa p hp) q := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  exact (rationalArithmeticPrimitiveRoot_isPrimitive a q hqa).map_of_injective
    (rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a).injective

/-- The original local coefficient identification uses the image of the
same chosen global root, while retaining the actual local arithmetic character. -/
def rationalArithmeticLocalRootCoefficientEquiv :
    coefficientCharacterRep
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom ≃+
    galoisRootOfUnityRepresentation
      (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q :=
  rationalPrimePrimitiveRootCoefficientEquiv p hp q
    (rationalArithmeticLocalPrimitiveRoot_isPrimitive a q hqa p hp)

/-- The coherently chosen local root identification intertwines the exact
original arithmetic character action with the actual local root action. -/
theorem rationalArithmeticLocalRootCoefficientEquiv_equivariant
    (g : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp)) (x : ZMod q) :
    rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp
      ((coefficientCharacterRep
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom).ρ g x) =
      (galoisRootOfUnityRepresentation
        (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q).ρ g
        (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp x) :=
  rationalPrimePrimitiveRootCoefficientEquiv_equivariant p hp q
    (rationalArithmeticLocalPrimitiveRoot_isPrimitive a q hqa p hp) g x

/-- Every scalar value is sent to the image of its original global root
power under the exact arithmetic embedding; this is literal compatibility,
not merely equality of cyclotomic characters. -/
theorem rationalArithmeticLocalRootCoefficientEquiv_compatible (x : ZMod q) :
    let U := rationalUnramifiedExtension a
    letI : Algebra ℚ U := U.algebra'
    (((Additive.toMul (Rep.toAdditive
      (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp x)) :
        rootsOfUnity q (rationalPrimeLocalClosure p hp)) : (rationalPrimeLocalClosure p hp)ˣ) :
        rationalPrimeLocalClosure p hp) =
      rationalArithmeticLocalEmbedding a ((rationalArithmeticPrimitiveRoot a q hqa) ^ x.val) := by
  let U := rationalUnramifiedExtension a
  letI : Algebra ℚ U := U.algebra'
  exact (rationalPrimePrimitiveRootCoefficientEquiv_apply p hp q
    (rationalArithmeticLocalPrimitiveRoot_isPrimitive a q hqa p hp) x).trans
      (map_pow (rationalArithmeticLocalEmbedding a) (rationalArithmeticPrimitiveRoot a q hqa) x.val).symm

end
end Dubon2026

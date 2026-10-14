import Dubon2026.WittCyclotomicChangedPrimitive
import Dubon2026.WittCyclotomicFractionField
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Norm.Basic

/-! # The minimal polynomial of the actual changed cyclotomic point

The proved primitive-point equation and Eisenstein criterion identify its
minimal polynomial over the actual Witt fraction field. Equal degrees
then prove that this evaluated point generates the original cyclotomic
fraction field. These are the precise prerequisites for the field norm in
DUB-17's auxiliary-uniformizer construction.
-/
namespace Dubon2026
noncomputable section
open Polynomial
attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootFaithful
  wittCyclotomicFieldAlgebra wittCyclotomicFieldTower wittCyclotomicFieldFinite

/-- The actual changed point embedded in the original cyclotomic fraction field. -/
def wittCyclotomicChangedFieldPoint (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n : ℕ) : wittCyclotomicField p n :=
  algebraMap (wittCyclotomicRootAlgebra p n) _ (wittCyclotomicChangedPoint p u n)

/-- Multiplication by the actual unit leaves the Witt prime a prime element. -/
theorem primeWittChangedUniformizer_prime (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    Prime (u.val * p) :=
  prime_mul_iff.mpr (Or.inr ⟨u.isUnit, (WittVector.irreducible p).prime⟩)

/-- The genuine changed primitive polynomial remains irreducible over the actual Witt fraction field. -/
theorem wittCyclotomicChangedPolynomial_irreducible (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n : ℕ) :
    Irreducible ((primeChangedPrimitivePolynomial p (u.val * p) n).map
      (algebraMap _ (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))))) :=
  (primeChangedPrimitivePolynomial_monic p (u.val * p) n).irreducible_iff_irreducible_map_fraction_map.mp
    (primeChangedPrimitivePolynomial_irreducible p (u.val * p) (primeWittChangedUniformizer_prime p u) n)

/-- The actual field point is a root of the original changed primitive polynomial over the coefficient field. -/
theorem wittCyclotomicChangedFieldPoint_aeval (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) (ha : ¬p ∣ a) :
    aeval (wittCyclotomicChangedFieldPoint p u n)
      ((primeChangedPrimitivePolynomial p (u.val * p) n).map
        (algebraMap _ (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))))) = 0 := by
  rw [aeval_map_algebraMap]
  change aeval ((IsScalarTower.toAlgHom (WittVector p (AlgebraicClosure (ZMod p)))
    (wittCyclotomicRootAlgebra p n) (wittCyclotomicField p n))
      (wittCyclotomicChangedPoint p u n)) _ = 0
  rw [aeval_algHom_apply]
  change algebraMap (wittCyclotomicRootAlgebra p n) (wittCyclotomicField p n)
    ((primeChangedPrimitivePolynomial p (u.val * p) n).eval₂
      (algebraMap _ (wittCyclotomicRootAlgebra p n)) (wittCyclotomicChangedPoint p u n)) = 0
  rw [wittCyclotomicChangedPoint_primitivePolynomial p u n a hu ha, map_zero]

/-- The exact minimal polynomial of the constructed field point is the changed primitive polynomial. -/
theorem wittCyclotomicChangedFieldPoint_minpoly (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) (ha : ¬p ∣ a) :
    minpoly (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
      (wittCyclotomicChangedFieldPoint p u n) =
      (primeChangedPrimitivePolynomial p (u.val * p) n).map
        (algebraMap _ (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))) := by
  have h := minpoly.eq_of_irreducible (wittCyclotomicChangedPolynomial_irreducible p u n)
    (wittCyclotomicChangedFieldPoint_aeval p u n a hu ha)
  rw [((primeChangedPrimitivePolynomial_monic p (u.val * p) n).map _).leadingCoeff,
    inv_one, Polynomial.C_1, mul_one] at h
  exact h.symm

/-- The evaluated changed point generates the whole original cyclotomic fraction field. -/
theorem wittCyclotomicChangedFieldPoint_adjoin (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) (ha : ¬p ∣ a) :
    IntermediateField.adjoin (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
      ({wittCyclotomicChangedFieldPoint p u n} : Set (wittCyclotomicField p n)) = ⊤ := by
  apply (Field.primitive_element_iff_minpoly_natDegree_eq _ _).mpr
  rw [wittCyclotomicChangedFieldPoint_minpoly p u n a hu ha,
    (primeChangedPrimitivePolynomial_monic p (u.val * p) n).natDegree_map,
    primeChangedPrimitivePolynomial_natDegree, (wittCyclotomicField_finrank_and_finite p n).1]

end
end Dubon2026

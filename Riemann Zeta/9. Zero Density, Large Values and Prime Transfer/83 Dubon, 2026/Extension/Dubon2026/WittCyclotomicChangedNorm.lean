import Dubon2026.WittCyclotomicChangedMinpoly
import Mathlib.RingTheory.Adjoin.PowerBasis

/-! # Exact norm of the actual evaluated changed point

Construct its power basis from the proved minimal polynomial and field
generation, then use the existing algebraic norm formula. The negative
of the actual changed point has norm exactly the changed uniformizer up.
This removes the completed-coefficient norm assumption on DUB-17's route;
descent to the actual original local auxiliary field remains separate.
-/
namespace Dubon2026
noncomputable section
open Polynomial
attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootFaithful
  wittCyclotomicFieldAlgebra wittCyclotomicFieldTower wittCyclotomicFieldFinite

/-- The actual evaluated point supplies a power basis of the original cyclotomic field. -/
def wittCyclotomicChangedPowerBasis (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) (ha : ¬p ∣ a) :
    PowerBasis (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) (wittCyclotomicField p n) := by
  have hi : IsIntegral (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
      (wittCyclotomicChangedFieldPoint p u n) :=
    ⟨_, (primeChangedPrimitivePolynomial_monic p (u.val * p) n).map _,
      wittCyclotomicChangedFieldPoint_aeval p u n a hu ha⟩
  apply PowerBasis.ofAdjoinEqTop hi
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic,
    wittCyclotomicChangedFieldPoint_adjoin p u n a hu ha, IntermediateField.top_toSubalgebra]

/-- This power basis has exactly the actual evaluated point as its generator. -/
@[simp]
theorem wittCyclotomicChangedPowerBasis_gen (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) (ha : ¬p ∣ a) :
    (wittCyclotomicChangedPowerBasis p u n a hu ha).gen = wittCyclotomicChangedFieldPoint p u n :=
  PowerBasis.ofAdjoinEqTop_gen _ _

/-- The negative actual point has norm exactly the original changed uniformizer. -/
theorem wittCyclotomicChangedFieldPoint_norm_neg (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) (ha : ¬p ∣ a) :
    Algebra.norm (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
      (-wittCyclotomicChangedFieldPoint p u n) =
      algebraMap _ (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) (u.val * p) := by
  let W := WittVector p (AlgebraicClosure (ZMod p))
  let F := FractionRing W
  let S := wittCyclotomicField p n
  let b := wittCyclotomicChangedPowerBasis p u n a hu ha
  have hb : b.gen = wittCyclotomicChangedFieldPoint p u n := wittCyclotomicChangedPowerBasis_gen p u n a hu ha
  have hnorm := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly b
  rw [hb, wittCyclotomicChangedFieldPoint_minpoly p u n a hu ha,
    Polynomial.coeff_map, primeChangedPrimitivePolynomial_coeff_zero] at hnorm
  have hneg : Algebra.norm F (-1 : S) = (-1 : F) ^ b.dim := by
    rw [show (-1 : S) = algebraMap F S (-1) by simp,
      Algebra.norm_algebraMap, b.finrank]
  rw [show -wittCyclotomicChangedFieldPoint p u n =
    (-1 : S) * wittCyclotomicChangedFieldPoint p u n by ring,
    map_mul, hneg, hnorm, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

end
end Dubon2026

import Dubon2026.WittCyclotomicPrimitiveRoot
import Dubon2026.MonicRootFractionDegree
import Dubon2026.OriginalFractionScalarAlgebra
import Dubon2026.AdjoinRootFractionGeneration

/-! # The actual Witt cyclotomic fraction field

Reuse the original monic-root fraction-degree theorem to construct the
actual finite cyclotomic field over the Witt fraction field. Its degree is
derived from the original shifted polynomial. This supplies the degree
comparison for DUB-17's evaluated changed point and its exact field norm.
-/
namespace Dubon2026
noncomputable section
attribute [local instance] wittCyclotomicRootDomain

/-- The actual fraction field of the cyclotomic integral root algebra. -/
abbrev wittCyclotomicField (p : ℕ) [Fact p.Prime] (n : ℕ) :=
  FractionRing (wittCyclotomicRootAlgebra p n)

/-- The original coefficient action on the actual root algebra is faithful. -/
local instance wittCyclotomicRootFaithful (p : ℕ) [Fact p.Prime] (n : ℕ) :
    FaithfulSMul (WittVector p (AlgebraicClosure (ZMod p))) (wittCyclotomicRootAlgebra p n) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (wittCyclotomicRoot_coefficient_injective p n)

/-- The actual cyclotomic field carries the induced Witt fraction-field algebra. -/
local instance wittCyclotomicFieldAlgebra (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Algebra (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) (wittCyclotomicField p n) :=
  originalFractionScalarAlgebra (WittVector p (AlgebraicClosure (ZMod p))) _ _

/-- The fraction-field action extends the original Witt coefficient action. -/
local instance wittCyclotomicFieldTower (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsScalarTower (WittVector p (AlgebraicClosure (ZMod p)))
      (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) (wittCyclotomicField p n) :=
  originalFractionScalarAlgebra_tower (WittVector p (AlgebraicClosure (ZMod p)))
    (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) (wittCyclotomicField p n)

/-- The actual cyclotomic field has exactly the degree of the original primitive polynomial. -/
theorem wittCyclotomicField_finrank_and_finite (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Module.finrank (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
      (wittCyclotomicField p n) = (p - 1) * p ^ n ∧
    FiniteDimensional (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
      (wittCyclotomicField p n) := by
  have h := monicRootFraction_finrank_and_finite
    (WittVector p (AlgebraicClosure (ZMod p)))
    (FractionRing (WittVector p (AlgebraicClosure (ZMod p)))) (wittCyclotomicField p n)
    (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n)
    (primePowerShiftedCyclotomic_monic _ p n) (by
      rw [primePowerShiftedCyclotomic_natDegree]
      exact Nat.mul_pos (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
        (pow_pos (Fact.out : p.Prime).pos n))
  simpa only [primePowerShiftedCyclotomic_natDegree] using h

/-- The original cyclotomic field is finite dimensional, as proved from its root algebra. -/
local instance wittCyclotomicFieldFinite (p : ℕ) [Fact p.Prime] (n : ℕ) :
    FiniteDimensional (FractionRing (WittVector p (AlgebraicClosure (ZMod p))))
      (wittCyclotomicField p n) := (wittCyclotomicField_finrank_and_finite p n).2

end
end Dubon2026

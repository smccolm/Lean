import Dubon2026.WittCyclotomicEvaluation
import Dubon2026.WittCyclotomicPowerAction

/-! # Actual continuous coefficient Frobenius on the cyclotomic root algebra

The defining polynomial has natural coefficients, so actual Witt Frobenius
extends while fixing the original cyclotomic root. Every ring endomorphism
preserves the original prime-adic ideal and is continuous. These concrete
facts justify semilinear evaluation for DUB-17's inverse-unit diagonal action.
-/
namespace Dubon2026
noncomputable section
open Polynomial
attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootWithIdeal
  wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space

/-- Actual Witt coefficient Frobenius extends to the original cyclotomic root algebra. -/
def wittCyclotomicCoefficientFrobenius (p : ℕ) [Fact p.Prime] (n : ℕ) :
    wittCyclotomicRootAlgebra p n ≃+* wittCyclotomicRootAlgebra p n :=
  AdjoinRoot.mapRingEquiv (WittVector.frobeniusEquiv p (AlgebraicClosure (ZMod p))) _ _ (by
    apply Associated.of_eq
    simp only [primePowerShiftedCyclotomic, Polynomial.map_comp, Polynomial.map_cyclotomic,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_one])

/-- The original cyclotomic translated root is fixed by coefficient Frobenius. -/
theorem wittCyclotomicCoefficientFrobenius_root (p : ℕ) [Fact p.Prime] (n : ℕ) :
    wittCyclotomicCoefficientFrobenius p n
      (AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n)) =
      AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n) := by
  simp only [wittCyclotomicCoefficientFrobenius, AdjoinRoot.coe_mapRingEquiv, AdjoinRoot.map_root]

/-- On the literal Witt coefficients this automorphism is the original Witt Frobenius. -/
theorem wittCyclotomicCoefficientFrobenius_coefficient (p : ℕ) [Fact p.Prime] (n : ℕ)
    (x : WittVector p (AlgebraicClosure (ZMod p))) :
    wittCyclotomicCoefficientFrobenius p n (algebraMap _ (wittCyclotomicRootAlgebra p n) x) =
      algebraMap _ (wittCyclotomicRootAlgebra p n) (WittVector.frobenius x) := by
  change AdjoinRoot.mapRingEquiv _ _ _ _ (AdjoinRoot.of _ x) = _
  simp only [AdjoinRoot.coe_mapRingEquiv, AdjoinRoot.map_of]
  rfl

/-- Every actual ring endomorphism of this root algebra is continuous for its original prime-adic topology. -/
theorem wittCyclotomicRootHom_continuous (p : ℕ) [Fact p.Prime] (n : ℕ)
    (f : wittCyclotomicRootAlgebra p n →+* wittCyclotomicRootAlgebra p n) : Continuous f := by
  apply (WithIdeal.uniformContinuous_of_map_le (f := f) ?_).continuous
  change ((Ideal.span {(p : WittVector p (AlgebraicClosure (ZMod p)))}).map
    (algebraMap _ (wittCyclotomicRootAlgebra p n))).map f ≤
    (Ideal.span {(p : WittVector p (AlgebraicClosure (ZMod p)))}).map
      (algebraMap _ (wittCyclotomicRootAlgebra p n))
  rw [Ideal.map_map]
  simp only [Ideal.map_span, Set.image_singleton, RingHom.comp_apply, map_natCast]
  exact le_rfl

end
end Dubon2026

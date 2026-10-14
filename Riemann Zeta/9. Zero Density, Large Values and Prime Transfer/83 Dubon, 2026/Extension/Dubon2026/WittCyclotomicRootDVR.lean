import Dubon2026.WittCyclotomicFractionField
import Dubon2026.MonicEisensteinRootDVR

/-! # The genuine cyclotomic integral root ring and its uniformizer

Apply the fully proved Eisenstein root-DVR theorem to the actual Witt
cyclotomic root algebra. Its literal translated root generates its
maximal ideal and is irreducible. This supplies the concrete valuation
ring required to compare ramification of DUB-17's auxiliary compositum.
-/
namespace Dubon2026
noncomputable section
attribute [local instance] wittCyclotomicRootDomain

/-- The actual Witt cyclotomic root algebra is a genuine discrete valuation ring. -/
local instance wittCyclotomicRootDVR (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsDiscreteValuationRing (wittCyclotomicRootAlgebra p n) := by
  apply monic_eisenstein_adjoinRoot_dvr _ (primePowerShiftedCyclotomic_monic _ p n) _
    (p : WittVector p (AlgebraicClosure (ZMod p))) (WittVector.irreducible p).prime
    (primePowerShiftedCyclotomic_coeff_zero _ p n) (wittCyclotomicPolynomial_isEisensteinAt p n)
  rw [primePowerShiftedCyclotomic_natDegree]
  exact Nat.mul_pos (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
    (pow_pos (Fact.out : p.Prime).pos n)

/-- The actual translated cyclotomic root generates the maximal ideal of the original root algebra. -/
theorem wittCyclotomicRoot_maximalIdeal (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsLocalRing.maximalIdeal (wittCyclotomicRootAlgebra p n) =
      Ideal.span {AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n)} := by
  symm
  exact IsLocalRing.eq_maximalIdeal (prime_constant_adjoinRoot_root_maximal _
    (p : WittVector p (AlgebraicClosure (ZMod p))) (WittVector.irreducible p).prime
    (primePowerShiftedCyclotomic_coeff_zero _ p n))

/-- The actual translated cyclotomic root is irreducible, hence a genuine uniformizer. -/
theorem wittCyclotomicRoot_irreducible (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Irreducible (AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n)) := by
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (wittCyclotomicRoot_maximalIdeal p n)

end
end Dubon2026

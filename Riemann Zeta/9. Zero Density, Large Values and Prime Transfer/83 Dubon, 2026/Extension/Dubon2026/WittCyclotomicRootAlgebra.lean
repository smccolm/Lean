import Dubon2026.PrimePowerCyclotomicEisenstein
import Dubon2026.PrimeWittFrobeniusRotation
import Dubon2026.FiniteBasisAdicCompleteness
import Mathlib.RingTheory.WittVector.Complete

/-! # The actual finite complete Witt cyclotomic root algebra

Use the translated cyclotomic polynomial and the existing monic-root
completeness theorem. The actual prime remains irreducible in Witt vectors,
so Eisenstein proves the root algebra is a domain. Its root has a power
in the original prime ideal, giving the topological nilpotence needed to
evaluate DUB-17's actual semilinear series and its inverse.
-/
namespace Dubon2026
noncomputable section
open Polynomial
variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- The actual Witt cyclotomic polynomial is Eisenstein at the original prime. -/
theorem wittCyclotomicPolynomial_isEisensteinAt :
    (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n).IsEisensteinAt
      (Ideal.span {(p : WittVector p (AlgebraicClosure (ZMod p)))}) :=
  primePowerShiftedCyclotomic_isEisensteinAt _ p (WittVector.irreducible p).prime n

/-- Eisenstein proves irreducibility over the actual Witt coefficients. -/
theorem wittCyclotomicPolynomial_irreducible :
    Irreducible (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n) := by
  apply (wittCyclotomicPolynomial_isEisensteinAt p n).irreducible
    ((Ideal.span_singleton_prime (WittVector.p_nonzero p _)).mpr (WittVector.irreducible p).prime)
    (primePowerShiftedCyclotomic_monic _ p n).isPrimitive
  rw [primePowerShiftedCyclotomic_natDegree]
  exact Nat.mul_pos (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
    (pow_pos (Fact.out : p.Prime).pos n)

/-- The actual root algebra of the shifted prime-power cyclotomic polynomial. -/
abbrev wittCyclotomicRootAlgebra :=
  AdjoinRoot (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n)

/-- This actual root algebra is an integral domain, derived by Eisenstein. -/
local instance wittCyclotomicRootDomain : IsDomain (wittCyclotomicRootAlgebra p n) :=
  AdjoinRoot.isDomain_of_prime (wittCyclotomicPolynomial_irreducible p n).prime

/-- Its original Witt algebra is finite by the actual monic power basis. -/
local instance wittCyclotomicRootFinite :
    Module.Finite (WittVector p (AlgebraicClosure (ZMod p))) (wittCyclotomicRootAlgebra p n) :=
  (primePowerShiftedCyclotomic_monic _ p n).finite_adjoinRoot

/-- The actual integral root algebra is complete for the original prime ideal. -/
theorem wittCyclotomicRoot_isAdicComplete :
    IsAdicComplete ((Ideal.span {(p : WittVector p (AlgebraicClosure (ZMod p)))}).map
      (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (wittCyclotomicRootAlgebra p n)))
      (wittCyclotomicRootAlgebra p n) :=
  monic_adjoinRoot_isAdicComplete _ _ (primePowerShiftedCyclotomic_monic _ p n)

/-- A positive power of the actual cyclotomic root belongs to the original prime ideal. -/
theorem wittCyclotomicRoot_pow_mem_prime :
    (AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n)) ^
        ((p - 1) * p ^ n) ∈
      (Ideal.span {(p : WittVector p (AlgebraicClosure (ZMod p)))}).map
        (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (wittCyclotomicRootAlgebra p n)) := by
  let f := primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n
  have hweak : f.IsWeaklyEisensteinAt (Ideal.span {(p : WittVector p (AlgebraicClosure (ZMod p)))}) :=
    ⟨(wittCyclotomicPolynomial_isEisensteinAt p n).mem⟩
  apply hweak.pow_natDegree_le_of_aeval_zero_of_monic_mem_map (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
    (primePowerShiftedCyclotomic_monic _ p n)
  rw [(primePowerShiftedCyclotomic_monic _ p n).natDegree_map,
    primePowerShiftedCyclotomic_natDegree]

end
end Dubon2026

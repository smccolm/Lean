import Dubon2026.WittCyclotomicPrimitiveRoot

/-! # Actual power actions on the cyclotomic integral root algebra

A natural exponent prime to the level acts on the original cyclotomic
root. Prove this on the actual quotient ring so the action can be combined
with coefficient Frobenius and compared with convergent evaluation.
This supplies the inverse-unit diagonal action needed for DUB-17 descent.
-/
namespace Dubon2026
noncomputable section
open Polynomial
attribute [local instance] wittCyclotomicRootDomain

/-- The actual power of the primitive root gives a root of the defining shifted polynomial. -/
theorem wittCyclotomicPowerRoot_aeval (p : ℕ) [Fact p.Prime] (n b : ℕ)
    (hb : b.Coprime (p ^ (n + 1))) :
    aeval ((wittCyclotomicPrimitiveRoot p n) ^ b - 1)
      (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n) = 0 := by
  change Polynomial.eval₂
    (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (wittCyclotomicRootAlgebra p n))
    ((wittCyclotomicPrimitiveRoot p n) ^ b - 1)
    ((cyclotomic (p ^ (n + 1)) (WittVector p (AlgebraicClosure (ZMod p)))).comp (X + 1)) = 0
  rw [Polynomial.eval₂_comp]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_one, sub_add_cancel]
  rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact ((wittCyclotomicPrimitiveRoot_isPrimitive p n).pow_of_coprime b hb).isRoot_cyclotomic
    (pow_pos (Fact.out : p.Prime).pos (n + 1))

/-- The original quotient-ring power action fixes Witt coefficients and sends the primitive root to its b-th power. -/
def wittCyclotomicPowerHom (p : ℕ) [Fact p.Prime] (n b : ℕ)
    (hb : b.Coprime (p ^ (n + 1))) :
    wittCyclotomicRootAlgebra p n →ₐ[WittVector p (AlgebraicClosure (ZMod p))]
      wittCyclotomicRootAlgebra p n :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) ((wittCyclotomicPrimitiveRoot p n) ^ b - 1)
    (wittCyclotomicPowerRoot_aeval p n b hb)

/-- The actual power action has its specified value at the original translated root. -/
theorem wittCyclotomicPowerHom_root (p : ℕ) [Fact p.Prime] (n b : ℕ)
    (hb : b.Coprime (p ^ (n + 1))) :
    wittCyclotomicPowerHom p n b hb
      (AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n)) =
      (wittCyclotomicPrimitiveRoot p n) ^ b - 1 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The original cyclotomic root is sent to its literal b-th power. -/
theorem wittCyclotomicPowerHom_primitive (p : ℕ) [Fact p.Prime] (n b : ℕ)
    (hb : b.Coprime (p ^ (n + 1))) :
    wittCyclotomicPowerHom p n b hb (wittCyclotomicPrimitiveRoot p n) =
      (wittCyclotomicPrimitiveRoot p n) ^ b := by
  rw [wittCyclotomicPrimitiveRoot, map_add, map_one, wittCyclotomicPowerHom_root,
    ← add_sub_assoc, add_sub_cancel_left]
  rfl

/-- Inverse exponents modulo the exact level induce inverse actual ring actions. -/
theorem wittCyclotomicPowerHom_comp_eq_id (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)]) :
    (wittCyclotomicPowerHom p n a ha).comp (wittCyclotomicPowerHom p n b hb) = AlgHom.id _ _ := by
  apply AdjoinRoot.algHom_ext
  rw [AlgHom.comp_apply, wittCyclotomicPowerHom_root, map_sub, map_pow,
    wittCyclotomicPowerHom_primitive, map_one, ← pow_mul]
  have hz := pow_eq_pow_of_modEq hab (wittCyclotomicPrimitiveRoot_isPrimitive p n).pow_eq_one
  rw [hz, pow_one, wittCyclotomicPrimitiveRoot, add_sub_cancel_left]
  rfl

/-- The genuine power action is an automorphism when supplied with inverse residue exponents. -/
def wittCyclotomicPowerEquiv (p : ℕ) [Fact p.Prime] (n a b : ℕ)
    (ha : a.Coprime (p ^ (n + 1))) (hb : b.Coprime (p ^ (n + 1)))
    (hab : a * b ≡ 1 [MOD p ^ (n + 1)]) :
    wittCyclotomicRootAlgebra p n ≃ₐ[WittVector p (AlgebraicClosure (ZMod p))]
      wittCyclotomicRootAlgebra p n :=
  AlgEquiv.ofAlgHom (wittCyclotomicPowerHom p n a ha) (wittCyclotomicPowerHom p n b hb)
    (wittCyclotomicPowerHom_comp_eq_id p n a b ha hb hab)
    (wittCyclotomicPowerHom_comp_eq_id p n b a hb ha (by simpa only [Nat.mul_comm] using hab))

end
end Dubon2026

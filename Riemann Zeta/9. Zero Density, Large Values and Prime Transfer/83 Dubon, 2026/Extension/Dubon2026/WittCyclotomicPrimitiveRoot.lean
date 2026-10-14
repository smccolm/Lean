import Dubon2026.WittCyclotomicRootAlgebra
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! # The actual primitive cyclotomic root in the Witt root algebra

The actual adjoined root plus one is proved to have exact order p^(n+1).
The original prime remains nonzero by the monic root embedding. This
identifies the point used by convergent evaluation with genuine primitive
torsion, needed to prove the changed point has the required primitive
polynomial and norm on DUB-17's ramified reciprocity route.
-/
namespace Dubon2026
noncomputable section
open Polynomial
attribute [local instance] wittCyclotomicRootDomain

/-- The actual cyclotomic root obtained by undoing the defining translation. -/
def wittCyclotomicPrimitiveRoot (p : ℕ) [Fact p.Prime] (n : ℕ) : wittCyclotomicRootAlgebra p n :=
  1 + AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n)

/-- The actual Witt coefficient map into the cyclotomic root algebra is injective. -/
theorem wittCyclotomicRoot_coefficient_injective (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Function.Injective (algebraMap (WittVector p (AlgebraicClosure (ZMod p)))
      (wittCyclotomicRootAlgebra p n)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  intro h
  have hd := Polynomial.natDegree_eq_of_degree_eq_some h
  rw [primePowerShiftedCyclotomic_natDegree] at hd
  exact (Nat.ne_of_gt (Nat.mul_pos (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
    (pow_pos (Fact.out : p.Prime).pos n))) hd

/-- The displayed original root has exact order p^(n+1), rather than merely an annihilating power. -/
theorem wittCyclotomicPrimitiveRoot_isPrimitive (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsPrimitiveRoot (wittCyclotomicPrimitiveRoot p n) (p ^ (n + 1)) := by
  let W := WittVector p (AlgebraicClosure (ZMod p))
  let S := wittCyclotomicRootAlgebra p n
  let f := primePowerShiftedCyclotomic W p n
  have hpS : (p : S) ≠ 0 := by
    have h := (wittCyclotomicRoot_coefficient_injective p n).ne (WittVector.p_nonzero p _)
    simpa only [map_natCast, map_zero] using h
  haveI : NeZero ((p ^ (n + 1) : ℕ) : S) := ⟨by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ hpS⟩
  apply Polynomial.isRoot_cyclotomic_iff.mp
  have h := AdjoinRoot.eval₂_root f
  change Polynomial.eval₂ (algebraMap W S) (AdjoinRoot.root f)
    ((cyclotomic (p ^ (n + 1)) W).comp (X + 1)) = 0 at h
  rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_comp, Polynomial.map_cyclotomic] at h
  simp only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_one,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] at h
  simpa only [wittCyclotomicPrimitiveRoot, add_comm] using h

end
end Dubon2026

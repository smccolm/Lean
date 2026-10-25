import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! DUB-17/18 -> divisorial Weil reciprocity -> norm evaluation on
ramified residue fibers. The native norm is the determinant of multiplication:
nilpotent perturbations of a scalar have the required scalar-power norm,
and a product algebra has the product norm. These exact calculations are
needed for the residue-fiber decomposition, including its empty product.
Adapted from S_Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap,
S_Algebra_norm_prod and S_Algebra_norm_of_subsingleton,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026
noncomputable section

theorem algebra_norm_nilpotent_scalar {R A : Type*} [CommRing R] [IsDomain R]
    [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    {a : A} {μ : R} (h : IsNilpotent (a - algebraMap R A μ)) :
    Algebra.norm R a = μ ^ Module.finrank R A := by
  have hN : IsNilpotent (Algebra.lmul R A (a - algebraMap R A μ)) := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← map_pow, hk, map_zero]⟩
  have hN' := hN.neg
  have he : (Algebra.lmul R A) a =
      algebraMap R (Module.End R A) μ - (-(Algebra.lmul R A (a - algebraMap R A μ))) := by
    rw [sub_neg_eq_add, ← (Algebra.lmul R A).commutes μ, ← map_add]
    congr 1
    abel
  rw [Algebra.norm_apply, he, ← LinearMap.eval_charpoly,
    IsNilpotent.charpoly_eq_X_pow_finrank hN', Polynomial.eval_pow, Polynomial.eval_X]

theorem algebra_norm_product {R A B : Type*} [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] [Module.Free R A] [Module.Finite R A]
    [Module.Free R B] [Module.Finite R B] (x : A × B) :
    Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have he : Algebra.lmul R (A × B) x =
      ((Algebra.lmul R A x.1).prodMap (Algebra.lmul R B x.2) : A × B →ₗ[R] A × B) := by
    ext y <;> rfl
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, he, LinearMap.det_prodMap]

theorem algebra_norm_subsingleton {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    [Subsingleton A] (a : A) : Algebra.norm R a = 1 :=
  LinearMap.det_eq_one_of_subsingleton _

end
end Dubon2026

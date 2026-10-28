import Mathlib.RingTheory.Norm.Basic
import P2M.Util
namespace P2MW.S_Algebra_norm_prod

theorem solution {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B] (x : A × B) : Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have lmul_prod : Algebra.lmul R (A × B) x
      = ((Algebra.lmul R A x.1).prodMap (Algebra.lmul R B x.2) : A × B →ₗ[R] A × B) := by
    ext y <;> rfl
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, lmul_prod,
    LinearMap.det_prodMap]

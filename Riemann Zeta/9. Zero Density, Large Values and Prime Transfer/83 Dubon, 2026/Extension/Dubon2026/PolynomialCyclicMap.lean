import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Analysis.Complex.Basic

/-! # Exact polynomial evaluation on an original cyclic vector -/

namespace Dubon2026

noncomputable section
open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Evaluate actual operator polynomials on their original cyclic generator. -/
def polynomialCyclicMap (E : Module.End ℂ V) (v : V) : ℂ[X] →ₗ[ℂ] V where
  toFun p := aeval E p v
  map_add' p q := by rw [map_add, LinearMap.add_apply]
  map_smul' c p := by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- Original monomials evaluate to the literal original successive operator powers. -/
theorem polynomialCyclicMap_X_pow (E : Module.End ℂ V) (v : V) (n : ℕ) :
    polynomialCyclicMap E v (X ^ n) = (E ^ n) v := by
  change aeval E (X ^ n) v = _
  rw [map_pow, aeval_X]

/-- The original constant polynomial evaluates to the exact original cyclic generator. -/
theorem polynomialCyclicMap_one (E : Module.End ℂ V) (v : V) : polynomialCyclicMap E v 1 = v := by
  change aeval E 1 v = v
  rw [map_one, Module.End.one_apply]

/-- Agreement on all actual monomials determines a genuine complex-linear polynomial map. -/
theorem polynomialLinearMap_eq_of_X_pow (T S : ℂ[X] →ₗ[ℂ] V)
    (h : ∀ n : ℕ, T (X ^ n) = S (X ^ n)) : T = S := by
  apply LinearMap.ext
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, map_smul, h]

end
end Dubon2026

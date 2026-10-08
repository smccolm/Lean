import Dubon2026.PolynomialCyclicMap

/-! # Actual polynomial actions under genuine linear intertwiners -/

namespace Dubon2026

noncomputable section
open Polynomial

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A genuine linear intertwiner transports every original operator power. -/
theorem linearIntertwiner_power (T : Module.End ℂ V) (S : Module.End ℂ W)
    (u : V →ₗ[ℂ] W) (h : ∀ v, u (T v) = S (u v)) (n : ℕ) (v : V) :
    u ((T ^ n) v) = (S ^ n) (u v) := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]

/-- The exact original intertwining relation extends to every actual polynomial in the two operators. -/
theorem polynomialEnd_intertwine (T : Module.End ℂ V) (S : Module.End ℂ W)
    (u : V →ₗ[ℂ] W) (h : ∀ v, u (T v) = S (u v)) (p : ℂ[X]) (v : V) :
    u (aeval T p v) = aeval S p (u v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial]
      simp only [map_mul, map_pow, aeval_C, aeval_X, Module.End.mul_apply,
        Module.algebraMap_end_apply, map_smul, linearIntertwiner_power T S u h]

end
end Dubon2026

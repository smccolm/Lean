import Dubon2026.SourceArithmeticSupportPowers
import Dubon2026.ArithmeticSupportRepresentationLocalConjugacy
import Mathlib.LinearAlgebra.Matrix.Trace

/-! DUB-17/18 -> residual Galois association -> original local values.
The already proved conjugacy of the actual chosen local embeddings
transports Frobenius trace, determinant and inertia through the actual
arithmetic support restriction. No embedding compatibility is assumed.
-/
namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {F : Type} [CommRing F]
  (a b : 𝓞 ℚ) (hab : a ∣ b)
  (η : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) F)
  (ρ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin 2) F)
  (hcomp : ∀ g, η (rationalArithmeticSupportRestriction a b hab g) = ρ g)
  (ell : ℕ) (hell : ell.Prime)

include hcomp

/-- Actual original local Frobenius traces survive descent of arithmetic support. -/
theorem sourceArithmeticSupport_local_trace
    (g : Gal(rationalPrimeLocalClosure ell hell / rationalPrimeLocalField ell hell)) :
    Matrix.trace (η (rationalPrimeArithmeticRestriction a ell hell g)).val =
      Matrix.trace (ρ (rationalPrimeArithmeticRestriction b ell hell g)).val := by
  obtain ⟨u, hu⟩ := rationalArithmeticSupportRestriction_local_conjugacy a b hab ell hell
  rw [← hcomp, hu g, map_mul, map_mul, map_inv]
  exact (Matrix.trace_units_conj' (η u)
    (η (rationalPrimeArithmeticRestriction a ell hell g)).val).symm

/-- Actual original local Frobenius determinants survive descent of arithmetic support. -/
theorem sourceArithmeticSupport_local_det
    (g : Gal(rationalPrimeLocalClosure ell hell / rationalPrimeLocalField ell hell)) :
    Matrix.det (η (rationalPrimeArithmeticRestriction a ell hell g)).val =
      Matrix.det (ρ (rationalPrimeArithmeticRestriction b ell hell g)).val := by
  obtain ⟨u, hu⟩ := rationalArithmeticSupportRestriction_local_conjugacy a b hab ell hell
  rw [← hcomp, hu g, map_mul, map_mul, map_inv]
  exact (Matrix.det_units_conj' (η u)
    (η (rationalPrimeArithmeticRestriction a ell hell g)).val).symm

/-- Triviality on the actual original local inertia survives support descent. -/
theorem sourceArithmeticSupport_local_eq_one
    (g : Gal(rationalPrimeLocalClosure ell hell / rationalPrimeLocalField ell hell))
    (hg : ρ (rationalPrimeArithmeticRestriction b ell hell g) = 1) :
    η (rationalPrimeArithmeticRestriction a ell hell g) = 1 := by
  obtain ⟨u, hu⟩ := rationalArithmeticSupportRestriction_local_conjugacy a b hab ell hell
  rw [← hcomp, hu g, map_mul, map_mul, map_inv] at hg
  have he := congrArg (fun x => η u * x * (η u)⁻¹) hg
  simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using he

end
end Dubon2026

import Dubon2026.SourceArithmeticSupportLocalValues
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! DUB-17/18 -> actual parabolic residual representation -> original
level support. Extend the existing local trace/determinant comparison
by the characteristic polynomial and the inflation direction of
inertia triviality. The already proved actual embedding conjugacy
and native matrix conjugation identity supply both statements. -/
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

theorem sourceArithmeticSupport_local_charpoly
    (g : Gal(rationalPrimeLocalClosure ell hell/rationalPrimeLocalField ell hell)) :
    (η (rationalPrimeArithmeticRestriction a ell hell g)).val.charpoly =
      (ρ (rationalPrimeArithmeticRestriction b ell hell g)).val.charpoly := by
  have hlocal := rationalArithmeticSupportRestriction_local_conjugacy a b hab ell hell
  rcases hlocal with ⟨u, hu⟩
  have he : ρ (rationalPrimeArithmeticRestriction b ell hell g) =
      (η u)⁻¹ * η (rationalPrimeArithmeticRestriction a ell hell g) * η u := by
    calc
      ρ (rationalPrimeArithmeticRestriction b ell hell g) =
          η (rationalArithmeticSupportRestriction a b hab
            (rationalPrimeArithmeticRestriction b ell hell g)) := (hcomp _).symm
      _ = η (u⁻¹ * rationalPrimeArithmeticRestriction a ell hell g * u) := congrArg η (hu g)
      _ = _ := by rw [map_mul, map_mul, map_inv]
  have hp := congrArg (fun x : GeneralLinearGroup (Fin 2) F => x.val.charpoly) he
  simp only [Units.val_mul, GeneralLinearGroup.coe_inv] at hp
  exact (hp.trans (Matrix.charpoly_units_conj' (η u)
    (η (rationalPrimeArithmeticRestriction a ell hell g)).val)).symm

theorem sourceArithmeticSupport_local_inflate_eq_one
    (g : Gal(rationalPrimeLocalClosure ell hell/rationalPrimeLocalField ell hell))
    (hg : η (rationalPrimeArithmeticRestriction a ell hell g) = 1) :
    ρ (rationalPrimeArithmeticRestriction b ell hell g) = 1 := by
  have hlocal := rationalArithmeticSupportRestriction_local_conjugacy a b hab ell hell
  rcases hlocal with ⟨u, hu⟩
  rw [← hcomp, hu g, map_mul, map_mul, map_inv, hg, mul_one, inv_mul_cancel]

end
end Dubon2026

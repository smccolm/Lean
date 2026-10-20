import Dubon2026.GenericSingularMatrix
import Dubon2026.IntegralPolynomialSingularVanishing
import Mathlib.RingTheory.Localization.FractionRing

/-! Divisibility of the exact original induced polynomial numerator.
The generic singular coordinate domain and its actual fraction field
turn singular vanishing into membership in the original determinant
ideal. This proves divisibility over the original integral coefficient
UFD itself, without assuming a fraction-field descent certificate.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [CharZero R]

/-- An original induced polynomial with nonzero first-row weight is divisible by the original generic determinant over the original coefficient ring. -/
theorem integralInducedPolynomial_determinant_dvd {n : ℕ}
    (lam : Fin (n + 1) → ℤ) (P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) R)
    (hP : generalLinearRegularPolynomialMap R (n + 1) P ∈
      generalLinearIntegralInducedSubmodule R (n + 1) lam)
    (ha : lam (0 : Fin (n + 1)).rev ≠ 0) :
    Matrix.det (Matrix.mvPolynomialX (Fin (n + 1)) (Fin (n + 1)) R) ∣ P := by
  let S := GenericSingularCoordinate R (n + 1)
  let K := FractionRing S
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
    (genericSingularMatrix R (n + 1)).map (algebraMap S K)
  have hdet : M.det = 0 := by
    change Matrix.det ((algebraMap S K).mapMatrix (genericSingularMatrix R (n + 1))) = 0
    rw [← RingHom.map_det, genericSingularMatrix_det, map_zero]
  have hcofactor : M.adjugate 0 0 ≠ 0 := by
    have h := congrArg (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) K => B 0 0)
      ((algebraMap S K).map_adjugate (genericSingularMatrix R (n + 1)))
    intro hz
    apply genericSingularMatrix_diagonal_cofactor_ne_zero R (n + 1) 0
    apply IsFractionRing.injective S K
    rw [map_zero]
    exact h.trans hz
  have hz := generalLinearIntegralPolynomial_singular_cofactor lam P hP K ha M hdet hcofactor
  have he : MvPolynomial.aeval (fun ij : Fin (n + 1) × Fin (n + 1) => M ij.1 ij.2) =
      (IsScalarTower.toAlgHom R S K).comp
        (Ideal.Quotient.mkₐ R (genericDeterminantIdeal R (n + 1))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    rw [MvPolynomial.aeval_X]
    rfl
  rw [he] at hz
  have hzero : Ideal.Quotient.mk (genericDeterminantIdeal R (n + 1)) P = 0 := by
    apply IsFractionRing.injective S K
    simpa only [map_zero] using hz
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hzero)

end
end Dubon2026

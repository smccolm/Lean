import Dubon2026.GeneralLinearIntegralCentralWeight
import Dubon2026.PolynomialCentralWeight

/-! The actual central covariance bounds the original numerator degree.
IntegralInducedDenominatorBound supplies the uniform determinant denominator
in the fixed source weight. This module proves the degree bound without
replacing the integral induced module by a different representation.
-/

namespace Dubon2026
noncomputable section
open Matrix MvPolynomial

universe u
variable {R : Type u} [CommRing R] [IsDomain R] {n : ℕ}

/-- The source covariance of an original polynomial regular function implies its literal polynomial scaling identity. -/
theorem generalLinearIntegralPolynomial_scalar (lam : Fin n → ℤ)
    (P : MvPolynomial (Fin n × Fin n) R)
    (hP : generalLinearRegularPolynomialMap R n P ∈
      generalLinearIntegralInducedSubmodule R n lam) (u : Rˣ) :
    MvPolynomial.aeval (fun ij : Fin n × Fin n => C (u : R) * X ij) P =
      ((u ^ (∑ i, lam i) : Rˣ) : R) • P := by
  let A := GeneralLinearRegularFunctions R n
  let v : Aˣ := Units.map (algebraMap R A).toMonoidHom u
  let g := generalLinearRegularGeneric R n
  have he : (generalLinearRegularPolynomialMap R n).comp
      (MvPolynomial.aeval fun ij : Fin n × Fin n => C (u : R) * X ij) =
      (generalLinearRegularEval (GeneralLinearGroup.scalar (Fin n) v * g)).comp
        (generalLinearRegularPolynomialMap R n) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, map_mul,
      generalLinearRegularEval_X]
    change algebraMap R A (u : R) * g.val i j =
      (Matrix.diagonal (fun _ : Fin n => (v : A)) * g.val) i j
    rw [Matrix.diagonal_mul]
    rfl
  have h := generalLinearIntegralInduced_scalar lam hP A v g
  have hv : ((v ^ (∑ i, lam i) : Aˣ) : A) =
      algebraMap R A ((u ^ (∑ i, lam i) : Rˣ) : R) := by
    change (((Units.map (algebraMap R A).toMonoidHom u) ^ (∑ i, lam i) : Aˣ) : A) = _
    rw [← map_zpow]
    rfl
  rw [hv, generalLinearRegularEval_generic] at h
  apply generalLinearRegularPolynomialMap_injective R n
  rw [show generalLinearRegularPolynomialMap R n
      (MvPolynomial.aeval (fun ij : Fin n × Fin n => C (u : R) * X ij) P) =
      generalLinearRegularEval (GeneralLinearGroup.scalar (Fin n) v * g)
        (generalLinearRegularPolynomialMap R n P) from AlgHom.congr_fun he P,
    map_smul, Algebra.smul_def]
  exact h

/-- The original polynomial numerator is homogeneous of the precise source weight plus the cleared determinant degree. -/
theorem generalLinearIntegralInduced_numerator_homogeneous
    (u : Rˣ) (hu : Function.Injective (fun w : ℤ => u ^ w))
    (lam : Fin n → ℤ) (d : ℕ) (P : MvPolynomial (Fin n × Fin n) R)
    (hP : generalLinearRegularFractionMap R n d P ∈
      generalLinearIntegralInducedSubmodule R n lam) :
    P.IsHomogeneous ((∑ i, lam i) + (n : ℤ) * d).toNat := by
  have h := polynomialCentralWeight_isHomogeneous u hu P
    (∑ i, (lam i + (d : ℤ)))
    (generalLinearIntegralPolynomial_scalar (fun i => lam i + (d : ℤ)) P
      (generalLinearIntegralInduced_polynomial_numerator R n lam d P hP) u)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h

/-- The exact original numerator's degree is bounded using only the source weight and its actual determinant denominator. -/
theorem generalLinearIntegralInduced_numerator_degree_le
    (u : Rˣ) (hu : Function.Injective (fun w : ℤ => u ^ w))
    (lam : Fin n → ℤ) (d : ℕ) (P : MvPolynomial (Fin n × Fin n) R)
    (hP : generalLinearRegularFractionMap R n d P ∈
      generalLinearIntegralInducedSubmodule R n lam) :
    P.totalDegree ≤ ((∑ i, lam i) + (n : ℤ) * d).toNat :=
  (generalLinearIntegralInduced_numerator_homogeneous u hu lam d P hP).totalDegree_le

end
end Dubon2026

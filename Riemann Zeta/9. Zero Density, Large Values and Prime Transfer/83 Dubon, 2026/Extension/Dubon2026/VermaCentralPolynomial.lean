import Dubon2026.VermaPolynomialEigenline
import Dubon2026.VermaEnvelopingMaps

/-! # The genuine polynomial dependence of every original central character on highest weight -/

namespace Dubon2026

noncomputable section
open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- The actual scalar of a genuine central element on the original Verma generator is its literal constant coefficient. -/
def vermaPolynomialCentralValue (μ : R)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) : R :=
  (vermaPolynomialEnvelopingAction μ z.val 1).coeff 0

/-- The actual central scalar gives the exact original generator action, in every characteristic-zero coefficient domain. -/
theorem vermaPolynomialCentralValue_generator [IsDomain R] [CharZero R] (μ : R)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    vermaPolynomialEnvelopingAction μ z.val 1 = vermaPolynomialCentralValue μ z • (1 : R[X]) := by
  rw [smul_eq_C_mul, mul_one]
  exact vermaPolynomial_center_generator μ z

/-- The actual center commutes with multiplication by the original polynomial variable. -/
theorem vermaPolynomial_center_commutes_F (μ : R)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    Commute vermaPolynomialF (vermaPolynomialEnvelopingAction μ z.val) := by
  have hz : Commute (UniversalEnvelopingAlgebra.ι ℂ compactSl2E) z.val :=
    Subalgebra.mem_center_iff.mp z.property _
  have hh := hz.map (vermaPolynomialEnvelopingAction μ)
  rwa [vermaPolynomialEnvelopingAction_generator, vermaPolynomialLieAction_E] at hh

/-- Every original polynomial monomial has the same actual central scalar as its genuine highest generator. -/
theorem vermaPolynomialCentralValue_X_pow [IsDomain R] [CharZero R] (μ : R)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) (n : ℕ) :
    vermaPolynomialEnvelopingAction μ z.val (X ^ n) =
      vermaPolynomialCentralValue μ z • (X ^ n : R[X]) := by
  induction n with
  | zero => simpa only [pow_zero] using vermaPolynomialCentralValue_generator μ z
  | succ n ih =>
      have hc := LinearMap.congr_fun (vermaPolynomial_center_commutes_F μ z).eq (X ^ n)
      change vermaPolynomialF (vermaPolynomialEnvelopingAction μ z.val (X ^ n)) =
        vermaPolynomialEnvelopingAction μ z.val (vermaPolynomialF (X ^ n)) at hc
      rw [ih, map_smul, vermaPolynomialF_X_pow] at hc
      exact hc.symm

/-- Changing actual coefficients evaluates the scalar of every genuine central element. -/
theorem vermaPolynomialCentralValue_map {S : Type*} [CommRing S] [Algebra ℂ S]
    (φ : R →ₐ[ℂ] S) (μ : R)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    φ (vermaPolynomialCentralValue μ z) = vermaPolynomialCentralValue (φ μ) z := by
  have he := congrArg (fun p : S[X] => p.coeff 0) (vermaPolynomialEnvelopingAction_map φ μ z.val 1)
  simpa only [vermaPolynomialCentralValue, coeff_mapAlgHom_apply, map_one] using he

/-- The actual universal central polynomial is obtained by using the original polynomial variable as the Verma highest weight. -/
def vermaUniversalCentralPolynomial
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) : ℂ[X] :=
  vermaPolynomialCentralValue (X : ℂ[X]) z

/-- Evaluating the genuine universal central polynomial gives exactly the original scalar at each complex highest weight. -/
theorem vermaUniversalCentralPolynomial_aeval (μ : ℂ)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ ComplexSl2)) :
    aeval μ (vermaUniversalCentralPolynomial z) = vermaPolynomialCentralValue μ z := by
  simpa only [vermaUniversalCentralPolynomial, aeval_X] using
    vermaPolynomialCentralValue_map (aeval μ) (X : ℂ[X]) z

end
end Dubon2026

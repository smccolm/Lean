import Dubon2026.SourceCurveFixedFieldExactDerivative
import Dubon2026.SourceCoordinatePolynomialEvaluation

/-! The conjugate polynomial's derivative has the same order as the
base parameter's actual local derivative. This combines the proved
fixed-field estimate with native polynomial differentiation. Coefficient
invariance, integrality and constant-term order are explicit inputs, to be
derived for the actual inertia polynomial in the DUB-17/18 wild estimate. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential IntermediateField Polynomial
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
variable [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField] [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem polynomial_derivative_order_of_fixed_coefficients
    (Z : IntermediateField K F) (x : F) (hxZ : x ∈ Z) (hx : 0 < v.ord x)
    (hgap : ∀ z ∈ Z, v.ord x ∣ v.ord z)
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    (hDx : v.coordinateDerivation x ≠ 0)
    (f : F[X]) (hf : f.eval v.uniformizer = 0)
    (hcoeffZ : ∀ k, f.coeff k ∈ Z)
    (hcoeff : ∀ k, f.coeff k ∈ v.toValuationSubring)
    (hord : v.ord (f.coeff 0) = v.ord x) :
    f.derivative.eval v.uniformizer ≠ 0 ∧
      v.ord (f.derivative.eval v.uniformizer) = v.ord (v.coordinateDerivation x) := by
  have hconst := v.coordinateDerivation_ne_zero_and_ord_eq_of_order_gap
    Z x hxZ hx hgap hres hDx (hcoeffZ 0) hord
  have htail : v.OrdGe (v.ord (v.coordinateDerivation x) + 1)
      (∑ k ∈ Finset.range f.natDegree,
        v.uniformizer ^ (k + 1) * v.coordinateDerivation (f.coeff (k + 1))) := by
    refine OrdGe.sum _ fun k _ => ?_
    have hpow : v.OrdGe ((k : ℤ) + 1) (v.uniformizer ^ (k + 1)) := Or.inr (by
      rw [← zpow_natCast, v.ord_zpow, v.ord_uniformizer, mul_one]
      exact le_of_eq (Nat.cast_add _ _).symm)
    exact (hpow.mul (v.ordGe_coordinateDerivation_of_order_gap Z x hxZ hx hgap hres
      (hcoeffZ (k + 1)) (hcoeff (k + 1)))).mono (by omega)
  have hsum := ord_add_eq_of_ordGe hconst.1 hconst.2 htail
  have he := v.polynomial_derivative_eval_uniformizer_eq_neg_sum f hf
  rw [Finset.sum_range_succ', pow_zero, one_mul, add_comm] at he
  rw [he]
  exact ⟨neg_ne_zero.mpr hsum.1, by simpa only [ord, Valuation.map_neg] using hsum.2⟩

end
end Dubon2026.SourceCurve.Place

import Dubon2026.SourceCurveCoordinateDerivation
import Mathlib.RingTheory.Derivation.MapCoeffs

/-! Native coefficient-wise differentiation replaces the expanded
polynomial differentiation in the FLT wild different proof. This supplies
the conjugate-uniformizer polynomial identity on the DUB-17/18 chain. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential Polynomial
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
variable [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem coordinateDerivation_mapCoeffs_eval (f : F[X]) (t : F) :
    PolynomialModule.eval t (v.coordinateDerivation.mapCoeffs f) =
      ∑ k ∈ Finset.range (f.natDegree + 1), t ^ k * v.coordinateDerivation (f.coeff k) := by
  change (f.toFinsupp.mapRange v.coordinateDerivation (map_zero _)).sum
    (fun k a => t ^ k * a) = _
  rw [Finsupp.sum_mapRange_index (by simp)]
  change f.sum (fun k a => t ^ k * v.coordinateDerivation a) = _
  rw [Polynomial.sum_over_range' _ _ (f.natDegree + 1) (Nat.lt_succ_self _)]
  intro k
  simp

theorem polynomial_derivative_eval_uniformizer_eq_neg_sum (f : F[X])
    (hf : f.eval v.uniformizer = 0) :
    f.derivative.eval v.uniformizer =
      -(∑ k ∈ Finset.range (f.natDegree + 1),
        v.uniformizer ^ k * v.coordinateDerivation (f.coeff k)) := by
  have h := v.coordinateDerivation.apply_eval_eq v.uniformizer f
  rw [hf, map_zero, v.coordinateDerivation_uniformizer, smul_eq_mul, mul_one,
    v.coordinateDerivation_mapCoeffs_eval] at h
  exact eq_neg_of_add_eq_zero_right h.symm

end
end Dubon2026.SourceCurve.Place

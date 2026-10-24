import Dubon2026.SourceEllipticDivisionZeros
import Dubon2026.SourceEllipticPointIntegral
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! Integral coordinates of prime-to-residue torsion, directly from division
polynomials. The existing exact zero criterion and native leading coefficient
n² avoid a formal-group construction. This supplies the actual integral odd
quotient models needed for the DUB-17/18 modular-polynomial reduction chain. -/

namespace Dubon2026.SourceEllipticFunctionField
open Polynomial WeierstrassCurve SourceEllipticPointFormula
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L]

omit [DecidableEq L] in
/-- An element integral over a valuation subring belongs to that subring. -/
theorem mem_valuationSubring_of_integral (A : ValuationSubring L) {x : L}
    (hx : IsIntegral A x) : x ∈ A := by
  have hv : A.valuation.Integers A :=
    ⟨Subtype.val_injective, A.valuation_le_one,
      fun z hz => ⟨⟨z, A.mem_of_valuation_le_one z hz⟩, rfl⟩⟩
  exact (A.valuation_le_one_iff x).mp (hv.isIntegral_iff_v_le_one.mp hx)

/-- The actual squared division polynomial vanishes at the x-coordinate of a torsion point. -/
theorem aeval_ΨSq_eq_zero_of_nsmul (A : ValuationSubring L) (W : WeierstrassCurve A)
    {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y) (n : ℕ)
    (hn : n • WeierstrassCurve.Affine.Point.some x y h = 0) :
    aeval x (W.ΨSq (n : ℤ)) = 0 := by
  have hz := (smul_eq_zero_iff_evalEval_ψ (W.map A.subtype) h (n : ℤ)).mp
    (by simpa only [natCast_zsmul] using hn)
  have hs := evalEval_ψ_sq (W.map A.subtype) h.1 (n : ℤ)
  rw [hz, zero_pow two_ne_zero, WeierstrassCurve.map_ΨSq, eval_map] at hs
  exact hs.symm

/-- Torsion killed by a unit integer has integral x-coordinate in the original valuation ring. -/
theorem torsion_x_mem_valuationSubring (A : ValuationSubring L) (W : WeierstrassCurve A)
    {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y) (n : ℕ)
    (hn : IsUnit (n : A)) (hP : n • WeierstrassCurve.Affine.Point.some x y h = 0) :
    x ∈ A := by
  have hi := isIntegral_leadingCoeff_smul (W.ΨSq (n : ℤ)) x
    (aeval_ΨSq_eq_zero_of_nsmul A W h n hP)
  rw [W.leadingCoeff_ΨSq (by exact_mod_cast hn.ne_zero), Algebra.smul_def] at hi
  obtain ⟨u, hu⟩ := hn.pow 2
  have hu' : (u : A) = (n : A) ^ 2 := hu
  have hi' : IsIntegral A (x * algebraMap A L (u : A)) := by
    simpa only [hu', Int.cast_natCast, mul_comm] using hi
  apply mem_valuationSubring_of_integral A
  exact IsIntegral.of_mul_unit (r := (↑(u⁻¹) : A))
    (by rw [← map_mul, Units.inv_mul, map_one]) hi'

omit [DecidableEq L] in
/-- Once x is integral, the actual monic quadratic Weierstrass equation makes y integral. -/
theorem equation_y_mem_valuationSubring (A : ValuationSubring L) (W : WeierstrassCurve A)
    {x y : L} (h : (W.map A.subtype).toAffine.Equation x y) (hx : x ∈ A) : y ∈ A := by
  have hxi : IsIntegral A x := by
    exact (show IsIntegral A (algebraMap A L ⟨x, hx⟩) from isIntegral_algebraMap)
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h
  apply mem_valuationSubring_of_integral A
  refine isIntegral_quadratic_root
    (b := algebraMap A L W.a₁ * x + algebraMap A L W.a₃)
    (c := -(x ^ 3 + algebraMap A L W.a₂ * x ^ 2 + algebraMap A L W.a₄ * x +
      algebraMap A L W.a₆))
    ((isIntegral_algebraMap.mul hxi).add isIntegral_algebraMap)
    ((((hxi.pow 3).add (isIntegral_algebraMap.mul (hxi.pow 2))).add
      (isIntegral_algebraMap.mul hxi)).add isIntegral_algebraMap).neg ?_
  change y ^ 2 + (A.subtype W.a₁ * x + A.subtype W.a₃) * y +
    -(x ^ 3 + A.subtype W.a₂ * x ^ 2 + A.subtype W.a₄ * x + A.subtype W.a₆) = 0
  linear_combination h

end
end Dubon2026.SourceEllipticFunctionField

import Dubon2026.SourceEllipticUniversalSpecialization

/-! Actual specialization and nonvanishing of generic division
polynomials. Specialization at the integral cusp certifies nonzero generic
denominators without restricting the characteristic of later point
specializations. This serves DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 through
the point multiplication formula, actual torsion count, finite exceptional
fibers, reverse genus and good reduction. Adapted from the Apache-2.0
anthropics/fermats-last-theorem EDSEngine at
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceEllipticUniversal
open WeierstrassCurve Polynomial Dubon2026.SourceEllipticDivision
open Dubon2026.SourceEllipticSequence
open scoped Polynomial.Bivariate
noncomputable section
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}

theorem evalEval_ψ₂ : W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂ := by
  simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]

theorem evalEval_Ψ₃ : (C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]

theorem evalEval_preΨ₄ : (C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]

variable {m n : ℤ}

theorem evalEval_ψ : (W.ψ n).evalEval x y = polyEval W x y (curve.ψ n) := by
  simp_rw [polyEval_apply, ← map_ψ, map_specialize]

theorem evalEval_φ : (W.φ n).evalEval x y = polyEval W x y (curve.φ n) := by
  simp_rw [polyEval_apply, ← map_φ, map_specialize]

theorem evalEval_ωe : ((ωe W) n).evalEval x y =  polyEval W x y ((ωe curve) n) := by
  simp_rw [polyEval_apply, ← map_ωe, map_specialize]

open WeierstrassCurve (ψ φ)

theorem cusp_ψ₂ : cusp.ψ₂ = 2 * Y := by
  simp [cusp, ψ₂, WeierstrassCurve.Affine.polynomialY, map_ofNat]

theorem cusp_Ψ₃ : cusp.Ψ₃ = 3 * X ^ 4 := by simp [cusp, Ψ₃, b₂, b₄, b₆, b₈]
theorem cusp_preΨ₄ : cusp.preΨ₄ = 2 * X ^ 6 := by simp [cusp, preΨ₄, b₂, b₄, b₆, b₈]

theorem polyEval_cusp_ψ : polyEval cusp 1 1 (curve.ψ n) = n := by
  rw [ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄]
  simp [evalEval, normEDS_two_three_two]

theorem polyEval_cusp_φ : polyEval cusp 1 1 (curve.φ n) = 1 := by
  simp_rw [φ, map_sub, map_mul, map_pow, polyEval_cusp_ψ, polyEval]
  simp only [coe_eval₂RingHom, eval₂_C, eval₂_X]; ring

theorem polyEval_cusp_ψc : polyEval cusp 1 1 ((ψc curve) n) = 2 := by
  rw [ψc, map_complEDS₂, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄]
  simp [cusp_ψ₂, cusp_Ψ₃, cusp_preΨ₄, evalEval, complEDS₂_two_three_two]

theorem polyEval_cusp_ωe : polyEval cusp 1 1 ((ωe curve) n) = 1 := by
  have := congr(polyEval cusp 1 1 $(two_mul_ωe curve n))
  simp_rw [map_sub, map_mul, map_ofNat, polyEval_cusp_ψc] at this
  simpa [cusp, polyEval, specialize, curve] using this


end
end Dubon2026.SourceEllipticUniversal

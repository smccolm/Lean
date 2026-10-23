import Dubon2026.SourceEllipticOddKernelGeometry
import Dubon2026.SourceEllipticVeluTwoSurjective

/-! Surjectivity of the actual odd quotient map over the algebraically
closed base. The retained numerator degree and coprimality give every
target abscissa a preimage away from the kernel. Reuse the existing affine
y-existence theorem and the native point/negative-point dichotomy. This
avoids a new general lying-over or point-place argument (DUB-17/18). -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
variable {Q : W.toAffine.Point} {n : ℕ}

/-- Every target abscissa is attained by the actual odd affine x-formula away from its denominator. -/
theorem exists_odd_veluAffineX_preimage (hQ : addOrderOf Q = 2 * n + 1) (r : F) :
    ∃ x : F, (hP (oddOrderSummingSet W Q n) Prod.fst).eval x ≠ 0 ∧
      veluAffineX W (oddOrderSummingSet W Q n) x = r := by
  let S := oddOrderSummingSet W Q n
  let A := AP S Prod.fst (fun P => veluT W P.1 P.2) (fun P => veluU W P.1 P.2)
  let D := hP S Prod.fst ^ 2
  let p := A - C r * D
  have hA : A.natDegree = 2 * n + 1 := odd_generic_numerator_degree hQ
  have hD : D.natDegree = 2 * n := odd_generic_denominator_degree hQ
  have hp : p.natDegree = 2 * n + 1 := by
    rw [show p = A - C r * D from rfl, natDegree_sub_eq_left_of_natDegree_lt, hA]
    exact (natDegree_C_mul_le r D).trans_lt (by rw [hA, hD]; omega)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root p
    ((natDegree_pos_iff_degree_pos.mp (by rw [hp]; omega)).ne')
  have he : A.eval x = r * D.eval x := by
    simpa only [p, IsRoot, eval_sub, eval_mul, eval_C, sub_eq_zero] using hx
  have hd : (hP S Prod.fst).eval x ≠ 0 := by
    intro hz
    have hDz : D.eval x = 0 := by simp only [D, eval_pow, hz, zero_pow (by decide : 2 ≠ 0)]
    have hAz : A.eval x = 0 := by rw [he, hDz, mul_zero]
    obtain ⟨a, b, hab⟩ := isCoprime_odd_generic hQ
    change a * A + b * D = 1 at hab
    have hc := congrArg (Polynomial.eval x) hab
    rw [eval_add, eval_mul, eval_mul, hAz, hDz, mul_zero, mul_zero, add_zero, eval_one] at hc
    exact zero_ne_one hc
  refine ⟨x, hd, ?_⟩
  have havoid : ∀ P ∈ S, x ≠ P.1 := by
    intro P hPmem heq
    exact hd ((eval_kernelPolynomial_eq_zero_iff S x).mpr ⟨P, hPmem, heq⟩)
  have hAe := AP_eval S Prod.fst (fun P => veluT W P.1 P.2) (fun P => veluU W P.1 P.2) x havoid
  change A.eval x = (hP S Prod.fst).eval x ^ 2 * veluAffineX W S x at hAe
  rw [he] at hAe
  dsimp only [D] at hAe
  rw [eval_pow] at hAe
  exact mul_left_cancel₀ (pow_ne_zero 2 hd) ((mul_comm _ _).trans hAe).symm

variable [W.IsElliptic]

/-- The actual additive odd quotient map is onto the actual quotient elliptic curve. -/
theorem oddPointNorm_surjective (hQ : addOrderOf Q = 2 * n + 1) :
    Function.Surjective (oddPointNorm W hQ) := by
  intro R
  cases R with
  | zero => exact ⟨0, (oddPointNorm W hQ).map_zero⟩
  | some r s hs =>
    obtain ⟨x, hd, hx⟩ := exists_odd_veluAffineX_preimage W hQ r
    obtain ⟨y, hy⟩ := exists_equation_y W x
    have hn : W.toAffine.Nonsingular x y := equation_iff_nonsingular.mp hy
    have hn' := odd_veluAffine_nonsingular W hy hQ hd
    have he := oddPointNorm_some W hn hQ hd
    rcases (Point.X_eq_iff (h₁ := hn') (h₂ := hs)).mp hx with hh | hh
    · exact ⟨Point.some x y hn, he.trans hh⟩
    · refine ⟨-(Point.some x y hn), ?_⟩
      rw [map_neg, he, hh, neg_neg]

end Dubon2026.SourceEllipticFunctionField

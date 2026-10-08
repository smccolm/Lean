import Dubon2026.HomogeneousPolynomialLie
import Dubon2026.CompactSl2Basis

/-! # The original compact lowest vector in the genuine algebraic polynomial representation -/

namespace Dubon2026

noncomputable section
open MvPolynomial

/-- The actual compact Cartan eigenvector X₀ minus iX₁ in the standard polynomial representation. -/
def compactPolynomialLowest : MvPolynomial (Fin 2) ℂ := X 0 - Complex.I • X 1

/-- The original compact eigenvector has genuine homogeneous degree one. -/
theorem compactPolynomialLowest_homogeneous : compactPolynomialLowest.IsHomogeneous 1 :=
  (isHomogeneous_X ℂ (0 : Fin 2)).sub
    ((homogeneousSubmodule (Fin 2) ℂ 1).smul_mem _ (isHomogeneous_X ℂ (1 : Fin 2)))

/-- Evaluation at the original coordinate vector proves the actual compact polynomial is nonzero. -/
theorem compactPolynomialLowest_ne_zero : compactPolynomialLowest ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1 : ℂ) else 0)) h
  norm_num [compactPolynomialLowest, map_sub, map_smul] at he

/-- The actual compact Cartan derivation gives weight minus one on the original linear form. -/
theorem compactPolynomialLowest_H :
    matrixPolynomialDerivation compactSl2H.val compactPolynomialLowest = -compactPolynomialLowest := by
  norm_num [compactPolynomialLowest, map_sub, Derivation.map_smul, matrixPolynomialDerivation_X,
    Fin.sum_univ_two, compactSl2H, complexSl2U, complexSl2F]
  simp only [smul_smul, ← pow_two, Complex.I_sq, neg_one_smul]
  module

/-- The actual compact lowering derivation kills the original algebraic lowest linear form. -/
theorem compactPolynomialLowest_F :
    matrixPolynomialDerivation compactSl2F.val compactPolynomialLowest = 0 := by
  norm_num [compactPolynomialLowest, map_sub, Derivation.map_smul, matrixPolynomialDerivation_X,
    Fin.sum_univ_two, compactSl2F, complexSl2A, complexSl2U, complexSl2F]
  match_scalars <;> ring_nf
  norm_num [Complex.I_sq]

/-- The original degree-n compact lowest vector in the actual finite-dimensional homogeneous space. -/
def homogeneousCompactGenerator (n : ℕ) : homogeneousSubmodule (Fin 2) ℂ n :=
  ⟨compactPolynomialLowest ^ n, by simpa only [one_mul] using compactPolynomialLowest_homogeneous.pow n⟩

/-- The original algebraic compact lowest vector is nonzero in every genuine symmetric degree. -/
theorem homogeneousCompactGenerator_ne_zero (n : ℕ) : homogeneousCompactGenerator n ≠ 0 := by
  intro h
  exact pow_ne_zero n compactPolynomialLowest_ne_zero (congrArg Subtype.val h)

/-- The genuine complex traceless matrices act by the restriction of their actual polynomial derivations. -/
def homogeneousSl2Action (n : ℕ) :
    ComplexSl2 →ₗ⁅ℂ⁆ Module.End ℂ (homogeneousSubmodule (Fin 2) ℂ n) :=
  (homogeneousMatrixLieAction n).comp (LieAlgebra.SpecialLinear.sl (Fin 2) ℂ).incl

/-- The actual algebraic compact lowest vector has its exact original weight minus n. -/
theorem homogeneousCompactGenerator_H (n : ℕ) :
    homogeneousSl2Action n compactSl2H (homogeneousCompactGenerator n) =
      (-(n : ℂ)) • homogeneousCompactGenerator n := by
  apply Subtype.ext
  change matrixPolynomialDerivation compactSl2H.val (compactPolynomialLowest ^ n) =
    (-(n : ℂ)) • compactPolynomialLowest ^ n
  rw [Derivation.leibniz_pow, compactPolynomialLowest_H]
  cases n with
  | zero => simp
  | succ n =>
      simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul, smul_eq_C_mul,
        map_neg, map_natCast, pow_succ]
      ring

/-- The actual algebraic lowest vector is annihilated by the genuine compact lowering infinitesimal. -/
theorem homogeneousCompactGenerator_F (n : ℕ) :
    homogeneousSl2Action n compactSl2F (homogeneousCompactGenerator n) = 0 := by
  apply Subtype.ext
  change matrixPolynomialDerivation compactSl2F.val (compactPolynomialLowest ^ n) = 0
  rw [Derivation.leibniz_pow, compactPolynomialLowest_F, smul_zero, smul_zero]

end
end Dubon2026

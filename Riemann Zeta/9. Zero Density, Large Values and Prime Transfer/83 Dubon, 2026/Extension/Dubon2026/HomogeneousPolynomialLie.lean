import Dubon2026.MatrixPolynomialDerivation
import Dubon2026.HomogeneousFiniteSpace
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! # Genuine infinitesimal action on the finite-dimensional homogeneous polynomial space -/

namespace Dubon2026

noncomputable section
open MvPolynomial

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
private theorem derivation_sum_apply {τ : Type*} [Fintype τ]
    (d : τ → Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ)) (p : MvPolynomial ι ℂ) :
    (∑ i, d i) p = ∑ i, d i p := by
  change Derivation.coeFnAddMonoidHom (∑ i, d i) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

/-- The actual matrix vector field is exactly its original linear forms times the original partial derivatives. -/
theorem matrixPolynomialDerivation_eq_sum (a : Matrix ι ι ℂ) :
    matrixPolynomialDerivation a = ∑ i, (∑ j, a j i • (X j : MvPolynomial ι ℂ)) • pderiv i := by
  classical
  apply MvPolynomial.derivation_ext
  intro i
  simp [matrixPolynomialDerivation_X, derivation_sum_apply, Derivation.smul_apply, pderiv_X,
    Pi.single_apply]

/-- The actual infinitesimal matrix action preserves the original homogeneous polynomial degree. -/
theorem matrixPolynomialDerivation_homogeneous (a : Matrix ι ι ℂ) {n : ℕ}
    {p : MvPolynomial ι ℂ} (hp : p.IsHomogeneous n) :
    (matrixPolynomialDerivation a p).IsHomogeneous n := by
  cases n with
  | zero =>
      rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hp
      rw [hp, derivation_C]
      exact (homogeneousSubmodule ι ℂ 0).zero_mem
  | succ n =>
      rw [matrixPolynomialDerivation_eq_sum]
      simp only [derivation_sum_apply, Derivation.smul_apply, smul_eq_mul]
      apply IsHomogeneous.sum
      intro i _
      have hc : (∑ j, a j i • (X j : MvPolynomial ι ℂ)).IsHomogeneous 1 := by
        apply IsHomogeneous.sum
        intro j _
        exact (homogeneousSubmodule ι ℂ 1).smul_mem _ (isHomogeneous_X ℂ j)
      simpa only [Nat.succ_sub_one, Nat.add_comm 1 n] using hc.mul (hp.pderiv (i := i))

variable [DecidableEq ι]

/-- Restrict the actual matrix derivation to the genuine finite-dimensional homogeneous space. -/
def homogeneousMatrixLieAction (n : ℕ) :
    Matrix ι ι ℂ →ₗ⁅ℂ⁆ Module.End ℂ (homogeneousSubmodule ι ℂ n) where
  toFun a := (matrixPolynomialLieAction a).restrict
    (fun _ hp => matrixPolynomialDerivation_homogeneous a hp)
  map_add' a b := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add matrixPolynomialLieAction a b) p.val
  map_smul' c a := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact LinearMap.congr_fun (map_smul matrixPolynomialLieAction c a) p.val
  map_lie' {a b} := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact LinearMap.congr_fun (matrixPolynomialLieAction.map_lie a b) p.val

/-- The finite-dimensional infinitesimal action retains the literal original polynomial derivation. -/
theorem homogeneousMatrixLieAction_apply (n : ℕ) (a : Matrix ι ι ℂ)
    (p : homogeneousSubmodule ι ℂ n) :
    (homogeneousMatrixLieAction n a p).val = matrixPolynomialDerivation a p.val := rfl

end
end Dubon2026

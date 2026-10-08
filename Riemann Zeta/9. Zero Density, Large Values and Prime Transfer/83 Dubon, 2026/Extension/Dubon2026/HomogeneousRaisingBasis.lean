import Dubon2026.HomogeneousDimension
import Dubon2026.HomogeneousCentralCharacter
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The genuine finite raising basis of the original homogeneous representation -/

namespace Dubon2026

noncomputable section
open MvPolynomial

/-- The literal successive raising derivatives of the original algebraic generator. -/
def homogeneousRaisingJet (n r : ℕ) : homogeneousSubmodule (Fin 2) ℂ n :=
  ((homogeneousSl2Action n compactSl2E) ^ r) (homogeneousCompactGenerator n)

/-- Original monomials under the genuine primitive map are the actual algebraic raising derivatives. -/
theorem homogeneousRaisingJet_verma (n r : ℕ) :
    primitiveVermaMap (homogeneousSl2Action n) (homogeneousCompactGenerator n) (Polynomial.X ^ r) =
      homogeneousRaisingJet n r := polynomialCyclicMap_X_pow _ _ r

/-- Every original algebraic raising derivative has its exact genuine compact weight. -/
theorem homogeneousRaisingJet_weight (n r : ℕ) :
    homogeneousSl2Action n compactSl2H (homogeneousRaisingJet n r) =
      (-(n : ℂ) + 2 * r) • homogeneousRaisingJet n r := by
  have he := primitiveVermaMap_matrix (homogeneousSl2Action n) (homogeneousCompactGenerator n)
    (n : ℂ) (homogeneousCompactGenerator_ne_zero n) (homogeneousCompactGenerator_H n)
    (homogeneousCompactGenerator_F n) compactSl2H (Polynomial.X ^ r)
  rw [vermaPolynomialLieAction_H, LinearMap.neg_apply, vermaPolynomialH_X_pow,
    map_neg, map_smul, homogeneousRaisingJet_verma,
    ← neg_smul ((n : ℂ) - 2 * r) (homogeneousRaisingJet n r)] at he
  convert he.symm using 1
  congr 1
  ring

/-- The genuine lowering derivative has the exact original finite-dimensional recurrence. -/
theorem homogeneousRaisingJet_lower (n r : ℕ) :
    homogeneousSl2Action n compactSl2F (homogeneousRaisingJet n (r + 1)) =
      (((r : ℂ) + 1) * ((n : ℂ) - r)) • homogeneousRaisingJet n r := by
  have he := primitiveVermaMap_matrix (homogeneousSl2Action n) (homogeneousCompactGenerator n)
    (n : ℂ) (homogeneousCompactGenerator_ne_zero n) (homogeneousCompactGenerator_H n)
    (homogeneousCompactGenerator_F n) compactSl2F (Polynomial.X ^ (r + 1))
  rw [vermaPolynomialLieAction_F, vermaPolynomialE_X_pow_succ, map_smul,
    homogeneousRaisingJet_verma, homogeneousRaisingJet_verma] at he
  exact he.symm

/-- Every original raising derivative through degree n is nonzero. -/
theorem homogeneousRaisingJet_ne_zero (n r : ℕ) (hr : r ≤ n) : homogeneousRaisingJet n r ≠ 0 := by
  induction r with
  | zero => exact homogeneousCompactGenerator_ne_zero n
  | succ r ih =>
      have hn : r < n := hr
      have hi := ih (Nat.le_of_lt hn)
      intro he
      have hl := homogeneousRaisingJet_lower n r
      rw [he, map_zero] at hl
      have h₁ : (r : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
      have h₂ : (n : ℂ) - r ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hn))
      exact smul_ne_zero (mul_ne_zero h₁ h₂) hi hl.symm

/-- The original n+1 algebraic raising derivatives are linearly independent by their genuine distinct compact weights. -/
theorem homogeneousRaisingJet_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (fun r : Fin (n + 1) => homogeneousRaisingJet n r.val) := by
  apply (homogeneousSl2Action n compactSl2H).eigenvectors_linearIndependent'
    (fun r : Fin (n + 1) => -(n : ℂ) + 2 * r.val)
  · intro r s he
    apply Fin.ext
    have hh : (r.val : ℂ) = s.val := by linear_combination he / 2
    exact_mod_cast hh
  · intro r
    exact ⟨Module.End.mem_eigenspace_iff.mpr (homogeneousRaisingJet_weight n r.val),
      homogeneousRaisingJet_ne_zero n r.val (Nat.le_of_lt_succ r.is_lt)⟩

/-- The literal n+1 raising derivatives give a basis of the entire original homogeneous polynomial space. -/
def homogeneousRaisingBasis (n : ℕ) :
    Module.Basis (Fin (n + 1)) ℂ (homogeneousSubmodule (Fin 2) ℂ n) :=
  basisOfLinearIndependentOfCardEqFinrank (homogeneousRaisingJet_linearIndependent n)
    (by rw [Fintype.card_fin, homogeneousBinary_finrank])

/-- The actual full-space basis consists of precisely the original raising derivatives. -/
theorem homogeneousRaisingBasis_apply (n : ℕ) (r : Fin (n + 1)) :
    homogeneousRaisingBasis n r = homogeneousRaisingJet n r.val :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) r

end
end Dubon2026

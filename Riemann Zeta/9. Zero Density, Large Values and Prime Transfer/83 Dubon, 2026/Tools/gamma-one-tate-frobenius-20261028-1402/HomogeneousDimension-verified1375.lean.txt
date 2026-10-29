import Dubon2026.HomogeneousFiniteSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-! # Exact dimension of the original binary homogeneous polynomial space -/

namespace Dubon2026

noncomputable section
open MvPolynomial

/-- The original homogeneous polynomial has exactly its genuine degree-n monomial coefficients. -/
def homogeneousCoefficientEquiv {ι : Type*} (n : ℕ) :
    homogeneousSubmodule ι ℂ n ≃ₗ[ℂ] {d : ι →₀ ℕ | d.degree = n} →₀ ℂ := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact Finsupp.supportedEquivFinsupp _

/-- Actual binary degree-n monomials are indexed exactly by their second exponent from zero through n. -/
def binaryHomogeneousExponentEquiv (n : ℕ) :
    {d : Fin 2 →₀ ℕ | d.degree = n} ≃ Fin (n + 1) where
  toFun d := ⟨d.val 1, by
    have hd : d.val.degree = n := d.property
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
    omega⟩
  invFun j := ⟨Finsupp.equivFunOnFinite.symm ![n - j.val, j.val], by
    change (Finsupp.equivFunOnFinite.symm ![n - j.val, j.val]).degree = n
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    change n - j.val + j.val = n
    omega⟩
  left_inv d := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    have hd : d.val.degree = n := d.property
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hd
    change ![n - d.val 1, d.val 1] i = d.val i
    fin_cases i
    · change n - d.val 1 = d.val 0
      omega
    · rfl
  right_inv j := by
    apply Fin.ext
    simp

/-- The genuine homogeneous binary representation has exact dimension n+1. -/
theorem homogeneousBinary_finrank (n : ℕ) :
    Module.finrank ℂ (homogeneousSubmodule (Fin 2) ℂ n) = n + 1 := by
  classical
  letI : Fintype {d : Fin 2 →₀ ℕ | d.degree = n} :=
    Fintype.ofEquiv (Fin (n + 1)) (binaryHomogeneousExponentEquiv n).symm
  rw [(homogeneousCoefficientEquiv n).finrank_eq, Module.finrank_finsupp_self,
    Fintype.card_congr (binaryHomogeneousExponentEquiv n), Fintype.card_fin]

end
end Dubon2026

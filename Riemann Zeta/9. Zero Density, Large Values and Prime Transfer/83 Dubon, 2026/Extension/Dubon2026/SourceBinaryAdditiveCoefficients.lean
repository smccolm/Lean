import Dubon2026.HomogeneousCoefficientChange
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-! Additive coefficient projections for the original binary representation.
DUB-17/18 -> residual modular Galois association -> integral H1 Hecke
character -> complex cocycles spanned by integral cocycles. Rational basis
coordinates are additive maps, so their compatibility with integer matrix
substitution must be proved without assuming multiplicativity.

The integer-coefficient expansion follows section MapA of
anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_span_coeffCocycles_binaryFormRepSL_map_intCast_eq_top.lean
(Apache-2.0; retained archive LICENSE and NOTICE), reusing the local
matrixPolynomialAction_map theorem and the original column substitution.
-/

namespace Dubon2026
noncomputable section
open MvPolynomial

variable {R S : Type} [CommRing R] [CommRing S]

/-- Literal additive change of every coefficient of the original binary polynomial. -/
def sourcePolynomialAdditiveMap (φ : R →+ S) :
    MvPolynomial (Fin 2) R →+ MvPolynomial (Fin 2) S where
  toFun := AddMonoidAlgebra.map φ
  map_zero' := by
    ext m
    exact φ.map_zero
  map_add' P Q := by
    ext m
    exact φ.map_add (coeff m P) (coeff m Q)

/-- The original polynomial coefficient is changed by exactly the given additive map. -/
theorem sourcePolynomialAdditiveMap_coeff (φ : R →+ S)
    (P : MvPolynomial (Fin 2) R) (m : Fin 2 →₀ ℕ) :
    coeff m (sourcePolynomialAdditiveMap φ P) = φ (coeff m P) := rfl

private def integerActionCoefficient (M : Matrix (Fin 2) (Fin 2) ℤ)
    (e d : Fin 2 →₀ ℕ) : ℤ :=
  coeff d (matrixPolynomialAction M (monomial e 1))

private theorem matrix_monomial_coefficient (M : Matrix (Fin 2) (Fin 2) ℤ)
    (e d : Fin 2 →₀ ℕ) :
    coeff d (matrixPolynomialAction (M.map (Int.castRingHom R)) (monomial e 1)) =
      (integerActionCoefficient M e d : R) := by
  have h := matrixPolynomialAction_map (Int.castRingHom R) M (monomial e 1)
  rw [map_monomial, (Int.castRingHom R).map_one] at h
  rw [← h, coeff_map]
  rfl

private theorem matrix_polynomial_coefficient (M : Matrix (Fin 2) (Fin 2) ℤ)
    (P : MvPolynomial (Fin 2) R) (d : Fin 2 →₀ ℕ) :
    coeff d (matrixPolynomialAction (M.map (Int.castRingHom R)) P) =
      ∑ e ∈ P.support, coeff e P * (integerActionCoefficient M e d : R) := by
  conv_lhs => rw [P.as_sum, map_sum]
  rw [coeff_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [show monomial e (coeff e P) = coeff e P • monomial e (1 : R) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, coeff_smul, matrix_monomial_coefficient, smul_eq_mul]

/-- An arbitrary additive coefficient projection commutes with the actual integer matrix substitution. -/
theorem sourcePolynomialAdditiveMap_matrix (φ : R →+ S)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) :
    sourcePolynomialAdditiveMap φ (matrixPolynomialAction (M.map (Int.castRingHom R)) P) =
      matrixPolynomialAction (M.map (Int.castRingHom S)) (sourcePolynomialAdditiveMap φ P) := by
  ext d
  rw [sourcePolynomialAdditiveMap_coeff, matrix_polynomial_coefficient,
    matrix_polynomial_coefficient, map_sum]
  have hs : (sourcePolynomialAdditiveMap φ P).support ⊆ P.support :=
    Finsupp.support_mapRange (hf := φ.map_zero)
  rw [← Finset.sum_subset hs]
  · apply Finset.sum_congr rfl
    intro e _
    rw [sourcePolynomialAdditiveMap_coeff, mul_comm (coeff e P), ← zsmul_eq_mul,
      map_zsmul, zsmul_eq_mul, mul_comm]
  · intro e _ he
    have h0 : coeff e (sourcePolynomialAdditiveMap φ P) = 0 := by
      simpa [MvPolynomial.mem_support_iff] using he
    rw [mul_comm (coeff e P), ← zsmul_eq_mul, map_zsmul,
      ← sourcePolynomialAdditiveMap_coeff, h0, smul_zero]

/-- Additive coefficient projections preserve the actual homogeneous binary degree. -/
def sourceHomogeneousAdditiveMap (w : ℕ) (φ : R →+ S) :
    homogeneousSubmodule (Fin 2) R w →+ homogeneousSubmodule (Fin 2) S w where
  toFun P := ⟨sourcePolynomialAdditiveMap φ P.val, by
    have hP := (mem_homogeneousSubmodule w _).mp P.property
    rw [mem_homogeneousSubmodule]
    intro m hm
    apply hP
    intro h0
    apply hm
    rw [sourcePolynomialAdditiveMap_coeff, h0, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ P.val Q.val)

/-- The actual homogeneous additive coefficient projection intertwines integer column substitution. -/
theorem sourceHomogeneousAdditiveMap_matrix (w : ℕ) (φ : R →+ S)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (P : homogeneousSubmodule (Fin 2) R w) :
    sourceHomogeneousAdditiveMap w φ (homogeneousMatrixAction w (M.map (Int.castRingHom R)) P) =
      homogeneousMatrixAction w (M.map (Int.castRingHom S))
        (sourceHomogeneousAdditiveMap w φ P) :=
  Subtype.ext (sourcePolynomialAdditiveMap_matrix φ M P.val)

end
end Dubon2026

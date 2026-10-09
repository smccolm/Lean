import Dubon2026.MatrixPolynomialAction

/-! # Coefficient change for the actual symmetric homogeneous representation -/

namespace Dubon2026

noncomputable section
open MvPolynomial

variable {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι]

/-- Changing the coefficients of an original polynomial commutes with the literal matrix substitution, with the same coefficient change applied to every matrix entry. -/
theorem matrixPolynomialAction_map (φ : R →+* S) (g : Matrix ι ι R)
    (p : MvPolynomial ι R) :
    MvPolynomial.map φ (matrixPolynomialAction g p) =
      matrixPolynomialAction (g.map φ) (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [matrixPolynomialAction]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.map_X, hp]
      congr 1
      simp [matrixPolynomialAction_X, smul_eq_C_mul]

/-- The original coefficient homomorphism acts on each genuine homogeneous space as a semilinear map. -/
def homogeneousCoefficientMap (n : ℕ) (φ : R →+* S) :
    homogeneousSubmodule ι R n →ₛₗ[φ] homogeneousSubmodule ι S n where
  toFun p := ⟨MvPolynomial.map φ p.val, p.property.map φ⟩
  map_add' p q := Subtype.ext (map_add (MvPolynomial.map φ) p.val q.val)
  map_smul' c p := by
    apply Subtype.ext
    simp [smul_eq_C_mul]

/-- The actual homogeneous coefficient map intertwines the original matrix action with its literal entrywise image. -/
theorem homogeneousCoefficientMap_intertwines (n : ℕ) (φ : R →+* S)
    (g : Matrix ι ι R) (p : homogeneousSubmodule ι R n) :
    homogeneousCoefficientMap n φ (homogeneousMatrixAction n g p) =
      homogeneousMatrixAction n (g.map φ) (homogeneousCoefficientMap n φ p) :=
  Subtype.ext (matrixPolynomialAction_map φ g p.val)

/-- Coefficient change commutes with the original symmetric representation of every invertible matrix. -/
theorem homogeneousCoefficientMap_GL [DecidableEq ι] (n : ℕ) (φ : R →+* S)
    (g : Matrix.GeneralLinearGroup ι R) (p : homogeneousSubmodule ι R n) :
    homogeneousCoefficientMap n φ (homogeneousGLRepresentation (R := R) (ι := ι) n g p) =
      homogeneousGLRepresentation (R := S) (ι := ι) n
        (Matrix.GeneralLinearGroup.map (n := ι) φ g)
        (homogeneousCoefficientMap n φ p) :=
  homogeneousCoefficientMap_intertwines n φ g.val p

omit [Fintype ι] in
/-- A faithful change of original coefficients remains injective on the actual homogeneous space. -/
theorem homogeneousCoefficientMap_injective (n : ℕ) (φ : R →+* S)
    (hφ : Function.Injective φ) : Function.Injective (homogeneousCoefficientMap (ι := ι) n φ) := by
  intro p q h
  apply Subtype.ext
  exact MvPolynomial.map_injective φ hφ (congrArg Subtype.val h)

end
end Dubon2026

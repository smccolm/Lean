import Dubon2026.MatrixPolynomialAction
import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Finite dimensionality of the genuine homogeneous polynomial representation -/

namespace Dubon2026

noncomputable section
open MvPolynomial

/-- For finitely many actual variables, the original degree-n homogeneous polynomial space is finite dimensional. -/
instance homogeneousPolynomial_finite {ι : Type*} [Finite ι] (n : ℕ) :
    Module.Finite ℂ (homogeneousSubmodule ι ℂ n) := by
  have hs : {d : ι →₀ ℕ | d.degree = n}.Finite :=
    (Finsupp.finite_of_degree_le n).subset (fun _ h => le_of_eq h)
  letI := hs.to_subtype
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Finite.equiv (Finsupp.supportedEquivFinsupp
    (R := ℂ) (M := ℂ) {d : ι →₀ ℕ | d.degree = n}).symm

/-- The actual homogeneous monomial in any chosen variable is a vector in the original finite-dimensional space. -/
def homogeneousPurePower {ι : Type*} (n : ℕ) (i : ι) : homogeneousSubmodule ι ℂ n :=
  ⟨X i ^ n, isHomogeneous_X_pow i n⟩

/-- The genuine pure-power vector is nonzero in the actual homogeneous representation. -/
theorem homogeneousPurePower_ne_zero {ι : Type*} (n : ℕ) (i : ι) : homogeneousPurePower n i ≠ 0 := by
  intro h
  have he := congrArg Subtype.val h
  exact pow_ne_zero n (MvPolynomial.X_ne_zero i) he

end
end Dubon2026

import Dubon2026.AdelicKFiniteGL2Character
import Dubon2026.HomogeneousAlgebraicCoefficients
import Dubon2026.HomogeneousGroupIrreducible
import Dubon2026.HomogeneousHighestWeight

/-! # The actual irreducible algebraic model for the original cusp infinitesimal character -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MvPolynomial
open scoped MatrixGroups

/-- The source's even weight at least two determines the actual nonnegative symmetric degree parameter. -/
theorem evenWeight_algebraic_degree {k : ℤ} (hk : 2 ≤ k) (he : Even k) :
    ∃ m : ℕ, k = (2 * m : ℕ) + 2 := by
  obtain ⟨r, hr⟩ := he
  refine ⟨(r - 1).toNat, ?_⟩
  have hn : 0 ≤ r - 1 := by omega
  have ht := Int.toNat_of_nonneg hn
  push_cast
  omega

/-- The original determinant twist is an irreducible algebraic representation: its actual matrix coefficients have determinant-power denominators, and its genuine invariant subspaces are trivial. -/
theorem homogeneousDeterminantTwist_algebraic_irreducible (m : ℕ) :
    (∀ v : homogeneousSubmodule (Fin 2) ℂ (2 * m),
      ∀ L : homogeneousSubmodule (Fin 2) ℂ (2 * m) →ₗ[ℂ] ℂ,
      ∃ q : MvPolynomial (Fin 2 × Fin 2) ℂ, ∀ g : Matrix.GeneralLinearGroup (Fin 2) ℂ,
        L (homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) g v) =
          MvPolynomial.eval (fun ij => g.val ij.1 ij.2) q / Matrix.det g.val ^ m) ∧
    (∀ p : Submodule ℂ (homogeneousSubmodule (Fin 2) ℂ (2 * m)),
      (∀ g v, v ∈ p → homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) g v ∈ p) →
        p = ⊥ ∨ p = ⊤) :=
  ⟨homogeneousDeterminantTwist_regular_coefficient m, homogeneousDeterminantTwist_irreducible m⟩

/-- The actual irreducible algebraic model has the original nonzero highest vector and dominant integral weight, with distinct rho-shifted entries, and its full infinitesimal character equals that of every genuine real K-finite cusp vector. -/
theorem adelicRealKFinite_regular_algebraic_model {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hf : f ≠ 0) (m : ℕ)
    (hk : k = (2 * m : ℕ) + 2)
    (z : Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)))
    (v : adelicRealSmoothSubmodule f) (hv : v.val ∈ adelicRealCyclicClosedSpan f)
    [FiniteDimensional ℂ (adelicCompactOrbitSpan f v.val)]
    (p : homogeneousSubmodule (Fin 2) ℂ (2 * m)) :
    (∀ w : homogeneousSubmodule (Fin 2) ℂ (2 * m),
      ∀ L : homogeneousSubmodule (Fin 2) ℂ (2 * m) →ₗ[ℂ] ℂ,
      ∃ q : MvPolynomial (Fin 2 × Fin 2) ℂ, ∀ g : Matrix.GeneralLinearGroup (Fin 2) ℂ,
        L (homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) g w) =
          MvPolynomial.eval (fun ij => g.val ij.1 ij.2) q / Matrix.det g.val ^ m) ∧
    (∀ U : Submodule ℂ (homogeneousSubmodule (Fin 2) ℂ (2 * m)),
      (∀ g w, w ∈ U → homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) g w ∈ U) →
        U = ⊥ ∨ U = ⊤) ∧
    homogeneousPurePower (2 * m) (0 : Fin 2) ≠ 0 ∧
    (-(m : ℤ) ≤ (m : ℤ) ∧ (m : ℤ) + 1 - (-(m : ℤ)) = 2 * m + 1 ∧
      0 < (m : ℤ) + 1 - (-(m : ℤ))) ∧
    (∀ u w : ℂˣ, homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) (complexDiagonalGL u w)
      (homogeneousPurePower (2 * m) (0 : Fin 2)) =
      ((u : ℂ) ^ m * (w : ℂ) ^ (-(m : ℤ))) • homogeneousPurePower (2 * m) (0 : Fin 2)) ∧
    adelicGL2EnvelopingAction f z.val v = adelicGL2InfinitesimalCharacter f hf z • v ∧
    homogeneousGL2EnvelopingAction m z.val p = adelicGL2InfinitesimalCharacter f hf z • p := by
  exact ⟨(homogeneousDeterminantTwist_algebraic_irreducible m).1,
    (homogeneousDeterminantTwist_algebraic_irreducible m).2,
    homogeneousPurePower_ne_zero _ _, homogeneousHighestWeight_regular m,
    homogeneousDeterminantTwist_highest_weight m,
    adelicRealKFinite_algebraic_character f hf m hk z v hv p⟩

end
end Dubon2026

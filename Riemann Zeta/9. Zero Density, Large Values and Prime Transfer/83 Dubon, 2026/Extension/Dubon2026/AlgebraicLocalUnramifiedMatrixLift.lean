import Dubon2026.AlgebraicLocalUnramifiedHom
import Dubon2026.ContinuousRepresentationDeterminant
import Dubon2026.ContinuousRepresentationFiniteQuotient

/-! Actual finite-coefficient unramified matrix lifts are constructed on
the original local Galois group from their Frobenius matrix. Their whole
residual representation and determinant are checked using the proved
unramified uniqueness theorem. This is DUB-17's local deformation existence
input, before proving the required matrix lifting and local-ring geometry. -/

namespace Dubon2026
noncomputable section
open Matrix

variable (K L : Type) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [IsGalois K L] [Finite (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))]

attribute [local instance] algebraicLocalIntegerAction algebraicLocalIntegerBaseAlgebra

variable (φ : Gal(L/K))
  (hφ : ∀ x : algebraicLocalIntegerRing L,
    IsLocalRing.residue _ (φ • x) = (IsLocalRing.residue _ x) ^
      Nat.card (IsLocalRing.ResidueField (algebraicLocalIntegerRing K)))

include hφ

/-- A finite-coefficient Frobenius matrix lifting the original residual
Frobenius extends to an actual continuous unramified lift of the entire
original residual representation. -/
theorem algebraicLocal_unramified_matrix_lift
    [IsSepClosed L] [CharZero L]
    {ι R k : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing k]
    [Finite R] [TopologicalSpace R] [DiscreteTopology R]
    [TopologicalSpace k] [DiscreteTopology k]
    (π : R →+* k) (σ : Gal(L/K) →ₜ* GeneralLinearGroup ι k)
    (hσ : algebraicLocalInertia K L ≤ σ.toMonoidHom.ker)
    (A : GeneralLinearGroup ι R) (hA : GeneralLinearGroup.map π A = σ φ) :
    ∃ τ : Gal(L/K) →ₜ* GeneralLinearGroup ι R,
      algebraicLocalInertia K L ≤ τ.toMonoidHom.ker ∧
      (GeneralLinearGroup.map π).comp τ.toMonoidHom = σ.toMonoidHom ∧ τ φ = A := by
  obtain ⟨τ, hτ, hτφ⟩ := algebraicLocal_exists_unramified_finite_hom K L φ hφ
    (GeneralLinearGroup ι R) A
  have hmap : Continuous (GeneralLinearGroup.map (n := ι) π) := continuous_of_discreteTopology
  let σ' : Gal(L/K) →ₜ* GeneralLinearGroup ι k :=
    ⟨(GeneralLinearGroup.map π).comp τ.toMonoidHom, hmap.comp τ.continuous⟩
  have hσ' : algebraicLocalInertia K L ≤ σ'.toMonoidHom.ker := by
    intro g hg
    change GeneralLinearGroup.map π (τ g) = 1
    rw [show τ g = 1 from hτ hg, map_one]
  have he : σ' φ = σ φ := by
    change GeneralLinearGroup.map π (τ φ) = σ φ
    rw [hτφ]
    exact hA
  have hwhole := algebraicLocal_unramified_hom_ext K L φ hφ σ' σ hσ' hσ he
  exact ⟨τ, hτ, congrArg ContinuousMonoidHom.toMonoidHom hwhole, hτφ⟩

/-- For actual unramified local matrix representations, the prescribed
whole determinant is forced by the determinant of the actual Frobenius
matrix and an unramified target character. -/
theorem algebraicLocal_unramified_determinant_eq
    {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    [TopologicalSpace R] [DiscreteTopology R]
    (τ : Gal(L/K) →ₜ* GeneralLinearGroup ι R) (δ : Gal(L/K) →ₜ* Rˣ)
    (hτ : algebraicLocalInertia K L ≤ τ.toMonoidHom.ker)
    (hδ : algebraicLocalInertia K L ≤ δ.toMonoidHom.ker)
    (hdet : GeneralLinearGroup.det (τ φ) = δ φ) :
    GeneralLinearGroup.det.comp τ.toMonoidHom = δ.toMonoidHom := by
  have hd : Continuous (GeneralLinearGroup.det : GeneralLinearGroup ι R →* Rˣ) :=
    continuous_of_discreteTopology
  let χ : Gal(L/K) →ₜ* Rˣ := ⟨GeneralLinearGroup.det.comp τ.toMonoidHom, hd.comp τ.continuous⟩
  have hχ : algebraicLocalInertia K L ≤ χ.toMonoidHom.ker := by
    intro g hg
    change GeneralLinearGroup.det (τ g) = 1
    rw [show τ g = 1 from hτ hg, map_one]
  exact congrArg ContinuousMonoidHom.toMonoidHom
    (algebraicLocal_unramified_hom_ext K L φ hφ χ δ hχ hδ hdet)

end
end Dubon2026

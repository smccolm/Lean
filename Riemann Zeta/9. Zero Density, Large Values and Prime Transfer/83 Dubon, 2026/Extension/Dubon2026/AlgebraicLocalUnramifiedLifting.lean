import Dubon2026.AlgebraicLocalUnramifiedMatrixLift
import Dubon2026.LocalCoefficientFixedDeterminantLifting

/-! The actual unramified fixed-determinant local deformation condition
lifts across finite local coefficient surjections. The original residue
Frobenius, a determinant-corrected matrix, and the whole local representation
are constructed. This is the lifting input to the required local-ring
description in DUB-17's arithmetic patching dependency. -/

namespace Dubon2026
noncomputable section
open Matrix

variable (K L : Type) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [IsGalois K L] [IsSepClosed L] [CharZero L]
  [Finite (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))]

/-- Every actual continuous unramified representation lifts across a
finite local coefficient surjection with any compatible prescribed
unramified determinant. No Frobenius or matrix lift is supplied. -/
theorem algebraicLocal_unramified_fixedDeterminant_lift
    {ι A B : Type} [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    [TopologicalSpace B] [DiscreteTopology B]
    (i₀ : ι) (f : A →+* B) (hf : Function.Surjective f) [IsLocalHom f]
    (σ : Gal(L/K) →ₜ* GeneralLinearGroup ι B)
    (hσ : algebraicLocalInertia K L ≤ σ.toMonoidHom.ker)
    (δ : Gal(L/K) →ₜ* Aˣ)
    (hδ : algebraicLocalInertia K L ≤ δ.toMonoidHom.ker)
    (hcompat : ∀ g, Units.map f.toMonoidHom (δ g) = GeneralLinearGroup.det (σ g)) :
    ∃ τ : Gal(L/K) →ₜ* GeneralLinearGroup ι A,
      algebraicLocalInertia K L ≤ τ.toMonoidHom.ker ∧
      (GeneralLinearGroup.map f).comp τ.toMonoidHom = σ.toMonoidHom ∧
      GeneralLinearGroup.det.comp τ.toMonoidHom = δ.toMonoidHom := by
  obtain ⟨φ, hφ⟩ := algebraicLocal_exists_residueFrobenius K L
  obtain ⟨M, hM, hdet⟩ := generalLinearGroup_fixedDeterminant_lift
    i₀ f hf (σ φ) (δ φ) (hcompat φ)
  obtain ⟨τ, hτ, hred, hτφ⟩ := algebraicLocal_unramified_matrix_lift K L φ hφ f σ hσ M hM
  refine ⟨τ, hτ, hred, ?_⟩
  apply algebraicLocal_unramified_determinant_eq K L φ hφ τ δ hτ hδ
  rw [hτφ]
  exact hdet

end
end Dubon2026

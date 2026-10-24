import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Tactic

/-! Actual coefficient conjugation by the valuation-ring decomposition
group. Inertia fixes its residue model. These are the field-action inputs
to inertia-equivariant torsion specialization and the DUB-17/18 fiber census.
Adapted from the finite inertia-reduction argument of
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
noncomputable section
variable {F M : Type*} [Field F] [Field M] [Algebra F M] {A : ValuationSubring M}

/-- The original field automorphism restricted to its stabilized valuation ring. -/
def decompRingHom (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) : A →+* A :=
  MulSemiringAction.toRingHom (A.decompositionSubgroup F) A ⟨σ, hσ⟩

theorem subtype_comp_decompRingHom (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) :
    A.subtype.comp (decompRingHom σ hσ) = (σ : M →+* M).comp A.subtype := by
  ext a
  rfl

theorem residue_comp_decompRingHom (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F) :
    (residue A).comp (decompRingHom σ hσ) = residue A := by
  have hfix : MulSemiringAction.toRingAut (A.decompositionSubgroup F) (ResidueField A)
      ⟨σ, hσ⟩ = 1 := hσI
  ext a
  change residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup F) • a) = residue A a
  rw [IsLocalRing.ResidueField.residue_smul]
  change MulSemiringAction.toRingAut (A.decompositionSubgroup F) (ResidueField A)
    ⟨σ, hσ⟩ (residue A a) = residue A a
  rw [hfix]
  rfl

/-- The literal integral equation obtained by conjugating each coefficient. -/
def conjugateModel (W : WeierstrassCurve A) (σ : M ≃ₐ[F] M)
    (hσ : σ ∈ A.decompositionSubgroup F) : WeierstrassCurve A :=
  W.map (decompRingHom σ hσ)

theorem conjugateModel_map_subtype (W : WeierstrassCurve A)
    (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) :
    (conjugateModel W σ hσ).map A.subtype = (W.map A.subtype).map (σ : M →+* M) := by
  rw [conjugateModel, WeierstrassCurve.map_map, WeierstrassCurve.map_map,
    subtype_comp_decompRingHom]

theorem conjugateModel_map_residue (W : WeierstrassCurve A)
    (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F) :
    (conjugateModel W σ hσ).map (residue A) = W.map (residue A) := by
  rw [conjugateModel, WeierstrassCurve.map_map, residue_comp_decompRingHom σ hσ hσI]

theorem isUnit_conjugateModel_discriminant (W : WeierstrassCurve A)
    (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) (hW : IsUnit W.Δ) :
    IsUnit (conjugateModel W σ hσ).Δ := by
  rw [conjugateModel, map_Δ]
  exact hW.map _

end
end Dubon2026.SourceEllipticReduction

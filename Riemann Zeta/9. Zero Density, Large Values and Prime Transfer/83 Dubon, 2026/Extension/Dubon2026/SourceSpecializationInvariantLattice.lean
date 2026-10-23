import Dubon2026.SourceIntegralTensorImage
import Dubon2026.SourceIntegralImageLattice
import Dubon2026.SourceIntegralLatticeRank

/-! DUB-17/18 -> actual primitive residual association -> integral model.
The integral source module supplies a finite full lattice through its
scalar-extension specialization. Intertwining derives invariance; the
native fraction-field lattice theorem derives freeness and exact rank. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct
variable {R K S E M V : Type*}
variable [CommRing R] [CommRing K] [Algebra R K]
variable [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [Algebra R S]
variable [Field E] [Algebra K E] [Algebra S E] [IsFractionRing S E]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable [AddCommGroup V] [Module R V] [Module K V] [Module S V] [Module E V]
variable [IsScalarTower R K V] [IsScalarTower R S V]
variable [IsScalarTower K E V] [IsScalarTower S E V]

theorem scalarSpecialization_lattice (π : K ⊗[R] M →ₗ[K] V)
    (hπ : Submodule.span E (Set.range π) = ⊤) :
    let L := integralImageLattice (S := S) (scalarExtensionIntegralMap π)
    Submodule.span E (L : Set V) = ⊤ ∧
      Module.Free S L ∧ Module.Finite S L ∧ Module.finrank S L = Module.finrank E V := by
  let L := integralImageLattice (S := S) (scalarExtensionIntegralMap π)
  have hspan : Submodule.span E (L : Set V) = ⊤ := by
    rw [integralImageLattice_span, ← scalarExtensionIntegralMap_span, hπ]
  exact ⟨hspan, fullIntegralLattice_free_finite_rank L (integralImageLattice_fg _) hspan⟩

omit [IsDomain S] [IsPrincipalIdealRing S] [Algebra R S]
    [Algebra K E] [Algebra S E] [IsFractionRing S E] [Module.Finite R M]
    [Module E V] [IsScalarTower R S V] [IsScalarTower K E V] [IsScalarTower S E V] in
theorem scalarSpecialization_lattice_invariant (π : K ⊗[R] M →ₗ[K] V)
    (u : V →ₗ[S] V) (r : M →ₗ[R] M)
    (he : ∀ z, u (π z) = π (r.baseChange K z)) :
    ∀ v, v ∈ integralImageLattice (S := S) (scalarExtensionIntegralMap π) →
      u v ∈ integralImageLattice (S := S) (scalarExtensionIntegralMap π) :=
  integralImageLattice_map_mem _ u r (scalarExtensionIntegralMap_intertwines π u r he)

end
end Dubon2026

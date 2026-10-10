import Dubon2026.OriginalTraceMatrixIdempotent
import Dubon2026.CoefficientMatrixAlgebraReductionKernel
import Dubon2026.MatrixIdempotentLeftIdealSpanning
import Dubon2026.ResidualMatrixColumnIndependence

/-! # A genuine original-dimensional basis of the actual trace-algebra idempotent left ideal -/

namespace Dubon2026
noncomputable section
open Matrix Module

variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R] [IsAdicComplete (WithIdeal.i : Ideal R) R]

/-- Original residual absolute irreducibility constructs a genuine idempotent left ideal over the actual closed trace coefficient algebra and a basis indexed by the original representation dimension, with the actual residual column units as its reductions. -/
theorem originalTraceLeftIdealBasis_exists
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] (i₀ : ι) :
    let S := closedMatrixTraceAlgebra (O := O) ρ
    let A := coefficientRepresentationMatrixAlgebra S ρ
    ∃ (e : A), e ^ 2 = e ∧
      (RingHom.mapMatrix (IsLocalRing.residue R)) e.val = Matrix.single i₀ i₀ 1 ∧
      ∃ b : Basis ι S (algebraIdempotentLeftIdeal (S := S) e),
        ∀ i, (RingHom.mapMatrix (IsLocalRing.residue R)) (b i).val.val =
          Matrix.single i i₀ 1 := by
  classical
  let S := closedMatrixTraceAlgebra (O := O) ρ
  let A := coefficientRepresentationMatrixAlgebra S ρ
  letI : IsLocalRing S := closedMatrixTraceAlgebra_isLocalRing hR eR ρ
  letI : IsLocalHom S.val.toRingHom := closedMatrixTraceAlgebra_isLocalHom hR eR ρ
  letI : Module.Finite S A := (originalClosedTraceMatrixAlgebra_finite_free_closed
    (L := L) hR eR ρ).1
  obtain ⟨κ, instκ, a, bR, hbR, hcoord⟩ := originalMatrixTraceBasis_exists (L := L) hR eR ρ
  letI := instκ
  obtain ⟨e, he, hebar⟩ := originalTraceMatrixIdempotent_exists (L := L) hR eR ρ i₀
  let M := algebraIdempotentLeftIdeal (S := S) e
  choose Y hY using fun i => coefficientRepresentationMatrixAlgebra_residue_surjective
    (L := L) eR S ρ (Matrix.single i i₀ 1)
  let v : ι → M := fun i => ⟨Y i * e, ⟨Y i, rfl⟩⟩
  have hv (i : ι) : (RingHom.mapMatrix (IsLocalRing.residue R)) (v i).val.val =
      Matrix.single i i₀ 1 := by
    change (RingHom.mapMatrix (IsLocalRing.residue R)) ((Y i).val * e.val) = _
    rw [map_mul, hebar]
    have hi : (RingHom.mapMatrix (IsLocalRing.residue R)) (Y i).val =
        Matrix.single i i₀ 1 := hY i
    rw [hi, Matrix.single_mul_single_same, one_mul]
  have hscalar : Function.Surjective (fun c : S => IsLocalRing.residue R c.val) := by
    intro z
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (eR z)
    refine ⟨⟨algebraMap O R o, S.algebraMap_mem o⟩, eR.injective ?_⟩
    change eR (algebraMap O (IsLocalRing.ResidueField R) o) = eR z
    rw [eR.commutes]
    exact ho
  have hspan : Submodule.span S (Set.range v) = ⊤ :=
    matrixIdempotentLeftIdeal_span S A e he i₀ hebar hscalar
      (fun x hx => coefficientRepresentationMatrixAlgebra_mem_maximal_smul
        S ρ a bR hbR hcoord x hx) v hv
  let F : M →ₗ[S] Matrix ι ι R := A.val.toLinearMap.comp M.subtype
  have hind : LinearIndependent S v :=
    LinearIndependent.of_comp F
      ((residualMatrixColumns_linearIndependent (fun i => (v i).val.val) i₀ hv).restrict_scalars' S)
  let b : Basis ι S M := Basis.mk hind hspan.ge
  refine ⟨e, he, hebar, b, ?_⟩
  intro i
  simpa only [b, Basis.mk_apply] using hv i

end
end Dubon2026

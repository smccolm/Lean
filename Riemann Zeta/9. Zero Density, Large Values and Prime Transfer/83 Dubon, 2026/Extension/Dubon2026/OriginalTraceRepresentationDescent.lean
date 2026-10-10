import Dubon2026.OriginalTraceLeftIdealBasis
import Dubon2026.CoefficientRepresentationAlgebraHom
import Dubon2026.MatrixIdempotentBasisIntertwiner
import Dubon2026.MatrixRepresentationStrictConjugacy

/-! # Genuine whole-representation descent to the actual original closed trace coefficient algebra -/

namespace Dubon2026
noncomputable section
open Matrix Module

variable {G ι O R : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R] [IsAdicComplete (WithIdeal.i : Ideal R) R]

/-- The whole original representation descends to its actual closed trace coefficient algebra up to a genuine original change of basis reducing to the identity; its original-dimensional left-ideal basis supplies the descended matrices and the conjugator. -/
theorem originalTraceRepresentationDescent_exists
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ)))] (i₀ : ι) :
    ∃ τ : G →* GeneralLinearGroup ι (closedMatrixTraceAlgebra (O := O) ρ),
      MatrixStrictlyConjugate (IsLocalRing.residue R)
        ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O) ρ).val.toRingHom).comp τ) ρ := by
  let S := closedMatrixTraceAlgebra (O := O) ρ
  let A := coefficientRepresentationMatrixAlgebra S ρ
  obtain ⟨e, _he, _hebar, b, hb⟩ := originalTraceLeftIdealBasis_exists (L := L) hR eR ρ i₀
  let σ : G →* A := coefficientRepresentationAlgebraHom S ρ
  let τ := algebraIdempotentMatrixRepresentation σ e b
  let B := residualColumnMatrix (fun i => (b i).val.val) i₀
  have hB : IsUnit B := residualColumnMatrix_isUnit (fun i => (b i).val.val) i₀ hb
  let U : GeneralLinearGroup ι R := hB.unit
  have hUval : U.val = B := hB.unit_spec
  refine ⟨τ, U, ?_, ?_⟩
  · apply Units.ext
    change (RingHom.mapMatrix (IsLocalRing.residue R)) U.val = 1
    rw [hUval]
    exact residualColumnMatrix_reduction (fun i => (b i).val.val) i₀ hb
  · intro g
    have hmul : ρ g * U = U * GeneralLinearGroup.map S.val.toRingHom (τ g) := by
      apply Units.ext
      change (ρ g).val * U.val = U.val * (RingHom.mapMatrix S.val.toRingHom) (τ g).val
      rw [hUval]
      exact matrixIdempotentBasis_intertwines S A σ e b i₀ g
    change ρ g = U * GeneralLinearGroup.map S.val.toRingHom (τ g) * U⁻¹
    calc
      ρ g = (ρ g * U) * U⁻¹ := by simp only [mul_assoc, mul_inv_cancel, mul_one]
      _ = (U * GeneralLinearGroup.map S.val.toRingHom (τ g)) * U⁻¹ :=
        congrArg (fun V : GeneralLinearGroup ι R => V * U⁻¹) hmul

end
end Dubon2026

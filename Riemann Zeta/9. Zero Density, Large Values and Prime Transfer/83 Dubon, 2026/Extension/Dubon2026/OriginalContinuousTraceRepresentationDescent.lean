import Dubon2026.OriginalTraceRepresentationDescent
import Dubon2026.CoefficientSubalgebraRepresentationContinuity
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Actual continuous whole-representation descent to the original closed trace coefficients -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O R : Type} [Group G] [TopologicalSpace G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [WithIdeal R] [IsAdicComplete (WithIdeal.i : Ideal R) R]

/-- The entire actual continuous original representation descends, up to original strict conjugacy, to a continuous representation over its literal closed trace coefficient algebra with the inherited original topology. -/
theorem originalContinuousTraceRepresentationDescent_exists
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →ₜ* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ.toMonoidHom)))] (i₀ : ι) :
    ∃ τ : G →ₜ* GeneralLinearGroup ι (closedMatrixTraceAlgebra (O := O) ρ.toMonoidHom),
      MatrixStrictlyConjugate (IsLocalRing.residue R)
        ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O) ρ.toMonoidHom).val.toRingHom).comp
          τ.toMonoidHom) ρ.toMonoidHom := by
  obtain ⟨τ, hτ⟩ := originalTraceRepresentationDescent_exists (L := L) hR eR ρ.toMonoidHom i₀
  exact ⟨⟨τ, matrixStrictlyConjugate_subalgebra_continuous (IsLocalRing.residue R)
    (closedMatrixTraceAlgebra (O := O) ρ.toMonoidHom) ρ.toMonoidHom ρ.continuous τ hτ⟩, hτ⟩

end
end Dubon2026

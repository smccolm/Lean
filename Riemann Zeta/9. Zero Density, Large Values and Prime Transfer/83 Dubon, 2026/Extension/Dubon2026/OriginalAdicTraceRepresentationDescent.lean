import Dubon2026.OriginalContinuousTraceRepresentationDescent

/-! # Whole original trace descent in a proved original maximal-adic topology -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι O R : Type} [Group G] [TopologicalSpace G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R]
  [Algebra O R] [t : TopologicalSpace R] [IsTopologicalRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- The original continuous representation descends over its actual closed trace algebra in the original topology whenever that topology is proved maximal-adic; the topology equality is transported explicitly. -/
theorem originalAdicContinuousTraceRepresentationDescent_exists
    {L : Type} [Field L] [Algebra (IsLocalRing.ResidueField R) L] [IsAlgClosed L]
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (ρ : G →ₜ* GeneralLinearGroup ι R)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue R)).comp ρ.toMonoidHom)))] (i₀ : ι) :
    ∃ τ : G →ₜ* GeneralLinearGroup ι (closedMatrixTraceAlgebra (O := O) ρ.toMonoidHom),
      MatrixStrictlyConjugate (IsLocalRing.residue R)
        ((GeneralLinearGroup.map (closedMatrixTraceAlgebra (O := O) ρ.toMonoidHom).val.toRingHom).comp
          τ.toMonoidHom) ρ.toMonoidHom := by
  change t = (IsLocalRing.maximalIdeal R).adicTopology at hR
  subst t
  letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
  exact originalContinuousTraceRepresentationDescent_exists (L := L) rfl eR ρ i₀

end
end Dubon2026

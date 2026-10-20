import Dubon2026.CoefficientSubalgebraResidue

/-! Compatibility of the actual trace-ring and universal coefficient
reductions in DUB-17. Every residue identification is over the original
base ring, whose residue map is already surjective. -/

namespace Dubon2026
noncomputable section

variable {O R : Type} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- The original base algebra uniquely determines a coefficient residue
identification; it cannot introduce a residual field automorphism. -/
theorem localCoefficientResidueEquiv_unique
    (e f : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O) : e = f := by
  ext x
  obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (e x)
  have hx : algebraMap O (IsLocalRing.ResidueField R) o = x := by
    apply e.injective
    rw [e.commutes]
    exact ho
  rw [← hx, e.commutes, f.commutes]

/-- Any original-base residue identification on a local coefficient
subalgebra yields exactly the ambient reduction restricted to it. -/
theorem localCoefficientReduction_subalgebra_eq
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom]
    (eS : IsLocalRing.ResidueField S ≃ₐ[O] IsLocalRing.ResidueField O) :
    localCoefficientReduction eS = (localCoefficientReduction eR).comp S.val := by
  rw [localCoefficientResidueEquiv_unique eS (coefficientSubalgebraResidueEquiv eR S)]
  exact coefficientSubalgebraReduction_eq eR S

end
end Dubon2026

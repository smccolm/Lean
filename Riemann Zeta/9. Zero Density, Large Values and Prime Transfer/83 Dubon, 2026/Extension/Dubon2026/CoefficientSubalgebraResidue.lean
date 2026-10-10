import Dubon2026.LocalCoefficientReduction
import Dubon2026.SurjectiveLocalResidue
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # Actual residue fields of local original coefficient subalgebras -/

namespace Dubon2026
noncomputable section

variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]

/-- The original coefficient constants already make the true residue map of a local subalgebra onto the ambient residue field surjective. The subalgebra inclusion itself need not be surjective. -/
theorem coefficientSubalgebra_residue_surjective
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom] :
    Function.Surjective (localResidueAlgebraMap S.val) := by
  intro y
  obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (eR y)
  refine ⟨algebraMap O (IsLocalRing.ResidueField S) o, ?_⟩
  apply eR.injective
  rw [(localResidueAlgebraMap S.val).commutes, eR.commutes]
  exact ho

/-- The genuine residue algebra of the original local subalgebra has the same original coefficient residue field. -/
def coefficientSubalgebraResidueEquiv
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom] :
    IsLocalRing.ResidueField S ≃ₐ[O] IsLocalRing.ResidueField O :=
  (AlgEquiv.ofBijective (localResidueAlgebraMap S.val)
    ⟨(localResidueAlgebraMap S.val).injective,
      coefficientSubalgebra_residue_surjective eR S⟩).trans eR

/-- The true residue equivalence evaluates to the actual ambient coefficient reduction on every original subalgebra element. -/
theorem coefficientSubalgebraResidueEquiv_residue
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom] (x : S) :
    coefficientSubalgebraResidueEquiv eR S (IsLocalRing.residue S x) =
      localCoefficientReduction eR (x : R) := rfl

/-- The entire original reduction map on the local coefficient subalgebra is the restriction of the actual ambient reduction. -/
theorem coefficientSubalgebraReduction_eq
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom] :
    localCoefficientReduction (coefficientSubalgebraResidueEquiv eR S) =
      (localCoefficientReduction eR).comp S.val := by
  ext x
  exact coefficientSubalgebraResidueEquiv_residue eR S x

end
end Dubon2026

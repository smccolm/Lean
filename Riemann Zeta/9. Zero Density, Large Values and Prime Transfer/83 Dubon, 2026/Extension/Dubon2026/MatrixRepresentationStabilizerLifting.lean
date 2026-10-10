import Dubon2026.LocalMatrixRepresentationCentralizer
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Lifting genuine representation stabilizers along original local coefficient surjections -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι A B L : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [Field L] [Algebra (IsLocalRing.ResidueField B) L] [IsAlgClosed L]

/-- A stabilizer of the actual scalar-reduced representation lifts to an original stabilizer along a genuine surjective local coefficient map when that reduced representation has absolutely irreducible true residue. -/
theorem matrixRepresentation_stabilizer_lifts
    (f : A →+* B) (hf : Function.Surjective f)
    (ρ : G →* GeneralLinearGroup ι A)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue B)).comp
          ((GeneralLinearGroup.map f).comp ρ))))]
    (U : GeneralLinearGroup ι B)
    (hU : ∀ g, U * GeneralLinearGroup.map f (ρ g) = GeneralLinearGroup.map f (ρ g) * U) :
    ∃ V : GeneralLinearGroup ι A,
      GeneralLinearGroup.map f V = U ∧ ∀ g, V * ρ g = ρ g * V := by
  letI : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨c, hc⟩ := localMatrixRepresentation_stabilizer_scalar_unit (L := L)
    ((GeneralLinearGroup.map f).comp ρ) U hU
  obtain ⟨a, ha⟩ := IsLocalRing.surjective_units_map_of_local_ringHom f hf inferInstance c
  refine ⟨GeneralLinearGroup.scalar ι a, ?_, ?_⟩
  · rw [hc]
    apply Units.ext
    ext i j
    have h : f (a : A) = (c : B) := congrArg (fun u : Bˣ => (u : B)) ha
    by_cases hij : i = j
    · simp [GeneralLinearGroup.scalar, GeneralLinearGroup.map, Matrix.scalar_apply, hij, h]
    · simp [GeneralLinearGroup.scalar, GeneralLinearGroup.map, Matrix.scalar_apply, hij]
  · intro g
    apply Units.ext
    exact Matrix.scalar_commute (a : A) (Commute.all (a : A)) (ρ g).val

end
end Dubon2026

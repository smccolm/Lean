import Dubon2026.AlgebraicLocalResidueLift

/-! The actual map to the original residue Galois group. The scalar field
is the original base residue field, and the kernel is actual inertia.
This is the entry bridge for finite inertia quotient cyclicity in DUB-17. -/

namespace Dubon2026
noncomputable section

variable (K L : Type) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [IsGalois K L]

attribute [local instance] algebraicLocalIntegerAction algebraicLocalIntegerBaseAlgebra

/-- The actual integer inclusion is a local ring homomorphism. -/
@[implicit_reducible]
def algebraicLocalIntegerBaseIsLocalHom :
    IsLocalHom (algebraMap (algebraicLocalIntegerRing K) (algebraicLocalIntegerRing L)) :=
  ((IsLocalRing.local_hom_TFAE _).out 4 0).mp
    (algebraicLocalInteger_maximalIdeal_under K L)

attribute [local instance] algebraicLocalIntegerBaseIsLocalHom

/-- The residue action is linear over the actual base residue field. -/
def algebraicLocalResidueGalois : Gal(L/K) →*
    Gal(IsLocalRing.ResidueField (algebraicLocalIntegerRing L)/
      IsLocalRing.ResidueField (algebraicLocalIntegerRing K)) where
  toFun g := {
    MulSemiringAction.toRingEquiv Gal(L/K) _ g with
    commutes' := fun x => by
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      rw [IsLocalRing.ResidueField.algebraMap_residue]
      change g • IsLocalRing.residue _ (algebraMap _ _ x) = _
      rw [← IsLocalRing.ResidueField.residue_smul]
      congr 1
      apply Subtype.ext
      exact g.commutes x.val }
  map_one' := AlgEquiv.ext (one_smul _)
  map_mul' g h := AlgEquiv.ext (mul_smul g h)

/-- The map on residue Galois groups acts on the same original residue elements. -/
theorem algebraicLocalResidueGalois_apply (g : Gal(L/K))
    (x : IsLocalRing.ResidueField (algebraicLocalIntegerRing L)) :
    algebraicLocalResidueGalois K L g x = g • x := rfl

/-- The original residue extension is algebraic, derived from the
profinite invariant action on the original integer rings. -/
theorem algebraicLocalResidue_isAlgebraic :
    Algebra.IsAlgebraic (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))
      (IsLocalRing.ResidueField (algebraicLocalIntegerRing L)) := by
  let R := algebraicLocalIntegerRing K
  let S := algebraicLocalIntegerRing L
  letI : SMulCommClass Gal(L/K) R S := algebraicLocalIntegerAction_smulComm K L
  letI : Algebra.IsInvariant R S Gal(L/K) := algebraicLocalIntegerAction_isInvariant K L
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  letI : ContinuousSMul Gal(L/K) S := algebraicLocalIntegerAction_continuous K L
  letI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral_of_profinite (G := Gal(L/K))
  letI : Algebra.IsIntegral R (IsLocalRing.ResidueField S) :=
    inferInstanceAs (Algebra.IsIntegral R (S ⧸ IsLocalRing.maximalIdeal S))
  exact ⟨fun x => ((Algebra.IsIntegral.isIntegral (R := R) x).tower_top
    (A := IsLocalRing.ResidueField R)).isAlgebraic⟩

end
end Dubon2026

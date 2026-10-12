import Dubon2026.ContinuousGaloisUnitBaseChange

/-! # Composition of the actual infinite Galois unit base-change maps -/

namespace Dubon2026
noncomputable section

variable (K E F L M N : Type) [Field K] [Field E] [Field F] [Field L] [Field M] [Field N]
  [Algebra K E] [Algebra E F] [Algebra K F]
  [Algebra K L] [Algebra K M] [Algebra K N]
  [Algebra E M] [Algebra E N] [Algebra F N]
  [Algebra L M] [Algebra M N] [Algebra L N]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [IsScalarTower E F N] [IsScalarTower E M N]
  [IsScalarTower K F N] [IsScalarTower K L N] [IsScalarTower L M N]
  [Normal K L] [Normal E M]

/-- Two original changes of fixed base and extension field compose
to the literal original restriction, as proved on every field element. -/
theorem galoisBaseChangeRestriction_comp (g : Gal(N/F)) :
    galoisBaseChangeRestriction K E L M (galoisBaseChangeRestriction E F M N g) =
      galoisBaseChangeRestriction K F L N g := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L N).injective
  calc
    algebraMap L N (galoisBaseChangeRestriction K E L M
        (galoisBaseChangeRestriction E F M N g) x) =
      algebraMap M N (algebraMap L M (galoisBaseChangeRestriction K E L M
        (galoisBaseChangeRestriction E F M N g) x)) :=
      IsScalarTower.algebraMap_apply L M N _
    _ = algebraMap M N (galoisBaseChangeRestriction E F M N g (algebraMap L M x)) :=
      congrArg (algebraMap M N) (galoisBaseChangeRestriction_commutes K E L M _ x)
    _ = g (algebraMap M N (algebraMap L M x)) :=
      galoisBaseChangeRestriction_commutes E F M N g _
    _ = g (algebraMap L N x) := congrArg g (IsScalarTower.algebraMap_apply L M N x).symm
    _ = algebraMap L N (galoisBaseChangeRestriction K F L N g x) :=
      (galoisBaseChangeRestriction_commutes K F L N g x).symm

variable [IsGalois K L] [IsGalois E M] [IsGalois F N]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits F N)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F N)]

/-- Composition preserves the exact original continuous two-cocycle,
including both literal field inclusions and both original argument restrictions. -/
theorem continuousGaloisUnitBaseChangeCocycle_comp
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    continuousGaloisUnitBaseChangeCocycle E F M N
        (continuousGaloisUnitBaseChangeCocycle K E L M c) =
      continuousGaloisUnitBaseChangeCocycle K F L N c := by
  apply Subtype.ext
  apply Subtype.ext
  funext z
  change Units.map (algebraMap M N).toMonoidHom
    (Units.map (algebraMap L M).toMonoidHom
      (Additive.toMul (Rep.toAdditive (c.val
        (galoisBaseChangeRestriction K E L M (galoisBaseChangeRestriction E F M N z.1),
         galoisBaseChangeRestriction K E L M (galoisBaseChangeRestriction E F M N z.2)))))) =
    Units.map (algebraMap L N).toMonoidHom
      (Additive.toMul (Rep.toAdditive (c.val
        (galoisBaseChangeRestriction K F L N z.1, galoisBaseChangeRestriction K F L N z.2))))
  rw [galoisBaseChangeRestriction_comp K E F L M N,
    galoisBaseChangeRestriction_comp K E F L M N]
  apply Units.ext
  exact (IsScalarTower.algebraMap_apply L M N _).symm

/-- The actual original continuous H2 maps compose under the
genuine field towers, with the original Krull topologies retained. -/
theorem continuousGaloisUnitBaseChangeH2_comp
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    continuousGaloisUnitBaseChangeH2 E F M N (continuousGaloisUnitBaseChangeH2 K E L M x) =
      continuousGaloisUnitBaseChangeH2 K F L N x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [continuousGaloisUnitBaseChangeH2_mk, continuousGaloisUnitBaseChangeH2_mk,
      continuousGaloisUnitBaseChangeH2_mk, continuousGaloisUnitBaseChangeCocycle_comp K E F L M N]

end
end Dubon2026

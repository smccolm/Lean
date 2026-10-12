import Dubon2026.ContinuousCharacterDualH2Pairing
import Dubon2026.ContinuousScalarH2Coordinates
import Dubon2026.TrivialCharacterDualCoordinates

/-! # The split H2/invariant pairing has zero H2 annihilator

Original dual basis coordinates are precisely evaluation on original invariant
basis vectors. The actual continuous coordinate-boundary reconstruction then
proves the H2-side injection in DUB-17's local-duality endpoint argument.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G ι : Type} [Field k] [Group G] [Fintype ι]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

  (b : Module.Basis ι k A) (htrivial : ∀ g a, A.ρ g a = a)

include b htrivial in
/-- The original dual H2 class vanishes if it pairs trivially with every
actual invariant of the split original coefficient module. -/
theorem continuousTrivialCharacterDualH2InvariantPairing_left_zero
    (x : ContinuousRepresentationH2 (characterDualCoefficientRep A χ)
      (finiteCharacterDualAction_continuous A χ hA hχ))
    (hx : ∀ w, continuousCharacterDualH2InvariantPairing A χ hχ hA x w = 0) : x = 0 := by
  classical
  apply continuousScalarH2_eq_zero_of_coordinates (characterDualCoefficientRep A χ) χ b.dualBasis
    (trivialCoefficient_characterDual_scalar A χ htrivial)
    (finiteCharacterDualAction_continuous A χ hA hχ) hχ x
  intro i
  let w : A.ρ.invariants := ⟨b i, fun g => htrivial g (b i)⟩
  have he : continuousCoefficientH2Map (characterDualCoefficientRep A χ) (coefficientCharacterRep χ)
      (b.dualBasis.coord i) continuous_of_discreteTopology
      (scalarCoefficientCoordinate_equivariant (characterDualCoefficientRep A χ) χ b.dualBasis
        (trivialCoefficient_characterDual_scalar A χ htrivial) i)
      (finiteCharacterDualAction_continuous A χ hA hχ) (coefficientCharacterAction_continuous χ hχ) x =
      continuousCharacterDualH2InvariantPairing A χ hχ hA x w := by
    induction x using Submodule.Quotient.induction_on with
    | _ c =>
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      apply Subtype.ext
      funext z
      exact b.dualBasis_repr (c.val z) i
  exact he.trans (hx w)

include b htrivial in
/-- Original split-module invariant evaluation detects each original dual
H2 class injectively, without assuming any dimension or endpoint duality theorem. -/
theorem continuousTrivialCharacterDualH2InvariantPairing_left_injective :
    Function.Injective (continuousCharacterDualH2InvariantPairing A χ hχ hA) := by
  intro x y h
  apply sub_eq_zero.mp
  apply continuousTrivialCharacterDualH2InvariantPairing_left_zero A χ hχ hA b htrivial
  intro w
  rw [map_sub, LinearMap.sub_apply]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h w)

end
end Dubon2026

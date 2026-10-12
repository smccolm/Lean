import Dubon2026.ContinuousTrivialCharacterDualH2Left

/-! # The opposite split H2/invariant annihilator

Original scalar H2 classes map along actual dual basis sections. Pairing their
images with an invariant recovers its original basis coordinates. A nonzero
scalar H2 class therefore detects every invariant, supplying the opposite
endpoint injection needed in DUB-17's local duality exact sequence.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G ι : Type} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

  (b : Module.Basis ι k A) (htrivial : ∀ g a, A.ρ g a = a)


include htrivial in
omit [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)] in
/-- An original dual basis vector gives an equivariant section from the
actual character line to the character dual of the split coefficient module. -/
theorem trivialCharacterDualBasisSection_equivariant (i : ι) (g : G) (t : k) :
    LinearMap.toSpanSingleton k (characterDualCoefficientRep A χ) (b.coord i)
      ((coefficientCharacterRep χ).ρ g t) =
    (characterDualCoefficientRep A χ).ρ g
      (LinearMap.toSpanSingleton k (characterDualCoefficientRep A χ) (b.coord i) t) := by
  rw [trivialCoefficient_characterDual_scalar A χ htrivial]
  change (χ g * t) • b.coord i = χ g • (t • b.coord i)
  exact mul_smul (χ g) t (b.coord i)

/-- Evaluation of an original H2 dual basis section is multiplication by
the original invariant's basis coordinate, in the original scalar H2 group. -/
theorem continuousTrivialCharacterDualH2_basisSection_pairing (i : ι)
    (c : ContinuousRepresentationH2 (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ))
    (w : A.ρ.invariants) :
    continuousCharacterDualH2InvariantPairing A χ hχ hA
      (continuousCoefficientH2Map (coefficientCharacterRep χ) (characterDualCoefficientRep A χ)
        (LinearMap.toSpanSingleton k (characterDualCoefficientRep A χ) (b.coord i))
        continuous_of_discreteTopology (trivialCharacterDualBasisSection_equivariant A χ b htrivial i)
        (coefficientCharacterAction_continuous χ hχ) (finiteCharacterDualAction_continuous A χ hA hχ) c) w =
      b.coord i w.val • c := by
  induction c using Submodule.Quotient.induction_on with
  | _ c =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change c.val z * b.coord i w.val = b.coord i w.val * c.val z
    exact mul_comm _ _

include b htrivial in
/-- A nonzero original scalar H2 class forces the split invariant-side
annihilator to vanish. This scalar input is provided by the local invariant. -/
theorem continuousTrivialCharacterDualH2InvariantPairing_right_zero
    (c : ContinuousRepresentationH2 (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ))
    (hc : c ≠ 0) (w : A.ρ.invariants)
    (hw : ∀ x, continuousCharacterDualH2InvariantPairing A χ hχ hA x w = 0) : w = 0 := by
  apply Subtype.ext
  apply b.ext_elem
  intro i
  have hz : b.coord i w.val • c = 0 :=
    (continuousTrivialCharacterDualH2_basisSection_pairing A χ hχ hA b htrivial i c w).symm.trans (hw _)
  exact ((smul_eq_zero.mp hz).resolve_right hc).trans (map_zero (b.coord i)).symm

include b htrivial in
/-- Under the same nonzero scalar H2 input, the original invariant-side map
of the split coefficient pairing is injective. -/
theorem continuousTrivialCharacterDualH2InvariantPairing_right_injective
    (c : ContinuousRepresentationH2 (coefficientCharacterRep χ) (coefficientCharacterAction_continuous χ hχ))
    (hc : c ≠ 0) : Function.Injective (continuousCharacterDualH2InvariantPairing A χ hχ hA).flip := by
  intro x y h
  apply sub_eq_zero.mp
  apply continuousTrivialCharacterDualH2InvariantPairing_right_zero A χ hχ hA b htrivial c hc
  intro z
  rw [map_sub]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h z)

end
end Dubon2026

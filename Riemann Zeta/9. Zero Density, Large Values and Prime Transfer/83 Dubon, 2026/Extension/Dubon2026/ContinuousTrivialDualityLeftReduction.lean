import Dubon2026.ContinuousScalarH1Coordinates
import Dubon2026.ContinuousCharacterDualCupNaturality

/-! # Split-module left nondegeneracy reduces to the scalar original cup

Actual basis coordinates and the proved original cup naturality reduce the
left annihilator to the scalar Kummer case. The scalar premise is explicit;
it must be instantiated by the existing local theorem before local duality
is asserted. This is the split-coefficient step serving DUB-17.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G ι : Type} [Field k] [Finite k] [Group G] [Fintype ι]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (χ : G →* k) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A χ)]
  [DiscreteTopology (characterDualCoefficientRep A χ)]
  [TopologicalSpace (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (coefficientCharacterRep (1 : G →* k)) χ)]
  (b : Module.Basis ι k A) (htrivial : ∀ g a, A.ρ g a = a)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

include b htrivial in
/-- For an actual split coefficient module, scalar left nondegeneracy implies
zero left annihilator of the original character-dual cup. The proof uses the
same original coordinates, coefficient maps and cohomology classes. -/
theorem continuousTrivialCharacterDualH1Cup_left_zero
    (hbase : Function.Injective (continuousCharacterDualH1Cup
      (coefficientCharacterRep (1 : G →* k)) χ hχ
      (coefficientCharacterAction_continuous (1 : G →* k) continuous_const)))
    (x : ContinuousRepresentationH1 A hA)
    (hx : ∀ y, continuousCharacterDualH1Cup A χ hχ hA x y = 0) : x = 0 := by
  have hscalar : ∀ g a, A.ρ g a = (1 : G →* k) g • a := by
    intro g a
    simpa only [MonoidHom.one_apply, one_smul] using htrivial g a
  apply continuousScalarH1_eq_zero_of_coordinates A (1 : G →* k) b hscalar hA continuous_const x
  intro i
  apply hbase
  apply LinearMap.ext
  intro y
  rw [map_zero, LinearMap.zero_apply]
  have he := continuousCharacterDualH1Cup_naturality A χ hχ hA
    (coefficientCharacterRep (1 : G →* k))
    (coefficientCharacterAction_continuous (1 : G →* k) continuous_const)
    (b.coord i) (scalarCoefficientCoordinate_equivariant A (1 : G →* k) b hscalar i) x y
  exact he.symm.trans (hx _)

end
end Dubon2026

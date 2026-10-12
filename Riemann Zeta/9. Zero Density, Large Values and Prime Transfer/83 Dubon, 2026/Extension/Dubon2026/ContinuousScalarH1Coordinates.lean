import Dubon2026.CharacterDualCoefficientSequence
import Dubon2026.ContinuousCohomologyCoefficientMap
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Actual scalar-action H1 is detected by its finite basis coordinates

Coordinate coboundaries reconstruct one original coefficient coboundary. This
is the finite direct-sum step needed to extend the proved local Kummer pairing
to the split coefficient module in DUB-17's induced-module duality argument.
It uses the original continuous cohomology quotient throughout.
-/

namespace Dubon2026
noncomputable section

variable {k G ι : Type} [Field k] [Group G]
  (A : Rep.{0} k G)
  (χ : G →* k) (b : Module.Basis ι k A)
  (hscalar : ∀ g a, A.ρ g a = χ g • a)

include hscalar in
/-- Each original basis coordinate intertwines the actual scalar action with
the same original character line. -/
theorem scalarCoefficientCoordinate_equivariant (i : ι) (g : G) (a : A) :
    b.coord i (A.ρ g a) = (coefficientCharacterRep χ).ρ g (b.coord i a) := by
  rw [hscalar, map_smul]
  rfl

variable [Fintype ι] [TopologicalSpace k] [IsTopologicalRing k]
  [TopologicalSpace G]
  [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul k A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hχ : Continuous χ)

/-- Vanishing of all actual scalar-coordinate H1 classes forces the original
class to vanish. Coordinate boundary witnesses reconstruct one original
coefficient, so no injectivity assumption on cohomology is retained. -/
theorem continuousScalarH1_eq_zero_of_coordinates (x : ContinuousRepresentationH1 A hA)
    (hx : ∀ i, continuousCoefficientH1Map A (coefficientCharacterRep χ) (b.coord i)
      continuous_of_discreteTopology (scalarCoefficientCoordinate_equivariant A χ b hscalar i)
      hA (coefficientCharacterAction_continuous χ hχ) x = 0) : x = 0 := by
  classical
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    have hv : ∀ i, ∃ v : k, ∀ g : G, χ g * v - v = b.coord i (c.val g) := by
      intro i
      have hi := hx i
      rw [continuousCoefficientH1Map_mk] at hi
      obtain ⟨v, he⟩ := (Submodule.Quotient.mk_eq_zero _).mp hi
      refine ⟨v, fun g => ?_⟩
      exact congrArg (fun u : continuousRepresentationCocyclesOne (coefficientCharacterRep χ) =>
        u.val g) he
    choose v hv using hv
    let a : A := b.equivFun.symm v
    have ha (i : ι) : b.coord i a = v i :=
      congrArg (fun f : ι → k => f i) (b.equivFun.apply_symm_apply v)
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext g
    apply b.equivFun.injective
    funext i
    change b.coord i (A.ρ g a - a) = b.coord i (c.val g)
    rw [map_sub, hscalar, map_smul, ha]
    exact hv i g

end
end Dubon2026

import Dubon2026.ContinuousScalarH1Coordinates

/-! # Original scalar-action H2 is detected by finite basis coordinates

Continuous coordinate boundaries reconstruct one original continuous
coefficient boundary. This supplies the split-module H0/H2 endpoint in the
exact-sequence local duality argument needed for DUB-17, without assuming an
H2 dimension or a cohomological coordinate equivalence.
-/

namespace Dubon2026
noncomputable section

variable {k G ι : Type} [Field k] [Group G] [Fintype ι]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul k A]
  (χ : G →* k) (b : Module.Basis ι k A) (hscalar : ∀ g a, A.ρ g a = χ g • a)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hχ : Continuous χ)

/-- If all actual scalar-coordinate H2 classes vanish, the original class
vanishes: continuous coordinate one-cochains reconstruct its original boundary. -/
theorem continuousScalarH2_eq_zero_of_coordinates (x : ContinuousRepresentationH2 A hA)
    (hx : ∀ i, continuousCoefficientH2Map A (coefficientCharacterRep χ) (b.coord i)
      continuous_of_discreteTopology (scalarCoefficientCoordinate_equivariant A χ b hscalar i)
      hA (coefficientCharacterAction_continuous χ hχ) x = 0) : x = 0 := by
  classical
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    have hv : ∀ i, ∃ v : C(G, k), ∀ g h : G,
        χ g * v h - v (g * h) + v g = b.coord i (c.val (g, h)) := by
      intro i
      have hi := hx i
      rw [continuousCoefficientH2Map_mk] at hi
      obtain ⟨v, he⟩ := (Submodule.Quotient.mk_eq_zero _).mp hi
      refine ⟨v, fun g h => ?_⟩
      exact congrArg (fun u : continuousRepresentationCocyclesTwo (coefficientCharacterRep χ) =>
        u.val (g, h)) he
    choose v hv using hv
    let f : C(G, A) := ⟨fun g => b.equivFun.symm (fun i => v i g),
      continuous_of_discreteTopology.comp (continuous_pi (fun i => (v i).continuous))⟩
    have hf (i : ι) (g : G) : b.coord i (f g) = v i g :=
      congrArg (fun u : ι → k => u i) (b.equivFun.apply_symm_apply (fun i => v i g))
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨f, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext z
    apply b.equivFun.injective
    funext i
    change b.coord i (A.ρ z.1 (f z.2) - f (z.1 * z.2) + f z.1) = b.coord i (c.val z)
    rw [map_add, map_sub, hscalar, map_smul, hf, hf, hf]
    exact hv i z.1 z.2

end
end Dubon2026

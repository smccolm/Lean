import Dubon2026.ContinuousAlgebraicConnecting
import Dubon2026.ContinuousCohomologyRestriction

/-! # Connecting naturality in the actual continuous H2 quotient

The existing independence-of-lift theorem supplies the continuous boundary
witness. This is the precise comparison needed to retain continuous H2
information in DUB-17's descended finite relation cup argument.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (π : G →* H) (hπ : Continuous π)
  (X : ShortComplex (Rep.{0} R H)) (Y : ShortComplex (Rep.{0} R G))
  (d : (Rep.resFunctor π).mapShortComplex.obj X ⟶ Y)
  (hX : X.ShortExact) (hY : Y.ShortExact)
  [TopologicalSpace X.X₁] [DiscreteTopology X.X₁] [ContinuousSMul R X.X₁]
  [TopologicalSpace X.X₂] [DiscreteTopology X.X₂] [ContinuousSMul R X.X₂]
  [TopologicalSpace X.X₃] [DiscreteTopology X.X₃] [ContinuousSMul R X.X₃]
  [TopologicalSpace Y.X₁] [DiscreteTopology Y.X₁] [ContinuousSMul R Y.X₁]
  [TopologicalSpace Y.X₂] [DiscreteTopology Y.X₂] [ContinuousSMul R Y.X₂]
  [TopologicalSpace Y.X₃] [DiscreteTopology Y.X₃] [ContinuousSMul R Y.X₃]
  (hX₁ : Continuous (fun z : H × X.X₁ => X.X₁.ρ z.1 z.2))
  (hX₂ : Continuous (fun z : H × X.X₂ => X.X₂.ρ z.1 z.2))
  (hX₃ : Continuous (fun z : H × X.X₃ => X.X₃.ρ z.1 z.2))
  (hY₁ : Continuous (fun z : G × Y.X₁ => Y.X₁.ρ z.1 z.2))
  (hY₂ : Continuous (fun z : G × Y.X₂ => Y.X₂.ρ z.1 z.2))
  (hY₃ : Continuous (fun z : G × Y.X₃ => Y.X₃.ρ z.1 z.2))

/-- The actual continuous connecting class commutes with a literal short
complex diagram over a continuous group map. No comparison with ordinary
cohomology or injectivity of a forgetful map is used. -/
theorem continuousShortComplexConnectingMap_groupChange
    (x : ContinuousRepresentationH1 X.X₃ hX₃) :
    continuousCoefficientH2Map (Rep.res π X.X₁) Y.X₁ d.τ₁.hom.toLinearMap
      continuous_of_discreteTopology (Rep.hom_comm_apply d.τ₁)
      (restrictedCoefficientAction_continuous X.X₁ π hπ hX₁) hY₁
      (continuousRepresentationH2Restriction X.X₁ hX₁ π hπ
        (continuousShortComplexConnectingMap X hX hX₁ hX₂ hX₃ x)) =
    continuousShortComplexConnectingMap Y hY hY₁ hY₂ hY₃
      (continuousCoefficientH1Map (Rep.res π X.X₃) Y.X₃ d.τ₃.hom.toLinearMap
        continuous_of_discreteTopology (Rep.hom_comm_apply d.τ₃)
        (restrictedCoefficientAction_continuous X.X₃ π hπ hX₃) hY₃
        (continuousRepresentationH1Restriction X.X₃ hX₃ π hπ x)) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    let hf := (Rep.mono_iff_injective X.f).mp hX.mono_f
    let hg := (Rep.epi_iff_surjective X.g).mp hX.epi_g
    let he := (hX.exact.map (forget₂ (Rep R H) (ModuleCat R))).moduleCat_range_eq_ker
    let b := coefficientConnectingOneLift X.X₂ X.X₃ X.g.hom.toLinearMap hg c
    let a := coefficientConnectingTwoCocycle X.X₁ X.X₂ X.X₃ X.f.hom.toLinearMap hf
      (Rep.hom_comm_apply X.f) X.g.hom.toLinearMap hg (Rep.hom_comm_apply X.g) he hX₂ c
    let c' := continuousCoefficientCocycleOneMap (Rep.res π X.X₃) Y.X₃
      d.τ₃.hom.toLinearMap continuous_of_discreteTopology (Rep.hom_comm_apply d.τ₃)
      (continuousRepresentationCocycleOneRestriction X.X₃ π hπ c)
    let a' := continuousCoefficientCocycleTwoMap (Rep.res π X.X₁) Y.X₁
      d.τ₁.hom.toLinearMap continuous_of_discreteTopology (Rep.hom_comm_apply d.τ₁)
      (continuousRepresentationCocycleTwoRestriction X.X₁ π hπ a)
    let b' : C(G, Y.X₂) := ⟨fun g => d.τ₂.hom (b (π g)),
      (continuous_of_discreteTopology : Continuous (fun z : X.X₂ => d.τ₂.hom z)).comp
        (b.continuous.comp hπ)⟩
    have hb' (g : G) : Y.g.hom (b' g) = c'.val g := by
      have hd := congrArg (fun m : Rep.res π X.X₂ ⟶ Y.X₃ => m.hom (b (π g))) d.comm₂₃
      change Y.g.hom (d.τ₂.hom (b (π g))) = d.τ₃.hom (c.val (π g))
      calc
        _ = d.τ₃.hom (X.g.hom (b (π g))) := hd
        _ = _ := congrArg d.τ₃.hom
          (coefficientConnectingOneLift_project X.X₂ X.X₃ X.g.hom.toLinearMap hg c (π g))
    have ha' (z : G × G) : Y.f.hom (a'.val z) =
        (continuousRepresentationCoboundaryTwo Y.X₂ hY₂ b').val z := by
      have hd := congrArg (fun m : Rep.res π X.X₁ ⟶ Y.X₂ =>
        m.hom (a.val (π z.1, π z.2))) d.comm₁₂
      change Y.f.hom (d.τ₁.hom (a.val (π z.1, π z.2))) =
        Y.X₂.ρ z.1 (d.τ₂.hom (b (π z.2))) - d.τ₂.hom (b (π (z.1 * z.2))) +
          d.τ₂.hom (b (π z.1))
      change Y.f.hom (d.τ₁.hom (a.val (π z.1, π z.2))) =
        d.τ₂.hom (X.f.hom (a.val (π z.1, π z.2))) at hd
      rw [hd]
      erw [coefficientConnectingTwoCocycle_map]
      change d.τ₂.hom (X.X₂.ρ (π z.1) (b (π z.2)) - b (π z.1 * π z.2) + b (π z.1)) = _
      erw [map_add, map_sub, ← π.map_mul]
      erw [Rep.hom_comm_apply d.τ₂]
    change (Submodule.Quotient.mk a' : ContinuousRepresentationH2 Y.X₁ hY₁) =
      Submodule.Quotient.mk
        (coefficientConnectingTwoCocycle Y.X₁ Y.X₂ Y.X₃ Y.f.hom.toLinearMap
          ((Rep.mono_iff_injective Y.f).mp hY.mono_f) (Rep.hom_comm_apply Y.f)
          Y.g.hom.toLinearMap ((Rep.epi_iff_surjective Y.g).mp hY.epi_g)
          (Rep.hom_comm_apply Y.g)
          (hY.exact.map (forget₂ (Rep R G) (ModuleCat R))).moduleCat_range_eq_ker hY₂ c')
    exact (coefficientConnectingClass_eq_of_lift Y.X₁ Y.X₂ Y.X₃ Y.f.hom.toLinearMap
      ((Rep.mono_iff_injective Y.f).mp hY.mono_f) (Rep.hom_comm_apply Y.f)
      Y.g.hom.toLinearMap ((Rep.epi_iff_surjective Y.g).mp hY.epi_g)
      (Rep.hom_comm_apply Y.g)
      (hY.exact.map (forget₂ (Rep R G) (ModuleCat R))).moduleCat_range_eq_ker
      hY₁ hY₂ c' a' b' hb' ha').symm

end
end Dubon2026

import Dubon2026.ContinuousShortComplexInvariantConnecting
import Dubon2026.ContinuousCohomologyCoefficientMap

/-! Compare the continuous invariant connecting class under an actual
coefficient diagram. The original chosen lift and its image prove the
comparison by native lift independence. This supplies the S-unit to local
unit coefficient step for DUB-17's prescribed local H1 recovery. -/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G]
  (X Y : ShortComplex (Rep.{0} R G)) (hX : X.ShortExact) (hY : Y.ShortExact)
  [TopologicalSpace X.X₁] [IsTopologicalAddGroup X.X₁] [ContinuousSMul R X.X₁]
  [TopologicalSpace X.X₂] [DiscreteTopology X.X₂]
  [TopologicalSpace Y.X₁] [IsTopologicalAddGroup Y.X₁] [ContinuousSMul R Y.X₁]
  [TopologicalSpace Y.X₂] [DiscreteTopology Y.X₂]
  (hA : Continuous (fun z : G × X.X₁ => X.X₁.ρ z.1 z.2))
  (hB : Continuous (fun z : G × X.X₂ => X.X₂.ρ z.1 z.2))
  (hA' : Continuous (fun z : G × Y.X₁ => Y.X₁.ρ z.1 z.2))
  (hB' : Continuous (fun z : G × Y.X₂ => Y.X₂.ρ z.1 z.2))
  (d : X ⟶ Y) (hd : Continuous d.τ₁.hom)

/-- The actual coefficient H1 map preserves the continuous invariant
connecting class through a commuting short-exact coefficient diagram. -/
theorem continuousInvariantConnecting_naturality (c : X.X₃.ρ.invariants) :
    let cY : Y.X₃.ρ.invariants := ⟨d.τ₃.hom c.val, fun g =>
      (Rep.hom_comm_apply d.τ₃ g c.val).symm.trans (congrArg d.τ₃.hom (c.property g))⟩
    continuousCoefficientH1Map X.X₁ Y.X₁ d.τ₁.hom.toLinearMap hd
      (Rep.hom_comm_apply d.τ₁) hA hA'
      (continuousShortComplexInvariantConnectingMap X hX hA hB c) =
        continuousShortComplexInvariantConnectingMap Y hY hA' hB' cY := by
  intro cY
  let hmono := (Rep.mono_iff_injective X.f).mp hX.mono_f
  let hepi := (Rep.epi_iff_surjective X.g).mp hX.epi_g
  let hexact := (hX.exact.map (forget₂ (Rep R G) (ModuleCat R))).moduleCat_range_eq_ker
  let a := coefficientInvariantConnectingCocycle X.X₁ X.X₂ X.X₃
    X.f.hom.toLinearMap hmono (Rep.hom_comm_apply X.f)
    X.g.hom.toLinearMap hepi (Rep.hom_comm_apply X.g) hexact hB c
  let b := exactCoefficientSection X.g.hom.toLinearMap hepi c.val
  let aY := continuousCoefficientCocycleOneMap X.X₁ Y.X₁ d.τ₁.hom.toLinearMap hd
    (Rep.hom_comm_apply d.τ₁) a
  change (Submodule.Quotient.mk aY : ContinuousRepresentationH1 Y.X₁ hA') = _
  symm
  apply coefficientInvariantConnectingClass_eq_of_lift Y.X₁ Y.X₂ Y.X₃
    Y.f.hom.toLinearMap ((Rep.mono_iff_injective Y.f).mp hY.mono_f) (Rep.hom_comm_apply Y.f)
    Y.g.hom.toLinearMap ((Rep.epi_iff_surjective Y.g).mp hY.epi_g) (Rep.hom_comm_apply Y.g)
    (hY.exact.map (forget₂ (Rep R G) (ModuleCat R))).moduleCat_range_eq_ker hA' hB' cY aY
    (d.τ₂.hom b)
  · exact (congrArg (fun m => m.hom b) d.comm₂₃).trans
      (congrArg d.τ₃.hom (exactCoefficientSection_rightInverse X.g.hom.toLinearMap hepi c.val))
  · intro g
    change Y.f.hom (d.τ₁.hom (a.val g)) = _
    calc
      Y.f.hom (d.τ₁.hom (a.val g)) = d.τ₂.hom (X.f.hom (a.val g)) :=
        congrArg (fun m => m.hom (a.val g)) d.comm₁₂
      _ = d.τ₂.hom (X.X₂.ρ g b - b) := congrArg d.τ₂.hom
        (coefficientInvariantConnectingCocycle_map X.X₁ X.X₂ X.X₃
          X.f.hom.toLinearMap hmono (Rep.hom_comm_apply X.f)
          X.g.hom.toLinearMap hepi (Rep.hom_comm_apply X.g) hexact hB c g)
      _ = Y.X₂.ρ g (d.τ₂.hom b) - d.τ₂.hom b := by
        rw [map_sub, Rep.hom_comm_apply]

end
end Dubon2026

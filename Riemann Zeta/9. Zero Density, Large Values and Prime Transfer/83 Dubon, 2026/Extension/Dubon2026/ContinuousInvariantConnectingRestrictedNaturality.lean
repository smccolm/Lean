import Dubon2026.ContinuousInvariantConnectingRestriction
import Dubon2026.ContinuousInvariantConnectingNaturality

/-! Restrict an original continuous connecting class and apply an actual
local coefficient diagram in one comparison. This is the precise map
used by the arithmetic S-unit localization diagram in DUB-17. -/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  (X : ShortComplex (Rep.{0} R G)) (hX : X.ShortExact)
  [TopologicalSpace X.X₁] [IsTopologicalAddGroup X.X₁] [ContinuousSMul R X.X₁]
  [TopologicalSpace X.X₂] [DiscreteTopology X.X₂]
  (hA : Continuous (fun z : G × X.X₁ => X.X₁.ρ z.1 z.2))
  (hB : Continuous (fun z : G × X.X₂ => X.X₂.ρ z.1 z.2))
  (j : H →* G) (hj : Continuous j)
  (Y : ShortComplex (Rep.{0} R H)) (hY : Y.ShortExact)
  [TopologicalSpace Y.X₁] [IsTopologicalAddGroup Y.X₁] [ContinuousSMul R Y.X₁]
  [TopologicalSpace Y.X₂] [DiscreteTopology Y.X₂]
  (hA' : Continuous (fun z : H × Y.X₁ => Y.X₁.ρ z.1 z.2))
  (hB' : Continuous (fun z : H × Y.X₂ => Y.X₂.ρ z.1 z.2))
  (d : X.map (Rep.resFunctor j) ⟶ Y)
  (hd : Continuous (show X.X₁ → Y.X₁ from d.τ₁.hom))

/-- The actual restriction followed by the local coefficient map
carries the original connecting class to the connecting class of the
same locally mapped invariant. -/
theorem continuousInvariantConnecting_restricted_naturality (c : X.X₃.ρ.invariants) :
    let cH : (restrictedCoefficientRep X.X₃ j).ρ.invariants :=
      ⟨c.val, fun h => c.property (j h)⟩
    let cY : Y.X₃.ρ.invariants := ⟨d.τ₃.hom cH.val, fun h =>
      (Rep.hom_comm_apply d.τ₃ h cH.val).symm.trans (congrArg d.τ₃.hom (cH.property h))⟩
    continuousCoefficientH1Map (restrictedCoefficientRep X.X₁ j) Y.X₁
      d.τ₁.hom.toLinearMap hd (Rep.hom_comm_apply d.τ₁)
      (restrictedCoefficientAction_continuous X.X₁ j hj hA) hA'
      (continuousRepresentationH1Restriction X.X₁ hA j hj
        (continuousShortComplexInvariantConnectingMap X hX hA hB c)) =
      continuousShortComplexInvariantConnectingMap Y hY hA' hB' cY := by
  intro cH cY
  have hXH : (X.map (Rep.resFunctor j)).ShortExact := by
    refine {
      mono_f := (Rep.mono_iff_injective _).mpr ((Rep.mono_iff_injective X.f).mp hX.mono_f)
      epi_g := (Rep.epi_iff_surjective _).mpr ((Rep.epi_iff_surjective X.g).mp hX.epi_g)
      exact := ?_ }
    apply ((X.map (Rep.resFunctor j)).exact_map_iff_of_faithful
      (forget₂ (Rep R H) (ModuleCat R))).mp
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact (hX.exact.map (forget₂ (Rep R G) (ModuleCat R))).moduleCat_range_eq_ker
  have hr := continuousInvariantConnecting_restriction X.X₁ X.X₂ X.X₃
    X.f.hom.toLinearMap ((Rep.mono_iff_injective X.f).mp hX.mono_f)
    (Rep.hom_comm_apply X.f) X.g.hom.toLinearMap
    ((Rep.epi_iff_surjective X.g).mp hX.epi_g) (Rep.hom_comm_apply X.g)
    (hX.exact.map (forget₂ (Rep R G) (ModuleCat R))).moduleCat_range_eq_ker
    hA hB j hj c
  exact (congrArg (continuousCoefficientH1Map (restrictedCoefficientRep X.X₁ j) Y.X₁
    d.τ₁.hom.toLinearMap hd (Rep.hom_comm_apply d.τ₁)
    (restrictedCoefficientAction_continuous X.X₁ j hj hA) hA') hr).trans
    (@continuousInvariantConnecting_naturality R H _ _ _ _
      (X.map (Rep.resFunctor j)) Y hXH hY
      (inferInstanceAs (TopologicalSpace X.X₁))
      (inferInstanceAs (IsTopologicalAddGroup X.X₁))
      (inferInstanceAs (ContinuousSMul R X.X₁))
      (inferInstanceAs (TopologicalSpace X.X₂))
      (inferInstanceAs (DiscreteTopology X.X₂))
      (inferInstanceAs (TopologicalSpace Y.X₁))
      (inferInstanceAs (IsTopologicalAddGroup Y.X₁))
      (inferInstanceAs (ContinuousSMul R Y.X₁))
      (inferInstanceAs (TopologicalSpace Y.X₂))
      (inferInstanceAs (DiscreteTopology Y.X₂))
      (restrictedCoefficientAction_continuous X.X₁ j hj hA)
      (restrictedCoefficientAction_continuous X.X₂ j hj hB) hA' hB' d hd cH)

end
end Dubon2026

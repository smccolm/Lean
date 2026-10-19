import Dubon2026.ContinuousInvariantConnectingFreeCorrection
import Dubon2026.OriginalContravariantHomSequence
import Mathlib.RepresentationTheory.Invariants

/-! An actual equivariant extension of the relation correction leaves
the dual connecting H1 class unchanged. The finite S-unit correction has
exactly this form after local projection, so this removes its free term
in DUB-17's prescribed local class comparison. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV1 Rep.hV2

variable {G : Type} [Group G] [TopologicalSpace G]
  (X : ShortComplex (Rep.{0} ℤ G)) (D : Rep.{0} ℤ G)
  (hY : (originalContravariantHomShortComplex X D).ShortExact)
  [TopologicalSpace ((Rep.ihom X.X₃).obj D)]
  [IsTopologicalAddGroup ((Rep.ihom X.X₃).obj D)]
  [@ContinuousSMul ℤ ((Rep.ihom X.X₃).obj D)
    ((Rep.ihom X.X₃).obj D).hV2.toSMul inferInstance inferInstance]
  [TopologicalSpace ((Rep.ihom X.X₂).obj D)]
  [DiscreteTopology ((Rep.ihom X.X₂).obj D)]
  (hA : Continuous (fun z : G × (Rep.ihom X.X₃).obj D =>
    ((Rep.ihom X.X₃).obj D).ρ z.1 z.2))
  (hB : Continuous (fun z : G × (Rep.ihom X.X₂).obj D =>
    ((Rep.ihom X.X₂).obj D).ρ z.1 z.2))

/-- A literal correction by an equivariant morphism on the original
middle coefficient does not change the dual continuous connecting class. -/
theorem originalDualConnecting_eq_of_free_correction
    (φ ψ : X.X₁ ⟶ D) (l : X.X₂ ⟶ D) (hφ : φ = ψ - X.f ≫ l) :
    continuousShortComplexInvariantConnectingMap
      (originalContravariantHomShortComplex X D) hY hA hB
      ((Representation.linHom.invariantsEquivRepHom _ _).symm φ) =
    continuousShortComplexInvariantConnectingMap
      (originalContravariantHomShortComplex X D) hY hA hB
      ((Representation.linHom.invariantsEquivRepHom _ _).symm ψ) := by
  apply continuousInvariantConnecting_eq_of_correction
    (originalContravariantHomShortComplex X D) hY hA hB _ _
    ((Representation.linHom.invariantsEquivRepHom _ _).symm (-l))
  apply LinearMap.ext
  intro x
  change -l.hom (X.f.hom x) = φ.hom x - ψ.hom x
  have hh := congrArg (fun m : X.X₁ ⟶ D => m.hom x) hφ
  change φ.hom x = ψ.hom x - l.hom (X.f.hom x) at hh
  rw [hh]
  abel

end
end Dubon2026

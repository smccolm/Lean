import Dubon2026.TraceZeroCharacterCohomologyCup
import Dubon2026.ContinuousAdjointRestrictionComparison

/-! # Genuine restriction of the original character-twisted trace-zero cohomology -/

namespace Dubon2026
noncomputable section
open Matrix

section Generic

variable {R J K V : Type} [CommRing R] [Group J] [Group K]
  [AddCommGroup V] [Module R V] [TopologicalSpace R]
  [TopologicalSpace J] [TopologicalSpace K] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul R V]
  {φ : Representation R J V} {τ : Representation R K V}
  (j : K →* J) (hj : Continuous j) (e : φ.comp j = τ)

/-- Compose the actual restriction and coefficient equality maps before any
specialization to a concrete coefficient representation. -/
private def restrictionWithCoefficientEquality :
    continuousRepresentationCocyclesOne (Rep.of φ) →ₗ[R]
      continuousRepresentationCocyclesOne (Rep.of τ) :=
  { toFun := fun c =>
      let d := continuousCocycleOneCoefficientCongr e
        (continuousRepresentationCocycleOneRestriction (Rep.of φ) j hj c)
      ⟨⟨fun h => c.val (j h), by
        have he : (fun h => c.val (j h)) = (d.val : K → V) :=
          funext (fun h => (continuousCocycleOneCoefficientCongr_apply e
            (continuousRepresentationCocycleOneRestriction (Rep.of φ) j hj c) h).symm)
        rw [he]
        exact d.val.property⟩, c.property.comp hj⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

/-- The composed original cocycle map has the literal restricted function. -/
private theorem restrictionWithCoefficientEquality_apply
    (c : continuousRepresentationCocyclesOne (Rep.of φ)) (h : K) :
    (restrictionWithCoefficientEquality j hj e c).val h = c.val (j h) := by
  rfl

variable (hφ : Continuous (fun z : J × V => φ z.1 z.2))
  (hτ : Continuous (fun z : K × V => τ z.1 z.2))

/-- Compose the same actual restriction and equality maps on original H1. -/
private def h1RestrictionWithCoefficientEquality :
    ContinuousRepresentationH1 (Rep.of φ) hφ →ₗ[R]
      ContinuousRepresentationH1 (Rep.of τ) hτ :=
  by
    let F := restrictionWithCoefficientEquality j hj e
    have hb : continuousRepresentationCoboundariesOne (Rep.of φ) hφ ≤
        (continuousRepresentationCoboundariesOne (Rep.of τ) hτ).comap F := by
      rintro _ ⟨v, rfl⟩
      refine ⟨v, ?_⟩
      apply Subtype.ext
      apply groupCohomology.cocycles₁_ext
      intro h
      change τ h v - v = φ (j h) v - v
      have he := DFunLike.congr_fun e h
      exact congrArg (fun w => w - v) (LinearMap.congr_fun he v).symm
    exact Submodule.mapQ (R := R) (R₂ := R)
      (M := continuousRepresentationCocyclesOne (Rep.of φ))
      (M₂ := continuousRepresentationCocyclesOne (Rep.of τ)) (τ₁₂ := RingHom.id R)
      (continuousRepresentationCoboundariesOne (Rep.of φ) hφ)
      (continuousRepresentationCoboundariesOne (Rep.of τ) hτ) F hb

/-- The composed original H1 map is induced by the same original cocycle map. -/
private theorem h1RestrictionWithCoefficientEquality_mk
    (c : continuousRepresentationCocyclesOne (Rep.of φ)) :
    h1RestrictionWithCoefficientEquality j hj e hφ hτ (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (restrictionWithCoefficientEquality j hj e c) := by
  rfl

end Generic


variable {G H ι k : Type} [Group G] [Group H] [Fintype ι] [DecidableEq ι] [Field k]

/-- Restricting the original character-twisted adjoint action is exactly the
twist of the restricted matrices by the restricted original character. -/
theorem matrixTraceZeroCharacterRepresentation_comp
    (ρ : G →* GeneralLinearGroup ι k) (χ : G →* k) (j : H →* G) :
    (matrixTraceZeroCharacterRep ρ χ).ρ.comp j =
      (matrixTraceZeroCharacterRep (ρ.comp j) (χ.comp j)).ρ := by
  change (coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation ρ) χ).comp j =
    coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation (ρ.comp j)) (χ.comp j)
  rw [coefficientCharacterTwist_comp, matrixTraceZeroAdjointRepresentation_comp]

variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace k] [IsTopologicalRing k]
  (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
  (χ : G →* k) (hχ : Continuous χ) (j : H →* G) (hj : Continuous j)

/-- Restrict the actual twisted continuous cocycle and transport it by the
proved equality of the original restricted coefficient actions. -/
def matrixTraceZeroCharacterCocycleRestriction :
    continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep ρ χ) →ₗ[k]
      continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep (ρ.comp j) (χ.comp j)) :=
  restrictionWithCoefficientEquality j hj
    (matrixTraceZeroCharacterRepresentation_comp ρ χ j)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The actual twisted cocycle restriction preserves its literal original
function evaluated at the same original group homomorphism. -/
theorem matrixTraceZeroCharacterCocycleRestriction_apply
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep ρ χ)) (h : H) :
    (matrixTraceZeroCharacterCocycleRestriction ρ χ j hj c).val h = c.val (j h) := by
  exact restrictionWithCoefficientEquality_apply j hj
    (matrixTraceZeroCharacterRepresentation_comp ρ χ j) c h

/-- Restriction of the same twisted continuous H1 classes, using the actual
restriction map and the separately proved original coefficient-action equality. -/
def matrixTraceZeroCharacterH1Restriction :
    ContinuousRepresentationH1 (matrixTraceZeroCharacterRep ρ χ)
        (matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ) →ₗ[k]
      ContinuousRepresentationH1 (matrixTraceZeroCharacterRep (ρ.comp j) (χ.comp j))
        (matrixTraceZeroCharacterAction_continuous (ρ.comp j) (hρ.comp hj)
          (χ.comp j) (hχ.comp hj)) :=
  h1RestrictionWithCoefficientEquality j hj
    (matrixTraceZeroCharacterRepresentation_comp ρ χ j)
    (matrixTraceZeroCharacterAction_continuous ρ hρ χ hχ)
    (matrixTraceZeroCharacterAction_continuous (ρ.comp j) (hρ.comp hj)
      (χ.comp j) (hχ.comp hj))

/-- Twisted H1 restriction has the same original restricted cocycle as its
representative, including the proved coefficient-action transport. -/
theorem matrixTraceZeroCharacterH1Restriction_mk
    (c : continuousRepresentationCocyclesOne (matrixTraceZeroCharacterRep ρ χ)) :
    matrixTraceZeroCharacterH1Restriction ρ hρ χ hχ j hj (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (matrixTraceZeroCharacterCocycleRestriction ρ χ j hj c) := by
  rfl

/-- The actual one-dimensional character H2 restriction has the restricted
original character as coefficient action, with the same continuous cochain witnesses. -/
def coefficientCharacterH2Restriction :
    ContinuousRepresentationH2 (coefficientCharacterRep χ)
        (coefficientCharacterAction_continuous χ hχ) →ₗ[k]
      ContinuousRepresentationH2 (coefficientCharacterRep (χ.comp j))
        (coefficientCharacterAction_continuous (χ.comp j) (hχ.comp hj)) :=
  continuousRepresentationH2Restriction (coefficientCharacterRep χ)
    (coefficientCharacterAction_continuous χ hχ) j hj

/-- The original character H2 restriction is represented by the same original
two-cocycle restricted in both group arguments. -/
theorem coefficientCharacterH2Restriction_mk
    (c : continuousRepresentationCocyclesTwo (coefficientCharacterRep χ)) :
    coefficientCharacterH2Restriction χ hχ j hj (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousRepresentationCocycleTwoRestriction
        (coefficientCharacterRep χ) j hj c) := by
  rfl

end
end Dubon2026

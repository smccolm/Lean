import Dubon2026.ContinuousRepresentationCocycles
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Actual continuous cohomology quotients in degrees one and two -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- The original degree-zero differential into actual continuous one-cocycles. -/
def continuousRepresentationCoboundaryOne : A →ₗ[R] continuousRepresentationCocyclesOne A where
  toFun x := ⟨⟨groupCohomology.d₀₁ A x,
    groupCohomology.d₀₁_apply_mem_cocycles₁ (A := A) x⟩,
      representationCoboundary_continuous A hA x⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (groupCohomology.d₀₁ A).hom x y
  map_smul' r x := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (groupCohomology.d₀₁ A).hom r x

/-- Actual degree-one continuous coboundaries, with no assumed quotient relation. -/
def continuousRepresentationCoboundariesOne :
    Submodule R (continuousRepresentationCocyclesOne A) :=
  LinearMap.range (continuousRepresentationCoboundaryOne A hA)

/-- Actual continuous one-cocycles modulo the original continuous coboundaries. -/
abbrev ContinuousRepresentationH1 :=
  letI := Submodule.hasQuotient (R := R) (M := continuousRepresentationCocyclesOne A)
  (continuousRepresentationCocyclesOne A : Type) ⧸
    continuousRepresentationCoboundariesOne A hA

/-- The original continuous H1 quotient has its canonical additive group. -/
instance continuousRepresentationH1AddCommGroup : AddCommGroup (ContinuousRepresentationH1 A hA) :=
  by
    let quotientGroup := Submodule.Quotient.addCommGroup (R := R)
      (M := continuousRepresentationCocyclesOne A) (continuousRepresentationCoboundariesOne A hA)
    exact quotientGroup

/-- The original continuous H1 quotient has its canonical coefficient module. -/
instance continuousRepresentationH1Module : Module R (ContinuousRepresentationH1 A hA) :=
  by
    let quotientModule := Submodule.Quotient.module (R := R)
      (M := continuousRepresentationCocyclesOne A) (continuousRepresentationCoboundariesOne A hA)
    exact quotientModule

/-- The original degree-one differential, restricted to continuous cochains, has
its image in genuine continuous two-cocycles by the pinned differential identity. -/
def continuousRepresentationCoboundaryTwo : C(G, A) →ₗ[R] continuousRepresentationCocyclesTwo A where
  toFun f := ⟨⟨groupCohomology.d₁₂ A f,
    groupCohomology.d₁₂_apply_mem_cocycles₂ (A := A) f⟩,
      representationOneDifferential_continuous A hA f f.continuous⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (groupCohomology.d₁₂ A).hom (f : G → A) (g : G → A)
  map_smul' r f := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (groupCohomology.d₁₂ A).hom r (f : G → A)

/-- Actual two-coboundaries are images of continuous one-cochains. An algebraic
coboundary represented only by a discontinuous cochain is not silently included. -/
def continuousRepresentationCoboundariesTwo :
    Submodule R (continuousRepresentationCocyclesTwo A) :=
  LinearMap.range (continuousRepresentationCoboundaryTwo A hA)

/-- Actual jointly continuous two-cocycles modulo actual continuous coboundaries. -/
abbrev ContinuousRepresentationH2 :=
  letI := Submodule.hasQuotient (R := R) (M := continuousRepresentationCocyclesTwo A)
  (continuousRepresentationCocyclesTwo A : Type) ⧸
    continuousRepresentationCoboundariesTwo A hA

/-- The original continuous H2 quotient has its canonical additive group. -/
instance continuousRepresentationH2AddCommGroup : AddCommGroup (ContinuousRepresentationH2 A hA) :=
  by
    let quotientGroup := Submodule.Quotient.addCommGroup (R := R)
      (M := continuousRepresentationCocyclesTwo A) (continuousRepresentationCoboundariesTwo A hA)
    exact quotientGroup

/-- The original continuous H2 quotient has its canonical coefficient module. -/
instance continuousRepresentationH2Module : Module R (ContinuousRepresentationH2 A hA) :=
  by
    let quotientModule := Submodule.Quotient.module (R := R)
      (M := continuousRepresentationCocyclesTwo A) (continuousRepresentationCoboundariesTwo A hA)
    exact quotientModule

/-- The continuous H2 relation retains its exact continuous cochain witness and
the original inhomogeneous differential, rather than an algebraic-only witness. -/
theorem continuousRepresentationH2_eq_iff
    (c d : continuousRepresentationCocyclesTwo A) :
    (Submodule.Quotient.mk c : ContinuousRepresentationH2 A hA) =
        Submodule.Quotient.mk d ↔
      ∃ f : C(G, A), continuousRepresentationCoboundaryTwo A hA f = c - d := by
  rw [Submodule.Quotient.eq]
  rfl

end
end Dubon2026

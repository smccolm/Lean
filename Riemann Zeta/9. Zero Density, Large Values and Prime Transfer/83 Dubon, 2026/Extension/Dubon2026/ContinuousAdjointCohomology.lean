import Dubon2026.ContinuousFirstOrderDeformation
import Dubon2026.FirstOrderCohomologyClassification
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Actual continuous degree-one adjoint cohomology -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

/-- The submodule of actual continuous cocycles in the original adjoint cocycle module. -/
def continuousMatrixAdjointCocycles (ρ : G →* GeneralLinearGroup ι R) :
    Submodule R (groupCohomology.cocycles₁ (matrixAdjointRep ρ)) where
  carrier := {c | Continuous (fun g => c g)}
  zero_mem' := continuous_const
  add_mem' hc hd := hc.add hd
  smul_mem' r _ hc := hc.const_smul r

omit [IsTopologicalGroup G] in
/-- Every original adjoint coboundary is continuous for the original continuous representation. -/
theorem matrixAdjointCoboundary_continuous (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) (X : Matrix ι ι R) :
    Continuous (fun g => groupCohomology.d₀₁ (matrixAdjointRep ρ) X g) := by
  change Continuous (fun g => (ρ g).val * X * (ρ g⁻¹).val - X)
  simp_rw [map_inv]
  exact ((((Units.continuous_val (M := Matrix ι ι R)).comp hρ).mul continuous_const).mul
    ((Units.continuous_val (M := Matrix ι ι R)).comp hρ.inv)).sub continuous_const

/-- The actual degree-zero coboundary map with its continuous cocycle codomain proved. -/
def continuousMatrixAdjointCoboundary (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) : Matrix ι ι R →ₗ[R] continuousMatrixAdjointCocycles ρ where
  toFun X := ⟨⟨groupCohomology.d₀₁ (matrixAdjointRep ρ) X,
    groupCohomology.d₀₁_apply_mem_cocycles₁ (A := matrixAdjointRep ρ) X⟩, matrixAdjointCoboundary_continuous ρ hρ X⟩
  map_add' X Y := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (groupCohomology.d₀₁ (matrixAdjointRep ρ)).hom X Y
  map_smul' r X := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (groupCohomology.d₀₁ (matrixAdjointRep ρ)).hom r X

/-- The actual submodule of continuous adjoint coboundaries, with its original degree-zero map. -/
def continuousMatrixAdjointCoboundaries (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) : Submodule R (continuousMatrixAdjointCocycles ρ) :=
  LinearMap.range (continuousMatrixAdjointCoboundary ρ hρ)

/-- The original continuous first cohomology: actual continuous cocycles modulo actual coboundaries. -/
abbrev ContinuousMatrixAdjointH1 (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) :=
  letI := Submodule.hasQuotient (R := R) (M := continuousMatrixAdjointCocycles ρ)
  (continuousMatrixAdjointCocycles ρ : Type) ⧸
    continuousMatrixAdjointCoboundaries ρ hρ

/-- The actual continuous quotient inherits its canonical additive group. -/
instance continuousMatrixAdjointH1AddCommGroup (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) : AddCommGroup (ContinuousMatrixAdjointH1 ρ hρ) := by
  let quotientGroup := Submodule.Quotient.addCommGroup (R := R)
    (M := continuousMatrixAdjointCocycles ρ) (continuousMatrixAdjointCoboundaries ρ hρ)
  exact quotientGroup

/-- The actual continuous quotient inherits its canonical coefficient module. -/
instance continuousMatrixAdjointH1Module (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) : Module R (ContinuousMatrixAdjointH1 ρ hρ) := by
  let quotientModule := Submodule.Quotient.module (R := R)
    (M := continuousMatrixAdjointCocycles ρ) (continuousMatrixAdjointCoboundaries ρ hρ)
  exact quotientModule

omit [IsTopologicalGroup G] in
/-- Equality of original continuous cohomology classes agrees with equality of their actual algebraic classes; all original coboundaries are continuous. -/
theorem continuousMatrixAdjointH1_eq_iff (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) (c d : continuousMatrixAdjointCocycles ρ) :
    (Submodule.Quotient.mk c : ContinuousMatrixAdjointH1 ρ hρ) = Submodule.Quotient.mk d ↔
      groupCohomology.H1π (matrixAdjointRep ρ) c.val =
        groupCohomology.H1π (matrixAdjointRep ρ) d.val := by
  rw [Submodule.Quotient.eq, groupCohomology.H1π_eq_iff]
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨X, ?_⟩
    exact congrArg (fun z : continuousMatrixAdjointCocycles ρ =>
      (z.val : G → Matrix ι ι R)) hX
  · rintro ⟨X, hX⟩
    refine ⟨X, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hX

/-- The actual continuous class of an original continuous first-order lift. -/
def continuousMatrixFirstOrderClass (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) : ContinuousMatrixAdjointH1 ρ hρ :=
  Submodule.Quotient.mk ⟨matrixFirstOrderCocycle ρ τ,
    matrixFirstOrderCocycle_continuous ρ hρ τ hτ⟩

omit [IsTopologicalGroup G] in
/-- Actual strict conjugacy of original continuous lifts is exactly equality in their genuine continuous first cohomology. -/
theorem continuousMatrixFirstOrderClass_eq_iff (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) (τ σ : MatrixFirstOrderLift ρ)
    (hτ : Continuous τ.val) (hσ : Continuous σ.val) :
    continuousMatrixFirstOrderClass ρ hρ τ hτ = continuousMatrixFirstOrderClass ρ hρ σ hσ ↔
      MatrixFirstOrderStrictlyConjugate ρ τ σ := by
  rw [continuousMatrixFirstOrderClass, continuousMatrixFirstOrderClass,
    continuousMatrixAdjointH1_eq_iff]
  exact (matrixFirstOrderStrictlyConjugate_iff ρ τ σ).symm

/-- Every original continuous first-cohomology class is represented by a genuine continuous first-order lift. -/
theorem continuousMatrixFirstOrderClass_surjective (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) :
    Function.Surjective (fun τ : {τ : MatrixFirstOrderLift ρ // Continuous τ.val} =>
      continuousMatrixFirstOrderClass ρ hρ τ.val τ.property) := by
  intro x
  induction x using Quotient.inductionOn' with
  | h c =>
    refine ⟨⟨firstOrderLiftFromCocycle ρ c.val,
      firstOrderLiftFromCocycle_continuous ρ hρ c.val c.property⟩, ?_⟩
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact matrixFirstOrderCocycle_fromCocycle ρ c.val

end
end Dubon2026

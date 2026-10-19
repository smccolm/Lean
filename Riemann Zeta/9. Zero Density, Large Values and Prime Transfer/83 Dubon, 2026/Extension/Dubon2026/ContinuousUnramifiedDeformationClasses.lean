import Dubon2026.ContinuousUnramifiedFirstOrder
import Mathlib.Data.Setoid.Basic

/-! Actual continuous unramified fixed-determinant lifts, with their genuine
strict-conjugacy classes. This reuses the existing global class construction
for the original local Galois groups required by DUB-17. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [TopologicalSpace R] [IsTopologicalRing R]

/-- The genuine continuous dual-number lifts with unchanged determinant
and trivial action on the specified actual inertia subgroup. -/
def ContinuousUnramifiedFirstOrderLift
    (ρ : G →* GeneralLinearGroup ι R) (N : Subgroup G) :=
  {τ : {τ : MatrixFirstOrderLift ρ // Continuous τ.val} //
    (∀ g, Matrix.det (τ.val.val g).val = TrivSqZeroExt.inl (Matrix.det (ρ g).val)) ∧
      N ≤ τ.val.val.ker}

/-- The original class of an actual local lift belongs to the simultaneous
determinant and inertia subspace by the proved criteria. -/
def continuousUnramifiedFirstOrderClass
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (N : Subgroup G) (hN : N ≤ ρ.ker)
    (τ : ContinuousUnramifiedFirstOrderLift ρ N) :
    continuousUnramifiedFixedDeterminantClasses ρ hρ N :=
  ⟨continuousMatrixFirstOrderClass ρ hρ τ.val.val τ.val.property,
    (continuousUnramifiedFixedDeterminantClasses_firstOrder_iff ρ hρ N hN
      τ.val.val τ.val.property).mpr τ.property⟩

/-- Every class in this original local subspace comes from a genuine
continuous lift satisfying both original local equations. -/
theorem continuousUnramifiedFirstOrderClass_surjective
    [IsTopologicalGroup G]
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (N : Subgroup G) (hN : N ≤ ρ.ker) :
    Function.Surjective (continuousUnramifiedFirstOrderClass ρ hρ N hN) := by
  intro c
  obtain ⟨⟨τ, hτ⟩, hc⟩ := continuousMatrixFirstOrderClass_surjective ρ hρ c.val
  change continuousMatrixFirstOrderClass ρ hρ τ hτ = c.val at hc
  have hmem : continuousMatrixFirstOrderClass ρ hρ τ hτ ∈
      continuousUnramifiedFixedDeterminantClasses ρ hρ N := hc.symm ▸ c.property
  refine ⟨⟨⟨τ, hτ⟩,
    (continuousUnramifiedFixedDeterminantClasses_firstOrder_iff ρ hρ N hN τ hτ).mp hmem⟩, ?_⟩
  exact Subtype.ext hc

/-- Equality of these actual local classes is exactly strict conjugacy
of the entire original continuous lifted representations. -/
theorem continuousUnramifiedFirstOrderClass_eq_iff
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (N : Subgroup G) (hN : N ≤ ρ.ker)
    (τ υ : ContinuousUnramifiedFirstOrderLift ρ N) :
    continuousUnramifiedFirstOrderClass ρ hρ N hN τ =
      continuousUnramifiedFirstOrderClass ρ hρ N hN υ ↔
        MatrixFirstOrderStrictlyConjugate ρ τ.val.val υ.val.val := by
  rw [Subtype.ext_iff]
  exact continuousMatrixFirstOrderClass_eq_iff ρ hρ τ.val.val υ.val.val
    τ.val.property υ.val.property

/-- The quotient by actual strict conjugacy is identified with the
original fixed-determinant unramified cohomology subspace. -/
def continuousUnramifiedFirstOrderClassesEquiv
    [IsTopologicalGroup G]
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (N : Subgroup G) (hN : N ≤ ρ.ker) :
    Quotient (Setoid.ker (continuousUnramifiedFirstOrderClass ρ hρ N hN)) ≃
      continuousUnramifiedFixedDeterminantClasses ρ hρ N :=
  Setoid.quotientKerEquivOfSurjective _ (continuousUnramifiedFirstOrderClass_surjective ρ hρ N hN)

end
end Dubon2026

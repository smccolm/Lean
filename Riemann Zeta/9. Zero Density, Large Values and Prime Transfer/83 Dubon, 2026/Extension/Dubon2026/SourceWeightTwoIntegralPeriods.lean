import Dubon2026.SourceWeightTwoEndpointPeriods

/-! DUB-17/18 -> Gamma1 Picard/H1 -> Abel-Jacobi reciprocity ->
actual integral periods. Form the integer span of the original scalar
period functionals and descend the normalized endpoint integral to the
actual subgroup orbit quotient. No lattice inclusion is assumed. -/
namespace Dubon2026
noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups
variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- The original scalar modular period as a functional on actual cusp forms. -/
def sourceWeightTwoDualPeriod (γ : Γ) :
    Module.Dual ℂ (CuspForm (Γ.map (mapGL ℝ)) 2) :=
  sourceWeightTwoAlong Γ UpperHalfPlane.I (γ.val • UpperHalfPlane.I)

theorem sourceWeightTwoDualPeriod_apply (γ : Γ)
    (f : CuspForm (Γ.map (mapGL ℝ)) 2) :
    sourceWeightTwoDualPeriod Γ γ f = sourceWeightTwoPeriodValue Γ f γ :=
  sourceWeightTwoAlong_smul Γ γ UpperHalfPlane.I f

/-- The integer span of the actual original modular periods. -/
def sourceWeightTwoIntegralLattice :
    Submodule ℤ (Module.Dual ℂ (CuspForm (Γ.map (mapGL ℝ)) 2)) :=
  Submodule.span ℤ (Set.range (sourceWeightTwoDualPeriod Γ))

theorem sourceWeightTwoDualPeriod_mem (γ : Γ) :
    sourceWeightTwoDualPeriod Γ γ ∈ sourceWeightTwoIntegralLattice Γ :=
  Submodule.subset_span ⟨γ, rfl⟩

theorem sourceWeightTwoAlong_smul_sub (γ : Γ) (z : ℍ) :
    sourceWeightTwoAlong Γ UpperHalfPlane.I (γ.val • z) -
        sourceWeightTwoAlong Γ UpperHalfPlane.I z =
      sourceWeightTwoDualPeriod Γ γ := by
  rw [← sourceWeightTwoAlong_eq_sub]
  ext f
  rw [sourceWeightTwoAlong_smul, sourceWeightTwoDualPeriod_apply]

theorem sourceWeightTwoAlong_quotient_smul (γ : Γ) (z : ℍ) :
    (sourceWeightTwoIntegralLattice Γ).mkQ (sourceWeightTwoAlong Γ UpperHalfPlane.I (γ.val • z)) =
      (sourceWeightTwoIntegralLattice Γ).mkQ (sourceWeightTwoAlong Γ UpperHalfPlane.I z) := by
  apply (Submodule.Quotient.eq (sourceWeightTwoIntegralLattice Γ)).mpr
  rw [sourceWeightTwoAlong_smul_sub]
  exact sourceWeightTwoDualPeriod_mem Γ γ

/-- Normalized Abel endpoint functional on the actual subgroup orbit space. -/
def sourceWeightTwoOrbitPeriod :
    Quotient (MulAction.orbitRel Γ ℍ) →
      (Module.Dual ℂ (CuspForm (Γ.map (mapGL ℝ)) 2) ⧸ sourceWeightTwoIntegralLattice Γ) :=
  Quotient.lift (fun z => (sourceWeightTwoIntegralLattice Γ).mkQ
    (sourceWeightTwoAlong Γ UpperHalfPlane.I z)) (by
      intro a b h
      obtain ⟨γ, rfl⟩ := (MulAction.orbitRel_apply.mp h)
      exact sourceWeightTwoAlong_quotient_smul Γ γ b)

theorem sourceWeightTwoOrbitPeriod_mk (z : ℍ) :
    sourceWeightTwoOrbitPeriod Γ (Quotient.mk (MulAction.orbitRel Γ ℍ) z) =
      (sourceWeightTwoIntegralLattice Γ).mkQ (sourceWeightTwoAlong Γ UpperHalfPlane.I z) := rfl

end
end Dubon2026

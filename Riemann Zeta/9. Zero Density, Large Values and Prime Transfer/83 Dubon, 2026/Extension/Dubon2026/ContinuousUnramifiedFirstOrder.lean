import Dubon2026.ContinuousAdjointRestriction
import Dubon2026.ContinuousFixedDeterminantClasses
import Dubon2026.FirstOrderInertiaCriterion

/-! The original continuous deformation criteria applied to an actual local
inertia subgroup. This is the subgroup form needed for DUB-17's prime-local
Galois group, rather than its global arithmetic quotient. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [TopologicalSpace R] [IsTopologicalRing R]

/-- For a residually trivial subgroup, vanishing of the restricted actual
first-order class means that the whole original lifted representation is
trivial on that subgroup. -/
theorem continuousMatrixFirstOrderClass_restriction_zero_iff
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (N : Subgroup G) (hN : N ≤ ρ.ker)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixAdjointH1Restriction ρ hρ N.subtype continuous_subtype_val
      (continuousMatrixFirstOrderClass ρ hρ τ hτ) = 0 ↔ N ≤ τ.val.ker := by
  change (Submodule.Quotient.mk
    (continuousMatrixAdjointRestriction ρ N.subtype continuous_subtype_val
      ⟨matrixFirstOrderCocycle ρ τ, matrixFirstOrderCocycle_continuous ρ hρ τ hτ⟩) :
      ContinuousMatrixAdjointH1 (ρ.comp N.subtype)
        (hρ.comp continuous_subtype_val)) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero,
    matrixFirstOrderLift_subgroup_kernel_iff ρ τ N hN]
  constructor
  · rintro ⟨X, hX⟩ g hg
    have he := congrArg (fun c : continuousMatrixAdjointCocycles
      (ρ.comp N.subtype) => c.val ⟨g, hg⟩) hX
    have hρg : ρ g = 1 := hN hg
    have hρgi : ρ g⁻¹ = 1 := by rw [map_inv, hρg, inv_one]
    change (ρ g).val * X * (ρ g⁻¹).val - X = matrixFirstOrderCocycle ρ τ g at he
    simpa only [hρg, hρgi, Units.val_one, one_mul, mul_one, sub_self] using he.symm
  · intro h
    refine ⟨0, ?_⟩
    apply Subtype.ext
    apply groupCohomology.cocycles₁_ext
    intro g
    change (ρ g.val).val * 0 * (ρ g.val⁻¹).val - 0 = matrixFirstOrderCocycle ρ τ g.val
    simp only [mul_zero, zero_mul, sub_self, h g.val g.property]

/-- The simultaneous fixed-determinant and actual subgroup restriction
condition in the original continuous adjoint cohomology. -/
def continuousUnramifiedFixedDeterminantClasses
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) (N : Subgroup G) :
    Submodule R (ContinuousMatrixAdjointH1 ρ hρ) :=
  continuousFixedDeterminantClasses ρ hρ ⊓
    (continuousMatrixAdjointH1Restriction ρ hρ N.subtype continuous_subtype_val).ker

/-- This actual local subspace characterizes the original continuous
dual-number lifts with fixed determinant and trivial actual inertia. -/
theorem continuousUnramifiedFixedDeterminantClasses_firstOrder_iff
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (N : Subgroup G) (hN : N ≤ ρ.ker)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixFirstOrderClass ρ hρ τ hτ ∈
      continuousUnramifiedFixedDeterminantClasses ρ hρ N ↔
        (∀ g, Matrix.det (τ.val g).val = TrivSqZeroExt.inl (Matrix.det (ρ g).val)) ∧
          N ≤ τ.val.ker := by
  change (_ ∈ continuousFixedDeterminantClasses ρ hρ ∧
    continuousMatrixAdjointH1Restriction ρ hρ N.subtype continuous_subtype_val
      (continuousMatrixFirstOrderClass ρ hρ τ hτ) = 0) ↔ _
  rw [continuousFixedDeterminantClasses_firstOrder_iff,
    continuousMatrixFirstOrderClass_restriction_zero_iff ρ hρ N hN]

end
end Dubon2026

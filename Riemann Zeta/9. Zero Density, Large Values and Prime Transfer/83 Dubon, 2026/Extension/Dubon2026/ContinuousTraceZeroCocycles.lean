import Dubon2026.TraceZeroAdjointRepresentation
import Dubon2026.ContinuousFixedDeterminantClasses

/-! # Genuine continuous cocycles in the original trace-zero coefficient representation -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

/-- The actual continuous cocycles with values in the original trace-zero coefficient representation. -/
def continuousTraceZeroAdjointCocycles (ρ : G →* GeneralLinearGroup ι R) :
    Submodule R (groupCohomology.cocycles₁ (matrixTraceZeroAdjointRep ρ)) where
  carrier := {c | Continuous (fun g => c g)}
  zero_mem' := continuous_const
  add_mem' hc hd := hc.add hd
  smul_mem' r _ hc := hc.const_smul r

/-- Include the genuine trace-zero coefficient cocycle as the same original continuous matrix cocycle. -/
def continuousTraceZeroCocycleInclusion (ρ : G →* GeneralLinearGroup ι R) :
    continuousTraceZeroAdjointCocycles ρ →ₗ[R] continuousMatrixAdjointCocycles ρ where
  toFun c := ⟨⟨fun g => (c.val g).val, by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g h
    exact congrArg Subtype.val ((groupCohomology.mem_cocycles₁_iff _).mp c.val.property g h)⟩,
    continuous_subtype_val.comp c.property⟩
  map_add' c d := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' r c := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The continuous trace-zero coefficient cocycles are exactly the original matrix cocycles with pointwise zero trace, with their genuine coefficient-linear structures. -/
def continuousTraceZeroCocycleEquiv (ρ : G →* GeneralLinearGroup ι R) :
    continuousTraceZeroAdjointCocycles ρ ≃ₗ[R] (continuousMatrixAdjointTrace ρ).ker where
  toFun c := ⟨continuousTraceZeroCocycleInclusion ρ c, by
    funext g
    exact (c.val g).property⟩
  invFun c := ⟨⟨fun g => ⟨c.val.val g, congrFun c.property g⟩, by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g h
    apply Subtype.ext
    exact (groupCohomology.mem_cocycles₁_iff _).mp c.val.val.property g h⟩,
    c.val.property.subtype_mk _⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_add' c d := by
    apply Subtype.ext
    exact map_add (continuousTraceZeroCocycleInclusion ρ) c d
  map_smul' r c := by
    apply Subtype.ext
    exact map_smul (continuousTraceZeroCocycleInclusion ρ) r c

omit [IsTopologicalGroup G] in
/-- The genuine coefficient comparison includes exactly the original matrix at every group element. -/
theorem continuousTraceZeroCocycleEquiv_apply (ρ : G →* GeneralLinearGroup ι R)
    (c : continuousTraceZeroAdjointCocycles ρ) (g : G) :
    (continuousTraceZeroCocycleEquiv ρ c).val.val g = (c.val g).val := rfl

omit [IsTopologicalGroup G] in
/-- Every original trace-zero continuous matrix cocycle comes uniquely from the actual trace-zero coefficient representation. -/
theorem continuousTraceZeroCocycleEquiv_bijective (ρ : G →* GeneralLinearGroup ι R) :
    Function.Bijective (continuousTraceZeroCocycleEquiv ρ) :=
  (continuousTraceZeroCocycleEquiv ρ).bijective

end
end Dubon2026

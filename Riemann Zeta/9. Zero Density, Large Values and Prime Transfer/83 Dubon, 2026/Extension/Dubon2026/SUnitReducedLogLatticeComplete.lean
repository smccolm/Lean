import Dubon2026.SUnitReducedLogDiscreteness
import Dubon2026.NumberFieldSUnitRank

/-! # The actual reduced S-unit image is a full lattice

The proved finite logarithmic kernel preserves the already proved
original S-unit rank. Discreteness then identifies integer and real
span dimensions. This supplies a full lattice without assuming the
equivariant Herbrand quotient needed by DUB-17.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The original logarithmic image has the original S-unit rank because its kernel is finite. -/
theorem sUnitReducedLogLattice_finrank :
    Module.finrank ℤ (sUnitReducedLogLattice K S) = Units.rank K + S.card := by
  let f := sUnitReducedLogLinearMap K S
  haveI : Finite f.ker := sUnitReducedLog_finite_kernel K S
  have hz : Module.rank ℤ f.ker = 0 :=
    rank_eq_zero_iff_isTorsion.mpr
      (AddMonoid.isTorsion_iff_isTorsion_int.mp is_add_torsion_of_finite)
  have h := f.rank_range_add_rank_ker
  rw [hz, add_zero] at h
  have h' := congrArg Cardinal.toNat h
  change Module.finrank ℤ (sUnitReducedLogLattice K S) =
    Module.finrank ℤ (Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) at h'
  rw [h', numberField_sUnit_finrank K S S.finite_toSet, Set.ncard_coe_finset]

/-- The original reduced real logarithmic space has the matching Dirichlet plus finite-place dimension. -/
theorem sUnitReducedLogSpace_finrank :
    Module.finrank ℝ (SUnitReducedLogSpace K S) = Units.rank K + S.card := by
  rw [Module.finrank_prod, Units.finrank_eq_rank]
  simp

/-- The actual discrete original logarithmic image spans its full original real ambient space. -/
theorem sUnitReducedLogLattice_span_eq_top :
    Submodule.span ℝ (sUnitReducedLogLattice K S : Set (SUnitReducedLogSpace K S)) = ⊤ := by
  letI := sUnitReducedLogLattice_discrete K S
  letI : DiscreteTopology
      (Submodule.span ℤ (sUnitReducedLogLattice K S : Set (SUnitReducedLogSpace K S))) := by
    rw [Submodule.span_eq]
    infer_instance
  apply Submodule.eq_top_of_finrank_eq
  change Set.finrank ℝ (sUnitReducedLogLattice K S : Set (SUnitReducedLogSpace K S)) = _
  rw [Real.finrank_eq_int_finrank_of_discrete inferInstance, Set.finrank, Submodule.span_eq,
    sUnitReducedLogLattice_finrank, sUnitReducedLogSpace_finrank]

/-- The original reduced S-unit image is a full integer lattice in its original real logarithmic space. -/
theorem sUnitReducedLogLattice_isZLattice :
    letI := sUnitReducedLogLattice_discrete K S
    IsZLattice ℝ (sUnitReducedLogLattice K S) := by
  letI := sUnitReducedLogLattice_discrete K S
  exact { span_top := sUnitReducedLogLattice_span_eq_top K S }

end
end Dubon2026

import Dubon2026.OriginalCoinducedGlobalDimensionShift
import Dubon2026.OriginalCoinducedPointCoordinates
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # The original coinduced shift preserves integral lattices

The direct degree-zero norm route to DUB-17 applies two actual
coinduced shifts to the original lattice. Evaluation at the identity
splits the orbit embedding integrally, so its literal quotient is
torsion-free. Finite generation then gives the integral projectivity
needed by the already proved internal-Hom acyclicity theorem.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module

/-- A split linear inclusion into torsion-free coefficients has torsion-free literal quotient. -/
theorem originalSplitRangeQuotient_torsionFree
    {k U V : Type} [CommRing k] [IsDomain k] [AddCommGroup U] [Module k U]
    [AddCommGroup V] [Module k V] [Module.IsTorsionFree k V]
    (u : U →ₗ[k] V) (e : V →ₗ[k] U) (he : e.comp u = LinearMap.id) :
    Module.IsTorsionFree k (V ⧸ u.range) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro n q hnq
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  obtain ⟨v, rfl⟩ := u.range.mkQ_surjective q
  have hv : n • v ∈ u.range := by
    apply (Submodule.Quotient.mk_eq_zero u.range).mp
    exact (u.range.mkQ.map_smul n v).trans hnq
  obtain ⟨x, hx⟩ := hv
  have hex : x = n • e v := by
    have h := congrArg e hx
    rw [← LinearMap.comp_apply, he, LinearMap.id_apply, map_smul] at h
    exact h
  apply (Submodule.Quotient.mk_eq_zero u.range).mpr
  refine ⟨e v, ?_⟩
  apply smul_right_injective V hn
  exact (u.map_smul n (e v)).symm.trans ((congrArg u hex.symm).trans hx)

variable {G : Type} [Group G] (M : Rep.{0} ℤ G)

/-- Identity evaluation is the literal integral retraction of the original coinduced orbit embedding. -/
theorem originalCoinducedEvaluation_unit (x : M) :
    originalCoinducedEvaluation M 1 ((originalCoinducedUnit M).hom x) = x := by
  change M.ρ 1 x = x
  rw [map_one, Module.End.one_apply]

variable [Module.IsTorsionFree ℤ M]

/-- Actual coinduced functions with torsion-free original values are torsion-free. -/
theorem originalCoinducedFunction_torsionFree :
    Module.IsTorsionFree ℤ (originalCoinducedFunctionRep M) := by
  infer_instance

/-- The literal original coinduced quotient is torsion-free by identity evaluation. -/
theorem originalCoinducedQuotient_torsionFree :
    Module.IsTorsionFree ℤ (originalCoinducedQuotient M) := by
  letI := originalCoinducedFunction_torsionFree M
  exact originalSplitRangeQuotient_torsionFree (originalCoinducedUnit M).hom.toLinearMap
    (originalCoinducedEvaluation M 1) (LinearMap.ext (originalCoinducedEvaluation_unit M))

variable [Fintype G] [Module.Finite ℤ M]

omit [Module.IsTorsionFree ℤ M] in
/-- The original coinduced function coefficient of a finite lattice is finite over the integers. -/
theorem originalCoinducedFunction_finite : Module.Finite ℤ (originalCoinducedFunctionRep M) := by
  infer_instance

omit [Module.IsTorsionFree ℤ M] in
/-- The literal original coinduced quotient is a finite integral module. -/
theorem originalCoinducedQuotient_finite : Module.Finite ℤ (originalCoinducedQuotient M) := by
  letI := originalCoinducedFunction_finite M
  exact Module.Finite.of_surjective
    (show originalCoinducedFunctionRep M →ₗ[ℤ] originalCoinducedQuotient M from
      (originalCoinducedShortComplex M).g.hom.toLinearMap)
    ((Rep.epi_iff_surjective _).mp (originalCoinducedShortComplex_shortExact M).epi_g)

/-- The actual coinduced lattice quotient is projective over the integers, with no projectivity certificate supplied. -/
theorem originalCoinducedQuotient_projective :
    Module.Projective ℤ (originalCoinducedQuotient M) := by
  letI := originalCoinducedQuotient_torsionFree M
  letI := originalCoinducedQuotient_finite M
  infer_instance

end
end Dubon2026

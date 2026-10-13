/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Rank argument adapted from NYLL ClassFieldTheory, commit
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/Rank.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.NumberFieldSUnitCoordinateVectors
import Dubon2026.NumberFieldSUnitFiniteGeneration
import Dubon2026.NumberFieldUnitRank
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! # Rank of the original number-field S-units

The existing ordinary-unit kernel and finite-generation proofs are reused.
Actual prime-power generators establish full rank of the valuation image.
This supplies the precise S-unit rank for the power-index calculation in
the global norm-index and reciprocity dependency of DUB-17.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K)))

private def sUnitCoordinateRangeVector (v : S) :
    (sUnitValuationLinearMap (K := K) S).range :=
  ⟨_, Additive.ofMul (numberFieldPrimePowerSUnit K S v), rfl⟩

private theorem sUnitCoordinateRangeVector_independent [Fintype S] :
    LinearIndependent ℤ (sUnitCoordinateRangeVector K S) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg v
  have hv := congrArg
    (fun z : (sUnitValuationLinearMap (K := K) S).range => z.val v) hg
  simp [sUnitCoordinateRangeVector, numberFieldPrimePowerSUnit_coordinate] at hv
  exact hv.resolve_right (NumberField.classNumber_ne_zero K)

/-- The actual original S-unit valuation image has full rank for every finite S. -/
theorem numberField_sUnit_valuation_range_finrank (hS : S.Finite) :
    Module.finrank ℤ (sUnitValuationLinearMap (K := K) S).range = S.ncard := by
  letI : Fintype S := hS.fintype
  letI : Module.Finite ℤ (sUnitValuationLinearMap (K := K) S).range :=
    Module.Finite.of_fg (IsNoetherian.noetherian _)
  apply le_antisymm
  · simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one, Set.fintypeCard_eq_ncard]
      using (Submodule.finrank_le (sUnitValuationLinearMap (K := K) S).range)
  · simpa only [Set.fintypeCard_eq_ncard] using
      (sUnitCoordinateRangeVector_independent K S).fintype_card_le_finrank

/-- The already proved original valuation kernel is the ordinary unit group, linearly. -/
def numberFieldSUnitValuationKernelLinearEquiv :
    (sUnitValuationLinearMap (K := K) S).ker ≃ₗ[ℤ] Additive (𝓞 K)ˣ :=
  (sUnitValuationKernelBaseEquiv (K := K) S).toAdditive.toIntLinearEquiv

/-- The original S-unit valuation kernel has the Dirichlet unit rank. -/
theorem numberField_sUnit_valuation_kernel_finrank :
    Module.finrank ℤ (sUnitValuationLinearMap (K := K) S).ker =
      NumberField.Units.rank K := by
  rw [(numberFieldSUnitValuationKernelLinearEquiv K S).finrank_eq]
  exact numberField_unit_finrank K

/-- The actual original S-unit group has rank equal to the unit rank plus the number of places. -/
theorem numberField_sUnit_finrank (hS : S.Finite) :
    Module.finrank ℤ (Additive (S.unit K)) = NumberField.Units.rank K + S.ncard := by
  letI := numberField_sUnit_fg K S hS
  letI : Module.Finite ℤ (Additive (S.unit K)) :=
    Module.Finite.iff_addGroup_fg.mpr inferInstance
  letI : Fintype S := hS.fintype
  letI : Module.Finite ℤ (sUnitValuationLinearMap (K := K) S).range :=
    Module.Finite.of_fg (IsNoetherian.noetherian _)
  letI : Module.Finite ℤ (sUnitValuationLinearMap (K := K) S).ker :=
    Module.Finite.of_fg (IsNoetherian.noetherian _)
  have h := (sUnitValuationLinearMap (K := K) S).rank_range_add_rank_ker
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank,
    ← Module.finrank_eq_rank] at h
  rw [← Nat.cast_add, Nat.cast_inj] at h
  simpa only [
    numberField_sUnit_valuation_range_finrank K S hS,
    numberField_sUnit_valuation_kernel_finrank, add_comm] using h.symm

end
end Dubon2026

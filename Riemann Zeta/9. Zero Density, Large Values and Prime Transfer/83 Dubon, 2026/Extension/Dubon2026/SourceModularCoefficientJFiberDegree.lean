import Dubon2026.SourceResidueAllLevelDegree
import Dubon2026.SourceModularCoefficientDivisorSupport
import Dubon2026.SourceModularCoefficientFieldFinite
import Dubon2026.SourceModularCoefficientSeparability
import Dubon2026.SourceModularCoefficientResidue
import Dubon2026.SourceCurveSeparatingCoordinateDegree

/-! DUB-17/18 -> good reduction -> reverse genus inequality -> exceptional
fiber contributions. Reuse the existing all-level coefficient-field degree
and separating-coordinate order sum to compute every finite j fiber's
total multiplicity. No fiber cardinality or ramification order is assumed. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve IntermediateField
open scoped IntermediateField

variable (N : ℕ) [NeZero N] (K : Type*) [Field K]

omit [NeZero N] in
/-- A finite translation of the actual modular coordinate is transcendental. -/
theorem coeff_j_sub_transcendental (c : K) :
    Transcendental K (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) c) := by
  intro h
  apply transcendental_jCoeff N K
  simpa only [sub_add_cancel] using h.add (isAlgebraic_algebraMap c)

omit [NeZero N] in
/-- Translating the actual coordinate preserves its literal intermediate field. -/
theorem coeff_j_sub_adjoin (c : K) :
    K⟮jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) c⟯ = K⟮jCoeff N K⟯ := by
  apply le_antisymm
  · exact adjoin_simple_le_iff.mpr
      (K⟮jCoeff N K⟯.sub_mem (mem_adjoin_simple_self _ _) (K⟮jCoeff N K⟯.algebraMap_mem c))
  · apply adjoin_simple_le_iff.mpr
    have h := (K⟮jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) c⟯).add_mem
      (mem_adjoin_simple_self _ _) (IntermediateField.algebraMap_mem _ c)
    simpa only [sub_add_cancel] using h

/-- Every finite actual j fiber has total multiplicity psi(N) away from the level characteristic. -/
theorem sum_coeff_j_fiber_orders_eq_psi [IsAlgClosed K] (hNK : (N : K) ≠ 0) (c : K) :
    (∑ᶠ v : {v : Place K (modularFunctionFieldCoeff N K) //
        0 < v.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) c)},
      v.1.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) c)) =
        (SourceLevelProjective.dedekindPsi N : ℤ) := by
  haveI : FiniteDimensional K⟮jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) c⟯
      (modularFunctionFieldCoeff N K) := by
    rw [coeff_j_sub_adjoin]
    exact finiteDimensional_coeff_field N K
  haveI : Algebra.IsSeparable K⟮jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) c⟯
      (modularFunctionFieldCoeff N K) := by
    rw [coeff_j_sub_adjoin]
    exact isSeparable_coeff_field N K
  have h := sum_positive_orders_eq_finrank_separating _ (coeff_j_sub_transcendental N K c)
  have hr : ∀ v : Place K (modularFunctionFieldCoeff N K), Module.finrank K v.ResidueField = 1 :=
    fun v => Module.finrank_of_bijective_algebraMap (coeff_place_residue_algebraMap_bijective N K v)
  simp only [hr, Nat.cast_one, mul_one] at h
  rw [coeff_j_sub_adjoin, finrank_coeff_over_j_eq_psi N hNK] at h
  exact h

end Dubon2026.SourceFunctionField

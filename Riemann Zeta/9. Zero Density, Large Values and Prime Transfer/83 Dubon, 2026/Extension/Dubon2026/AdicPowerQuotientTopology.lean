import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # The genuine quotient topology on the original adic power quotients -/

namespace Dubon2026

open Matrix

variable {R ι : Type*} [CommRing R] [WithIdeal R] [Fintype ι] [DecidableEq ι]

/-- The actual quotient by each original adic ideal power is discrete in its genuine quotient topology. -/
theorem adicPowerQuotient_discrete (n : ℕ) :
    DiscreteTopology (R ⧸ (WithIdeal.i : Ideal R) ^ n) := by
  apply QuotientAddGroup.discreteTopology
    (N := ((WithIdeal.i : Ideal R) ^ n).toAddSubgroup)
  exact (isAdic_iff.mp (rfl : IsAdic (WithIdeal.i : Ideal R))).1 n

/-- The literal quotient map to an original adic power quotient is continuous. -/
theorem adicPowerQuotient_continuous (n : ℕ) :
    Continuous (Ideal.Quotient.mk ((WithIdeal.i : Ideal R) ^ n)) :=
  (QuotientRing.isOpenQuotientMap_mk _).continuous

/-- The original whole-matrix reduction to each genuine adic power quotient is continuous. -/
theorem adicMatrixPowerReduction_continuous (n : ℕ) :
    Continuous (GeneralLinearGroup.map (n := ι) (R := R)
      (S := R ⧸ (WithIdeal.i : Ideal R) ^ n)
      (Ideal.Quotient.mk ((WithIdeal.i : Ideal R) ^ n))) := by
  apply Units.continuous_map
  apply continuous_matrix
  intro i j
  exact (adicPowerQuotient_continuous n).comp (continuous_apply_apply i j)

end Dubon2026

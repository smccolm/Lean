import Dubon2026.SourceReductionNormalizedFactors
import Dubon2026.SourceCurveChartFactorDegree
import Dubon2026.SourceIntegralChartPoleBound
import Dubon2026.SourceConstantFieldOrderResidues
import Dubon2026.SourceReductionEquationSpecialization
import Dubon2026.SourceValuationResidueAlgClosed

/-! DUB-17/18 -> modular good reduction -> principal-divisor pushforward ->
total chart-order equality. Normalized coordinate factors have equal total
original and residue orders. The integral-constant case is the already proved
separating-coordinate degree formula; the other case uses uniqueness of
constant values to show all relevant original orders vanish. This avoids
auxiliary place existence and constant-field dimension arguments. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
open scoped Classical
variable {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem normalizedChartFactor_ord_eq_zero_of_not_mem
    (R : RegularProlongation A F Fbar) (x : R.integers) {c : L} (hc : c ∉ A)
    (P : Place L F) (hP : ChartDomain A P (x : F)) :
    P.ord (normalizedChartFactor R x c : F) = 0 := by
  obtain ⟨a, ha⟩ := hP
  have hxP : (x : F) ∈ P.toValuationSubring := mem_of_sub_algebraMap_mem_nonunits P ha
  have hyP := P.mem_of_integral_adjoin hxP (isIntegral_normalizedChartFactor R x c)
  have hn : (normalizedChartFactor R x c : F) ∉ P.toValuationSubring.nonunits := by
    intro h
    have hxc : (x : F) - algebraMap L F c ∈ P.toValuationSubring.nonunits := by
      rw [ValuationSubring.mem_nonunits_iff, sub_eq_scalar_mul_normalizedChartFactor R x c,
        map_mul, P.valuation_algebraMap_eq_one (chartFactorScalar_ne_zero c), one_mul]
      rwa [ValuationSubring.mem_nonunits_iff] at h
    exact hc ((P.const_unique ha hxc) ▸ a.2)
  apply ConstantField.ord_coe_isUnit P (X := ⟨_, hyP⟩)
  by_contra hu
  exact hn (ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu))

theorem chartOrderSum_normalizedChartFactor_eq [IsAlgClosed L] [CharZero L]
    [HasPrincipalDivisors L F] [HasPrincipalDivisors (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    [Algebra.IsSeparable
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar]
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (c : L) :
    chartOrderSum (ChartDomain A · (x : F)) (normalizedChartFactor R x c : F) =
      chartOrderSum (fun Q : Place (ResidueField A) Fbar => R.residue x ∈ Q.toValuationSubring)
        (R.residue (normalizedChartFactor R x c)) := by
  haveI : IsAlgClosed (ResidueField A) := SourceEllipticReduction.residueField_isAlgClosed A
  haveI : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  haveI : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  have hxL := transcendental_of_residue_transcendental R x hx
  by_cases hc : c ∈ A
  · rw [coe_normalizedChartFactor_of_mem R x hc, residue_normalizedChartFactor_of_mem R x hc]
    have hleft := chartOrderSum_sub_algebraMap (x : F) hxL c (ChartDomain A · (x : F))
      (fun P ⟨a, ha⟩ => mem_of_sub_algebraMap_mem_nonunits P ha) (fun P hP => by
        refine ⟨⟨c, hc⟩, ?_⟩
        have hn : (x : F) - algebraMap L F c ≠ 0 := by
          intro hz
          rw [hz, P.ord_zero] at hP
          omega
        exact ValuationSubring.coe_mem_nonunits_iff.mpr
          ((P.mem_maximalIdeal_iff_ord_pos hn (P.mem_of_ord_nonneg hP.le)).mpr hP))
    have hright := chartOrderSum_sub_algebraMap (R.residue x) hx (IsLocalRing.residue A ⟨c, hc⟩)
      (fun Q : Place (ResidueField A) Fbar => R.residue x ∈ Q.toValuationSubring)
      (fun _ hQ => hQ) (fun Q hQ => by
        have hm := add_mem (Q.mem_of_ord_nonneg hQ.le) (Q.algebraMap_mem' (IsLocalRing.residue A ⟨c, hc⟩))
        simpa using hm)
    rw [hleft, hright, hdeg]
  · rw [residue_normalizedChartFactor_of_not_mem R x hc, chartOrderSum_one]
    exact chartOrderSum_eq_zero _ fun P hP => normalizedChartFactor_ord_eq_zero_of_not_mem R x hc P hP

end
end Dubon2026.SourceCurve.RegularProlongation

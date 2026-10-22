import Dubon2026.SourceOriginalChartFiberOrders
import Dubon2026.SourceOriginalChartGermDerivation
import Dubon2026.SourceOriginalRegularEvaluationSeparation

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel -> express every regular differential as h Df for a
nonconstant original function f. Finite original divisor support supplies
a regular place, and the actual derivative germ cannot vanish there.
This discharges nonvanishing of Df without an additional algebraic
separability interface or an assumed analytic realization.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_D_ne_zero_of_nonconstant {f : F}
    (hfc : ∀ a : ℂ, f ≠ algebraMap ℂ F a) : D ℂ F f ≠ 0 := by
  haveI := place_infinite N
  haveI : Nontrivial Ω[F⁄ℂ] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N ℂ)
  obtain ⟨v, hv⟩ := (finite_original_divisor_support N ℂ f).infinite_compl.nonempty
  have hord : v.ord f = 0 := by simpa only [mem_compl_iff, mem_setOf_eq, not_not] using hv
  have hf : f ∈ v.toValuationSubring := v.mem_of_ord_nonneg (by rw [hord])
  intro hD
  have hr := readDifferential_eq_expression_germ N v 0 1 f (by rw [hD, smul_zero])
  have hd : ∀ᶠ z in 𝓝[≠] (0 : ℂ), deriv (chartRead N v f) z = 0 := by
    filter_upwards [hr] with z hz
    haveI := original_place_dCoordGenerates N ℂ v
    have hzero : readDifferential N v 0 z = 0 := by
      rw [readDifferential, v.differentialCoeff_zero, chartRead, originalPlaceEval_zero, zero_mul]
    have hone : chartRead N v 1 z = 1 := by
      simpa only [map_one] using originalPlaceEval_algebraMap N ℂ (placeFamily N v z) 1
    simpa only [Pi.mul_apply, hzero, hone, one_mul] using hz.symm
  exact (hd.and (eventually_deriv_chartRead_ne_zero N v hf hfc)).exists.elim
    fun z hz => hz.2 hz.1

theorem original_differential_eq_smul_D {f : F}
    (hfc : ∀ a : ℂ, f ≠ algebraMap ℂ F a) (ω : Ω[F⁄ℂ]) :
    ∃ h : F, ω = h • D ℂ F f := by
  obtain ⟨h, hh⟩ := (finrank_eq_one_iff_of_nonzero' _
    (original_D_ne_zero_of_nonconstant N hfc)).mp (finrank_original_differentials N ℂ) ω
  exact ⟨h, hh.symm⟩

end
end Dubon2026.SourceFunctionField.OriginalChart

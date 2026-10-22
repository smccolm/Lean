import Dubon2026.SourceOriginalLocalRegularPrimitives
import Dubon2026.SourceOriginalComplexHausdorff
import Dubon2026.SourceOriginalCanonicalDivisors

/-! DUB-17/18 -> raw reciprocity -> differential coefficients in actual cells.
The already proved finite differential divisor and Hausdorff topology give an
open regular locus. This avoids reproving local order estimates for each cell.
The existing punctured Kaehler identity extends across each regular center.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem eventually_differentialCoeff_mem (v : Place ℂ F) (θ : Ω[F⁄ℂ])
    (hθ : v.differentialCoeff θ ∈ v.toValuationSubring) :
    ∀ᶠ w in 𝓝 v, w.differentialCoeff θ ∈ w.toValuationSubring := by
  letI := place_t2Space N
  haveI : ∀ w : Place ℂ F, w.DCoordGenerates := original_place_dCoordGenerates N ℂ
  haveI : Nontrivial Ω[F⁄ℂ] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N ℂ)
  by_cases h0 : θ = 0
  · subst θ
    exact Eventually.of_forall fun w => by rw [w.differentialCoeff_zero]; exact zero_mem _
  have hfin : {w : Place ℂ F | w.ordDifferential θ < 0}.Finite :=
    (finite_original_differential_support N ℂ h0).subset fun _ hw => ne_of_lt hw
  have hv : v ∈ {w : Place ℂ F | w.ordDifferential θ < 0}ᶜ :=
    not_lt.mpr (v.ord_nonneg_of_mem hθ)
  filter_upwards [hfin.isClosed.isOpen_compl.mem_nhds hv] with w hw
  exact w.mem_of_ord_nonneg (not_lt.mp hw)

theorem readDifferential_eq_expression_of_coeff_mem (v : Place ℂ F)
    (θ : Ω[F⁄ℂ]) (hθ : v.differentialCoeff θ ∈ v.toValuationSubring)
    (h g : F) (hh : h ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring)
    (he : θ = h • D ℂ F g) :
    readDifferential N v θ =ᶠ[𝓝 (0 : ℂ)] chartRead N v h * deriv (chartRead N v g) := by
  exact (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (analyticAt_readDifferential_of_coeff_mem N v θ hθ).continuousAt
    ((analyticAt_place_reading N v hh).continuousAt.mul
      (analyticAt_place_reading N v hg).deriv.continuousAt)).mp
    (readDifferential_eq_expression_germ N v θ h g he)

end
end Dubon2026.SourceFunctionField.OriginalChart

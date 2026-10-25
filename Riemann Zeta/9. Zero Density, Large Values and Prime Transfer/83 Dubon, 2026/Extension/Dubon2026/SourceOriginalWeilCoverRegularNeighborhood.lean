import Dubon2026.SourceOriginalWeilCoverCanonicalSupport
import Dubon2026.SourceOriginalWeilCoverLocalRegularPrimitives
import Dubon2026.SourceOriginalWeilCoverHausdorff

/-! DUB-17/18 -> cover reciprocity -> coordinate differential coefficients.
The already proved finite differential support and Hausdorff cover topology
give an open regular locus. No new local order calculation is needed. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders


theorem cover_eventually_differentialCoeff_mem (v : Place ℂ EE) (θ : Ω[EE⁄ℂ])
    (hθ : v.differentialCoeff θ ∈ v.toValuationSubring) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ᶠ w in 𝓝 v, w.differentialCoeff θ ∈ w.toValuationSubring := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI := place_t2Space N n radicand baseDivisor hRadicand hOrders
  haveI : ∀ w : Place ℂ EE, w.DCoordGenerates := cover_place_dCoordGenerates N n radicand
  haveI : Nontrivial Ω[EE⁄ℂ] := cover_differentials_nontrivial N n radicand
  by_cases h0 : θ = 0
  · subst θ
    exact Eventually.of_forall fun w => by rw [w.differentialCoeff_zero]; exact zero_mem _
  have hfin : {w : Place ℂ EE | w.ordDifferential θ < 0}.Finite :=
    (finite_cover_differential_support N n radicand h0).subset fun _ hw => ne_of_lt hw
  have hv : v ∈ {w : Place ℂ EE | w.ordDifferential θ < 0}ᶜ :=
    not_lt.mpr (v.ord_nonneg_of_mem hθ)
  filter_upwards [hfin.isClosed.isOpen_compl.mem_nhds hv] with w hw
  exact w.mem_of_ord_nonneg (not_lt.mp hw)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart

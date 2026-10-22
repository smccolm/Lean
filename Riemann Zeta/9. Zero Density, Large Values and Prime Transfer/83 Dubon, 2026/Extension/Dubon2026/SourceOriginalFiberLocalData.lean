import Dubon2026.SourceOriginalNonconstantDifferential
import Dubon2026.SourceOriginalLocalAbelJacobi
import Dubon2026.SourceOriginalPrescribedFiberCover

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel -> analytic fiber sum. Assemble the already proved original
chart orders, primitives and differential germ identity on a disk inside
any prescribed place neighborhood. Off its center both the function
minus its central value and its derivative are nonzero. All chart,
primitive, compatibility and nonvanishing inputs are derived here.
Adapted from S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ
attribute [local instance] placeTopology

theorem original_fiber_local_data {n : ℕ}
    (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (P₀ : Place ℂ F) {f : F} (h : Fin n → F) (hh : ∀ i, b i = h i • D ℂ F f)
    (hfc : ∀ a : ℂ, f ≠ algebraMap ℂ F a) (t₀ : ℂ) (v : Place ℂ F)
    (hv : 0 < v.ord (f - algebraMap ℂ F t₀))
    (O : Set (Place ℂ F)) (hO : IsOpen O) (hvO : v ∈ O) :
    ∃ ρ : ℝ, ∃ Φ : Fin n → ℂ → ℂ, 0 < ρ ∧
      ball (0 : ℂ) ρ ⊆ ball 0 (placeRadius N v) ∧
      (∀ z ∈ ball (0 : ℂ) ρ, placeFamily N v z ∈ O ∧
        f ∈ (placeFamily N v z).toValuationSubring) ∧
      (∀ i, ∀ z ∈ ball (0 : ℂ) ρ, HasDerivAt (Φ i) (readDifferential N v (b i) z) z) ∧
      (∀ z ∈ ball (0 : ℂ) ρ,
        abelJacobiVec N b P₀ (placeFamily N v z) - abelJacobiVec N b P₀ v -
          (fun i => Φ i z - Φ i 0) ∈ pathPeriodLattice N b) ∧
      (∀ z ∈ ball (0 : ℂ) ρ, AnalyticAt ℂ (chartRead N v f) z) ∧
      chartRead N v f 0 = t₀ ∧
      (∀ z ∈ ball (0 : ℂ) ρ, z ≠ 0 →
        chartRead N v f z ≠ t₀ ∧ deriv (chartRead N v f) z ≠ 0 ∧
          ∀ i, readDifferential N v (b i) z =
            chartRead N v (h i) z * deriv (chartRead N v f) z) := by
  have hf : f ∈ v.toValuationSubring :=
    (original_sub_const_mem_iff N v f t₀).mp (v.mem_of_ord_nonneg hv.le)
  have hreg0 : f ∈ (placeFamily N v 0).toValuationSubring := by
    rwa [(place_spec N v).2.1]
  have hval : chartRead N v f 0 = t₀ := by
    rw [chartRead, (place_spec N v).2.1]
    exact originalPlaceEval_eq_of_ord_sub_pos N ℂ v f t₀ hv
  obtain ⟨Φ, hΦ, hAJ⟩ := exists_abelJacobiVec_chart_primitive N b hb P₀ v
  have ha : AnalyticAt ℂ (chartRead N v f) 0 := analyticAt_place_reading N v hf
  have hfin := (chartRead_order_sub N v (mem_ball_self (place_spec N v).1) hreg0 t₀
    (fun he => hfc t₀ (sub_eq_zero.mp he))).1
  have hR : ∀ᶠ z in 𝓝[≠] (0 : ℂ), chartRead N v f z ≠ t₀ := by
    rcases (ha.sub analyticAt_const).eventually_eq_zero_or_eventually_ne_zero with h0 | h1
    · exact False.elim (hfin (analyticOrderAt_eq_top.mpr h0))
    · exact h1.mono fun z hz he => hz (sub_eq_zero.mpr he)
  have hd := eventually_deriv_chartRead_ne_zero N v hf hfc
  have he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ i,
      readDifferential N v (b i) z = chartRead N v (h i) z * deriv (chartRead N v f) z :=
    Filter.eventually_all.mpr fun i => readDifferential_eq_expression_germ N v (b i) (h i) f (hh i)
  have hpunct : ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
      chartRead N v f z ≠ t₀ ∧ deriv (chartRead N v f) z ≠ 0 ∧
        ∀ i, readDifferential N v (b i) z =
          chartRead N v (h i) z * deriv (chartRead N v f) z :=
    eventually_nhdsWithin_iff.mp (hR.and (hd.and he))
  have hO' : ∀ᶠ z in 𝓝 (0 : ℂ), placeFamily N v z ∈ O := by
    have hn : O ∈ 𝓝 (placeFamily N v 0) := by
      rw [(place_spec N v).2.1]
      exact hO.mem_nhds hvO
    exact (placeFamily_continuousAt_zero N v).eventually hn
  have hreg := (place_spec N v).2.2.1.eventually_mem
    (ball_mem_nhds 0 (place_spec N v).1) hreg0
  have hball : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball 0 (placeRadius N v) :=
    ball_mem_nhds 0 (place_spec N v).1
  obtain ⟨ρ, hρ, hall⟩ := Metric.eventually_nhds_iff_ball.mp
    (hball.and ((hO'.and hreg).and (ha.eventually_analyticAt.and hpunct)))
  exact ⟨ρ, Φ, hρ, fun z hz => (hall z hz).1, fun z hz => (hall z hz).2.1,
    fun i z hz => hΦ i z (hall z hz).1, fun z hz => hAJ z (hall z hz).1,
    fun z hz => (hall z hz).2.2.1, hval, fun z hz he => (hall z hz).2.2.2 he⟩

end
end Dubon2026.SourceFunctionField.OriginalChart

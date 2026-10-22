import Dubon2026.SourceOriginalNearbyOrders
import Dubon2026.SourceOriginalRamificationIsolated

/-! DUB-17/18 -> original torsion cardinality -> compatible finite
complex-place charts. The actual descended family has normalized orders
throughout one fixed neighborhood, for every nonzero original function.
Existing E4/E6 multiplicities remove nearby ramification; the power-descent
center theorem handles the center. Regularity implies analytic evaluation
at each point. The radius is independent of the function.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter EllipticCoordinate
open scoped Topology

theorem originalRamifiedPlace_chart_orders (N : ℕ) [NeZero N] (τ : ℍ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball (0 : ℂ) δ,
      ∀ f : modularFunctionFieldOver N ℂ, f ≠ 0 →
        MeromorphicAt (fun t => originalPlaceEval N ℂ (originalRamifiedPlace N τ t) f) z ∧
        meromorphicOrderAt (fun t => originalPlaceEval N ℂ (originalRamifiedPlace N τ t) f) z =
          ((originalRamifiedPlace N τ z).ord f : WithTop ℤ) ∧
        (f ∈ (originalRamifiedPlace N τ z).toValuationSubring →
          AnalyticAt ℂ (fun t => originalPlaceEval N ℂ (originalRamifiedPlace N τ t) f) z) := by
  obtain ⟨R, hR, horders⟩ := originalRamifiedPlace_nearby_orders N τ
  have hi := originalAnalyticRamification_param_eventually_one N τ
  rw [eventually_nhdsWithin_iff] at hi
  obtain ⟨ε, hε, hεeq⟩ := Metric.eventually_nhds_iff_ball.mp hi
  let e := originalAnalyticRamification N τ
  have he : e ≠ 0 := (originalAnalyticRamification_pos N τ).ne'
  let B := min R ε
  have hB : 0 < B := lt_min hR hε
  refine ⟨B ^ e, pow_pos hB e, ?_⟩
  intro z hz f hf
  by_cases hz0 : z = 0
  · subst z
    refine ⟨meromorphicAt_originalRamifiedPlace_eval N τ f, ?_, ?_⟩
    · rw [originalRamifiedPlace_zero]
      exact originalRamifiedPlace_meromorphicOrderAt N τ f hf
    · intro hmem
      rw [originalRamifiedPlace_zero] at hmem
      exact (originalRamifiedPlace_regular_analytic N τ f hmem).1
  · let w := PowerDescent.root e he z
    have hw : ‖w‖ < B := by
      have hz' : ‖z‖ < B ^ e := by simpa only [Metric.mem_ball, dist_zero_right] using hz
      by_contra! h
      have hp : B ^ e ≤ ‖w‖ ^ e := pow_le_pow_left₀ hB.le h e
      have hn : ‖w‖ ^ e = ‖z‖ := by rw [← norm_pow, PowerDescent.root_pow]
      rw [hn] at hp
      exact (not_le_of_gt hz') hp
    have hw0 : w ≠ 0 := by
      intro h
      have hp := PowerDescent.root_pow e he z
      change w ^ e = z at hp
      rw [h, zero_pow he] at hp
      exact hz0 hp.symm
    have hwε : w ∈ Metric.ball (0 : ℂ) ε := by
      simpa only [Metric.mem_ball, dist_zero_right] using hw.trans_le (min_le_right R ε)
    have heq : originalAnalyticRamification N (ofComplex (param τ w)) = 1 :=
      hεeq w hwε hw0
    obtain ⟨hm, ho, ha⟩ := horders z hz0 (hw.trans_le (min_le_left R ε)) f hf
    refine ⟨hm, ?_, ha⟩
    change meromorphicOrderAt (fun t => originalPlaceEval N ℂ (originalRamifiedPlace N τ t) f) z =
      (((originalAnalyticRamification N (ofComplex (param τ w)) : ℤ) *
        (originalRamifiedPlace N τ z).ord f : ℤ) : WithTop ℤ) at ho
    simpa only [heq, Nat.cast_one, one_mul] using ho

end
end Dubon2026.SourceFunctionField

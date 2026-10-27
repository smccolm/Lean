import Dubon2026.SourceGammaOneNearbyOrders
import Dubon2026.SourceGammaOneRamificationIsolation

/-! DUB-17/18 -> actual Gamma1 period comparison -> compatible finite
complex-place charts. The actual descended family has normalized orders
throughout one fixed neighborhood, for every nonzero original function.
Existing E4/E6 multiplicities remove nearby ramification; the power-descent
center theorem handles the center. Regularity implies analytic evaluation
at each point. The radius is independent of the function.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane CongruenceSubgroup Filter EllipticCoordinate
open scoped Topology MatrixGroups

theorem analyticRamification_param_eventually_one {Γ : Subgroup SL(2, ℤ)}
    (hT : ModularGroup.T ∈ Γ) (τ : ℍ) :
    ∀ᶠ u in 𝓝[≠] (0 : ℂ),
      analyticRamification hT (ofComplex (EllipticCoordinate.param τ u)) = 1 := by
  have ht := (EllipticCoordinate.hasDerivAt_param τ).tendsto_nhdsNE
    (sub_ne_zero.mpr (EllipticCoordinate.upper_ne_conj τ τ))
  rw [EllipticCoordinate.param_zero] at ht
  exact ht.eventually (analyticRamification_eventually_one hT τ)

theorem ramifiedPlace_chart_orders (N : ℕ) [NeZero N] (hT : ModularGroup.T ∈ Gamma1 N) (τ : ℍ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball (0 : ℂ) δ,
      ∀ f : functionFieldOver (Gamma1 N) ℂ, f ≠ 0 →
        MeromorphicAt (fun t => placeEval hT (ramifiedPlace N hT τ t) f) z ∧
        meromorphicOrderAt (fun t => placeEval hT (ramifiedPlace N hT τ t) f) z =
          ((ramifiedPlace N hT τ z).ord f : WithTop ℤ) ∧
        (f ∈ (ramifiedPlace N hT τ z).toValuationSubring →
          AnalyticAt ℂ (fun t => placeEval hT (ramifiedPlace N hT τ t) f) z) := by
  obtain ⟨R, hR, horders⟩ := ramifiedPlace_nearby_orders N hT τ
  have hi := analyticRamification_param_eventually_one hT τ
  rw [eventually_nhdsWithin_iff] at hi
  obtain ⟨ε, hε, hεeq⟩ := Metric.eventually_nhds_iff_ball.mp hi
  let e := analyticRamification hT τ
  have he : e ≠ 0 := (analyticRamification_pos hT τ).ne'
  let B := min R ε
  have hB : 0 < B := lt_min hR hε
  refine ⟨B ^ e, pow_pos hB e, ?_⟩
  intro z hz f hf
  by_cases hz0 : z = 0
  · subst z
    refine ⟨meromorphicAt_ramifiedPlace_eval N hT τ f, ?_, ?_⟩
    · rw [ramifiedPlace_zero]
      exact ramifiedPlace_meromorphicOrderAt N hT τ f hf
    · intro hmem
      rw [ramifiedPlace_zero] at hmem
      exact (ramifiedPlace_regular_analytic N hT τ f hmem).1
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
    have heq : analyticRamification hT (ofComplex (param τ w)) = 1 :=
      hεeq w hwε hw0
    obtain ⟨hm, ho, ha⟩ := horders z hz0 (hw.trans_le (min_le_left R ε)) f hf
    refine ⟨hm, ?_, ha⟩
    change meromorphicOrderAt (fun t => placeEval hT (ramifiedPlace N hT τ t) f) z =
      (((analyticRamification hT (ofComplex (param τ w)) : ℤ) *
        (ramifiedPlace N hT τ z).ord f : ℤ) : WithTop ℤ) at ho
    simpa only [heq, Nat.cast_one, one_mul] using ho

end
end Dubon2026.SourceFunctionField.GammaOne

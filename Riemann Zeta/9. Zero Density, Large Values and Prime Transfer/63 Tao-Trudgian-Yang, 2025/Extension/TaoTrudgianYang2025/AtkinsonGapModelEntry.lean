import TaoTrudgianYang2025.AtkinsonGapModelJets
import TaoTrudgianYang2025.ExponentPairShiftJets

/-! Every required model-phase jet is derived for the literal physical gap phase. -/

noncomputable section
open Set Filter Expdb
open scoped ContDiff Topology
namespace TaoTrudgianYang2025

theorem contDiffAt_atkinsonNormalizedGapPhase {M t u x : ℝ}
    (hM : 0 < M) (hu : 0 < u) (htu : u < t) (hx : 0 < x) :
    ContDiffAt ℝ ∞ (atkinsonNormalizedGapPhase M t u) x := by
  have ht : 0 < t := hu.trans htu
  unfold atkinsonNormalizedGapPhase atkinsonIndexPhaseDifference atkinsonIndexRealPhase
  fun_prop (disch := positivity)

theorem modelPhase_half_eq_inv_sqrt {x : ℝ} (hx : 0 < x) :
    modelPhase (1/2) x = 1/Real.sqrt x := by
  rw [modelPhase,Real.rpow_neg hx.le,← Real.sqrt_eq_rpow,one_div]

theorem atkinsonNormalizedGapPhase_approximate (P : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ M t u : ℝ,
      0 < M → 0 < u → u < t → t ≤ 2*u →
      Real.pi*M/(2*u) < δ →
      IsApproximateModelPhaseFunction (atkinsonNormalizedGapPhase M t u) (1/2) P ε := by
  obtain ⟨δ,hδ,hjets⟩ := atkinsonGapSlopeProfile_uniform_finite_jets P hε
  refine ⟨δ,hδ,?_⟩
  intro M t u hM hu htu ht2 hq
  have hr : t/u ∈ Icc (1 : ℝ) 2 := by
    constructor
    · exact (le_div_iff₀ hu).mpr (by linarith)
    · exact (div_le_iff₀ hu).mpr ht2
  have hq0 : 0 < Real.pi*M/(2*u) := by positivity
  have hqabs : |Real.pi*M/(2*u)| < δ := by rwa [abs_of_pos hq0]
  apply approximateModelPhase_of_interior_bounds
  · intro x hx
    exact (contDiffAt_atkinsonNormalizedGapPhase hM hu htu
      (zero_lt_one.trans_le hx.1)).contDiffWithinAt
  · intro x hx p hp
    have hx0 : 0 < x := by linarith [hx.1]
    have he : deriv (atkinsonNormalizedGapPhase M t u) =ᶠ[𝓝 x]
        atkinsonGapSlopeProfile (Real.pi*M/(2*u)) (t/u) := by
      filter_upwards [eventually_gt_nhds hx0] with y hy
      exact (hasDerivAt_atkinsonNormalizedGapPhase hM hu htu hy).deriv
    have hm : (fun y : ℝ => 1/Real.sqrt y) =ᶠ[𝓝 x] modelPhase (1/2) := by
      filter_upwards [eventually_gt_nhds hx0] with y hy
      exact (modelPhase_half_eq_inv_sqrt hy).symm
    rw [iteratedDeriv_succ',he.iteratedDeriv_eq p,← hm.iteratedDeriv_eq p]
    exact (hjets p hp (Real.pi*M/(2*u)) (t/u) x hqabs hr ⟨hx.1.le,hx.2.le⟩).le

end TaoTrudgianYang2025

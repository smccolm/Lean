import Mathlib

/-! DUB-17/18 -> actual Gamma1 Picard/H1 -> principal-divisor converse ->
construct a meromorphic function with the prescribed divisor. The local
integer-residue expansion gives finite polar products on an exhaustion
by disks; analytic primitives of the regular part are exponentiated and
normalized to agree on overlaps. Local residue expansions remain an
explicit upstream analytic obligation, not a function-existence premise.
Adapted from anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue.lean,
Apache-2.0; retained LICENSE and NOTICE. -/

namespace Dubon2026.SourceUpperHalfPlaneMeromorphicPrimitive
open scoped Topology
open Filter Set Metric

theorem int_eq_zero_of_div_eventuallyEq_analytic {n : ℤ} {a : ℂ} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h a) (heq : ∀ᶠ z in 𝓝[≠] a, (n : ℂ) / (z - a) = h z) : n = 0 := by

  have h1 : Tendsto (fun z : ℂ => h z * (z - a)) (𝓝[≠] a) (𝓝 (h a * (a - a))) :=
    ((hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
      ((continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  rw [sub_self, mul_zero] at h1
  have h2 : Tendsto (fun _ : ℂ => (n : ℂ)) (𝓝[≠] a) (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards [heq, self_mem_nhdsWithin] with z hz hza
    have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
    rw [← hz, div_mul_cancel₀ _ hza']
  have h3 : (n : ℂ) = 0 := tendsto_nhds_unique tendsto_const_nhds h2
  exact_mod_cast h3

variable {m : ℂ → ℤ} {ω : ℂ → ℂ}

/-- The actual local integer-residue expansion, with the regular point value. -/
def ResidueHyp (m : ℂ → ℤ) (ω : ℂ → ℂ) : Prop :=
  ∀ a : ℂ, 0 < a.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
    (∀ᶠ z in 𝓝[≠] a, ω z = (m a : ℂ) / (z - a) + g z) ∧ (m a = 0 → ω a = g a)

theorem ResidueHyp.analyticAt (H : ResidueHyp m ω) {a : ℂ} (ha : 0 < a.im) (hm : m a = 0) :
    AnalyticAt ℂ ω a := by
  obtain ⟨g, hg, heq, hval⟩ := H a ha
  refine hg.congr ?_
  have heq' : ∀ᶠ z in 𝓝 a, z ≠ a → ω z = g z := by
    have := eventually_nhdsWithin_iff.mp heq
    filter_upwards [this] with z hz hza
    rw [hz hza, hm, Int.cast_zero, zero_div, zero_add]
  filter_upwards [heq'] with z hz
  by_cases hza : z = a
  · rw [hza, hval hm]
  · exact (hz hza).symm

theorem ResidueHyp.eventually_eq_zero (H : ResidueHyp m ω) {a : ℂ} (ha : 0 < a.im) :
    ∀ᶠ z in 𝓝[≠] a, m z = 0 := by
  obtain ⟨g, hg, heq, -⟩ := H a ha

  have h1 : ∀ᶠ z in 𝓝 a, z ≠ a → ω z = (m a : ℂ) / (z - a) + g z :=
    eventually_nhdsWithin_iff.mp heq
  have h2 : ∀ᶠ z in 𝓝 a, AnalyticAt ℂ g z := hg.eventually_analyticAt
  have h3 : ∀ᶠ z in 𝓝 a, 0 < z.im := (Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds ha
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and (h2.and h3))
  have hmem : ∀ᶠ z in 𝓝[≠] a, z ∈ ball a ε ∧ z ≠ a := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [ball_mem_nhds a hε] with z hz hza using ⟨hz, hza⟩
  filter_upwards [hmem] with z ⟨hz, hza⟩
  obtain ⟨-, hgz, hzim⟩ := hball z hz

  have hωz : AnalyticAt ℂ ω z := by
    have hP : ∀ᶠ w in 𝓝 z, w ∈ ball a ε ∧ w ≠ a :=
      (isOpen_ball.inter isOpen_ne).mem_nhds ⟨hz, hza⟩
    have : AnalyticAt ℂ (fun w => (m a : ℂ) / (w - a) + g w) z := by
      refine AnalyticAt.add ?_ hgz
      exact analyticAt_const.div ((analyticAt_id).sub analyticAt_const) (sub_ne_zero.mpr hza)
    refine this.congr ?_
    filter_upwards [hP] with w ⟨hw, hwa⟩
    exact ((hball w hw).1 hwa).symm

  obtain ⟨g₁, hg₁, heq₁, -⟩ := H z hzim
  refine int_eq_zero_of_div_eventuallyEq_analytic (hωz.sub hg₁) ?_
  filter_upwards [heq₁] with w hw
  simp only [Pi.sub_apply, hw, add_sub_cancel_right]

theorem ResidueHyp.eventually_imp_eq_zero (H : ResidueHyp m ω) {a : ℂ} (ha : 0 < a.im) :
    ∀ᶠ z in 𝓝 a, z ≠ a → m z = 0 :=
  eventually_nhdsWithin_iff.mp (H.eventually_eq_zero ha)

theorem ResidueHyp.finite_support_inter (H : ResidueHyp m ω) {K : Set ℂ} (hK : IsCompact K)
    (hKU : ∀ z ∈ K, 0 < z.im) : {z ∈ K | m z ≠ 0}.Finite := by
  let V : ℂ → Set ℂ := fun a => {z | z ≠ a → m z = 0}
  have hV : ∀ a ∈ K, V a ∈ 𝓝 a := fun a ha => H.eventually_imp_eq_zero (hKU a ha)
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover V hV
  refine (t.finite_toSet).subset ?_
  intro z ⟨hzK, hmz⟩
  obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp (hcover hzK)
  by_contra hzt
  have : z ≠ a := fun h => hzt (h ▸ ha)
  exact hmz (hza this)

end Dubon2026.SourceUpperHalfPlaneMeromorphicPrimitive

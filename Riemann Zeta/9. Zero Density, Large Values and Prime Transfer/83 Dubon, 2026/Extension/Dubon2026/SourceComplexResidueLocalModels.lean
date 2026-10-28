import Dubon2026.SourceComplexCauchyPompeiu

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> compact-support logarithmic residue identity.
Actual local simple-pole expansions give finite residue support and an
analytic remainder. Previously proved dbar integrability and the kernel
normalization are reused; no integration formula is assumed. -/
namespace Dubon2026.SourceComplexReciprocity.Residue
noncomputable section
open MeasureTheory Filter Complex Metric Set DbarFundamental
open scoped Topology Real

theorem tsupport_D_subset (f : ℂ → ℂ) : tsupport (D f) ⊆ tsupport f :=
  closure_minimal (fun _ hz => by
    by_contra h'
    exact hz (D_eq_zero_of_notMem_tsupport h')) (isClosed_tsupport f)

/-- The finite part after subtracting the prescribed simple pole at each center. -/
noncomputable def Freg (F c : ℂ → ℂ) (z : ℂ) : ℂ :=
  limUnder (𝓝[≠] z) fun w => F w - c z / (w - z)

theorem Freg_eq {F c : ℂ → ℂ} {a : ℂ} {g : ℂ → ℂ} (hg : ContinuousAt g a)
    (hev : ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z) : Freg F c a = g a := by
  have ht : Tendsto (fun w => F w - c a / (w - a)) (𝓝[≠] a) (𝓝 (g a)) := by
    refine ((hg.tendsto).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [hev] with w hw
    rw [hw]
    ring
  exact ht.limUnder_eq

section

variable {U : Set ℂ} {F c : ℂ → ℂ} (hU : IsOpen U)
  (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
include hU hloc

theorem local_ball {a : ℂ} (ha : a ∈ U) : ∃ g : ℂ → ℂ, ∃ r > 0, ball a r ⊆ U ∧
    (∀ z ∈ ball a r, AnalyticAt ℂ g z) ∧ ∀ z ∈ ball a r, z ≠ a → F z = c a / (z - a) + g z := by
  obtain ⟨g, hg, hev⟩ := hloc a ha
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhds_iff.1 hg.eventually_analyticAt
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε₂, hε₂, hball₂⟩ := hev
  obtain ⟨ε₃, hε₃, hball₃⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds ha)
  have h1 : min ε₁ (min ε₂ ε₃) ≤ ε₁ := min_le_left _ _
  have h2 : min ε₁ (min ε₂ ε₃) ≤ ε₂ := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : min ε₁ (min ε₂ ε₃) ≤ ε₃ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨g, min ε₁ (min ε₂ ε₃), by positivity, (ball_subset_ball h3).trans hball₃,
    fun z hz => hball₁ (ball_subset_ball h1 hz), fun z hz hza => ?_⟩
  exact hball₂ (mem_ball.1 (ball_subset_ball h2 hz)) hza

omit hU in

theorem c_eq_zero_near {a : ℂ} {g : ℂ → ℂ} {r : ℝ} (hsub : ball a r ⊆ U)
    (hg : ∀ z ∈ ball a r, AnalyticAt ℂ g z)
    (hF : ∀ z ∈ ball a r, z ≠ a → F z = c a / (z - a) + g z) {z : ℂ} (hz : z ∈ ball a r)
    (hza : z ≠ a) : c z = 0 := by
  obtain ⟨gz, hgz, hevz⟩ := hloc z (hsub hz)
  have hnhds : ∀ᶠ w in 𝓝 z, w ∈ ball a r ∧ w ≠ a :=
    (isOpen_ball.inter isOpen_ne).mem_nhds ⟨hz, hza⟩
  have hΦ : ContinuousAt (fun w => c a / (w - a) + g w - gz w) z := by
    have h1 : ContinuousAt (fun w => c a / (w - a)) z :=
      continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 hza)
    exact (h1.add (hg z hz).continuousAt).sub hgz.continuousAt
  have hev : (fun w => (c a / (w - a) + g w - gz w) * (w - z)) =ᶠ[𝓝[≠] z] fun _ => c z := by
    filter_upwards [hevz, mem_nhdsWithin_of_mem_nhds hnhds, self_mem_nhdsWithin]
      with w hw1 hw2 hw3
    have hwz : w - z ≠ 0 := sub_ne_zero.2 hw3
    have : c z / (w - z) = c a / (w - a) + g w - gz w := by
      rw [← hF w hw2.1 hw2.2, hw1]
      ring
    exact ((div_eq_iff hwz).1 this).symm
  have ht : Tendsto (fun w => (c a / (w - a) + g w - gz w) * (w - z)) (𝓝[≠] z) (𝓝 0) := by
    have h2 : Tendsto (fun w : ℂ => w - z) (𝓝 z) (𝓝 0) := by
      have := ((continuous_id.sub continuous_const).tendsto z : Tendsto (fun w : ℂ => w - z) _ _)
      simp at this
      exact this
    have := (hΦ.tendsto.mul h2).mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
    simpa using this
  exact tendsto_const_nhds_iff.1 (ht.congr' hev)

theorem clean {a : ℂ} (ha : a ∈ U) : ∃ g : ℂ → ℂ, ∃ r > 0, ball a r ⊆ U ∧
    (∀ z ∈ ball a r, AnalyticAt ℂ g z) ∧
    (∀ z ∈ ball a r, Freg F c z = c a / (z - a) + g z) ∧
    ∀ z ∈ ball a r, z ≠ a → c z = 0 ∧ F z = Freg F c z := by
  obtain ⟨g, r, hr, hsub, hg, hF⟩ := local_ball hU hloc ha
  have hc0 : ∀ z ∈ ball a r, z ≠ a → c z = 0 := fun z hz hza =>
    c_eq_zero_near hloc hsub hg hF hz hza
  have hFF : ∀ z ∈ ball a r, z ≠ a → F z = Freg F c z := by
    intro z hz hza
    obtain ⟨gz, hgz, hevz⟩ := hloc z (hsub hz)
    rw [Freg_eq hgz.continuousAt hevz]
    have hnhds : ∀ᶠ w in 𝓝 z, w ∈ ball a r ∧ w ≠ a :=
      (isOpen_ball.inter isOpen_ne).mem_nhds ⟨hz, hza⟩
    have hΦc : ContinuousAt (fun w => c a / (w - a) + g w) z :=
      (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.2 hza)).add (hg z hz).continuousAt
    have h1 : Tendsto (fun w => c a / (w - a) + g w) (𝓝[≠] z) (𝓝 (gz z)) := by
      refine ((hgz.continuousAt.tendsto).mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [hevz, mem_nhdsWithin_of_mem_nhds hnhds] with w hw1 hw2
      rw [← hF w hw2.1 hw2.2, hw1, hc0 z hz hza, zero_div, zero_add]
    have h2 : Tendsto (fun w => c a / (w - a) + g w) (𝓝[≠] z) (𝓝 (c a / (z - a) + g z)) :=
      hΦc.tendsto.mono_left nhdsWithin_le_nhds
    rw [hF z hz hza]
    exact tendsto_nhds_unique h2 h1
  refine ⟨g, r, hr, hsub, hg, fun z hz => ?_, fun z hz hza => ⟨hc0 z hz hza, hFF z hz hza⟩⟩
  by_cases hza : z = a
  · rw [hza, sub_self, div_zero, zero_add]
    refine Freg_eq (hg a (mem_ball_self hr)).continuousAt ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a hr), self_mem_nhdsWithin]
      with w hw hwa
    exact hF w hw hwa
  · rw [← hFF z hz hza, hF z hz hza]

theorem finite_exceptional {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    {z ∈ K | c z ≠ 0 ∨ F z ≠ Freg F c z}.Finite := by
  choose g r hr hsub hg hFreg hexc using fun (x : ℂ) (hx : x ∈ K) => clean hU hloc (hKU hx)
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx => ball x (r x hx))
    fun x hx => ball_mem_nhds x (hr x hx)
  refine (t.finite_toSet.image (fun x : K => (x : ℂ))).subset ?_
  rintro z ⟨hzK, hz⟩
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (ht hzK)
  refine ⟨x, hxt, ?_⟩
  by_contra hne
  have := hexc x x.2 z hzx (fun h' => hne h'.symm)
  rcases hz with hz | hz
  · exact hz this.1
  · exact hz this.2

end

end
end Dubon2026.SourceComplexReciprocity.Residue

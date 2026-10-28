import Dubon2026.SourceMeromorphicCuspPrimitive
import Dubon2026.SourceMeromorphicCuspAnalyticData

/-! DUB17/18 -> actual Gamma1 Picard/H1 -> principal-divisor converse ->
actual meromorphic function -> nonzero translated cusp limits. The actual
weight-two differential decay rules out poles high in each cusp. Its
primitive has a uniform limit, and the actual function is a nonzero constant
times its exponential. The analytic differential input remains. -/
namespace Dubon2026.SourceMeromorphicPrimitiveMultiplier
noncomputable section
open scoped MatrixGroups Topology ModularForm
open UpperHalfPlane Filter Set Metric

theorem norm_sub_le_of_exp_decay {Ψ f : ℂ → ℂ} {A C δ : ℝ} (hδ : 0 < δ)
    (hΨ : ∀ z : ℂ, A < z.im → HasDerivAt Ψ (f z) z)
    (hf : ∀ z : ℂ, A < z.im → ‖f z‖ ≤ C * Real.exp (-δ * z.im))
    {y : ℝ} (hy : A < y) {z w : ℂ} (hz : y ≤ z.im) (hw : y ≤ w.im) :
    ‖Ψ w - Ψ z‖ ≤ C * Real.exp (-δ * y) * ‖w - z‖ := by
  have hseg : ∀ x ∈ segment ℝ z w, y ≤ x.im := by
    intro x hx
    rw [segment_eq_image] at hx
    obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hx
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    nlinarith
  have hA : ∀ x ∈ segment ℝ z w, A < x.im := fun x hx => lt_of_lt_of_le hy (hseg x hx)
  refine (convex_segment z w).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hΨ x (hA x hx)).hasDerivWithinAt) (fun x hx => ?_)
    (left_mem_segment ℝ z w) (right_mem_segment ℝ z w)
  refine (hf x (hA x hx)).trans ?_
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hf x (hA x hx))
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  nlinarith [hseg x hx, hδ]

theorem exists_uniform_limit_of_exp_decay {Ψ f : ℂ → ℂ} {A C δ : ℝ} (hδ : 0 < δ)
    (hΨ : ∀ z : ℂ, A < z.im → HasDerivAt Ψ (f z) z)
    (hf : ∀ z : ℂ, A < z.im → ‖f z‖ ≤ C * Real.exp (-δ * z.im)) :
    ∃ (L : ℂ) (M : ℝ), ∀ z : ℂ, A < z.im → ‖Ψ z - L‖ ≤ M * Real.exp (-δ * z.im) := by
  set q : ℝ := Real.exp (-δ) with hq
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq0 : 0 < q := Real.exp_pos _

  let u : ℂ → ℕ → ℂ := fun z n => Ψ (z + n * Complex.I)
  have him : ∀ (z : ℂ) (n : ℕ), (z + n * Complex.I).im = z.im + n := fun z n => by simp
  have hstep : ∀ z : ℂ, A < z.im → ∀ n : ℕ,
      dist (u z n) (u z (n + 1)) ≤ C * Real.exp (-δ * z.im) * q ^ n := by
    intro z hz n
    have hy : A < z.im + n := lt_of_lt_of_le hz (le_add_of_nonneg_right n.cast_nonneg)
    have h := norm_sub_le_of_exp_decay hδ hΨ hf hy (z := z + n * Complex.I)
      (w := z + (n + 1 : ℕ) * Complex.I) (by rw [him]) (by rw [him]; push_cast; linarith)
    rw [dist_comm, dist_eq_norm]
    refine h.trans (le_of_eq ?_)
    have hn : ‖(z + ((n + 1 : ℕ) : ℂ) * Complex.I) - (z + (n : ℂ) * Complex.I)‖ = 1 := by
      push_cast
      ring_nf
      exact Complex.norm_I
    rw [hn, mul_one, hq, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 1
    ring_nf
  have hlim : ∀ z : ℂ, A < z.im → ∃ a : ℂ, Tendsto (u z) atTop (𝓝 a) ∧
      dist (u z 0) a ≤ C * Real.exp (-δ * z.im) / (1 - q) := by
    intro z hz
    have hcs : CauchySeq (u z) := cauchySeq_of_le_geometric q _ hq1 (hstep z hz)
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hcs
    exact ⟨a, ha, dist_le_of_le_geometric_of_tendsto₀ q _ hq1 (hstep z hz) ha⟩

  set zb : ℂ := ((A + 1 : ℝ) : ℂ) * Complex.I with hzb_def
  have hzb : A < zb.im := by simp [zb]
  obtain ⟨L, hL, -⟩ := hlim zb hzb
  refine ⟨L, C / (1 - q), fun z hz => ?_⟩
  obtain ⟨a, ha, hdist⟩ := hlim z hz

  have haL : a = L := by
    set y : ℝ := min z.im zb.im
    have hy : A < y := lt_min hz hzb
    have hbound : ∀ n : ℕ, ‖u z n - u zb n‖ ≤ C * Real.exp (-δ * y) * ‖z - zb‖ * q ^ n := by
      intro n
      have hyn : A < y + n := lt_of_lt_of_le hy (le_add_of_nonneg_right n.cast_nonneg)
      have h := norm_sub_le_of_exp_decay hδ hΨ hf hyn (z := zb + n * Complex.I)
        (w := z + n * Complex.I) (by rw [him]; gcongr; exact min_le_right _ _)
        (by rw [him]; gcongr; exact min_le_left _ _)
      refine h.trans (le_of_eq ?_)
      have : (z + (n : ℂ) * Complex.I) - (zb + (n : ℂ) * Complex.I) = z - zb := by ring
      have hexp : Real.exp (-δ * (y + n)) = Real.exp (-δ * y) * q ^ n := by
        rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      rw [this, hexp]
      ring
    have h0 : Tendsto (fun n => u z n - u zb n) atTop (𝓝 0) := by
      refine squeeze_zero_norm hbound ?_
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).const_mul
        (C * Real.exp (-δ * y) * ‖z - zb‖)
      rwa [mul_zero] at this
    have h1 : Tendsto (fun n => u z n - u zb n) atTop (𝓝 (a - L)) := ha.sub hL
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h0)
  subst haL
  have h0 : u z 0 = Ψ z := by simp [u]
  rw [← dist_eq_norm, ← h0]
  refine hdist.trans (le_of_eq ?_)
  ring

end
end Dubon2026.SourceMeromorphicPrimitiveMultiplier

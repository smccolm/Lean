import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> path periods.
Glue analytic primitives across a finite subdivision of the actual path
parameter interval. Equal derivatives give a locally constant difference;
the adjustment at each subdivision endpoint preserves that derivative.
The following original-path consumer supplies the local primitives and
coordinate functions, so no global primitive is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalPrimitiveGlue
noncomputable section
open Filter Set
open scoped Topology

theorem eventually_sub_eq_of_hasDerivAt {Φ₁ Φ₂ h : ℂ → ℂ} {z₀ : ℂ}
    (h₁ : ∀ᶠ z in 𝓝 z₀, HasDerivAt Φ₁ (h z) z) (h₂ : ∀ᶠ z in 𝓝 z₀, HasDerivAt Φ₂ (h z) z) :
    ∀ᶠ z in 𝓝 z₀, Φ₁ z - Φ₂ z = Φ₁ z₀ - Φ₂ z₀ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (h₁.and h₂)
  filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz
  have key := (convex_ball z₀ r).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => Φ₁ z - Φ₂ z) (f' := fun _ => (0 : ℂ)) (C := 0)
    (fun x hx => ((hball hx).1.sub (hball hx).2).hasDerivWithinAt.congr_deriv (sub_self _))
    (fun x _ => by simp) (Metric.mem_ball_self hr) hz
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at key
  exact key

section Glue

variable (R : ℝ → ℂ → ℂ) (k : ℝ → ℝ → ℂ)

/-- A local analytic primitive of the coefficient reading in a path coordinate. -/
def IsPrimNear (G : ℝ → ℂ) (t₀ : ℝ) : Prop :=
  ∃ Φ : ℂ → ℂ, (∀ᶠ z in 𝓝 (k t₀ t₀), HasDerivAt Φ (R t₀ z) z) ∧ ∀ᶠ t in 𝓝 t₀, G t = Φ (k t₀ t)

/-- Local analytic primitives representing a function on the specified parameter set. -/
def IsPrimOn (G : ℝ → ℂ) (S : Set ℝ) : Prop :=
  ∀ t₀ ∈ S, ∃ Φ : ℂ → ℂ, (∀ᶠ z in 𝓝 (k t₀ t₀), HasDerivAt Φ (R t₀ z) z) ∧
    ∀ᶠ t in 𝓝 t₀, t ∈ S → G t = Φ (k t₀ t)

variable {R k}

theorem IsPrimOn.mono {G : ℝ → ℂ} {S S' : Set ℝ} (h : IsPrimOn R k G S) (hS : S' ⊆ S) :
    IsPrimOn R k G S' := fun t₀ ht₀ => by
  obtain ⟨Φ, hΦ, hG⟩ := h t₀ (hS ht₀)
  exact ⟨Φ, hΦ, hG.mono fun t ht hts => ht (hS hts)⟩

theorem isPrimOn_of_isPrimNear {G : ℝ → ℂ} {S : Set ℝ} (h : ∀ t₀ ∈ S, IsPrimNear R k G t₀) :
    IsPrimOn R k G S := fun t₀ ht₀ => by
  obtain ⟨Φ, hΦ, hG⟩ := h t₀ ht₀
  exact ⟨Φ, hΦ, hG.mono fun t ht _ => ht⟩

theorem IsPrimOn.extend {G G' : ℝ → ℂ} {a b : ℝ} (hk : ∀ t₀, ContinuousAt (k t₀) t₀)
    (hG : IsPrimOn R k G (Icc 0 a)) (hG' : ∀ t₀ ∈ Icc a b, IsPrimNear R k G' t₀)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    IsPrimOn R k (fun t => if t ≤ a then G t else G' t + (G a - G' a)) (Icc 0 b) := by
  intro t₀ ht₀
  rcases eq_or_ne t₀ a with heq | hne
  · rw [heq]
    obtain ⟨Φ₁, hΦ₁, hG₁⟩ := hG a ⟨ha, le_rfl⟩
    obtain ⟨Φ₂, hΦ₂, hG₂⟩ := hG' a ⟨le_rfl, hab⟩
    refine ⟨Φ₁, hΦ₁, ?_⟩
    have hsub : ∀ᶠ t in 𝓝 a, Φ₁ (k a t) - Φ₂ (k a t) = Φ₁ (k a a) - Φ₂ (k a a) :=
      Filter.Tendsto.eventually (hk a) (eventually_sub_eq_of_hasDerivAt hΦ₁ hΦ₂)
    have h1 : G a = Φ₁ (k a a) := hG₁.self_of_nhds ⟨ha, le_rfl⟩
    have h2 : G' a = Φ₂ (k a a) := hG₂.self_of_nhds
    filter_upwards [hG₁, hG₂, hsub] with t ht1 ht2 hts htmem
    by_cases hta : t ≤ a
    · rw [if_pos hta]
      exact ht1 ⟨htmem.1, hta⟩
    · rw [if_neg hta, ht2, h1, h2]
      linear_combination (-1 : ℂ) * hts
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨Φ, hΦ, hGt⟩ := hG t₀ ⟨ht₀.1, hlt.le⟩
    refine ⟨Φ, hΦ, ?_⟩
    filter_upwards [hGt, Iio_mem_nhds hlt] with t ht htlt hts
    rw [if_pos (le_of_lt htlt)]
    exact ht ⟨hts.1, le_of_lt htlt⟩
  · obtain ⟨Φ, hΦ, hGt⟩ := hG' t₀ ⟨hgt.le, ht₀.2⟩
    refine ⟨fun z => Φ z + (G a - G' a), hΦ.mono fun z hz => hz.add_const _, ?_⟩
    filter_upwards [hGt, Ioi_mem_nhds hgt] with t ht htgt _
    rw [if_neg (not_le.2 htgt), ht]

theorem exists_isPrimOn_Icc (hk : ∀ t₀, ContinuousAt (k t₀) t₀)
    (hloc : ∀ s : ℝ, ∃ G : ℝ → ℂ, ∀ᶠ t₀ in 𝓝 s, IsPrimNear R k G t₀) :
    ∃ G : ℝ → ℂ, IsPrimOn R k G (Icc 0 1) := by
  choose G hG using hloc
  have hε : ∀ s : ℝ, ∃ ε > 0, ∀ t₀ ∈ Metric.ball s ε, IsPrimNear R k (G s) t₀ := fun s =>
    Metric.eventually_nhds_iff_ball.1 (hG s)
  choose ε hε0 hεG using hε
  obtain ⟨δ, hδ0, hδ⟩ := lebesgue_number_lemma_of_metric (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    (c := fun s => Metric.ball s (ε s)) (fun _ => Metric.isOpen_ball)
    (fun s _ => mem_iUnion.2 ⟨s, Metric.mem_ball_self (hε0 s)⟩)
  have key : ∀ x ∈ Icc (0 : ℝ) 1, ∃ G₀ : ℝ → ℂ, ∀ t₀ ∈ Metric.ball x δ, IsPrimNear R k G₀ t₀ := by
    intro x hx
    obtain ⟨i, hi⟩ := hδ x hx
    exact ⟨G i, fun t₀ ht₀ => hεG i t₀ (hi ht₀)⟩
  set d : ℝ := δ / 2 with hd
  have hd0 : 0 < d := by positivity
  have hdδ : d < δ := by linarith

  have step : ∀ n : ℕ, (n : ℝ) * d ≤ 1 →
      ∃ G₀ : ℝ → ℂ, IsPrimOn R k G₀ (Icc 0 (((n : ℝ) + 1) * d)) := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨G₀, hG₀⟩ := key 0 ⟨le_rfl, zero_le_one⟩
      refine ⟨G₀, isPrimOn_of_isPrimNear fun t₀ ht₀ => hG₀ t₀ ?_⟩
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht₀.1]
      have h2 := ht₀.2
      simp only [Nat.cast_zero, zero_add, one_mul] at h2
      linarith
    | succ n ih =>
      intro hn
      rw [Nat.cast_succ] at hn ⊢
      have ha0 : 0 ≤ ((n : ℝ) + 1) * d := by positivity
      have hn' : (n : ℝ) * d ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_right (by linarith) hd0.le) hn
      obtain ⟨G₀, hG₀⟩ := ih hn'
      obtain ⟨G₁, hG₁⟩ := key _ ⟨ha0, hn⟩
      refine ⟨_, hG₀.extend hk (b := ((n : ℝ) + 1 + 1) * d) (fun t₀ ht₀ => hG₁ t₀ ?_) ha0
        (mul_le_mul_of_nonneg_right (by linarith) hd0.le)⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 ht₀.1)]
      have h2 := ht₀.2
      nlinarith
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, (N : ℝ) * d ≤ 1 ∧ 1 ≤ ((N : ℝ) + 1) * d := by
    refine ⟨⌊1 / d⌋₊, ?_, ?_⟩
    · calc (⌊1 / d⌋₊ : ℝ) * d ≤ (1 / d) * d :=
            mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) hd0.le
        _ = 1 := one_div_mul_cancel hd0.ne'
    · have h := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (1 / d)) hd0
      rw [one_div_mul_cancel hd0.ne'] at h
      exact h.le
  obtain ⟨G₀, hG₀⟩ := step N hN1
  exact ⟨G₀, hG₀.mono (Icc_subset_Icc le_rfl hN2)⟩

end Glue

end
end Dubon2026.SourceFunctionField.OriginalPrimitiveGlue

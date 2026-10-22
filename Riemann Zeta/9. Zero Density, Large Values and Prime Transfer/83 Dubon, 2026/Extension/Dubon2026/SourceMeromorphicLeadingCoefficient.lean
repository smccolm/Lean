import Dubon2026.SourceMeromorphicCompactConstancy

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
original-function comparison. Meromorphic functions with a fixed effective
pole bound satisfy a linear relation once their number exceeds its degree
plus one. Removing one leading coefficient reduces the allowed pole degree;
compact holomorphic constancy supplies degree zero. This is the analytic
dimension bound required to identify functions with original field elements.
Adapted from S_Manifold_exists_ne_zero_and_sum_mul_eventuallyEq_zero_of_degree_lt_card,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.MeromorphicCompact
noncomputable section
open Filter Topology Set
open scoped Manifold ContDiff Topology

variable {f f₁ f₂ G G₁ G₂ : ℂ → ℂ} {c : ℂ}

theorem apply_eq_of_eventuallyEq (h₁ : AnalyticAt ℂ G₁ c) (h₂ : AnalyticAt ℂ G₂ c)
    (h : G₁ =ᶠ[𝓝[≠] c] G₂) : G₁ c = G₂ c :=
  tendsto_nhds_unique_of_eventuallyEq (h₁.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (h₂.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h

/-- Multiplication by the prescribed power of the centered coordinate. -/
abbrev wt (k : ℕ) (c : ℂ) (f : ℂ → ℂ) : ℂ → ℂ := fun z => (z - c) ^ k * f z

theorem meromorphicAt_pow_sub (k : ℕ) (c : ℂ) : MeromorphicAt (fun z : ℂ => (z - c) ^ k) c :=
  ((analyticAt_id.sub analyticAt_const).pow k).meromorphicAt

theorem meromorphicOrderAt_pow_sub (k : ℕ) (c : ℂ) :
    meromorphicOrderAt (fun z : ℂ => (z - c) ^ k) c = (k : ℤ) := by
  refine (meromorphicOrderAt_eq_int_iff (meromorphicAt_pow_sub k c)).2 ⟨1, analyticAt_const,
    one_ne_zero, Eventually.of_forall fun z => ?_⟩
  simp [zpow_natCast]

theorem meromorphicAt_wt (k : ℕ) (hf : MeromorphicAt f c) : MeromorphicAt (wt k c f) c :=
  (meromorphicAt_pow_sub k c).mul hf

theorem meromorphicOrderAt_wt (k : ℕ) (hf : MeromorphicAt f c) :
    meromorphicOrderAt (wt k c f) c = (k : ℤ) + meromorphicOrderAt f c := by
  rw [show wt k c f = (fun z : ℂ => (z - c) ^ k) * f from rfl,
    meromorphicOrderAt_mul (meromorphicAt_pow_sub k c) hf, meromorphicOrderAt_pow_sub]

theorem le_order_iff (k : ℕ) (hf : MeromorphicAt f c) :
    ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f c ↔ 0 ≤ meromorphicOrderAt (wt k c f) c := by
  rw [meromorphicOrderAt_wt k hf]
  generalize meromorphicOrderAt f c = o
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    norm_cast
    omega

theorem exists_rep (k : ℕ) (hf : MeromorphicAt f c)
    (hk : ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f c) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G c ∧ wt k c f =ᶠ[𝓝[≠] c] G :=
  exists_analyticAt_eventuallyEq (meromorphicAt_wt k hf) ((le_order_iff k hf).1 hk)

open Classical in

/-- Value of the holomorphic filling after multiplication by the pole bound. -/
def lead (k : ℕ) (f : ℂ → ℂ) (c : ℂ) : ℂ :=
  if h : ∃ G : ℂ → ℂ, AnalyticAt ℂ G c ∧ wt k c f =ᶠ[𝓝[≠] c] G then h.choose c else 0

theorem lead_eq {k : ℕ} (hG : AnalyticAt ℂ G c) (heq : wt k c f =ᶠ[𝓝[≠] c] G) :
    lead k f c = G c := by
  have h : ∃ G : ℂ → ℂ, AnalyticAt ℂ G c ∧ wt k c f =ᶠ[𝓝[≠] c] G := ⟨G, hG, heq⟩
  rw [lead, dif_pos h]
  exact apply_eq_of_eventuallyEq h.choose_spec.1 hG (h.choose_spec.2.symm.trans heq)

theorem lead_add {k : ℕ} (h₁ : MeromorphicAt f₁ c) (hk₁ : ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f₁ c)
    (h₂ : MeromorphicAt f₂ c) (hk₂ : ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f₂ c) :
    lead k (f₁ + f₂) c = lead k f₁ c + lead k f₂ c := by
  obtain ⟨G₁, hG₁, he₁⟩ := exists_rep k h₁ hk₁
  obtain ⟨G₂, hG₂, he₂⟩ := exists_rep k h₂ hk₂
  have he : wt k c (f₁ + f₂) =ᶠ[𝓝[≠] c] (G₁ + G₂) := by
    filter_upwards [he₁, he₂] with z h1 h2
    simp only [wt, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  rw [lead_eq (hG₁.add hG₂) he, lead_eq hG₁ he₁, lead_eq hG₂ he₂, Pi.add_apply]

theorem lead_smul {k : ℕ} (a : ℂ) (h₁ : MeromorphicAt f c)
    (hk₁ : ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f c) :
    lead k (a • f) c = a * lead k f c := by
  obtain ⟨G, hG, he⟩ := exists_rep k h₁ hk₁
  have he' : wt k c (a • f) =ᶠ[𝓝[≠] c] (a • G) := by
    filter_upwards [he] with z h1
    simp only [wt, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [← h1]; ring
  rw [lead_eq (hG.const_smul (c := a)) he', lead_eq hG he, Pi.smul_apply, smul_eq_mul]

theorem le_order_of_lead_eq_zero {k : ℕ} (hf : MeromorphicAt f c)
    (hk : ((-((k + 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f c)
    (h0 : lead (k + 1) f c = 0) : ((-(k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f c := by
  obtain ⟨G, hG, he⟩ := exists_rep (k + 1) hf hk
  have hGc : G c = 0 := by rw [← lead_eq hG he, h0]

  have hG₁ : AnalyticAt ℂ (dslope G c) c := by
    obtain ⟨p, hp⟩ := hG
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  have hfac : ∀ z, G z = (z - c) * dslope G c z := fun z => by
    have := sub_smul_dslope G c z
    rw [smul_eq_mul, hGc, sub_zero] at this
    exact this.symm

  have he' : wt k c f =ᶠ[𝓝[≠] c] dslope G c := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at he ⊢
    filter_upwards [he] with z hz hne
    have hz' := hz hne
    simp only [wt] at hz' ⊢
    rw [hfac z, pow_succ] at hz'
    have hzc : z - c ≠ 0 := sub_ne_zero.2 hne
    have : (z - c) * ((z - c) ^ k * f z) = (z - c) * dslope G c z := by
      rw [← hz']; ring
    exact mul_left_cancel₀ hzc this
  rw [le_order_iff k hf, meromorphicOrderAt_congr he']
  exact hG₁.meromorphicOrderAt_nonneg


end
end Dubon2026.SourceFunctionField.MeromorphicCompact

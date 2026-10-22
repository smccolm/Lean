import Dubon2026.SourceOriginalFiberDisks
import Dubon2026.SourceComplexWeightedFiberContour
import Dubon2026.SourceComplexFiberConstancy

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel -> weighted fiber contour. Shrink the actual disjoint disks
and choose a common parameter neighborhood. The proved compact fiber cover
locates every nearby fiber, and the weighted argument principle computes
the two contour sums with their exact analytic multiplicities. This data
contains no conclusion about period membership or constancy of a fiber sum.
Adapted from S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential ComplexFiberContour
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ
attribute [local instance] placeTopology

/-- Actual original chart contours and finite zeros in a common parameter neighborhood. -/
structure OriginalFiberContours {n : ℕ} (bb : Fin n → Ω[F⁄ℂ])
    (P₀ : Place ℂ F) (f : F) (h : Fin n → F) (t₀ : ℂ) (Z₀ : Finset (Place ℂ F))
    extends OriginalFiberDisks N bb P₀ f h t₀ Z₀ where
  /-- Smaller positive radii whose closed disks lie in the primitive charts. -/
  r : Place ℂ F → ℝ
  /-- Radius of the common neighborhood of the central fiber parameter. -/
  ε : ℝ
  /-- Coordinate zeros of each nearby fiber inside each smaller disk. -/
  Zf : Place ℂ F → ℂ → Finset ℂ
  hε : 0 < ε
  hzeros : ∀ t ∈ ball t₀ ε, ∀ w : Place ℂ F,
    0 < w.ord (f - algebraMap ℂ F t) → ∃ v ∈ Z₀, ∃ a ∈ ball (0 : ℂ) (r v), placeFamily N v a = w
  hr : ∀ v, 0 < r v
  hcb : ∀ v, Metric.closedBall ((0 : ℂ)) (r v) ⊆
      Metric.ball ((0 : ℂ)) (ρ v)
  hbb' : ∀ v, Metric.ball ((0 : ℂ)) (r v) ⊆
      Metric.ball ((0 : ℂ)) (ρ v)
  hsph : ∀ v, Metric.sphere ((0 : ℂ)) (r v) ⊆
      Metric.ball ((0 : ℂ)) (ρ v)
  hΦan : ∀ v ∈ Z₀, ∀ i, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      AnalyticAt ℂ (Φ v i) z
  hΨan : ∀ v ∈ Z₀, ∀ i, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      AnalyticAt ℂ (readDifferential N v (bb i)) z
  hcirc' : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀,
      ∀ z ∈ Metric.sphere ((0 : ℂ)) (r v), chartRead N v f z ≠ t
  hZf : ∀ v ∈ Z₀, ∀ t ∈ Metric.ball t₀ ε, ∀ a,
      a ∈ Zf v t ↔ a ∈ Metric.ball ((0 : ℂ)) (r v) ∧ chartRead N v f a = t
  hI0 : ∀ v ∈ Z₀, ∀ t ∈ Metric.ball t₀ ε,
      (∮ z in C((0 : ℂ), r v),
          (fun _ => (1 : ℂ)) z * deriv (chartRead N v f) z / (chartRead N v f z - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf v t, (analyticOrderNatAt (fun z => chartRead N v f z - t) a : ℂ) * 1
  hIΦ : ∀ v ∈ Z₀, ∀ t ∈ Metric.ball t₀ ε, ∀ i,
      (∮ z in C((0 : ℂ), r v),
          Φ v i z * deriv (chartRead N v f) z / (chartRead N v f z - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf v t, (analyticOrderNatAt (fun z => chartRead N v f z - t) a : ℂ) * Φ v i a

theorem exists_originalFiberContours {n : ℕ} (bb : Fin n → Ω[F⁄ℂ])
    (P₀ : Place ℂ F) (f : F) (h : Fin n → F) (t₀ : ℂ) (Z₀ : Finset (Place ℂ F))
    (hZ₀ : ∀ v, v ∈ Z₀ ↔ 0 < v.ord (f - algebraMap ℂ F t₀))
    (hne : ∀ t : ℂ, f - algebraMap ℂ F t ≠ 0)
    (d : OriginalFiberDisks N bb P₀ f h t₀ Z₀) :
    Nonempty (OriginalFiberContours N bb P₀ f h t₀ Z₀) := by
  classical
  obtain ⟨O, ρ, Φ, hρ, hOdisj, htar, hOf, hΦd, hAJloc, hRan, hRc, hpunct⟩ := d
  have hΦan : ∀ v ∈ Z₀, ∀ i, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      AnalyticAt ℂ (Φ v i) z := by
    intro v hv i z hz
    have hd : DifferentiableOn ℂ (Φ v i) (Metric.ball ((0 : ℂ)) (ρ v)) :=
      fun y hy => (hΦd v hv i y hy).differentiableAt.differentiableWithinAt
    exact hd.analyticAt (Metric.isOpen_ball.mem_nhds hz)
  have hΨan : ∀ v ∈ Z₀, ∀ i, ∀ z ∈ Metric.ball ((0 : ℂ)) (ρ v),
      AnalyticAt ℂ (readDifferential N v (bb i)) z := by
    intro v hv i z hz
    have h1 : AnalyticAt ℂ (deriv (Φ v i)) z := (hΦan v hv i z hz).deriv
    refine h1.congr ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with y hy
    exact (hΦd v hv i y hy).deriv

  set r : Place ℂ F → ℝ := fun v => ρ v / 2 with hrdef
  have hr : ∀ v, 0 < r v := fun v => by simp only [hrdef]; linarith [hρ v]
  have hrρ : ∀ v, r v < ρ v := fun v => by simp only [hrdef]; linarith [hρ v]
  have hcb : ∀ v, Metric.closedBall ((0 : ℂ)) (r v) ⊆
      Metric.ball ((0 : ℂ)) (ρ v) := fun v =>
    Metric.closedBall_subset_ball (hrρ v)
  have hbb' : ∀ v, Metric.ball ((0 : ℂ)) (r v) ⊆
      Metric.ball ((0 : ℂ)) (ρ v) := fun v =>
    Metric.ball_subset_ball (hrρ v).le
  have hsph : ∀ v, Metric.sphere ((0 : ℂ)) (r v) ⊆
      Metric.ball ((0 : ℂ)) (ρ v) := fun v =>
    Metric.sphere_subset_closedBall.trans (hcb v)
  have hsph_ne : ∀ v, ∀ z ∈ Metric.sphere ((0 : ℂ)) (r v),
      z ≠ (0 : ℂ) := fun v z hz => Metric.ne_of_mem_sphere hz (hr v).ne'
  set Dv : Place ℂ F → Set (Place ℂ F) := fun v =>
    placeFamily N v '' Metric.ball (0 : ℂ) (r v) with hDvdef
  have hDo : ∀ v ∈ Z₀, IsOpen (Dv v) := fun v hv =>
    isOpen_placeFamily_image N v Metric.isOpen_ball ((hbb' v).trans (htar v hv))
  have hDv : ∀ v ∈ Z₀, v ∈ Dv v := fun v _ =>
    ⟨0, Metric.mem_ball_self (hr v), (place_spec N v).2.1⟩
  obtain ⟨ε₁, hε₁, hzeros⟩ := exists_original_prescribed_fiber_cover N t₀ (hne t₀) Z₀ hZ₀ Dv hDo hDv
  have hcirc : ∀ᶠ t in 𝓝 t₀, ∀ v ∈ Z₀, ∀ z ∈ Metric.sphere ((0 : ℂ)) (r v),
      chartRead N v f z ≠ t := by
    refine (Filter.eventually_all_finset Z₀).2 fun v hv => ?_
    refine eventually_forall_sphere_ne (fun z hz => (hRan v hv z (hsph v hz)).continuousAt
      |>.continuousWithinAt) fun z hz => (hpunct v hv z (hsph v hz) (hsph_ne v z hz)).1
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (Metric.ball_mem_nhds t₀ hε₁) hcirc)
  have hε₁' : ∀ t ∈ Metric.ball t₀ ε, dist t t₀ < ε₁ := fun t ht => Metric.mem_ball.1 (hεball ht).1
  have hcirc' : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀,
      ∀ z ∈ Metric.sphere ((0 : ℂ)) (r v), chartRead N v f z ≠ t :=
    fun t ht => (hεball ht).2

  have hH1 : ∀ (v : Place ℂ F) (t : ℂ), ∃ Zf : Finset ℂ, v ∈ Z₀ → t ∈ Metric.ball t₀ ε →
      (∀ a, a ∈ Zf ↔ a ∈ Metric.ball ((0 : ℂ)) (r v) ∧ chartRead N v f a = t) ∧
      (∮ z in C((0 : ℂ), r v),
          (fun _ => (1 : ℂ)) z * deriv (chartRead N v f) z / (chartRead N v f z - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf, (analyticOrderNatAt (fun z => chartRead N v f z - t) a : ℂ) * 1 ∧
      ∀ i, (∮ z in C((0 : ℂ), r v),
          Φ v i z * deriv (chartRead N v f) z / (chartRead N v f z - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf, (analyticOrderNatAt (fun z => chartRead N v f z - t) a : ℂ) * Φ v i a := by
    intro v t
    by_cases hv : v ∈ Z₀
    · by_cases ht : t ∈ Metric.ball t₀ ε
      · have hRcl : ∀ z ∈ Metric.closedBall ((0 : ℂ)) (r v),
            AnalyticAt ℂ (chartRead N v f) z := fun z hz => hRan v hv z (hcb v hz)
        obtain ⟨Zf, hZf, hint⟩ :=
          circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt (G := fun _ => (1 : ℂ))
            (hr v) hRcl (fun z _ => analyticAt_const) (hcirc' t ht v hv)
        refine ⟨Zf, fun _ _ => ⟨hZf, hint, fun i => ?_⟩⟩
        obtain ⟨Zf', hZf', hint'⟩ :=
          circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt (G := Φ v i)
            (hr v) hRcl (fun z hz => hΦan v hv i z (hcb v hz)) (hcirc' t ht v hv)
        have hZZ : Zf' = Zf := Finset.ext fun a => (hZf' a).trans (hZf a).symm
        rw [hint', hZZ]
      · exact ⟨∅, fun _ h' => absurd h' ht⟩
    · exact ⟨∅, fun h' => absurd h' hv⟩
  choose Zf hZfP using hH1
  have hZf : ∀ v ∈ Z₀, ∀ t ∈ Metric.ball t₀ ε, ∀ a,
      a ∈ Zf v t ↔ a ∈ Metric.ball ((0 : ℂ)) (r v) ∧ chartRead N v f a = t :=
    fun v hv t ht => (hZfP v t hv ht).1
  have hI0 : ∀ v ∈ Z₀, ∀ t ∈ Metric.ball t₀ ε,
      (∮ z in C((0 : ℂ), r v),
          (fun _ => (1 : ℂ)) z * deriv (chartRead N v f) z / (chartRead N v f z - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf v t, (analyticOrderNatAt (fun z => chartRead N v f z - t) a : ℂ) * 1 :=
    fun v hv t ht => (hZfP v t hv ht).2.1
  have hIΦ : ∀ v ∈ Z₀, ∀ t ∈ Metric.ball t₀ ε, ∀ i,
      (∮ z in C((0 : ℂ), r v),
          Φ v i z * deriv (chartRead N v f) z / (chartRead N v f z - t)) =
        2 * Real.pi * Complex.I *
          ∑ a ∈ Zf v t, (analyticOrderNatAt (fun z => chartRead N v f z - t) a : ℂ) * Φ v i a :=
    fun v hv t ht => (hZfP v t hv ht).2.2

  exact ⟨⟨⟨O, ρ, Φ, hρ, hOdisj, htar, hOf, hΦd, hAJloc, hRan, hRc, hpunct⟩,
    r, ε, Zf, hε, fun t ht => hzeros t (hε₁' t ht), hr, hcb, hbb', hsph, hΦan, hΨan, hcirc', hZf, hI0, hIΦ⟩⟩

end
end Dubon2026.SourceFunctionField.OriginalChart

import Dubon2026.SourceOriginalFiberContours
import Dubon2026.SourceOriginalChartFiberMultiplicity

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel -> reindex the weighted fiber contour by actual places.
The finite coordinate zeros are in bijection with the support of the
actual fiber divisor. Their analytic multiplicities equal its coefficients.
The producer derives these facts from the exact original chart orders,
inverse laws, disjoint chart images and the already proved nearby cover.
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

/-- The actual nearby fiber support indexed without repetition by coordinate zeros. -/
structure OriginalFiberIndexing {n : ℕ} (bb : Fin n → Ω[F⁄ℂ])
    (P₀ : Place ℂ F) (f : F) (h : Fin n → F) (t₀ : ℂ) (Z₀ : Finset (Place ℂ F))
    (Z : ℂ → Divisor ℂ F) extends OriginalFiberContours N bb P₀ f h t₀ Z₀ where
  hfibA : ∀ t ∈ Metric.ball t₀ ε, ∀ w : Place ℂ F, 0 < w.ord (f - algebraMap ℂ F t) →
      ∃ v ∈ Z₀, w ∈ (placeChart N v).source ∧
        placeChart N v w ∈ Zf v t ∧
        (w.ord (f - algebraMap ℂ F t) : ℤ) = analyticOrderNatAt (fun z => chartRead N v f z - t) (placeChart N v w)
  hfibB : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀, ∀ a ∈ Zf v t,
      placeFamily N v a ∈ (placeChart N v).source ∧ placeChart N v (placeFamily N v a) = a ∧
      a ∈ Metric.ball ((0 : ℂ)) (r v) ∧ chartRead N v f a = t ∧
      0 < (placeFamily N v a).ord (f - algebraMap ℂ F t) ∧
      ((placeFamily N v a).ord (f - algebraMap ℂ F t) : ℤ) = analyticOrderNatAt (fun z => chartRead N v f z - t) a
  hsurj : ∀ t ∈ Metric.ball t₀ ε, ∀ w ∈ (Z t).support, ∃ v ∈ Z₀, ∃ a ∈ Zf v t, placeFamily N v a = w
  hmem : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀, ∀ a ∈ Zf v t, placeFamily N v a ∈ (Z t).support
  hinj : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀, ∀ v' ∈ Z₀, ∀ a ∈ Zf v t, ∀ a' ∈ Zf v' t,
      placeFamily N v a = placeFamily N v' a' → v = v' ∧ a = a'
  hmult : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀, ∀ a ∈ Zf v t,
      (Z t) (placeFamily N v a) = (analyticOrderNatAt (fun z => chartRead N v f z - t) a : ℤ)

theorem exists_originalFiberIndexing {n : ℕ} (bb : Fin n → Ω[F⁄ℂ])
    (P₀ : Place ℂ F) (f : F) (h : Fin n → F) (t₀ : ℂ) (Z₀ : Finset (Place ℂ F))
    (Z : ℂ → Divisor ℂ F)
    (hZ : ∀ (t : ℂ) (v : Place ℂ F), Z t v = max (v.ord (f - algebraMap ℂ F t)) 0)
    (hne : ∀ t : ℂ, f - algebraMap ℂ F t ≠ 0)
    (c : OriginalFiberContours N bb P₀ f h t₀ Z₀) :
    Nonempty (OriginalFiberIndexing N bb P₀ f h t₀ Z₀ Z) := by
  classical
  obtain ⟨⟨O, ρ, Φ, hρ, hOdisj, htar, hOf, hΦd, hAJloc, hRan, hRc, hpunct⟩,
    r, ε, Zf, hε, hzeros, hr, hcb, hbb', hsph, hΦan, hΨan, hcirc', hZf, hI0, hIΦ⟩ := c
  have hsupp : ∀ (t : ℂ) (w : Place ℂ F), w ∈ (Z t).support ↔ 0 < w.ord (f - algebraMap ℂ F t) := by
    intro t w
    rw [Finsupp.mem_support_iff, hZ t w]
    omega
  set m : Place ℂ F → ℂ → ℂ → ℕ := fun v t a =>
    analyticOrderNatAt (fun z => chartRead N v f z - t) a with hmdef
  set sy : Place ℂ F → ℂ → Place ℂ F := fun v a => (placeChart N v).symm a with hsydef

  have hfibA : ∀ t ∈ Metric.ball t₀ ε, ∀ w : Place ℂ F, 0 < w.ord (f - algebraMap ℂ F t) →
      ∃ v ∈ Z₀, w ∈ (placeChart N v).source ∧
        placeChart N v w ∈ Zf v t ∧
        (w.ord (f - algebraMap ℂ F t) : ℤ) = m v t (placeChart N v w) := by
    intro t ht w hw
    obtain ⟨v, hv, a, ha, haw⟩ := hzeros t ht w hw
    have hatar : a ∈ (placeChart N v).target := htar v hv (hbb' v ha)
    have hwsrc : w ∈ (placeChart N v).source := by
      rw [← haw]
      exact (placeChart N v).map_target hatar
    have hcoord : placeChart N v w = a := by
      rw [← haw]
      exact (placeChart N v).right_inv hatar
    have hwball' : placeChart N v w ∈ Metric.ball (0 : ℂ) (r v) := by rwa [hcoord]
    have hfw : f ∈ w.toValuationSubring := by
      have := (hOf v hv _ (hbb' v hwball')).2
      rwa [(placeChart N v).left_inv hwsrc] at this
    obtain ⟨-, hord⟩ := original_chart_order_at_place N v w hwsrc hfw t (hne t)
    have hmpos : 0 < m v t (placeChart N v w) := by
      have := hw
      rw [hord] at this
      exact_mod_cast this
    have hRa : chartRead N v f (placeChart N v w) = t := by
      have := apply_eq_zero_of_analyticOrderNatAt_ne_zero hmpos.ne'
      exact sub_eq_zero.1 this
    exact ⟨v, hv, hwsrc, (hZf v hv t ht _).2 ⟨hwball', hRa⟩, hord⟩
  have hfibB : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀, ∀ a ∈ Zf v t,
      sy v a ∈ (placeChart N v).source ∧ placeChart N v (sy v a) = a ∧
      a ∈ Metric.ball ((0 : ℂ)) (r v) ∧ chartRead N v f a = t ∧
      0 < (sy v a).ord (f - algebraMap ℂ F t) ∧
      ((sy v a).ord (f - algebraMap ℂ F t) : ℤ) = m v t a := by
    intro t ht v hv a ha
    obtain ⟨haball, hRa⟩ := (hZf v hv t ht a).1 ha
    have hatar : a ∈ (placeChart N v).target := htar v hv (hbb' v haball)
    have hsrc : sy v a ∈ (placeChart N v).source := (placeChart N v).map_target hatar
    have hφa : placeChart N v (sy v a) = a := (placeChart N v).right_inv hatar
    have hfw : f ∈ (sy v a).toValuationSubring := (hOf v hv a (hbb' v haball)).2
    obtain ⟨htop, hord⟩ := original_chart_order_at_place N v (sy v a) hsrc hfw t (hne t)
    rw [hφa] at htop hord
    have hmne : m v t a ≠ 0 := by
      have han : AnalyticAt ℂ (fun z => chartRead N v f z - t) a :=
        (hRan v hv a (hbb' v haball)).sub analyticAt_const
      have hne0 : analyticOrderAt (fun z => chartRead N v f z - t) a ≠ 0 := by
        rw [ne_eq, han.analyticOrderAt_eq_zero]
        simp [hRa]
      simp only [hmdef, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero, not_or]
      exact ⟨hne0, htop⟩
    refine ⟨hsrc, hφa, haball, hRa, ?_, hord⟩
    rw [hord]
    exact_mod_cast Nat.pos_of_ne_zero hmne

  have hsurj : ∀ t ∈ Metric.ball t₀ ε, ∀ w ∈ (Z t).support, ∃ v ∈ Z₀, ∃ a ∈ Zf v t, sy v a = w := by
    intro t ht w hw
    obtain ⟨v, hv, hwsrc, ha, -⟩ := hfibA t ht w ((hsupp t w).1 hw)
    exact ⟨v, hv, _, ha, (placeChart N v).left_inv hwsrc⟩
  have hmem : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀, ∀ a ∈ Zf v t, sy v a ∈ (Z t).support := by
    intro t ht v hv a ha
    exact (hsupp t _).2 (hfibB t ht v hv a ha).2.2.2.2.1
  have hinj : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀, ∀ v' ∈ Z₀, ∀ a ∈ Zf v t, ∀ a' ∈ Zf v' t,
      sy v a = sy v' a' → v = v' ∧ a = a' := by
    intro t ht v hv v' hv' a ha a' ha' heq
    obtain ⟨-, hφa, haball, -⟩ := hfibB t ht v hv a ha
    obtain ⟨-, hφa', haball', -⟩ := hfibB t ht v' hv' a' ha'
    have hO1 : sy v a ∈ O v := (hOf v hv a (hbb' v haball)).1
    have hO2 : sy v' a' ∈ O v' := (hOf v' hv' a' (hbb' v' haball')).1
    have hvv : v = v' := by
      by_contra hne'
      have hdisj := hOdisj (Finset.mem_coe.2 hv) (Finset.mem_coe.2 hv') hne'
      rw [← heq] at hO2
      exact Set.disjoint_left.1 hdisj hO1 hO2
    subst hvv
    exact ⟨rfl, by rw [← hφa, ← hφa', heq]⟩
  have hmult : ∀ t ∈ Metric.ball t₀ ε, ∀ v ∈ Z₀, ∀ a ∈ Zf v t,
      (Z t) (sy v a) = (m v t a : ℤ) := by
    intro t ht v hv a ha
    obtain ⟨-, -, -, -, hpos, hord⟩ := hfibB t ht v hv a ha
    rw [hZ, hord, max_eq_left]
    exact_mod_cast Nat.zero_le _

  exact ⟨⟨⟨⟨O, ρ, Φ, hρ, hOdisj, htar, hOf, hΦd, hAJloc, hRan, hRc, hpunct⟩,
    r, ε, Zf, hε, hzeros, hr, hcb, hbb', hsph, hΦan, hΨan, hcirc', hZf, hI0, hIΦ⟩,
    hfibA, hfibB, hsurj, hmem, hinj, hmult⟩⟩

end
end Dubon2026.SourceFunctionField.OriginalChart

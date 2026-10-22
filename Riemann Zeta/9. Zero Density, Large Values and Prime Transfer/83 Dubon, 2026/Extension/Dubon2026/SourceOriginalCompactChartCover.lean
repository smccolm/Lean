import Dubon2026.SourceOriginalNearbyFiberCover

/-! DUB-17/18 -> original torsion cardinality -> compact original curve.
Use the actual j function and its reciprocal. Nearby-fiber exhaustion,
a finite subcover of a closed complex disk and the reciprocal chart at
infinity give finitely many compact parameter disks covering every place.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_ord_sub_eval_pos (v : Place ℂ F) {f : F}
    (hf : f ∈ v.toValuationSubring)
    (hne : f - algebraMap ℂ F (originalPlaceEval N ℂ v f) ≠ 0) :
    0 < v.ord (f - algebraMap ℂ F (originalPlaceEval N ℂ v f)) := by
  apply (originalPlaceEval_eq_zero_iff_ord_pos N ℂ v
    (sub_mem hf (v.algebraMap_mem' _)) hne).mp
  rw [originalPlaceEval_sub_algebraMap N ℂ v hf, sub_self]

theorem exists_original_compact_chart_cover :
    ∃ (S : Finset (Place ℂ F)) (r : Place ℂ F → ℝ), (∀ v ∈ S, 0 ≤ r v ∧ r v < placeRadius N v) ∧
      ∀ w : Place ℂ F, ∃ v ∈ S, ∃ z : ℂ, ‖z‖ ≤ r v ∧ placeFamily N v z = w := by
  classical
  let f : F := jOver N ℂ
  have hf : ∀ c : ℂ, f ≠ algebraMap ℂ F c := by
    intro c hc
    apply transcendental_jOver N ℂ
    change IsAlgebraic ℂ f
    rw [hc]
    exact isAlgebraic_algebraMap c
  have hf0 : f ≠ 0 := by simpa only [map_zero] using hf 0
  have hfi : ∀ c : ℂ, f⁻¹ ≠ algebraMap ℂ F c := by
    intro c hc
    apply hf c⁻¹
    rw [map_inv₀, ← hc, inv_inv]
  have hfc : ∀ c c' : ℂ, f - algebraMap ℂ F c ≠ algebraMap ℂ F c' := by
    intro c c' h
    apply hf (c' + c)
    rw [map_add, ← h, sub_add_cancel]

  have hfib : ∀ c : ℂ, ∃ ε : ℝ, 0 < ε ∧ ∃ T : Finset (Place ℂ F), ∃ δ : Place ℂ F → ℝ,
      (∀ w ∈ T, 0 < δ w ∧ δ w < placeRadius N w) ∧ (∀ w ∈ T, 0 < w.ord (f - algebraMap ℂ F c)) ∧
      ∀ a : ℂ, ‖a‖ < ε → ∀ w' : Place ℂ F,
        0 < w'.ord (f - algebraMap ℂ F c - algebraMap ℂ F a) →
        ∃ w ∈ T, ∃ u : ℂ, ‖u‖ < δ w ∧ placeFamily N w u = w' := fun c => nearby_original_fiber_cover N (hfc c)
  choose ε hε T δ hδ hT hcov using hfib
  obtain ⟨εi, hεi, Ti, δi, hδi, hTi, hcovi⟩ := nearby_original_fiber_cover N hfi

  set R : ℝ := εi⁻¹ with hR_def
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).elim_finite_subcover
    (fun c : ℂ => ball c (ε c)) (fun _ => isOpen_ball)
    (fun c _ => mem_iUnion.mpr ⟨c, mem_ball_self (hε c)⟩)

  set S : Finset (Place ℂ F) := Ti ∪ C.biUnion T with hS_def
  set A : Place ℂ F → Finset ℝ := fun w =>
    (if w ∈ Ti then {δi w} else ∅) ∪ (C.filter (fun c => w ∈ T c)).image (fun c => δ c w)
    with hA_def
  have hA : ∀ w, ∀ x ∈ A w, 0 < x ∧ x < placeRadius N w := by
    intro w x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · by_cases hw : w ∈ Ti
      · rw [if_pos hw, Finset.mem_singleton] at hx
        rw [hx]; exact hδi w hw
      · rw [if_neg hw] at hx; exact absurd hx (Finset.notMem_empty _)
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
      exact hδ c w (Finset.mem_filter.mp hc).2
  set r : Place ℂ F → ℝ := fun w => if h : (A w).Nonempty then (A w).max' h else 0 with hr_def
  have hr_le : ∀ w x, x ∈ A w → x ≤ r w := by
    intro w x hx
    have hne : (A w).Nonempty := ⟨x, hx⟩
    simp only [hr_def, dif_pos hne]
    exact Finset.le_max' _ _ hx
  have hr : ∀ v ∈ S, 0 ≤ r v ∧ r v < placeRadius N v := by
    intro v _
    by_cases h : (A v).Nonempty
    · simp only [hr_def, dif_pos h]
      have hm := hA v _ (Finset.max'_mem _ h)
      exact ⟨hm.1.le, hm.2⟩
    · simp only [hr_def, dif_neg h]
      exact ⟨le_rfl, (place_spec N v).1⟩
  have hAi : ∀ v ∈ Ti, δi v ∈ A v := by
    intro v hv
    simp only [hA_def]
    exact Finset.mem_union_left _ (by rw [if_pos hv]; exact Finset.mem_singleton_self _)
  have hAc : ∀ c ∈ C, ∀ v ∈ T c, δ c v ∈ A v := by
    intro c hc v hv
    simp only [hA_def]
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, hv⟩, rfl⟩)
  refine ⟨S, r, hr, fun w' => ?_⟩

  by_cases hfm : f ∈ w'.toValuationSubring
  ·
    set c' : ℂ := originalPlaceEval N ℂ w' f with hc'_def
    have hpos : 0 < w'.ord (f - algebraMap ℂ F c') :=
      original_ord_sub_eval_pos N w' hfm (sub_ne_zero.mpr (hf _))
    by_cases hc' : ‖c'‖ ≤ R
    ·
      have hmem : c' ∈ closedBall (0 : ℂ) R := by rwa [mem_closedBall, dist_zero_right]
      obtain ⟨c, hcC, hc⟩ := mem_iUnion₂.mp (hC hmem)
      have ha : ‖c' - c‖ < ε c := by rwa [mem_ball, dist_eq_norm] at hc
      have hpos' : 0 < w'.ord (f - algebraMap ℂ F c - algebraMap ℂ F (c' - c)) := by
        rwa [map_sub, sub_sub, add_sub_cancel]
      obtain ⟨v, hvT, u, hu, hγu⟩ := hcov c (c' - c) ha w' hpos'
      exact ⟨v, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, hcC, hvT⟩), u,
        hu.le.trans (hr_le v _ (hAc c hcC v hvT)), hγu⟩
    ·
      push Not at hc'
      have hRnn : 0 ≤ R := inv_nonneg.mpr hεi.le
      have hc'0 : c' ≠ 0 := by
        intro h; rw [h, norm_zero] at hc'; exact not_lt.mpr hRnn hc'
      have hordf : w'.ord f = 0 := by
        rcases (w'.ord_nonneg_of_mem hfm).eq_or_lt with h | h
        · exact h.symm
        · exact absurd ((originalPlaceEval_eq_zero_iff_ord_pos N ℂ w' hfm hf0).mpr h) hc'0
      have hfim : f⁻¹ ∈ w'.toValuationSubring :=
        w'.mem_of_ord_nonneg (by rw [Place.ord_inv, hordf, neg_zero])
      have hev : originalPlaceEval N ℂ w' f⁻¹ = c'⁻¹ := originalPlaceEval_inv N ℂ w' f
      have hpos'' : 0 < w'.ord (f⁻¹ - algebraMap ℂ F c'⁻¹) := by
        rw [← hev]
        exact original_ord_sub_eval_pos N w' hfim (sub_ne_zero.mpr (hfi _))
      have ha : ‖c'⁻¹‖ < εi := by
        rw [norm_inv]; exact inv_lt_of_inv_lt₀ hεi hc'
      obtain ⟨v, hvT, u, hu, hγu⟩ := hcovi c'⁻¹ ha w' hpos''
      exact ⟨v, Finset.mem_union_left _ hvT, u, hu.le.trans (hr_le v _ (hAi v hvT)), hγu⟩
  ·
    have hpos : 0 < w'.ord (f⁻¹ - algebraMap ℂ F 0) := by
      rw [map_zero, sub_zero, Place.ord_inv]
      have := lt_of_not_ge (fun h => hfm (w'.mem_of_ord_nonneg h))
      omega
    obtain ⟨v, hvT, u, hu, hγu⟩ := hcovi 0 (by rwa [norm_zero]) w' hpos
    exact ⟨v, Finset.mem_union_left _ hvT, u, hu.le.trans (hr_le v _ (hAi v hvT)), hγu⟩

end
end Dubon2026.SourceFunctionField.OriginalChart

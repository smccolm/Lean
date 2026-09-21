import TaoTrudgianYang2025.PointValueRanges

/-!
# Lebesgue measure of actual zeta superlevels

A maximal finite unit-separated family covers the entire superlevel by
closed unit balls. Its existence follows from the proved finite cardinality
bound, and the full measure costs only twice the number of points.
-/

noncomputable section

open MeasureTheory Set RiemannZeta.GuthMaynard
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem exists_unitSeparated_closedBall_cover_of_card_bound
    {S : Set ℝ} {B : ℝ}
    (hcount : ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ S) →
      IsSeparated 1 W → (W.card:ℝ) ≤ B) :
    ∃ W : Finset ℝ, (∀ t ∈ W, t ∈ S) ∧ IsSeparated 1 W ∧
      ∀ t ∈ S, ∃ u ∈ W, dist t u ≤ 1 := by
  classical
  let N : ℕ := Nat.ceil B
  let Q : Finset ℕ := (Finset.range (N+1)).filter (fun n =>
    ∃ W : Finset ℝ, (∀ t ∈ W, t ∈ S) ∧ IsSeparated 1 W ∧ W.card = n)
  have hN : B ≤ (N:ℝ) := Nat.le_ceil B
  have hmem : ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ S) →
      IsSeparated 1 W → W.card ∈ Q := by
    intro W hWS hsep
    have hcard : W.card ≤ N := by exact_mod_cast (hcount W hWS hsep).trans hN
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega),W,hWS,hsep,rfl⟩
  have hzero : 0 ∈ Q := by
    simpa using hmem ∅ (by simp) (by intro x hx; simp at hx)
  have hQ : Q.Nonempty := ⟨0,hzero⟩
  obtain ⟨W,hWS,hsep,hcard⟩ := (Finset.mem_filter.mp (Q.max'_mem hQ)).2
  refine ⟨W,hWS,hsep,?_⟩
  intro t ht
  by_contra hnot
  have hfar : ∀ u ∈ W, 1 < dist t u := by
    intro u hu
    exact lt_of_not_ge (fun h => hnot ⟨u,hu,h⟩)
  have htW : t ∉ W := by
    intro htW
    have hh := hfar t htW
    norm_num at hh
  have hWS' : ∀ u ∈ insert t W, u ∈ S := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact ht
    · exact hWS u hu
  have hsep' : IsSeparated 1 (insert t W) := by
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hxW
    · rcases Finset.mem_insert.mp hy with rfl | hyW
      · exact (hxy rfl).elim
      · exact (hfar y hyW).le
    · rcases Finset.mem_insert.mp hy with rfl | hyW
      · simpa only [dist_comm] using (hfar x hxW).le
      · exact hsep x hxW y hyW hxy
  have hmax : (insert t W).card ≤ Q.max' hQ :=
    Q.le_max' (insert t W).card (hmem (insert t W) hWS' hsep')
  rw [Finset.card_insert_of_notMem htW,← hcard] at hmax
  omega

theorem volume_le_two_mul_of_separated_card_bound
    {S : Set ℝ} {B : ℝ}
    (hcount : ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ S) →
      IsSeparated 1 W → (W.card:ℝ) ≤ B) :
    volume S ≤ ENNReal.ofReal (2*B) := by
  classical
  obtain ⟨W,hWS,hsep,hcover⟩ :=
    exists_unitSeparated_closedBall_cover_of_card_bound hcount
  have hsub : S ⊆ ⋃ u ∈ W, Metric.closedBall u 1 := by
    intro t ht
    obtain ⟨u,hu,hut⟩ := hcover t ht
    exact Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,hut⟩⟩
  calc
    volume S ≤ volume (⋃ u ∈ W, Metric.closedBall u 1) := measure_mono hsub
    _ ≤ ∑ u ∈ W, volume (Metric.closedBall u 1) := measure_biUnion_finset_le W _
    _ = (W.card:ℝ≥0∞)*2 := by simp [Real.volume_closedBall]
    _ = ENNReal.ofReal (2*(W.card:ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      simp [mul_comm]
    _ ≤ ENNReal.ofReal (2*B) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hcount W hWS hsep) (by norm_num))

def pointValueSuperlevel (H V : ℝ) : Set ℝ :=
  {t | H ≤ t ∧ t ≤ 2*H ∧ V ≤ zetaMomentCriticalNorm t}

theorem isClosed_pointValueSuperlevel (H V : ℝ) :
    IsClosed (pointValueSuperlevel H V) := by
  have hs : IsClosed (Icc H (2*H) ∩ {t | V ≤ zetaMomentCriticalNorm t}) :=
    isClosed_Icc.inter
    (isClosed_le continuous_const continuous_zetaMomentCriticalNorm)
  convert hs using 1
  ext t
  simp only [pointValueSuperlevel,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_Icc]
  tauto

theorem measurableSet_pointValueSuperlevel (H V : ℝ) :
    MeasurableSet (pointValueSuperlevel H V) :=
  (isClosed_pointValueSuperlevel H V).measurableSet

theorem exists_volume_pointValueSuperlevel_le {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H V : ℝ,
      H₀ ≤ H → 0 < V → H^(1/8+ε) ≤ V →
      volume (pointValueSuperlevel H V) ≤ ENNReal.ofReal (2*H^(2+ε)/V^12) := by
  obtain ⟨H₀,hH₀,hcount⟩ := exists_pointValue_twelfth_weighted_card_le hε
  refine ⟨H₀,hH₀,?_⟩
  intro H V hH hV hLower
  have hc : ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ pointValueSuperlevel H V) →
      IsSeparated 1 W → (W.card:ℝ) ≤ H^(2+ε)/V^12 := by
    intro W hWS hsep
    apply (le_div_iff₀ (by positivity)).mpr
    exact hcount H V W hH hV hLower hsep
      (fun t ht => ⟨(hWS t ht).1,(hWS t ht).2.1⟩)
      (fun t ht => (hWS t ht).2.2)
  have hm := volume_le_two_mul_of_separated_card_bound hc
  convert hm using 1
  congr 1
  ring

end TaoTrudgianYang2025

import Dubon2026.SourceOriginalFiberDegreeConservation
import Dubon2026.SourceOriginalChartFiberData
import Dubon2026.SourceAnalyticFiberPreimages

/-! DUB-17/18 -> original torsion cardinality -> compact original curve.
Analytic multiplicity produces nearby preimages in finitely many disjoint
original charts. Their total number exhausts the proved positive divisor
degree, excluding any further nearby places. All chart, residue and degree
inputs are derived for the actual original field.
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

omit [NeZero N] in
private theorem exists_pos_forall_le {ι : Type*} (s : Finset ι) (p : ι → ℝ) (hp : ∀ i ∈ s, 0 < p i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ p i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨δ, hδ, hδs⟩ := ih fun i hi => hp i (Finset.mem_insert_of_mem hi)
    refine ⟨min δ (p a), lt_min hδ (hp a (Finset.mem_insert_self a s)), fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hδs i hi)

theorem nearby_original_fiber_cover {g : F} (hg : ∀ c : ℂ, g ≠ algebraMap ℂ F c) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ T : Finset (Place ℂ F), ∃ δ : Place ℂ F → ℝ,
      (∀ w ∈ T, 0 < δ w ∧ δ w < placeRadius N w) ∧ (∀ w ∈ T, 0 < w.ord g) ∧
      ∀ a : ℂ, ‖a‖ < ε → ∀ w' : Place ℂ F, 0 < w'.ord (g - algebraMap ℂ F a) →
        ∃ w ∈ T, ∃ u : ℂ, ‖u‖ < δ w ∧ placeFamily N w u = w' := by
  classical
  have hg0 : g ≠ 0 := by simpa using hg 0
  have hga : ∀ a : ℂ, g - algebraMap ℂ F a ≠ 0 := fun a h => hg a (sub_eq_zero.mp h)

  let D := fun a : ℂ => originalPrincipalDivisor N ℂ (g - algebraMap ℂ F a)
  have hD : ∀ a w, D a w = w.ord (g - algebraMap ℂ F a) := fun _ _ => rfl
  let Z := originalPositiveFiber N g
  have memZ : ∀ a w, w ∈ Z a ↔ 0 < w.ord (g - algebraMap ℂ F a) :=
    mem_originalPositiveFiber N g
  have posZ : ∀ a, ∀ w ∈ Z a, 0 < D a w := fun a w hw => (memZ a w).mp hw
  have sumZ : ∀ a, (∑ w ∈ Z a, D a w) = ∑ w ∈ Z 0, D 0 w := by
    intro a
    simpa only [hD, map_zero, sub_zero] using original_fiber_total_order_constant N g a

  set T : Finset (Place ℂ F) := Z 0 with hT_def
  have hT : ∀ w ∈ T, 0 < w.ord g := by
    intro w hw
    have := (memZ 0 w).mp hw
    simpa using this
  have hTmem : ∀ w ∈ T, g ∈ w.toValuationSubring := fun w hw =>
    w.mem_of_ord_nonneg (hT w hw).le

  have hsep : ∀ w w' : Place ℂ F, w ≠ w' → ∃ δ : ℝ, 0 < δ ∧ ∃ δ' : ℝ, 0 < δ' ∧
      ∀ u u' : ℂ, ‖u‖ < δ → ‖u'‖ < δ' → placeFamily N w u ≠ placeFamily N w' u' := fun w w' h => place_families_separated N h
  choose! Δ hΔ Δ' hΔ' hsepΔ using hsep
  have hδ₁ : ∀ w : Place ℂ F, ∃ δ₁ : ℝ, 0 < δ₁ ∧
      ∀ w' ∈ T, w' ≠ w → δ₁ ≤ Δ w w' ∧ δ₁ ≤ Δ' w' w := by
    intro w
    obtain ⟨δ₁, h1, h2⟩ := exists_pos_forall_le (T.erase w) (fun w' => min (Δ w w') (Δ' w' w))
      (fun w' hw' => lt_min (hΔ w w' (Finset.ne_of_mem_erase hw').symm)
        (hΔ' w' w (Finset.ne_of_mem_erase hw')))
    refine ⟨δ₁, h1, fun w' hw' hne => ?_⟩
    have := h2 w' (Finset.mem_erase.mpr ⟨hne, hw'⟩)
    exact ⟨this.trans (min_le_left _ _), this.trans (min_le_right _ _)⟩
  choose δ₁ hδ₁pos hδ₁le using hδ₁

  have hδ₂ : ∀ w : Place ℂ F, ∃ δ₂ : ℝ, 0 < δ₂ ∧
      (g ∈ w.toValuationSubring → ∀ u : ℂ, ‖u‖ < δ₂ → g ∈ (placeFamily N w u).toValuationSubring) := by
    intro w
    by_cases hw : g ∈ w.toValuationSubring
    · obtain ⟨δ₂, h1, h2⟩ := exists_place_reading_regular_disk N w hw
      exact ⟨δ₂, h1, fun _ => h2⟩
    · exact ⟨1, one_pos, fun h => absurd h hw⟩
  choose δ₂ hδ₂pos hδ₂mem using hδ₂

  set δ : Place ℂ F → ℝ := fun w => min (min (δ₁ w) (δ₂ w)) (placeRadius N w / 2) with hδ_def
  have hδpos : ∀ w, 0 < δ w := fun w =>
    lt_min (lt_min (hδ₁pos w) (hδ₂pos w)) (half_pos ((place_spec N w).1))
  have hδρ : ∀ w, δ w < placeRadius N w := fun w =>
    (min_le_right _ _).trans_lt (half_lt_self ((place_spec N w).1))
  have hδle₁ : ∀ w, δ w ≤ δ₁ w := fun w => (min_le_left _ _).trans (min_le_left _ _)
  have hδle₂ : ∀ w, δ w ≤ δ₂ w := fun w => (min_le_left _ _).trans (min_le_right _ _)

  have hη : ∀ w : Place ℂ F, ∃ η : ℝ, 0 < η ∧ (w ∈ T → ∀ a : ℂ, a ≠ 0 → ‖a‖ < η →
      ∃ U : Finset ℂ, (D 0 w).toNat ≤ U.card ∧
        ∀ u ∈ U, ‖u‖ < δ w ∧ originalPlaceEval N ℂ (placeFamily N w u) g = a) := by
    intro w
    by_cases hw : w ∈ T
    · have hpos : 0 < D 0 w := posZ 0 w hw
      have he : 0 < (D 0 w).toNat := by omega
      have han : AnalyticAt ℂ (fun u : ℂ => originalPlaceEval N ℂ (placeFamily N w u) g) 0 :=
        analyticAt_place_reading N w (hTmem w hw)
      have horder : meromorphicOrderAt (fun u : ℂ => originalPlaceEval N ℂ (placeFamily N w u) g) 0
          = (((D 0 w).toNat : ℕ) : ℤ) := by
        rw [meromorphicOrderAt_place_reading N w hg0, Int.toNat_of_nonneg hpos.le, hD 0 w, map_zero,
          sub_zero]
      obtain ⟨η, hη, H⟩ :=
        AnalyticFiber.exists_finset_preimages_of_meromorphicOrderAt_eq han he horder (hδpos w)
      exact ⟨η, hη, fun _ => H⟩
    · exact ⟨1, one_pos, fun h => absurd h hw⟩
  choose η hηpos hηU using hη
  obtain ⟨ε, hε, hεle⟩ := exists_pos_forall_le T η (fun w _ => hηpos w)
  refine ⟨ε, hε, T, δ, fun w _ => ⟨hδpos w, hδρ w⟩, hT, fun a ha w' hw' => ?_⟩

  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨w', (memZ 0 w').mpr hw', 0, by simpa using hδpos w', (place_spec N w').2.1⟩

  have hU : ∀ w ∈ T, ∃ U : Finset ℂ, (D 0 w).toNat ≤ U.card ∧
      ∀ u ∈ U, ‖u‖ < δ w ∧ originalPlaceEval N ℂ (placeFamily N w u) g = a :=
    fun w hw => hηU w hw a ha0 (ha.trans_le (hεle w hw))
  choose! U hUcard hUmem using hU
  set Q : Finset (Σ _ : Place ℂ F, ℂ) := T.sigma fun w => U w with hQ_def
  set ι : (Σ _ : Place ℂ F, ℂ) → Place ℂ F := fun q => placeFamily N q.1 q.2 with hι_def

  have hιZ : ∀ q ∈ Q, ι q ∈ Z a := by
    rintro ⟨w, u⟩ hq
    obtain ⟨hw, hu⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hu1, hu2⟩ := hUmem w hw u hu
    rw [memZ]
    have hgm : g ∈ (placeFamily N w u).toValuationSubring :=
      hδ₂mem w (hTmem w hw) u (hu1.trans_le (hδle₂ w))
    apply (originalPlaceEval_eq_zero_iff_ord_pos N ℂ (placeFamily N w u)
      (sub_mem hgm ((placeFamily N w u).algebraMap_mem' a)) (hga a)).mp
    rw [originalPlaceEval_sub_algebraMap N ℂ (placeFamily N w u) hgm, hu2, sub_self]
  have hιZ' : ∀ p ∈ Q.image ι, p ∈ Z a := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hιZ q hq

  have hinj : Set.InjOn ι (Q : Set (Σ _ : Place ℂ F, ℂ)) := by
    rintro ⟨w, u⟩ hq ⟨w', u'⟩ hq' heq
    rw [Finset.mem_coe] at hq hq'
    obtain ⟨hw, hu⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hw', hu'⟩ := Finset.mem_sigma.mp hq'
    obtain ⟨hu1, -⟩ := hUmem w hw u hu
    obtain ⟨hu1', -⟩ := hUmem w' hw' u' hu'
    change placeFamily N w u = placeFamily N w' u' at heq
    by_cases hww : w = w'
    · subst hww
      have huu : u = u' := placeFamily_injOn N w
        (by rw [mem_ball, dist_zero_right]; exact hu1.trans (hδρ w))
        (by rw [mem_ball, dist_zero_right]; exact hu1'.trans (hδρ w)) heq
      subst huu
      rfl
    · exfalso
      have h1 := (hδ₁le w w' hw' (Ne.symm hww)).1
      have h2 := (hδ₁le w' w hw hww).2
      exact hsepΔ w w' hww u u' (hu1.trans_le ((hδle₁ w).trans h1))
        (hu1'.trans_le ((hδle₁ w').trans h2)) heq

  have hcard : ((Q.image ι).card : ℤ) = ∑ w ∈ T, ((U w).card : ℤ) := by
    rw [Finset.card_image_of_injOn hinj, hQ_def, Finset.card_sigma]
    push_cast
    rfl
  have hn_le : ∑ w ∈ T, D 0 w ≤ ((Q.image ι).card : ℤ) := by
    rw [hcard]
    refine Finset.sum_le_sum fun w hw => ?_
    calc D 0 w = (((D 0 w).toNat : ℕ) : ℤ) := (Int.toNat_of_nonneg (posZ 0 w hw).le).symm
      _ ≤ ((U w).card : ℤ) := by exact_mod_cast hUcard w hw
  by_contra hnot
  push Not at hnot
  have hw'not : w' ∉ Q.image ι := by
    intro h
    obtain ⟨⟨w, u⟩, hq, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hw, hu⟩ := Finset.mem_sigma.mp hq
    exact hnot w hw u (hUmem w hw u hu).1 heq
  have hw'Z : w' ∈ Z a := (memZ a w').mpr hw'
  have hsub : Q.image ι ⊆ (Z a).erase w' := fun p hp =>
    Finset.mem_erase.mpr ⟨fun h => hw'not (h ▸ hp), hιZ' p hp⟩
  have h1 : ∑ p ∈ Q.image ι, D a p ≤ ∑ p ∈ (Z a).erase w', D a p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun p hp _ => (posZ a p (Finset.mem_of_mem_erase hp)).le)
  have h2 : ∑ p ∈ (Z a).erase w', D a p < ∑ p ∈ Z a, D a p := by
    rw [← Finset.add_sum_erase _ _ hw'Z]
    linarith [posZ a w' hw'Z]
  have h3 : ((Q.image ι).card : ℤ) ≤ ∑ p ∈ Q.image ι, D a p := by
    have := Finset.card_nsmul_le_sum (Q.image ι) (fun p => D a p) 1
      (fun p hp => Int.add_one_le_of_lt (posZ a p (hιZ' p hp)))
    simpa using this
  have h4 : ∑ p ∈ Z a, D a p = ∑ w ∈ T, D 0 w := sumZ a
  linarith

end
end Dubon2026.SourceFunctionField.OriginalChart

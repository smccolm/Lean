import Dubon2026.InterpolationDerivative
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Finite interval covers from derivative lower bounds -/

namespace Dubon2026

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

theorem exists_small_finite_cover_of_separated_card_le (S : Set ℝ) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ)
    (hcard : ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ S →
      (∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) → s.card ≤ n) :
    ∃ s : Finset ℝ, (↑s : Set ℝ) ⊆ S ∧ s.card ≤ n ∧
      ∀ y ∈ S, ∃ x ∈ s, |y - x| < δ := by
  classical
  let A : Set ℕ := {k | ∃ s : Finset ℝ, (↑s : Set ℝ) ⊆ S ∧
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) ∧ s.card = k}
  have hA : A.Finite := (Set.finite_Iic n).subset (by
    rintro k ⟨s, hs, hsep, rfl⟩
    exact hcard s hs hsep)
  have hne : A.Nonempty := ⟨0, ∅, by simp⟩
  obtain ⟨k, hk, hmax⟩ := Set.exists_max_image A (fun k => k) hA hne
  obtain ⟨s, hs, hsep, hsk⟩ := hk
  refine ⟨s, hs, hcard s hs hsep, ?_⟩
  intro y hy
  by_contra hcover
  push Not at hcover
  have hys : y ∉ s := by
    intro h
    have hb := hcover y h
    simp only [sub_self, abs_zero] at hb
    linarith
  have hsub : (↑(insert y s) : Set ℝ) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hy
    · exact hs hx
  have hsep' : ∀ x ∈ insert y s, ∀ z ∈ insert y s, x ≠ z → δ ≤ |x - z| := by
    intro x hx z hz hxz
    rcases Finset.mem_insert.mp hx with rfl | hxs
    · rcases Finset.mem_insert.mp hz with rfl | hzs
      · exact (hxz rfl).elim
      · exact hcover z hzs
    · rcases Finset.mem_insert.mp hz with rfl | hzs
      · simpa only [abs_sub_comm] using hcover x hxs
      · exact hsep x hxs z hzs hxz
  have hb := hmax (insert y s).card ⟨insert y s, hsub, hsep', rfl⟩
  rw [Finset.card_insert_of_notMem hys, hsk] at hb
  exact (Nat.not_succ_le_self k) hb

theorem derivative_sublevel_separated_card_le (n : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) {a b δ ε L : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hsmall : (n.factorial : ℝ) * (n + 1) * ε < L * δ ^ n)
    (hlower : ∀ t ∈ Icc a b, L ≤ |iteratedDeriv n f t|)
    (s : Finset ℝ) (hs : (↑s : Set ℝ) ⊆ {t ∈ Icc a b | |f t| ≤ ε})
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ |x - y|) : s.card ≤ n := by
  classical
  by_contra hcard
  have hn : n + 1 ≤ s.card := by omega
  obtain ⟨u, hus, huc⟩ := Finset.exists_subset_card_eq hn
  let x := u.orderEmbOfFin huc
  have hxmem (i : Fin (n + 1)) : x i ∈ s := hus (u.orderEmbOfFin_mem huc i)
  have hbound := derivative_sublevel_spacing_constraint n f hf x x.strictMono hδ hε
    (fun i j hij => hsep _ (hxmem i) _ (hxmem j) (x.injective.ne hij))
    (fun i => (hs (hxmem i)).2) (fun t ht => hlower t
      ⟨(hs (hxmem 0)).1.1.trans ht.1, ht.2.trans (hs (hxmem (Fin.last n))).1.2⟩)
  exact (not_lt_of_ge hbound) hsmall

theorem derivative_sublevel_finite_cover (n : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) {a b δ ε L : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hsmall : (n.factorial : ℝ) * (n + 1) * ε < L * δ ^ n)
    (hlower : ∀ t ∈ Icc a b, L ≤ |iteratedDeriv n f t|) :
    ∃ s : Finset ℝ, (↑s : Set ℝ) ⊆ {t ∈ Icc a b | |f t| ≤ ε} ∧ s.card ≤ n ∧
      ∀ y ∈ Icc a b, |f y| ≤ ε → ∃ x ∈ s, |y - x| < δ := by
  obtain ⟨s, hs, hc, hcover⟩ := exists_small_finite_cover_of_separated_card_le
    {t ∈ Icc a b | |f t| ≤ ε} n hδ
    (derivative_sublevel_separated_card_le n f hf hδ hε hsmall hlower)
  exact ⟨s, hs, hc, fun y hy hf => hcover y ⟨hy, hf⟩⟩


theorem volume_sublevel_le_of_derivative (n : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ ∞ f) {a b δ ε L : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hsmall : (n.factorial : ℝ) * (n + 1) * ε < L * δ ^ n)
    (hlower : ∀ t ∈ Icc a b, L ≤ |iteratedDeriv n f t|) :
    volume {t ∈ Icc a b | |f t| ≤ ε} ≤ ENNReal.ofReal (2 * n * δ) := by
  classical
  obtain ⟨s, _, hc, hcover⟩ := derivative_sublevel_finite_cover n f hf hδ hε hsmall hlower
  have hsub : {t ∈ Icc a b | |f t| ≤ ε} ⊆ ⋃ x ∈ s, Ioo (x - δ) (x + δ) := by
    rintro y ⟨hy, hf⟩
    obtain ⟨x, hx, hdist⟩ := hcover y hy hf
    refine Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, ?_⟩⟩
    have hh := abs_lt.mp hdist
    constructor <;> linarith
  have hvol (x : ℝ) : volume (Ioo (x - δ) (x + δ)) = ENNReal.ofReal (2 * δ) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  calc
    _ ≤ volume (⋃ x ∈ s, Ioo (x - δ) (x + δ)) := measure_mono hsub
    _ ≤ ∑ x ∈ s, volume (Ioo (x - δ) (x + δ)) := measure_biUnion_finset_le s _
    _ = (s.card : ℝ≥0∞) * ENNReal.ofReal (2 * δ) := by simp only [hvol, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ≥0∞) * ENNReal.ofReal (2 * δ) := mul_le_mul_left (by exact_mod_cast hc) _
    _ = ENNReal.ofReal (2 * n * δ) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      congr 1
      ring

end Dubon2026

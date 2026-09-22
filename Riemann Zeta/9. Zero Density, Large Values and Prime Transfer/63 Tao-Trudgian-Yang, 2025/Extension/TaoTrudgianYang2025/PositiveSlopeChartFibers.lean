import TaoTrudgianYang2025.PositiveSlopeCharts

/-!
# Contiguous integer fibers of the positive-slope grid

Fibers are taken from the literal integer interval. Monotonicity proves
that every nonempty fiber is an interval, not an arbitrary subsequence.
Positive-frequency fibers are reindexed by consecutive natural numbers.
-/

noncomputable section

open Set Expdb
open scoped BigOperators

namespace TaoTrudgianYang2025

def positiveSlopeChartFiber (s : Finset ℤ) (d N T : ℝ) (j : ℕ) : Finset ℤ := by
  classical
  exact s.filter (fun q => positiveSlopeChartIndex d ((q : ℝ)*N/T) = j)

theorem mem_positiveSlopeChartFiber {s : Finset ℤ} {d N T : ℝ} {j : ℕ} {q : ℤ} :
    q ∈ positiveSlopeChartFiber s d N T j ↔
      q ∈ s ∧ positiveSlopeChartIndex d ((q : ℝ)*N/T) = j := by
  classical
  simp only [positiveSlopeChartFiber,Finset.mem_filter]

theorem positiveSlopeChart_frequency_mono {d N T : ℝ}
    (hd : 0 < d) (hN : 0 < N) (hT : 0 < T) :
    Monotone (fun q : ℤ => positiveSlopeChartIndex d ((q : ℝ)*N/T)) := by
  intro q r hqr
  apply positiveSlopeChartIndex_mono hd
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hqr) hN.le) hT.le

theorem sum_positiveSlopeChartFibers {s : Finset ℤ} {d N T : ℝ}
    (hd : 0 < d)
    (hwindow : ∀ q ∈ s, (q : ℝ)*N/T ∈ Icc (4*d) 2)
    (f : ℤ → ℂ) :
    ∑ j ∈ positiveSlopeChartIndices d, ∑ q ∈ positiveSlopeChartFiber s d N T j, f q =
      ∑ q ∈ s, f q := by
  classical
  exact Finset.sum_fiberwise_of_maps_to
    (fun q hq => positiveSlopeChartIndex_mem hd (hwindow q hq)) f

theorem positiveSlopeChartFiber_Ioo_eq_Icc {x y : ℤ} {d N T : ℝ} {j : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hT : 0 < T)
    (hne : (positiveSlopeChartFiber (Finset.Ioo x y) d N T j).Nonempty) :
    positiveSlopeChartFiber (Finset.Ioo x y) d N T j =
      Finset.Icc ((positiveSlopeChartFiber (Finset.Ioo x y) d N T j).min' hne)
        ((positiveSlopeChartFiber (Finset.Ioo x y) d N T j).max' hne) := by
  classical
  let s := positiveSlopeChartFiber (Finset.Ioo x y) d N T j
  have hlo := mem_positiveSlopeChartFiber.mp (Finset.min'_mem s hne)
  have hhi := mem_positiveSlopeChartFiber.mp (Finset.max'_mem s hne)
  have hmono := positiveSlopeChart_frequency_mono hd hN hT
  ext q
  rw [Finset.mem_Icc]
  constructor
  · intro hq
    exact ⟨Finset.min'_le s q hq,Finset.le_max' s q hq⟩
  · rintro ⟨hql,hqr⟩
    apply mem_positiveSlopeChartFiber.mpr
    refine ⟨Finset.mem_Ioo.mpr ⟨(Finset.mem_Ioo.mp hlo.1).1.trans_le hql,
      hqr.trans_lt (Finset.mem_Ioo.mp hhi.1).2⟩,?_⟩
    exact le_antisymm ((hmono hqr).trans_eq hhi.2)
      (hlo.2.symm.trans_le (hmono hql))

theorem int_Icc_eq_image_nat_Icc {x y : ℤ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    Finset.Icc x y = (Finset.Icc x.toNat y.toNat).image (fun n : ℕ => (n : ℤ)) := by
  classical
  ext q
  simp only [Finset.mem_Icc,Finset.mem_image]
  constructor
  · rintro ⟨hqlo,hqhi⟩
    refine ⟨q.toNat,⟨?_,?_⟩,?_⟩ <;> omega
  · rintro ⟨n,⟨hnlo,hnhi⟩,rfl⟩
    constructor <;> omega

theorem positiveSlopeChartFiber_Ioo_natural_interval {x y : ℤ} {d N T : ℝ} {j : ℕ}
    (hd : 0 < d) (hN : 0 < N) (hT : 0 < T)
    (hne : (positiveSlopeChartFiber (Finset.Ioo x y) d N T j).Nonempty)
    (hnonneg : ∀ q ∈ positiveSlopeChartFiber (Finset.Ioo x y) d N T j, 0 ≤ q) :
    ∃ a L : ℕ, positiveSlopeChartFiber (Finset.Ioo x y) d N T j =
      (Finset.Icc a (a+L)).image (fun n : ℕ => (n : ℤ)) := by
  classical
  let s := positiveSlopeChartFiber (Finset.Ioo x y) d N T j
  let lo := s.min' hne
  let hi := s.max' hne
  have hlo : 0 ≤ lo := hnonneg _ (Finset.min'_mem s hne)
  have horder : lo ≤ hi := Finset.min'_le_max' s hne
  refine ⟨lo.toNat,hi.toNat-lo.toNat,?_⟩
  rw [show lo.toNat+(hi.toNat-lo.toNat) = hi.toNat by omega]
  exact (positiveSlopeChartFiber_Ioo_eq_Icc hd hN hT hne).trans
    (int_Icc_eq_image_nat_Icc hlo horder)

end TaoTrudgianYang2025

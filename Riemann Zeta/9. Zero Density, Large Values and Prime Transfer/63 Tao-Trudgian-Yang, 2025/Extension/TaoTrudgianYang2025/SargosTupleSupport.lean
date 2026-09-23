import TaoTrudgianYang2025.SargosSextuplePhase

/-! Actual maximum-offset support and the unit-character tuple product. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosTupleRadius {H : ℕ} (t : SargosInitialMomentTuple H 3) : ℤ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => (t i:ℤ))

theorem sargos_tuple_coordinate_le_radius {H : ℕ}
    (t : SargosInitialMomentTuple H 3) (i : Fin 3) :
    (t i:ℤ) ≤ sargosTupleRadius t :=
  Finset.le_sup' (fun i => (t i:ℤ)) (Finset.mem_univ i)

theorem sargosTupleRadius_bounds {H : ℕ} (t : SargosInitialMomentTuple H 3) :
    1 ≤ sargosTupleRadius t ∧ sargosTupleRadius t ≤ H := by
  constructor
  · have hn := Finset.mem_Ioc.mp (t (0 : Fin 3)).property
    have hm := sargos_tuple_coordinate_le_radius t 0
    omega
  · apply Finset.sup'_le
    intro i hi
    exact (Finset.mem_Ioc.mp (t i).property).2

theorem sargos_tuple_interval_iff {H : ℕ}
    (t : SargosInitialMomentTuple H 3) (M : ℕ) (m : ℤ) :
    m ∈ Finset.Icc (sargosTupleRadius t+1) ((M:ℤ)-sargosTupleRadius t) ↔
      ∀ i, m ∈ Finset.Icc ((t i:ℤ)+1) ((M:ℤ)-(t i:ℤ)) := by
  constructor
  · intro hm i
    have hx := Finset.mem_Icc.mp hm
    have hn := sargos_tuple_coordinate_le_radius t i
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  · intro hm
    have hleft : sargosTupleRadius t ≤ m-1 := by
      apply Finset.sup'_le
      intro i hi
      have hx := (Finset.mem_Icc.mp (hm i)).1
      omega
    have hright : sargosTupleRadius t ≤ (M:ℤ)-m := by
      apply Finset.sup'_le
      intro i hi
      have hx := (Finset.mem_Icc.mp (hm i)).2
      omega
    apply Finset.mem_Icc.mpr
    constructor <;> omega

theorem sargosSourceSymmetricTriple_support {H : ℕ} (a : ℤ → ℂ)
    (M : ℕ) (m : ℤ) (t : SargosInitialMomentTuple H 3) :
    sargosSourceSymmetricTriple a M H m t =
      if m ∈ Finset.Icc (sargosTupleRadius t+1) ((M:ℤ)-sargosTupleRadius t)
      then ∏ i, a (m+(t i:ℤ))*a (m-(t i:ℤ)) else 0 := by
  classical
  by_cases hm : m ∈ Finset.Icc (sargosTupleRadius t+1) ((M:ℤ)-sargosTupleRadius t)
  · rw [if_pos hm]
    apply Finset.prod_congr rfl
    intro i hi
    have hn := Finset.mem_Ioc.mp (t i).property
    rw [sargosSourceSequence_symmetric_support a M m (t i) (by omega),
      if_pos ((sargos_tuple_interval_iff t M m).mp hm i)]
  · rw [if_neg hm]
    have hnot : ¬∀ i, m ∈ Finset.Icc ((t i:ℤ)+1) ((M:ℤ)-(t i:ℤ)) :=
      fun h => hm ((sargos_tuple_interval_iff t M m).mpr h)
    push Not at hnot
    obtain ⟨i,hi⟩ := hnot
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hn := Finset.mem_Ioc.mp (t i).property
    rw [sargosSourceSequence_symmetric_support a M m (t i) (by omega),if_neg hi]

theorem sargosSourceSymmetricTriple_character {H : ℕ} (f : ℝ → ℝ)
    (M : ℕ) (m : ℤ) (t : SargosInitialMomentTuple H 3) :
    sargosSourceSymmetricTriple (fun n => fordAdditiveCharacter (f n)) M H m t =
      if m ∈ Finset.Icc (sargosTupleRadius t+1) ((M:ℤ)-sargosTupleRadius t)
      then fordAdditiveCharacter (sargosSymmetricTuplePhase f t m) else 0 := by
  rw [sargosSourceSymmetricTriple_support]
  split_ifs
  · have he (i : Fin 3) :
        fordAdditiveCharacter (f ((m+(t i:ℤ):ℤ):ℝ))*
          fordAdditiveCharacter (f ((m-(t i:ℤ):ℤ):ℝ)) =
        fordAdditiveCharacter (f ((m:ℝ)+((t i:ℤ):ℝ))+f ((m:ℝ)-((t i:ℤ):ℝ))) := by
      rw [Int.cast_add,Int.cast_sub,← fordAdditiveCharacter_add]
    simp_rw [he]
    exact sargos_character_finset_prod Finset.univ _
  · rfl

end TaoTrudgianYang2025

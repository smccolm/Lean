import TaoTrudgianYang2025.SargosSymmetricTaylorJets
import TaoTrudgianYang2025.SargosSourceDifferencing

/-! Actual triple and sextuple Taylor remainders and their original-phase jet bounds. -/

noncomputable section

open Set
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

def sargosTupleRemainder {H : ℕ} (f : ℝ → ℝ)
    (t : SargosInitialMomentTuple H 3) (m : ℝ) : ℝ :=
  ∑ i, sargosSymmetricRemainder f (t i:ℤ) m

def sargosSextupleRemainder {H : ℕ} (f : ℝ → ℝ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (m : ℝ) : ℝ :=
  sargosTupleRemainder f q.1 m-sargosTupleRemainder f q.2 m

theorem sargos_tuple_coordinate_bounds {H : ℕ}
    (t : SargosInitialMomentTuple H 3) (i : Fin 3) :
    0 < ((t i:ℤ):ℝ) ∧ ((t i:ℤ):ℝ) ≤ (H:ℝ) := by
  exact_mod_cast Finset.mem_Ioc.mp (t i).property

theorem sargos_tuple_segment_subset {H : ℕ}
    (t : SargosInitialMomentTuple H 3) (i : Fin 3) (m : ℝ) :
    Icc (m-((t i:ℤ):ℝ)) (m+((t i:ℤ):ℝ)) ⊆ Icc (m-(H:ℝ)) (m+(H:ℝ)) := by
  have hn := (sargos_tuple_coordinate_bounds t i).2
  intro x hx
  constructor <;> linarith [hx.1,hx.2]

theorem sargosTupleRemainder_contDiffAt {H : ℕ} {f : ℝ → ℝ} {m : ℝ}
    (hf : ∀ x ∈ Icc (m-(H:ℝ)) (m+(H:ℝ)), ContDiffAt ℝ ∞ f x)
    (t : SargosInitialMomentTuple H 3) :
    ContDiffAt ℝ ∞ (sargosTupleRemainder f t) m := by
  apply ContDiffAt.sum
  intro i hi
  have hn := sargos_tuple_coordinate_bounds t i
  apply sargosSymmetricRemainder_contDiffAt
  · apply hf
    constructor <;> linarith [hn.1,hn.2]
  · apply hf
    constructor <;> linarith [hn.1,hn.2]
  · apply hf
    constructor <;> linarith [show (0:ℝ) ≤ H from Nat.cast_nonneg H]

theorem iteratedDeriv_sargosTupleRemainder {H : ℕ} {f : ℝ → ℝ} {m : ℝ}
    (hf : ∀ x ∈ Icc (m-(H:ℝ)) (m+(H:ℝ)), ContDiffAt ℝ ∞ f x)
    (t : SargosInitialMomentTuple H 3) (j : ℕ) :
    iteratedDeriv j (sargosTupleRemainder f t) m =
      sargosTupleRemainder (iteratedDeriv j f) t m := by
  have hpoint (i : Fin 3) :
      ContDiffAt ℝ ∞ f (m+((t i:ℤ):ℝ)) ∧
      ContDiffAt ℝ ∞ f (m-((t i:ℤ):ℝ)) ∧ ContDiffAt ℝ ∞ f m := by
    have hn := sargos_tuple_coordinate_bounds t i
    refine ⟨hf _ ⟨by linarith [hn.1,hn.2],by linarith [hn.2]⟩,
      hf _ ⟨by linarith [hn.2],by linarith [hn.1,hn.2]⟩,
      hf _ ⟨by linarith [show (0:ℝ) ≤ H from Nat.cast_nonneg H],
        by linarith [show (0:ℝ) ≤ H from Nat.cast_nonneg H]⟩⟩
  have hj : (j : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  unfold sargosTupleRemainder
  rw [iteratedDeriv_fun_sum (fun i _hi =>
    (sargosSymmetricRemainder_contDiffAt (hpoint i).1 (hpoint i).2.1 (hpoint i).2.2).of_le hj)]
  apply Finset.sum_congr rfl
  intro i hi
  exact iteratedDeriv_sargosSymmetricRemainder (hpoint i).1 (hpoint i).2.1 (hpoint i).2.2 j

theorem abs_sargosTupleRemainder_le {H : ℕ} {f : ℝ → ℝ} {m B : ℝ}
    (hf : ∀ x ∈ Icc (m-(H:ℝ)) (m+(H:ℝ)), ContDiffAt ℝ ∞ f x)
    (hB : ∀ x ∈ Icc (m-(H:ℝ)) (m+(H:ℝ)), |iteratedDeriv 6 f x| ≤ B)
    (t : SargosInitialMomentTuple H 3) :
    |sargosTupleRemainder f t m| ≤ B*(H:ℝ)^6/120 := by
  have hc : m ∈ Icc (m-(H:ℝ)) (m+(H:ℝ)) := by
    constructor <;> linarith [show (0:ℝ) ≤ H from Nat.cast_nonneg H]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB m hc)
  have hb (i : Fin 3) :
      |sargosSymmetricRemainder f ((t i:ℤ):ℝ) m| ≤ B*(H:ℝ)^6/360 := by
    have hn := sargos_tuple_coordinate_bounds t i
    have hi := sargos_tuple_segment_subset t i m
    exact (abs_sargosSymmetricRemainder_le hn.1.le
      (fun x hx => hf x (hi hx)) (fun x hx => hB x (hi hx))).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn.1.le hn.2 6) hB0) (by norm_num))
  calc
    _ ≤ ∑ i : Fin 3, |sargosSymmetricRemainder f ((t i:ℤ):ℝ) m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, B*(H:ℝ)^6/360 := Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by simp; ring

theorem iteratedDeriv_sargosSextupleRemainder {H : ℕ} {f : ℝ → ℝ} {m : ℝ}
    (hf : ∀ x ∈ Icc (m-(H:ℝ)) (m+(H:ℝ)), ContDiffAt ℝ ∞ f x)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (j : ℕ) :
    iteratedDeriv j (sargosSextupleRemainder f q) m =
      sargosSextupleRemainder (iteratedDeriv j f) q m := by
  have hj : (j : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl j
  unfold sargosSextupleRemainder
  rw [iteratedDeriv_fun_sub ((sargosTupleRemainder_contDiffAt hf q.1).of_le hj)
    ((sargosTupleRemainder_contDiffAt hf q.2).of_le hj),
    iteratedDeriv_sargosTupleRemainder hf,iteratedDeriv_sargosTupleRemainder hf]

theorem abs_iteratedDeriv_sargosSextupleRemainder_le {H : ℕ} {f : ℝ → ℝ} {m B : ℝ}
    (hf : ∀ x ∈ Icc (m-(H:ℝ)) (m+(H:ℝ)), ContDiffAt ℝ ∞ f x)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) (j : ℕ)
    (hB : ∀ x ∈ Icc (m-(H:ℝ)) (m+(H:ℝ)), |iteratedDeriv (j+6) f x| ≤ B) :
    |iteratedDeriv j (sargosSextupleRemainder f q) m| ≤ B*(H:ℝ)^6/60 := by
  rw [iteratedDeriv_sargosSextupleRemainder hf]
  have hf' := fun x hx => contDiffAt_iteratedDeriv_infty (hf x hx) j
  have hb : ∀ x ∈ Icc (m-(H:ℝ)) (m+(H:ℝ)), |iteratedDeriv 6 (iteratedDeriv j f) x| ≤ B := by
    intro x hx
    rw [iteratedDeriv_real_comp_order,Nat.add_comm 6 j]
    exact hB x hx
  have h1 := abs_sargosTupleRemainder_le hf' hb q.1
  have h2 := abs_sargosTupleRemainder_le hf' hb q.2
  exact (abs_sub _ _).trans (by linarith only [h1,h2])

end TaoTrudgianYang2025

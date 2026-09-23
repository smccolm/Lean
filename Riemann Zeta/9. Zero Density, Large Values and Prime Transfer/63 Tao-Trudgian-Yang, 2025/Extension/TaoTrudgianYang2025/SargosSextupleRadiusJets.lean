import TaoTrudgianYang2025.SargosSourceSextuplePhase

/-! Local remainder jets on each sextuple's actual maximum-offset segment. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem sargosSextupleRadius_bounds {H : ℕ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) :
    1 ≤ sargosSextupleRadius q ∧ sargosSextupleRadius q ≤ H := by
  obtain ⟨h1,h1H⟩ := sargosTupleRadius_bounds q.1
  obtain ⟨h2,h2H⟩ := sargosTupleRadius_bounds q.2
  exact ⟨h1.trans (le_max_left _ _),max_le h1H h2H⟩

theorem abs_iteratedDeriv_sargosSextupleRemainder_le_radius {H : ℕ}
    {f : ℝ → ℝ} {m B : ℝ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ x ∈ Icc (m-(sargosSextupleRadius q:ℝ)) (m+(sargosSextupleRadius q:ℝ)),
      ContDiffAt ℝ ∞ f x) (j : ℕ)
    (hB : ∀ x ∈ Icc (m-(sargosSextupleRadius q:ℝ)) (m+(sargosSextupleRadius q:ℝ)),
      |iteratedDeriv (j+6) f x| ≤ B) :
    |iteratedDeriv j (sargosSextupleRemainder f q) m| ≤ B*(sargosSextupleRadius q:ℝ)^6/60 := by
  let R : ℕ := (sargosSextupleRadius q).toNat
  have hr0 : 0 ≤ sargosSextupleRadius q := by
    have h := (sargosSextupleRadius_bounds q).1
    omega
  have hR : (R:ℤ) = sargosSextupleRadius q := Int.toNat_of_nonneg hr0
  have hRR : (R:ℝ) = (sargosSextupleRadius q:ℝ) := by exact_mod_cast hR
  have hb1 (i : Fin 3) : (q.1 i:ℤ) ≤ (R:ℤ) := by
    rw [hR]
    exact (sargos_tuple_coordinate_le_radius q.1 i).trans (le_max_left _ _)
  have hb2 (i : Fin 3) : (q.2 i:ℤ) ≤ (R:ℤ) := by
    rw [hR]
    exact (sargos_tuple_coordinate_le_radius q.2 i).trans (le_max_right _ _)
  let t1 : SargosInitialMomentTuple R 3 := fun i =>
    ⟨(q.1 i:ℤ),Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp (q.1 i).property).1,hb1 i⟩⟩
  let t2 : SargosInitialMomentTuple R 3 := fun i =>
    ⟨(q.2 i:ℤ),Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp (q.2 i).property).1,hb2 i⟩⟩
  have he : sargosSextupleRemainder f (t1,t2) = sargosSextupleRemainder f q := rfl
  have h := abs_iteratedDeriv_sargosSextupleRemainder_le
    (H := R) (f := f) (m := m) (B := B)
    (by simpa only [hRR] using hf) (t1,t2) j (by simpa only [hRR] using hB)
  rw [he,hRR] at h
  exact h

theorem abs_iteratedDeriv_sargosSextupleRemainder_le_local {H : ℕ}
    {f : ℝ → ℝ} {m B : ℝ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ x ∈ Icc (m-(sargosSextupleRadius q:ℝ)) (m+(sargosSextupleRadius q:ℝ)),
      ContDiffAt ℝ ∞ f x) (j : ℕ)
    (hB : ∀ x ∈ Icc (m-(sargosSextupleRadius q:ℝ)) (m+(sargosSextupleRadius q:ℝ)),
      |iteratedDeriv (j+6) f x| ≤ B) :
    |iteratedDeriv j (sargosSextupleRemainder f q) m| ≤ B*(H:ℝ)^6/60 := by
  have hr := sargosSextupleRadius_bounds q
  have hr0 : (0:ℝ) ≤ sargosSextupleRadius q := by exact_mod_cast (show 0 ≤ sargosSextupleRadius q by omega)
  have hrH : (sargosSextupleRadius q:ℝ) ≤ H := by exact_mod_cast hr.2
  have hm : m ∈ Icc (m-(sargosSextupleRadius q:ℝ)) (m+(sargosSextupleRadius q:ℝ)) :=
    ⟨by linarith,by linarith⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB m hm)
  exact (abs_iteratedDeriv_sargosSextupleRemainder_le_radius q hf j hB).trans
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrH 6) hB0) (by norm_num))

theorem abs_iteratedDeriv_sargosSextupleRemainder_source_interior {H M : ℕ}
    {f : ℝ → ℝ} {m B : ℝ}
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hf : ∀ x ∈ Ioo (1:ℝ) M, ContDiffAt ℝ ∞ f x) (j : ℕ)
    (hB : ∀ x ∈ Ioo (1:ℝ) M, |iteratedDeriv (j+6) f x| ≤ B)
    (hm : m ∈ Ioo ((sargosSextupleRadius q:ℝ)+1) ((M:ℝ)-(sargosSextupleRadius q:ℝ))) :
    |iteratedDeriv j (sargosSextupleRemainder f q) m| ≤ B*(H:ℝ)^6/60 := by
  have hi : Icc (m-(sargosSextupleRadius q:ℝ)) (m+(sargosSextupleRadius q:ℝ)) ⊆ Ioo (1:ℝ) M := by
    intro x hx
    constructor <;> linarith [hm.1,hm.2,hx.1,hx.2]
  exact abs_iteratedDeriv_sargosSextupleRemainder_le_local q
    (fun x hx => hf x (hi hx)) j (fun x hx => hB x (hi hx))

end TaoTrudgianYang2025

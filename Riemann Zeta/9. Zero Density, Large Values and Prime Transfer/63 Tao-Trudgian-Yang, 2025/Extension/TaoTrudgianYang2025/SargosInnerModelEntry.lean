import TaoTrudgianYang2025.SargosSourceModelEntry
import TaoTrudgianYang2025.SargosOrientedModelSource

/-! Exact inner integer-to-natural source interval, with its actual dyadic scale conditions. -/

noncomputable section

open Expdb GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosInnerStart {H : ℕ} (a : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) : ℕ :=
  a+(sargosSextupleRadius q).toNat+2

def sargosInnerEnd {H : ℕ} (a M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3) : ℕ :=
  a+M-(sargosSextupleRadius q).toNat-1

theorem sargosInnerEndpoints {H : ℕ} (a M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hne : (sargosSextupleInterior M q).Nonempty) :
    a ≤ sargosInnerStart a q ∧ sargosInnerStart a q ≤ sargosInnerEnd a M q ∧
      sargosInnerEnd a M q ≤ a+M ∧
      (sargosInnerStart a q:ℤ) = (a:ℤ)+sargosSextupleRadius q+2 ∧
      (sargosInnerEnd a M q:ℤ) = (a:ℤ)+(M:ℤ)-sargosSextupleRadius q-1 := by
  obtain ⟨m,hm⟩ := hne
  have hi := Finset.mem_Ioo.mp hm
  have hr := (sargosSextupleRadius_bounds q).1
  have hR := Int.toNat_of_nonneg (show 0 ≤ sargosSextupleRadius q by omega)
  dsimp [sargosInnerStart,sargosInnerEnd]
  omega

theorem sargos_inner_sum_eq_exponentialSumAt {H : ℕ}
    (G : ℝ → ℝ) (T N : ℝ) (a M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hne : (sargosSextupleInterior M q).Nonempty) :
    (∑ m ∈ sargosSextupleInterior M q, fordAdditiveCharacter (T * G (((a:ℝ)+m)/N))) =
      exponentialSumAt G T N (sargosInnerStart a q) (sargosInnerEnd a M q) := by
  have hb := sargosInnerEndpoints a M q hne
  have hr := (sargosSextupleRadius_bounds q).1
  unfold exponentialSumAt
  apply Finset.sum_bij (fun m _ => a+m.toNat)
  case hi =>
    intro m hm
    have hm' := Finset.mem_Ioo.mp hm
    have hm0 : 0 ≤ m := by omega
    have ht := Int.toNat_of_nonneg hm0
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  case i_inj =>
    intro m hm n hn he
    have hm' := Finset.mem_Ioo.mp hm
    have hn' := Finset.mem_Ioo.mp hn
    have hm0 : 0 ≤ m := by omega
    have hn0 : 0 ≤ n := by omega
    have he' : m.toNat = n.toNat := by omega
    have hh := congrArg (fun k : ℕ => (k:ℤ)) he'
    simpa only [Int.toNat_of_nonneg hm0,Int.toNat_of_nonneg hn0] using hh
  case i_surj =>
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    refine ⟨((n-a:ℕ):ℤ),?_,by omega⟩
    apply Finset.mem_Ioo.mpr
    constructor <;> omega
  case h =>
    intro m hm
    have hm' := Finset.mem_Ioo.mp hm
    have hm0 : 0 ≤ m := by omega
    have ht : (m.toNat:ℝ) = (m:ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hm0 : (m.toNat:ℤ) = m)
    rw [sargos_ford_character_eq_fourier]
    simp only [oscillatory,Nat.cast_add,ht]

theorem sargosInnerEndpoints_dyadic {H : ℕ} {N : ℝ} (a M : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hne : (sargosSextupleInterior M q).Nonempty)
    (ha : N ≤ (a:ℝ)) (hb : (a:ℝ)+M ≤ 2*N) :
    N ≤ (sargosInnerStart a q:ℝ) ∧ (sargosInnerEnd a M q:ℝ) ≤ 2*N := by
  have hg := sargosInnerEndpoints a M q hne
  have hstart : (a:ℝ) ≤ sargosInnerStart a q := by exact_mod_cast hg.1
  have hend : (sargosInnerEnd a M q:ℝ) ≤ (a:ℝ)+M := by exact_mod_cast hg.2.2.1
  exact ⟨ha.trans hstart,hend.trans hb⟩

end TaoTrudgianYang2025

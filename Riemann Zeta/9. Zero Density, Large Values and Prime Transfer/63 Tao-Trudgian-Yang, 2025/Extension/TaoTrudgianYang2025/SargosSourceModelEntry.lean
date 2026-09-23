import TaoTrudgianYang2025.SargosScaledTransformedSource

/-! Exact entry of the paper's closed natural source interval into one-based symmetric differencing. -/

noncomputable section

open Expdb GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_source_model_Ioc (F : ℝ → ℝ) (T N : ℝ) (a M : ℕ) :
    (∑ m ∈ Finset.Ioc (0:ℤ) M,
      fordAdditiveCharacter (heathBrownPhysicalPhase F T N a 1 m)) =
      ∑ n ∈ Finset.Ioc a (a+M), oscillatory F T N n := by
  apply Finset.sum_bij (fun m _ => a+m.toNat)
  case hi =>
    intro m hm
    have hm' := Finset.mem_Ioc.mp hm
    have ht : (m.toNat:ℤ) = m := Int.toNat_of_nonneg hm'.1.le
    apply Finset.mem_Ioc.mpr
    constructor <;> omega
  case i_inj =>
    intro m hm n hn he
    have hm0 := (Finset.mem_Ioc.mp hm).1.le
    have hn0 := (Finset.mem_Ioc.mp hn).1.le
    have he' : m.toNat = n.toNat := by omega
    have hh := congrArg (fun k : ℕ => (k:ℤ)) he'
    simpa only [Int.toNat_of_nonneg hm0,Int.toNat_of_nonneg hn0] using hh
  case i_surj =>
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    refine ⟨((n-a:ℕ):ℤ),?_,by omega⟩
    apply Finset.mem_Ioc.mpr
    constructor <;> exact_mod_cast (by omega)
  case h =>
    intro m hm
    have hm0 := (Finset.mem_Ioc.mp hm).1.le
    have ht : (m.toNat:ℝ) = (m:ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hm0 : (m.toNat:ℤ) = m)
    rw [sargos_ford_character_eq_fourier]
    simp only [heathBrownPhysicalPhase,one_mul,oscillatory,Nat.cast_add,ht]

theorem sargos_exponentialSumAt_source_entry (F : ℝ → ℝ) (T N : ℝ) (a M : ℕ) :
    exponentialSumAt F T N a (a+M) =
      oscillatory F T N a+
      ∑ m ∈ Finset.Ioc (0:ℤ) M,
        fordAdditiveCharacter (heathBrownPhysicalPhase F T N a 1 m) := by
  rw [sargos_source_model_Ioc]
  exact (Finset.add_sum_Ioc_eq_sum_Icc (f := fun n : ℕ => oscillatory F T N n)
    (by omega : a ≤ a+M)).symm

theorem sargos_exponentialSumAt_source_endpoint (F : ℝ → ℝ) (T N : ℝ) (a M : ℕ) :
    ‖exponentialSumAt F T N a (a+M)-
      (∑ m ∈ Finset.Ioc (0:ℤ) M,
        fordAdditiveCharacter (heathBrownPhysicalPhase F T N a 1 m))‖ = 1 := by
  rw [sargos_exponentialSumAt_source_entry,add_sub_cancel_right,norm_oscillatory]

theorem sargos_exponentialSumAt_le_source (F : ℝ → ℝ) (T N : ℝ) (a M : ℕ) :
    ‖exponentialSumAt F T N a (a+M)‖ ≤
      1+‖∑ m ∈ Finset.Ioc (0:ℤ) M,
        fordAdditiveCharacter (heathBrownPhysicalPhase F T N a 1 m)‖ := by
  rw [sargos_exponentialSumAt_source_entry]
  simpa only [norm_oscillatory] using norm_add_le (oscillatory F T N a)
    (∑ m ∈ Finset.Ioc (0:ℤ) M,
      fordAdditiveCharacter (heathBrownPhysicalPhase F T N a 1 m))

end TaoTrudgianYang2025

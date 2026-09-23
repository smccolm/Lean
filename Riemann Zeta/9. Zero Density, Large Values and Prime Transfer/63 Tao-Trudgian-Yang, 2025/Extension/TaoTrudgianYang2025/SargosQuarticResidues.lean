import TaoTrudgianYang2025.SargosPrefixMaximum

/-! Exact residue indexing of the literal half-open source interval. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosSourceLift {N : ℕ} [NeZero N] (k : ZMod N) : ℤ := (N : ℤ)+k.val+1

def sargosSourceResidue (N : ℕ) (n : ℤ) : ZMod N := (n : ZMod N)-(N : ZMod N)-1

theorem sargosSourceLift_mem {N : ℕ} [NeZero N] (k : ZMod N) :
    sargosSourceLift k ∈ sargosSourceInterval N := by
  have hk := ZMod.val_lt k
  rw [sargosSourceInterval,Finset.mem_Ioc]
  unfold sargosSourceLift
  constructor <;> omega

theorem sargosSourceResidue_lift {N : ℕ} [NeZero N] (k : ZMod N) :
    sargosSourceResidue N (sargosSourceLift k) = k := by
  unfold sargosSourceResidue sargosSourceLift
  push_cast
  rw [ZMod.natCast_zmod_val]
  ring

theorem sargosSourceLift_injective {N : ℕ} [NeZero N] :
    Function.Injective (sargosSourceLift (N := N)) := by
  intro k l he
  have h := congrArg (sargosSourceResidue N) he
  simpa only [sargosSourceResidue_lift] using h

theorem exists_sargosSourceLift {N : ℕ} [NeZero N] {n : ℤ}
    (hn : n ∈ sargosSourceInterval N) :
    ∃ k : ZMod N, sargosSourceLift k = n := by
  rw [sargosSourceInterval,Finset.mem_Ioc] at hn
  have hn0 : 0 ≤ n-(N : ℤ)-1 := by omega
  have hc := Int.toNat_of_nonneg hn0
  have hj : (n-(N : ℤ)-1).toNat < N := by omega
  refine ⟨((n-(N : ℤ)-1).toNat : ZMod N), ?_⟩
  unfold sargosSourceLift
  rw [ZMod.val_cast_of_lt hj]
  omega

theorem sargosSourceLift_residue {N : ℕ} [NeZero N] {n : ℤ}
    (hn : n ∈ sargosSourceInterval N) :
    sargosSourceLift (sargosSourceResidue N n) = n := by
  obtain ⟨k,rfl⟩ := exists_sargosSourceLift hn
  rw [sargosSourceResidue_lift]

theorem sargos_sum_sourceLift {N : ℕ} [NeZero N] (g : ℤ → ℂ) :
    (∑ k : ZMod N, g (sargosSourceLift k)) = ∑ n ∈ sargosSourceInterval N, g n := by
  refine Finset.sum_bij (fun k _ => sargosSourceLift k) ?_ ?_ ?_ ?_
  · intro k hk
    exact sargosSourceLift_mem k
  · intro k hk l hl he
    exact sargosSourceLift_injective he
  · intro n hn
    obtain ⟨k,he⟩ := exists_sargosSourceLift hn
    exact ⟨k,Finset.mem_univ _,he⟩
  · intro k hk
    rfl

end TaoTrudgianYang2025

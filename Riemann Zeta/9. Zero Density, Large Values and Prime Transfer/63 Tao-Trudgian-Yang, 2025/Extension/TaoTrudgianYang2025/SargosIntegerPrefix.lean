import TaoTrudgianYang2025.SargosPrefixMaximum

/-! Actual prefix maxima and endpoint-exact reindexing for arbitrary integer intervals. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosIntegerPrefix (a : ℤ) (H : ℕ) (f : ℤ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range H, f (a+j)

def sargosIntegerPrefixMaximum (a : ℤ) (H : ℕ) (f : ℤ → ℂ) : ℝ :=
  (Finset.range (H+1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero H))
    (fun L => ‖sargosIntegerPrefix a L f‖)

theorem sargosIntegerPrefixMaximum_attained (a : ℤ) (H : ℕ) (f : ℤ → ℂ) :
    ∃ L : ℕ, L ≤ H ∧ sargosIntegerPrefixMaximum a H f = ‖sargosIntegerPrefix a L f‖ := by
  obtain ⟨L,hL,he⟩ := Finset.exists_mem_eq_sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero H)) (fun L => ‖sargosIntegerPrefix a L f‖)
  exact ⟨L,Nat.le_of_lt_succ (Finset.mem_range.mp hL),he⟩

theorem sargosIntegerPrefixMaximum_nonneg (a : ℤ) (H : ℕ) (f : ℤ → ℂ) :
    0 ≤ sargosIntegerPrefixMaximum a H f := by
  obtain ⟨L,hL,he⟩ := sargosIntegerPrefixMaximum_attained a H f
  rw [he]
  exact norm_nonneg _

theorem norm_sargosIntegerPrefix_le_maximum (a : ℤ) (H L : ℕ) (f : ℤ → ℂ) (hL : L ≤ H) :
    ‖sargosIntegerPrefix a L f‖ ≤ sargosIntegerPrefixMaximum a H f :=
  Finset.le_sup' (fun L => ‖sargosIntegerPrefix a L f‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hL))

theorem sargos_sum_Icc_eq_range {A : Type*} [AddCommMonoid A] (a b : ℤ) (f : ℤ → A) :
    (∑ y ∈ Finset.Icc a b, f y) = ∑ j ∈ Finset.range (b+1-a).toNat, f (a+j) := by
  rw [Int.Icc_eq_finset_map,Finset.sum_map]
  rfl

theorem norm_sargos_sum_Icc_le_prefixMaximum (a b : ℤ) (f : ℤ → ℂ) :
    ‖∑ y ∈ Finset.Icc a b, f y‖ ≤ sargosIntegerPrefixMaximum a (b+1-a).toNat f := by
  rw [sargos_sum_Icc_eq_range]
  exact norm_sargosIntegerPrefix_le_maximum a _ _ f le_rfl

end TaoTrudgianYang2025


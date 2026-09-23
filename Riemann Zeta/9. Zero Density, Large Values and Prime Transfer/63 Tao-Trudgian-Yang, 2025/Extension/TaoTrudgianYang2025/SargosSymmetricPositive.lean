import TaoTrudgianYang2025.SargosSymmetricFibers

/-! Positive offsets and the actual diagonal term of symmetric differencing. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosPositiveOffsets (H j : ℕ) : Finset ℤ :=
  (sargosSymmetricOffsets H j).filter (fun n => 0 < n)

theorem sargosPositiveOffsets_subset (H j : ℕ) :
    sargosPositiveOffsets H j ⊆ Finset.Ioc (0:ℤ) H := by
  intro n hn
  obtain ⟨hn,hpos⟩ := Finset.mem_filter.mp hn
  exact Finset.mem_Ioc.mpr ⟨hpos,(sargosSymmetricOffsets_bounds hn).2.le⟩

theorem sargos_finite_even_sum (S : Finset ℤ)
    (hS : ∀ n ∈ S, -n ∈ S) (f : ℤ → ℂ)
    (hf : ∀ n, f (-n) = f n) :
    (∑ n ∈ S, f n) =
      (if (0:ℤ) ∈ S then f 0 else 0)+2*(∑ n ∈ S with 0 < n, f n) := by
  classical
  have hn : (∑ n ∈ S with n < 0, f n) = ∑ n ∈ S with 0 < n, f n := by
    apply Finset.sum_bij (fun n _ => -n)
    · intro n hn
      obtain ⟨hn,hn0⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨hS n hn,by omega⟩
    · intro n hn m hm he
      omega
    · intro n hn
      obtain ⟨hn,hn0⟩ := Finset.mem_filter.mp hn
      exact ⟨-n,Finset.mem_filter.mpr ⟨hS n hn,by omega⟩,by simp⟩
    · intro n hn
      exact (hf n).symm
  have h0 : (∑ n ∈ S with n = 0, f n) = if (0:ℤ) ∈ S then f 0 else 0 := by
    rw [Finset.sum_filter,Finset.sum_eq_ite 0]
    · simp
    · intro n hn hn0
      simp [hn0]
  have hsplit : (∑ n ∈ S, f n) =
      (∑ n ∈ S with n = 0, f n)+
        ((∑ n ∈ S with n < 0, f n)+(∑ n ∈ S with 0 < n, f n)) := by
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rcases lt_trichotomy n 0 with h | h | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le]
    · simp [h]
    · simp [h,ne_of_gt h,not_lt_of_ge h.le]
  rw [hsplit,h0,hn]
  ring

theorem sargosSymmetricOffsets_sum (φ : ℤ → ℂ) (H j : ℕ) (m : ℤ) :
    (∑ n ∈ sargosSymmetricOffsets H j, φ (m+n)*φ (m-n)) =
      (if (0:ℤ) ∈ sargosSymmetricOffsets H j then φ m^2 else 0)+
        2*(∑ n ∈ sargosPositiveOffsets H j, φ (m+n)*φ (m-n)) := by
  have h := sargos_finite_even_sum (sargosSymmetricOffsets H j)
    (fun _ hn => sargosSymmetricOffsets_neg hn)
    (fun n => φ (m+n)*φ (m-n)) (fun n => by simp [sub_eq_add_neg,mul_comm])
  simpa only [add_zero,sub_zero,pow_two,sargosPositiveOffsets] using h

theorem sargosSymmetricOffsets_norm (φ : ℤ → ℂ) (H j : ℕ) (m : ℤ) :
    ‖∑ n ∈ sargosSymmetricOffsets H j, φ (m+n)*φ (m-n)‖ ≤
      ‖φ m‖^2+2*‖∑ n ∈ sargosPositiveOffsets H j, φ (m+n)*φ (m-n)‖ := by
  rw [sargosSymmetricOffsets_sum]
  have hdiag : ‖if (0:ℤ) ∈ sargosSymmetricOffsets H j then φ m^2 else 0‖ ≤ ‖φ m‖^2 := by
    split_ifs
    · rw [norm_pow]
    · simp
  calc
    _ ≤ ‖if (0:ℤ) ∈ sargosSymmetricOffsets H j then φ m^2 else 0‖+
        ‖(2:ℂ)*(∑ n ∈ sargosPositiveOffsets H j, φ (m+n)*φ (m-n))‖ :=
      norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul]
      norm_num only [Complex.norm_ofNat]
      exact add_le_add hdiag le_rfl

end TaoTrudgianYang2025

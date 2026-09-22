import TaoTrudgianYang2025.ExponentPairSourceCorrelation
import TaoTrudgianYang2025.ExponentPairWeylSum

/-!
# Summed-correlation Weyl inequality for the literal source sum

The padded sequence is constructed from the source oscillatory terms.
All index and sign bridges are proved before using the finite inequality.
-/

noncomputable section

open Expdb RiemannZeta.GuthMaynard
open scoped BigOperators

namespace TaoTrudgianYang2025

def sourceOscillatorySequence (F : ℝ → ℝ) (T N : ℝ) (a : ℕ) (n : ℤ) : ℂ :=
  oscillatory F T N ((a : ℝ)+n)

theorem sum_sourceOscillatorySequence (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) :
    (∑ n ∈ Finset.Ico (0 : ℤ) ((L+1 : ℕ) : ℤ), sourceOscillatorySequence F T N a n) =
      exponentialSumAt F T N a (a+L) := by
  unfold exponentialSumAt
  apply Finset.sum_bij (fun n _ => a+n.toNat)
  case hi =>
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hto : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn'.1
    have hbound : n.toNat ≤ L := by omega
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  case i_inj =>
    intro n hn m hm he
    have hn0 := (Finset.mem_Ico.mp hn).1
    have hm0 := (Finset.mem_Ico.mp hm).1
    have hto : n.toNat = m.toNat := by omega
    have he' := congrArg (fun k : ℕ => (k : ℤ)) hto
    dsimp at he'
    rw [Int.toNat_of_nonneg hn0,Int.toNat_of_nonneg hm0] at he'
    exact he'
  case i_surj =>
    intro m hm
    have hm' := Finset.mem_Icc.mp hm
    refine ⟨(m-a : ℕ),?_,by omega⟩
    exact Finset.mem_Ico.mpr ⟨by positivity,by exact_mod_cast (show m-a < L+1 by omega)⟩
  case h =>
    intro n hn
    have hn0 := (Finset.mem_Ico.mp hn).1
    have hto : (n.toNat : ℝ) = (n : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hn0 : (n.toNat : ℤ) = n)
    simp only [sourceOscillatorySequence,Nat.cast_add,hto]

theorem padded_source_correlation_eq (F : ℝ → ℝ) (T N : ℝ) (a L H h k : ℕ)
    (hh : h < H) (hk : k < H) (hhk : h < k) :
    (∑ n ∈ Finset.Ico (-(H : ℤ)) ((L+1 : ℕ) : ℤ),
      star (paddedShift (sourceOscillatorySequence F T N a) (L+1) n h)*
        paddedShift (sourceOscillatorySequence F T N a) (L+1) n k) =
      sourceShiftCorrelation F T N a L (k-h) := by
  rw [padded_sequence_correlation_eq _ (L+1) H h k hh hk hhk]
  unfold sourceShiftCorrelation sourceOscillatorySequence
  apply Finset.sum_congr rfl
  intro j _
  simp only [Int.cast_add,Int.cast_sub,Int.cast_natCast,Nat.cast_sub hhk.le,add_assoc,starRingEnd_apply]

theorem norm_padded_source_correlation (F : ℝ → ℝ) (T N : ℝ) (a L H h k : ℕ)
    (hh : h < H) (hk : k < H) (hne : h ≠ k) :
    ‖∑ n ∈ Finset.Ico (-(H : ℤ)) ((L+1 : ℕ) : ℤ),
      star (paddedShift (sourceOscillatorySequence F T N a) (L+1) n h)*
        paddedShift (sourceOscillatorySequence F T N a) (L+1) n k‖ =
      ‖sourceShiftCorrelation F T N a L (shiftDistance h k)‖ := by
  by_cases hhk : h < k
  · rw [padded_source_correlation_eq F T N a L H h k hh hk hhk]
    simp only [shiftDistance,Nat.sub_eq_zero_of_le hhk.le,zero_add]
  · have hkh : k < h := by omega
    rw [padded_sequence_correlation_reverse _ (L+1) H h k,norm_star,
      padded_source_correlation_eq F T N a L H k h hk hh hkh]
    simp only [shiftDistance,Nat.sub_eq_zero_of_le hkh.le,add_zero]

theorem source_exponentialSum_weyl (F : ℝ → ℝ) (T N : ℝ) (a L H : ℕ) :
    (H : ℝ)^2*‖exponentialSumAt F T N a (a+L)‖^2 ≤
      ((L+1+H : ℕ) : ℝ)*((H : ℝ)*(L+1)+
        2*H*∑ r ∈ Finset.Icc 1 (H-1), ‖sourceShiftCorrelation F T N a L r‖) := by
  have h := interval_weyl_differencing_sum
    (sourceOscillatorySequence F T N a) (L+1) H
    (fun r => ‖sourceShiftCorrelation F T N a L r‖)
    (fun n _ => by simp [sourceOscillatorySequence])
    (fun _ _ => norm_nonneg _)
    (fun h hh k hk hne => (norm_padded_source_correlation F T N a L H h k
      (Finset.mem_range.mp hh) (Finset.mem_range.mp hk) hne).le)
  rw [sum_sourceOscillatorySequence] at h
  simpa only [Nat.cast_add,Nat.cast_one] using h

end TaoTrudgianYang2025

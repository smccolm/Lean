import TaoTrudgianYang2025.ExponentPairFiniteCorrelation
import TaoTrudgianYang2025.ExponentPairWeylSum
import GafniTao.FordEquation54Expansion

/-! Weyl differencing of an arbitrary continuous real phase at its literal samples. -/

noncomputable section
open GafniTao RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

def continuousPhaseCorrelation (F : ℝ → ℝ) (A : ℝ) (N r : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N-r), fordAdditiveCharacter (F (A+n+r)-F (A+n))

theorem sum_integer_zero_interval_eq_range (a : ℤ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Ico (0:ℤ) N, a n) = ∑ n ∈ Finset.range N, a n := by
  symm
  apply Finset.sum_bij (fun (n : ℕ) _ => (n:ℤ))
  · intro n hn
    exact Finset.mem_Ico.mpr ⟨by positivity,by exact_mod_cast Finset.mem_range.mp hn⟩
  · intro n _ m _ he
    exact_mod_cast he
  · intro n hn
    have hni := Finset.mem_Ico.mp hn
    refine ⟨n.toNat,Finset.mem_range.mpr (by omega),Int.toNat_of_nonneg hni.1⟩
  · intro _ _
    rfl

theorem padded_continuousPhase_correlation
    (F : ℝ → ℝ) (A : ℝ) (N H h k : ℕ)
    (hh : h < H) (hk : k < H) (hhk : h < k) :
    (∑ n ∈ Finset.Ico (-(H:ℤ)) N,
      star (paddedShift (fun j => fordAdditiveCharacter (F (A+j))) N n h)*
        paddedShift (fun j => fordAdditiveCharacter (F (A+j))) N n k) =
      continuousPhaseCorrelation F A N (k-h) := by
  rw [padded_sequence_correlation_eq _ N H h k hh hk hhk]
  unfold continuousPhaseCorrelation
  apply Finset.sum_congr rfl
  intro n _
  simp only [Int.cast_add,Int.cast_natCast]
  change (starRingEnd ℂ) _ * _ = _
  rw [conj_fordAdditiveCharacter,← fordAdditiveCharacter_add]
  congr 1
  push_cast
  simp only [Nat.cast_sub hhk.le,add_assoc,sub_eq_add_neg,add_comm]

theorem norm_padded_continuousPhase_correlation
    (F : ℝ → ℝ) (A : ℝ) (N H h k : ℕ)
    (hh : h < H) (hk : k < H) (hne : h ≠ k) :
    ‖∑ n ∈ Finset.Ico (-(H:ℤ)) N,
      star (paddedShift (fun j => fordAdditiveCharacter (F (A+j))) N n h)*
        paddedShift (fun j => fordAdditiveCharacter (F (A+j))) N n k‖ =
      ‖continuousPhaseCorrelation F A N (shiftDistance h k)‖ := by
  by_cases hhk : h < k
  · rw [padded_continuousPhase_correlation F A N H h k hh hk hhk]
    simp only [shiftDistance,Nat.sub_eq_zero_of_le hhk.le,zero_add]
  · have hkh : k < h := by omega
    rw [padded_sequence_correlation_reverse _ N H h k,norm_star,
      padded_continuousPhase_correlation F A N H k h hk hh hkh]
    simp only [shiftDistance,Nat.sub_eq_zero_of_le hkh.le,add_zero]

theorem continuous_phase_weyl
    (F : ℝ → ℝ) (A : ℝ) (N H : ℕ) :
    (H:ℝ)^2*‖∑ n ∈ Finset.range N, fordAdditiveCharacter (F (A+n))‖^2 ≤
      ((N+H:ℕ):ℝ)*((H:ℝ)*N+
        2*H*∑ r ∈ Finset.Icc 1 (H-1), ‖continuousPhaseCorrelation F A N r‖) := by
  have hb := interval_weyl_differencing_sum
    (fun j => fordAdditiveCharacter (F (A+j))) N H
    (fun r => ‖continuousPhaseCorrelation F A N r‖)
    (fun _ _ => by simp [fordAdditiveCharacter,Complex.norm_exp])
    (fun _ _ => norm_nonneg _)
    (fun h hh k hk hne => (norm_padded_continuousPhase_correlation F A N H h k
      (Finset.mem_range.mp hh) (Finset.mem_range.mp hk) hne).le)
  rw [sum_integer_zero_interval_eq_range] at hb
  simpa only [Int.cast_natCast] using hb

end TaoTrudgianYang2025

import TaoTrudgianYang2025.RobertSargosSourceAProcess
import TaoTrudgianYang2025.DoubledBlockSelection

/-! The actual source phase sequence, its coefficient bound, and doubled blocks. -/

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

def robertSargosPhaseSequence (f : ℝ → ℝ) (M n : ℕ) : ℂ :=
  if n = 0 then 0 else robertSargosSourceCenteredPhase f M n

theorem robertSargos_source_centered_phase_norm (f : ℝ → ℝ) (M : ℕ) (h : ℤ)
    (hh : 0 ≤ h) : ‖robertSargosSourceCenteredPhase f M h‖ ≤ M := by
  have hc : (Finset.Icc (h+1) ((M:ℤ)-h)).card ≤ M := by
    rw [Int.card_Icc]
    omega
  unfold robertSargosSourceCenteredPhase
  calc
    _ ≤ ∑ m ∈ Finset.Icc (h+1) ((M:ℤ)-h),
        ‖fordAdditiveCharacter (robertSargosSymmetricDifference f m h)‖ := norm_sum_le _ _
    _ = ((Finset.Icc (h+1) ((M:ℤ)-h)).card:ℝ) := by
      simp only [sargos_character_norm,Finset.sum_const,nsmul_eq_mul,mul_one]
    _ ≤ M := by exact_mod_cast hc

theorem robertSargos_phase_sequence_norm (f : ℝ → ℝ) (M n : ℕ) :
    ‖robertSargosPhaseSequence f M n‖ ≤ M := by
  unfold robertSargosPhaseSequence
  split_ifs
  · simpa only [norm_zero] using Nat.cast_nonneg (α := ℝ) M
  · exact robertSargos_source_centered_phase_norm f M n (Nat.cast_nonneg n)

theorem robertSargos_phase_sequence_block (f : ℝ → ℝ) (M k : ℕ) (hk : 0 < k) :
    (∑ j ∈ Finset.range k, robertSargosPhaseSequence f M (k+j)) =
      robertSargosSymmetricSum f M k := by
  unfold robertSargosSymmetricSum
  apply Finset.sum_bij (fun (j : ℕ) _ => (k:ℤ)+(j:ℤ))
  · intro j hj
    have ht := Finset.mem_range.mp hj
    simp only [Finset.mem_Ico]
    constructor <;> omega
  · intro j _ l _ he
    omega
  · intro h hh
    have ht := Finset.mem_Ico.mp hh
    have hp : 0 ≤ h-(k:ℤ) := by omega
    have hc := Int.toNat_of_nonneg hp
    refine ⟨(h-(k:ℤ)).toNat,Finset.mem_range.mpr (by omega),by omega⟩
  · intro j _
    rw [robertSargosPhaseSequence,if_neg (by omega)]
    unfold robertSargosSourceCenteredPhase
    simp only [Nat.cast_add]

theorem robertSargos_phase_sequence_weighted (f : ℝ → ℝ) (M H : ℕ) :
    (∑ n ∈ Finset.range H, ((1-(n:ℝ)/H : ℝ):ℂ)*robertSargosPhaseSequence f M n) =
      robertSargosWeightedSymmetricPhase f M H := by
  classical
  let F : ℕ → ℂ := fun n => ((1-(n:ℝ)/H : ℝ):ℂ)*robertSargosPhaseSequence f M n
  have hfilt : (∑ n ∈ (Finset.range H).filter (fun n => 0 < n), F n) =
      ∑ n ∈ Finset.range H, F n := by
    apply Finset.sum_filter_of_ne
    intro n _ hn
    by_contra hp
    have he : n = 0 := by omega
    subst n
    simp [F,robertSargosPhaseSequence] at hn
  change (∑ n ∈ Finset.range H, F n) = _
  rw [← hfilt]
  unfold robertSargosWeightedSymmetricPhase
  apply Finset.sum_bij (fun (n : ℕ) _ => (n:ℤ))
  · intro n hn
    have ht := Finset.mem_filter.mp hn
    have hr := Finset.mem_range.mp ht.1
    apply Finset.mem_Ioo.mpr
    constructor <;> omega
  · intro n _ m _ he
    omega
  · intro h hh
    have ht := Finset.mem_Ioo.mp hh
    have hc := Int.toNat_of_nonneg (le_of_lt ht.1)
    refine ⟨h.toNat,Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega),by omega⟩,hc⟩
  · intro n hn
    have ht := (Finset.mem_filter.mp hn).2
    dsimp only [F]
    rw [robertSargosPhaseSequence,if_neg (by omega)]
    simp only [Int.cast_natCast]

end TaoTrudgianYang2025

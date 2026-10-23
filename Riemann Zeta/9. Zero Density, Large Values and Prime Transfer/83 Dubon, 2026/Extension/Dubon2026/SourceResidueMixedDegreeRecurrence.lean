import Dubon2026.SourceResidueRelativeDegree
import Dubon2026.SourceResiduePrimeExactDegree

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
all-level residue degree. Compare the actual forward and reverse expansion
towers. The previous degree and the first-step coprime nonmembership are
the explicit induction inputs; all generation equalities and reverse degree
bounds are derived. This avoids characteristic-zero cyclotomic actions.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_relfinrank_fullC_mul_prime_pow, relfinrank_fullC_step. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem residue_mixed_step_degree_of_previous
    (K : Type*) [Field K] [IsAlgClosed K] (M p : ℕ) [NeZero M] [hp : Fact p.Prime]
    (a : ℕ) (hpM : ¬ p ∣ M) (hMK : ((M * p ^ (a + 1) : ℕ) : K) ≠ 0)
    (hprev : ∀ b : ℕ, a = b + 1 →
      relfinrank (modularFunctionFieldCoeff (M * p ^ b) K)
        (modularFunctionFieldCoeff (M * p ^ (b + 1)) K) = if b = 0 then p + 1 else p)
    (hnm : a = 0 → qExpand K p (jqModC K) ∉ modularFunctionFieldCoeff M K) :
    relfinrank (modularFunctionFieldCoeff (M * p ^ a) K)
      (modularFunctionFieldCoeff (M * p ^ (a + 1)) K) = if a = 0 then p + 1 else p := by
  cases a with
  | zero =>
    have hpK : (p : K) ≠ 0 :=
      ne_zero_of_dvd_ne_zero hMK ((dvd_pow_self p (by decide : 0 + 1 ≠ 0)).mul_left M).natCast
    rw [residue_full_mixed_prime_power_step_eq_adjoin K M p 0 hpM hMK]
    simp only [pow_zero, zero_add, pow_one, mul_one, ↓reduceIte]
    rw [coefficient_relfinrank_adjoin_union_singleton]
    exact prime_extension_degree_coeff_of_not_mem K p hpK _ (jq_mem_coeff_field M K) (hnm rfl)
  | succ b =>
    rw [if_neg (Nat.succ_ne_zero b)]
    have hL0 : M * p ^ (b + 1) = M * p ^ b * p := by ring
    have hL1 : M * p ^ (b + 1 + 1) = M * p ^ (b + 1) * p := by ring
    have hlow : ((M * p ^ b * p : ℕ) : K) ≠ 0 := by
      rw [← hL0]
      exact ne_zero_of_dvd_ne_zero hMK
        (mul_dvd_mul_left M (pow_dvd_pow p (Nat.le_succ (b + 1)))).natCast
    have htop : ((M * p ^ (b + 1) * p : ℕ) : K) ≠ 0 := by
      rw [← hL1]
      exact hMK
    have hGE : expandedCoefficientField K p (M * p ^ b) ≤
        expandedCoefficientField K p (M * p ^ (b + 1)) :=
      expandedCoefficientField_mono p (mul_dvd_mul_left M (pow_dvd_pow p (Nat.le_succ b)))
    have hG0 : expandedCoefficientField K p (M * p ^ b) ≤
        modularFunctionFieldCoeff (M * p ^ (b + 1)) K := by
      rw [hL0]
      exact expandedCoefficientField_le K p _
    have hE1 : expandedCoefficientField K p (M * p ^ (b + 1)) ≤
        modularFunctionFieldCoeff (M * p ^ (b + 1 + 1)) K := by
      rw [hL1]
      exact expandedCoefficientField_le K p _
    have h01 : modularFunctionFieldCoeff (M * p ^ (b + 1)) K ≤
        modularFunctionFieldCoeff (M * p ^ (b + 1 + 1)) K :=
      coefficient_field_mono (mul_dvd_mul_left M (pow_dvd_pow p (Nat.le_succ _)))
    have t1 := IntermediateField.relfinrank_mul_relfinrank hG0 h01
    have t2 := IntermediateField.relfinrank_mul_relfinrank hGE hE1
    have hδ : relfinrank (expandedCoefficientField K p (M * p ^ b))
        (expandedCoefficientField K p (M * p ^ (b + 1))) = if b = 0 then p + 1 else p := by
      rw [expandedCoefficientField, expandedCoefficientField, IntermediateField.relfinrank_map_map]
      exact hprev b rfl
    have hδpos : 0 < relfinrank (expandedCoefficientField K p (M * p ^ b))
        (expandedCoefficientField K p (M * p ^ (b + 1))) := by
      rw [hδ]
      split_ifs <;> have := hp.out.pos <;> omega
    have hx : relfinrank (expandedCoefficientField K p (M * p ^ b))
        (modularFunctionFieldCoeff (M * p ^ (b + 1)) K) ≤
        relfinrank (expandedCoefficientField K p (M * p ^ b))
          (expandedCoefficientField K p (M * p ^ (b + 1))) := by
      rw [hδ, hL0]
      by_cases hb : b = 0
      · rw [if_pos hb]
        exact residue_reverse_relfinrank_le K (M * p ^ b) p hlow
      · rw [if_neg hb]
        exact le_of_eq (residue_reverse_relfinrank_eq_of_dvd K (M * p ^ b) p hlow
          ((dvd_pow_self p hb).mul_left M))
    have hy : p ≤ relfinrank (expandedCoefficientField K p (M * p ^ (b + 1)))
        (modularFunctionFieldCoeff (M * p ^ (b + 1 + 1)) K) := by
      rw [hL1, residue_reverse_relfinrank_eq_of_dvd K (M * p ^ (b + 1)) p htop
        ((dvd_pow_self p (Nat.succ_ne_zero b)).mul_left M)]
    have hdle := residue_mixed_step_relfinrank_le K M p (b + 1) hpM hMK
    rw [if_neg (Nat.succ_ne_zero b)] at hdle
    have hsq : relfinrank (expandedCoefficientField K p (M * p ^ b))
        (expandedCoefficientField K p (M * p ^ (b + 1))) * p ≤
        relfinrank (expandedCoefficientField K p (M * p ^ b))
          (expandedCoefficientField K p (M * p ^ (b + 1))) *
            relfinrank (modularFunctionFieldCoeff (M * p ^ (b + 1)) K)
              (modularFunctionFieldCoeff (M * p ^ (b + 1 + 1)) K) :=
      calc _ ≤ _ := Nat.mul_le_mul le_rfl hy
        _ = _ := t2
        _ = _ := t1.symm
        _ ≤ _ := Nat.mul_le_mul hx le_rfl
    exact le_antisymm hdle (Nat.le_of_mul_le_mul_left hsq hδpos)

end
end Dubon2026.SourceFunctionField

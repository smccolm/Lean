import Dubon2026.SourceResidueReverseGeneration
import Dubon2026.SourceResidueMixedPrimePowerFields

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> forward and reverse full-field towers. Existing native
relative degrees identify the generated fields with their actual simple
extensions. The reverse degree bounds therefore apply to the full next-level
field, rather than a separately generated auxiliary field. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem coefficient_relfinrank_adjoin_union_singleton
    {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K)) (x : LaurentSeries K) :
    relfinrank F (IntermediateField.adjoin K ((F : Set (LaurentSeries K)) ∪ {x})) =
      Module.finrank F (IntermediateField.adjoin F ({x} : Set (LaurentSeries K))) := by
  have h : F ≤ IntermediateField.adjoin K ((F : Set (LaurentSeries K)) ∪ {x}) :=
    fun _ hx => subset_adjoin K _ (Or.inl hx)
  have he : IntermediateField.adjoin F ((F : Set (LaurentSeries K)) ∪ {x}) =
      IntermediateField.adjoin F ({x} : Set (LaurentSeries K)) := by
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro y (hy | hy)
      · exact (IntermediateField.adjoin F {x}).algebraMap_mem (⟨y, hy⟩ : F)
      · exact subset_adjoin F _ hy
    · exact IntermediateField.adjoin.mono F _ _ Set.subset_union_right
  rw [relfinrank_eq_finrank_of_le h, extendScalars_adjoin h, he]

theorem residue_reverse_relfinrank_le
    (K : Type*) [Field K] [IsAlgClosed K] (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNK : ((N * p : ℕ) : K) ≠ 0) :
    relfinrank (expandedCoefficientField K p N) (modularFunctionFieldCoeff (N * p) K) ≤ p + 1 := by
  rw [residue_full_prime_eq_adjoin_expanded K N p hNK,
    coefficient_relfinrank_adjoin_union_singleton,
    IntermediateField.adjoin.finrank (residue_reverse_prime_integral _ p
      (prime_j_mem_expandedCoefficientField K p N))]
  exact residue_reverse_prime_degree_le _ p (prime_j_mem_expandedCoefficientField K p N)

theorem residue_reverse_relfinrank_eq_of_dvd
    (K : Type*) [Field K] [IsAlgClosed K] (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNK : ((N * p : ℕ) : K) ≠ 0) (hpN : p ∣ N) :
    relfinrank (expandedCoefficientField K p N) (modularFunctionFieldCoeff (N * p) K) = p := by
  rw [residue_full_prime_eq_adjoin_expanded K N p hNK,
    coefficient_relfinrank_adjoin_union_singleton]
  exact residue_expanded_reverse_prime_finrank_eq K p N
    (ne_zero_of_dvd_ne_zero hNK (dvd_mul_left p N).natCast) hpN

theorem residue_mixed_step_relfinrank_eq_minpoly
    (K : Type*) [Field K] [IsAlgClosed K] (M p : ℕ) [NeZero M] [Fact p.Prime]
    (a : ℕ) (hpM : ¬ p ∣ M) (hMK : ((M * p ^ (a + 1) : ℕ) : K) ≠ 0) :
    relfinrank (modularFunctionFieldCoeff (M * p ^ a) K)
      (modularFunctionFieldCoeff (M * p ^ (a + 1)) K) =
        (minpoly (modularFunctionFieldCoeff (M * p ^ a) K)
          (qExpand K (p ^ (a + 1)) (jqModC K))).natDegree := by
  obtain ⟨P, hm, _, hrel⟩ := exists_prime_adjacent_relations_coeff p
  have hi : IsIntegral (modularFunctionFieldCoeff (M * p ^ a) K)
      (qExpand K (p ^ (a + 1)) (jqModC K)) := by
    apply integral_of_relationAtSeed_root _ P hm
      (jqd_mem_coeff_field (M * p ^ a) K (dvd_mul_left _ M))
    simpa only [← pow_succ] using (hrel K (p ^ a)).1
  rw [residue_full_mixed_prime_power_step_eq_adjoin K M p a hpM hMK,
    coefficient_relfinrank_adjoin_union_singleton, IntermediateField.adjoin.finrank hi]

theorem residue_mixed_step_relfinrank_le
    (K : Type*) [Field K] [IsAlgClosed K] (M p : ℕ) [NeZero M] [hp : Fact p.Prime]
    (a : ℕ) (hpM : ¬ p ∣ M) (hMK : ((M * p ^ (a + 1) : ℕ) : K) ≠ 0) :
    relfinrank (modularFunctionFieldCoeff (M * p ^ a) K)
      (modularFunctionFieldCoeff (M * p ^ (a + 1)) K) ≤ if a = 0 then p + 1 else p := by
  rw [residue_mixed_step_relfinrank_eq_minpoly K M p a hpM hMK]
  obtain ⟨P, hm, hd, hrel⟩ := exists_prime_adjacent_relations_coeff p
  have hs := jqd_mem_coeff_field (M * p ^ a) K (dvd_mul_left (p ^ a) M)
  have hr : (relationAtSeed P (qExpand K (p ^ a) (jqModC K))).eval
      (qExpand K (p ^ (a + 1)) (jqModC K)) = 0 := by
    simpa only [← pow_succ] using (hrel K (p ^ a)).1
  cases a with
  | zero =>
    rw [if_pos rfl]
    exact (minpoly_degree_le_relationAtSeed _ P hm hs hr).trans_eq hd
  | succ b =>
    rw [if_neg (Nat.succ_ne_zero b)]
    have hprev := jqd_mem_coeff_field (M * p ^ (b + 1)) K
      ((pow_dvd_pow p (Nat.le_succ b)).trans (dvd_mul_left _ M))
    have hprevroot : (relationAtSeed P (qExpand K (p ^ (b + 1)) (jqModC K))).eval
        (qExpand K (p ^ b) (jqModC K)) = 0 := by
      simpa only [← pow_succ] using (hrel K (p ^ b)).2
    have hne : qExpand K (p ^ (b + 1 + 1)) (jqModC K) ≠ qExpand K (p ^ b) (jqModC K) := by
      intro he
      have ht : PrimeDegreeAux.TS K (p ^ (b + 1 + 1)) 1 = PrimeDegreeAux.TS K (p ^ b) 1 := by
        simpa only [PrimeDegreeAux.TS, qTwist_one_apply] using he
      have h := Nat.pow_right_injective hp.out.two_le (PrimeDegreeAux.TS_injective ht).1
      omega
    have h := minpoly_degree_lt_relation_of_known_root _ P hm hs hprev hprevroot hr hne
    omega

end
end Dubon2026.SourceFunctionField

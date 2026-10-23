import Dubon2026.SourceResidueMixedDegreeRecurrence
import Dubon2026.SourceLevelPsiPrimeStep

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue j-map degree. The actual all-divisor field has degree dedekindPsi(p^a)
over its literal j coordinate, for every prime power away from the coefficient
characteristic. The reverse/forward degree recurrence and the proved prime
nonmembership discharge the induction inputs. General levels, genus preservation
and good reduction still require their own consumers. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField SourceLevelProjective
open scoped IntermediateField

theorem coefficient_level_one_eq (K : Type*) [Field K] :
    modularFunctionFieldCoeff 1 K = IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by
  change IntermediateField.adjoin K (divisorExpansionsCoeff 1 K) = _
  apply congrArg (IntermediateField.adjoin K)
  ext x
  constructor
  · rintro ⟨d, hd, hdvd, rfl⟩
    have he : d = 1 := Nat.dvd_one.mp hdvd
    rw [qExpand_congr he (jqModC K), qExpand_one_apply]
    exact Set.mem_singleton _
  · rintro rfl
    exact ⟨1, inferInstance, dvd_rfl, (qExpand_one_apply (jqModC K)).symm⟩

theorem residue_prime_power_step_relfinrank
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime]
    (hpK : (p : K) ≠ 0) (a : ℕ) :
    relfinrank (modularFunctionFieldCoeff (p ^ a) K)
      (modularFunctionFieldCoeff (p ^ (a + 1)) K) = if a = 0 then p + 1 else p := by
  have hcast (b : ℕ) : ((1 * p ^ (b + 1) : ℕ) : K) ≠ 0 := by
    simpa only [Nat.cast_mul, Nat.cast_one, Nat.cast_pow, one_mul] using pow_ne_zero (b + 1) hpK
  have hbase : qExpand K p (jqModC K) ∉ modularFunctionFieldCoeff 1 K := by
    rw [coefficient_level_one_eq]
    exact prime_j_not_mem_rational_j_away_characteristic p K hpK
  induction a with
  | zero =>
    have h := residue_mixed_step_degree_of_previous K 1 p 0 hp.out.not_dvd_one (hcast 0)
      (fun b hb => by omega) (fun _ => hbase)
    simpa only [one_mul] using h
  | succ a ih =>
    have h := residue_mixed_step_degree_of_previous K 1 p (a + 1) hp.out.not_dvd_one (hcast (a + 1))
      (fun b hb => by
        have he : b = a := by omega
        subst b
        simpa only [one_mul] using ih)
      (fun he => False.elim (Nat.succ_ne_zero a he))
    simpa only [one_mul] using h

theorem residue_prime_power_relfinrank_eq_psi
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [hp : Fact p.Prime]
    (hpK : (p : K) ≠ 0) (a : ℕ) :
    relfinrank K⟮jqModC K⟯ (modularFunctionFieldCoeff (p ^ a) K) = dedekindPsi (p ^ a) := by
  induction a with
  | zero => rw [pow_zero, coefficient_level_one_eq, relfinrank_self, dedekindPsi_one]
  | succ a ih =>
    have hbase : K⟮jqModC K⟯ ≤ modularFunctionFieldCoeff (p ^ a) K :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jq_mem_coeff_field _ K))
    have htower := IntermediateField.relfinrank_mul_relfinrank hbase
      (coefficient_field_mono (pow_dvd_pow p (Nat.le_succ a)))
    rw [← htower, ih, residue_prime_power_step_relfinrank K p hpK a]
    by_cases ha : a = 0
    · simp only [ha, pow_zero, zero_add, pow_one, ↓reduceIte, dedekindPsi_one, one_mul]
      simpa only [dedekindPsi_one, one_mul] using
        (dedekindPsi_mul_prime_not_dvd hp.out hp.out.not_dvd_one).symm
    · rw [if_neg ha, pow_succ]
      exact (dedekindPsi_mul_prime_dvd (NeZero.ne (p ^ a)) hp.out (dvd_pow_self p ha)).symm

theorem coefficient_field_finrank_over_j_eq_relfinrank
    (N : ℕ) (K : Type*) [Field K] :
    Module.finrank (IntermediateField.adjoin K
      ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))) (modularFunctionFieldCoeff N K) =
        relfinrank K⟮jqModC K⟯ (modularFunctionFieldCoeff N K) := by
  let F := modularFunctionFieldCoeff N K
  let B₀ : IntermediateField K F := IntermediateField.adjoin K {jCoeff N K}
  have hB : lift B₀ = K⟮jqModC K⟯ := lift_adjoin_simple K F (jCoeff N K)
  have htop : lift (⊤ : IntermediateField K F) = F := lift_top K F
  have h := relfinrank_map_map B₀ (⊤ : IntermediateField K F) F.val
  change relfinrank (lift B₀) (lift (⊤ : IntermediateField K F)) = _ at h
  rw [hB, htop, relfinrank_top_right] at h
  exact h.symm

theorem finrank_coeff_over_j_prime_power_eq_psi
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime]
    (hpK : (p : K) ≠ 0) (a : ℕ) :
    Module.finrank (IntermediateField.adjoin K
      ({jCoeff (p ^ a) K} : Set (modularFunctionFieldCoeff (p ^ a) K)))
        (modularFunctionFieldCoeff (p ^ a) K) = dedekindPsi (p ^ a) := by
  rw [coefficient_field_finrank_over_j_eq_relfinrank]
  exact residue_prime_power_relfinrank_eq_psi K p hpK a

end
end Dubon2026.SourceFunctionField

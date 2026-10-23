import Dubon2026.SourceResidueCoprimeInduction
import Dubon2026.SourceResidueGenerationInduction
import Dubon2026.SourceResiduePrimePowerDegree

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
all-level residue degree. Lower divisor generation/degree derives coprime
prime nonmembership. The proved reverse-expansion recurrence then determines
every step of the actual mixed prime-power tower. No characteristic-zero
coefficient action is needed; the coefficient characteristic avoids the level. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField SourceLevelProjective
open scoped IntermediateField
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem residue_mixed_prime_power_step_relfinrank (M p : ℕ)
    [NeZero M] [hp : Fact p.Prime] (a : ℕ) (hpM : ¬ p ∣ M)
    (hMK : (M : K) ≠ 0) (hpK : (p : K) ≠ 0)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      modularFunctionFieldCoeff d K = IntermediateField.adjoin K
        ({jqModC K, qExpand K d (jqModC K)} : Set (LaurentSeries K)) ∧
      relfinrank K⟮jqModC K⟯ (modularFunctionFieldCoeff d K) = dedekindPsi d) :
    relfinrank (modularFunctionFieldCoeff (M * p ^ a) K)
      (modularFunctionFieldCoeff (M * p ^ (a + 1)) K) = if a = 0 then p + 1 else p := by
  have hcast (b : ℕ) : ((M * p ^ (b + 1) : ℕ) : K) ≠ 0 := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using mul_ne_zero hMK (pow_ne_zero (b + 1) hpK)
  have hbase := prime_j_not_mem_residue_coprime_of_divisor_induction M p hpM hMK hpK hall
  induction a with
  | zero =>
    exact residue_mixed_step_degree_of_previous K M p 0 hpM (hcast 0)
      (fun b hb => by omega) (fun _ => hbase)
  | succ a ih =>
    exact residue_mixed_step_degree_of_previous K M p (a + 1) hpM (hcast (a + 1))
      (fun b hb => by
        have he : b = a := by omega
        subst b
        exact ih)
      (fun he => False.elim (Nat.succ_ne_zero a he))

end
end Dubon2026.SourceFunctionField

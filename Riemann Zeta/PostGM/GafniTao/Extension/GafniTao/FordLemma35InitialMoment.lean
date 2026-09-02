import GafniTao.FordMomentEventually

/-!
# Ford Lemma 3.5: the initial mean value

This is the source bound `J_{k,k}(P) ≤ k! P^k`.  Equality of the first `k`
power sums is converted, through Newton's identities over `ℚ`, into equality
of multisets and hence a permutation of the source tuple.
-/

namespace GafniTao

noncomputable section

open Finset

theorem ford_elementary_eq_of_powerSums_eq_rat
    {d : ℕ} (c c' : Fin d → ℚ)
    (hpow : ∀ r, 1 ≤ r → r ≤ d →
      fordPowerSum c r = fordPowerSum c' r) :
    ∀ r, r ≤ d → fordElementary c r = fordElementary c' r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro hrd
      by_cases hr0 : r = 0
      · subst r
        simp [fordElementary]
      · have hrpos : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
        have hrcast : (r : ℚ) ≠ 0 := by exact_mod_cast hr0
        have hc := ford_newton_identity c r
        have hc' := ford_newton_identity c' r
        apply (mul_left_cancel₀ hrcast)
        rw [hc, hc']
        congr 1
        apply Finset.sum_congr rfl
        intro a ha
        have haanti := (Finset.mem_filter.mp ha).1
        have halt := (Finset.mem_filter.mp ha).2
        have hasum := mem_antidiagonal.mp haanti
        have ha1le : a.1 ≤ d := le_trans (Nat.le_of_lt halt) hrd
        have helem := ih a.1 halt ha1le
        have hpower : fordPowerSum c a.2 = fordPowerSum c' a.2 := by
          by_cases ha20 : a.2 = 0
          · rw [ha20]
            simp [fordPowerSum]
          · apply hpow a.2 (Nat.one_le_iff_ne_zero.mpr ha20)
            omega
        rw [helem, hpower]

theorem ford_multiset_eq_of_powerSums_eq_rat
    {d : ℕ} (c c' : Fin d → ℚ)
    (hpow : ∀ r, 1 ≤ r → r ≤ d →
      fordPowerSum c r = fordPowerSum c' r) :
    Finset.univ.val.map c = Finset.univ.val.map c' := by
  have helem := ford_elementary_eq_of_powerSums_eq_rat c c' hpow
  have hpoly := fordRootPolynomial_eq_of_elementary_eq c c' helem
  have hroots := congrArg Polynomial.roots hpoly
  simpa only [fordRootPolynomial, Polynomial.roots_multiset_prod_X_sub_C] using hroots

theorem ford_power_solution_exists_perm
    {k Q : ℕ} (v : FordPowerSolution k k Q) :
    ∃ σ : Equiv.Perm (Fin k), v.1.2 = v.1.1 ∘ σ := by
  let x : Fin k → ℚ := fun i => ((v.1.1 i : ℕ) + 1 : ℚ)
  let y : Fin k → ℚ := fun i => ((v.1.2 i : ℕ) + 1 : ℚ)
  have hpow : ∀ r, 1 ≤ r → r ≤ k →
      fordPowerSum x r = fordPowerSum y r := by
    intro r hr hrk
    let j : Fin k := ⟨r - 1, by omega⟩
    have hv := congrFun v.2 j
    simp only [fordVinogradovPowerVector, j] at hv
    have hv' :
        (∑ i : Fin k, (((v.1.1 i : ℕ) + 1 : ℤ) ^ r)) =
          ∑ i : Fin k, (((v.1.2 i : ℕ) + 1 : ℤ) ^ r) := by
      simpa [show r - 1 + 1 = r by omega] using hv
    simp only [fordPowerSum, x, y]
    exact_mod_cast hv'
  have hmulti := ford_multiset_eq_of_powerSums_eq_rat x y hpow
  obtain ⟨σ, hσ⟩ := ford_exists_perm_of_multiset_eq x y hmulti
  refine ⟨σ, funext fun i => Fin.ext ?_⟩
  have hi := congrFun hσ i
  simp only [x, y, Function.comp_apply] at hi
  have hiNat : (v.1.2 i : ℕ) + 1 = (v.1.1 (σ i) : ℕ) + 1 := by
    exact_mod_cast hi
  change (v.1.2 i : ℕ) = (v.1.1 (σ i) : ℕ)
  omega

def fordInitialMomentMap (k Q : ℕ) :
    FordVinogradovTuple k Q × Equiv.Perm (Fin k) → FordPowerSolution k k Q :=
  fun u => ⟨(u.1, u.1 ∘ u.2), by
    funext j
    unfold fordVinogradovPowerVector
    simpa only [Function.comp_apply] using
      (Equiv.sum_comp u.2
        (fun i => (((u.1 i : ℕ) + 1 : ℤ) ^ ((j : ℕ) + 1)))).symm⟩

theorem fordInitialMomentMap_surjective (k Q : ℕ) :
    Function.Surjective (fordInitialMomentMap k Q) := by
  intro v
  obtain ⟨σ, hσ⟩ := ford_power_solution_exists_perm v
  refine ⟨(v.1.1, σ), Subtype.ext ?_⟩
  exact Prod.ext rfl hσ.symm

/-- Ford's initial `J_{k,k}` bound at integral endpoints. -/
theorem fordVinogradovMomentNat_initial_le (k Q : ℕ) :
    fordVinogradovMomentNat k k Q ≤ k.factorial * Q ^ k := by
  rw [← card_fordPowerSolution]
  calc
    Nat.card (FordPowerSolution k k Q) ≤
        Nat.card (FordVinogradovTuple k Q × Equiv.Perm (Fin k)) :=
      Nat.card_le_card_of_surjective (fordInitialMomentMap k Q)
        (fordInitialMomentMap_surjective k Q)
    _ = k.factorial * Q ^ k := by
      rw [Nat.card_prod, Nat.card_perm, Nat.card_fin]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
      ring

/-- Ford's initial permissible exponent
`Delta_1 = k^2(1-1/k)/2`, in its cancellation-safe form. -/
def fordDeltaInitial35 (k : ℕ) : ℝ :=
  ((k : ℝ) ^ 2 - k) / 2

theorem fordDeltaInitial35_source_form {k : ℕ} (hk : 0 < k) :
    fordDeltaInitial35 k =
      (1 / 2 : ℝ) * (k : ℝ) ^ 2 * (1 - 1 / (k : ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  unfold fordDeltaInitial35
  field_simp [hk0]

theorem fordLambda34_initial (k : ℕ) :
    fordLambda34 k k (fordDeltaInitial35 k) = k := by
  unfold fordLambda34 fordDeltaInitial35
  ring

theorem fordVinogradovMomentBound_initial (k : ℕ) :
    FordVinogradovMomentBound k k (k.factorial : ℝ) (fordDeltaInitial35 k) := by
  intro Q hQ
  have h := fordVinogradovMomentNat_initial_le k Q
  rw [fordLambda34_initial]
  exact_mod_cast h

#print axioms ford_elementary_eq_of_powerSums_eq_rat
#print axioms ford_multiset_eq_of_powerSums_eq_rat
#print axioms ford_power_solution_exists_perm
#print axioms fordVinogradovMomentNat_initial_le
#print axioms fordVinogradovMomentBound_initial

end

end GafniTao

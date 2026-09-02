import GafniTao.FordLemma34Step

/-!
# Ford Lemma 3.4: the terminal `L_s` branch

When `P < p^r`, every polynomial-coordinate congruence in (3.2) is an
equality.  The remaining variables form an exact Vinogradov solution.  The
source bound `L_s ≤ P^k J_{s,k}(Q)` is therefore a finite injection, proved
here without a cardinality surrogate.
-/

namespace GafniTao

noncomputable section

theorem fordL_terminal_polynomial_coordinates_eq
    {k d T s P Q p q r : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hPpr : P < p ^ r)
    (v : FordLSolution Ψ s P Q p q r) :
    v.1.1.1 = v.1.1.2 := by
  funext i
  apply Fin.ext
  have hcong := v.2.1 i
  have hzP : fordBoxValue v.1.1.1 i ≤ P := by
    unfold fordBoxValue
    omega
  have hwP : fordBoxValue v.1.1.2 i ≤ P := by
    unfold fordBoxValue
    omega
  have hzlt : fordBoxValue v.1.1.1 i < p ^ r := hzP.trans_lt hPpr
  have hwlt : fordBoxValue v.1.1.2 i < p ^ r := hwP.trans_lt hPpr
  unfold Nat.ModEq at hcong
  rw [Nat.mod_eq_of_lt hzlt, Nat.mod_eq_of_lt hwlt] at hcong
  unfold fordBoxValue at hcong
  omega

theorem fordL_terminal_power_solution
    {k d T s P Q p q r : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hp : 0 < p) (hq : 0 < q) (hPpr : P < p ^ r)
    (v : FordLSolution Ψ s P Q p q r) :
    fordVinogradovPowerVector s k Q v.1.2.1 =
      fordVinogradovPowerVector s k Q v.1.2.2 := by
  funext j
  have hzw := fordL_terminal_polynomial_coordinates_eq Ψ hPpr v
  have heq := v.2.2 j
  rw [hzw] at heq
  have hpower : fordPowerDifference v.1.2.1 v.1.2.2 ((j : ℕ) + 1) = 0 := by
    have hbase : (((p * q : ℕ) : ℤ) ^ ((j : ℕ) + 1)) ≠ 0 := by
      positivity
    unfold fordPolynomialDifference at heq
    simp only [sub_self, Finset.sum_const_zero, zero_add] at heq
    exact (mul_eq_zero.mp heq).resolve_left hbase
  unfold fordPowerDifference at hpower
  rw [Finset.sum_sub_distrib] at hpower
  unfold fordVinogradovPowerVector
  exact sub_eq_zero.mp hpower

def fordLTerminalMap
    {k d T s P Q p q r : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hp : 0 < p) (hq : 0 < q) (hPpr : P < p ^ r) :
    FordLSolution Ψ s P Q p q r →
      FordBox k P × FordPowerSolution s k Q :=
  fun v => (v.1.1.1,
    ⟨v.1.2, fordL_terminal_power_solution Ψ hp hq hPpr v⟩)

theorem fordLTerminalMap_injective
    {k d T s P Q p q r : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hp : 0 < p) (hq : 0 < q) (hPpr : P < p ^ r) :
    Function.Injective
      (fordLTerminalMap (s := s) (Q := Q) Ψ hp hq hPpr :
        FordLSolution Ψ s P Q p q r →
          FordBox k P × FordPowerSolution s k Q) := by
  intro v w hvw
  have hz : v.1.1.1 = w.1.1.1 :=
    congrArg (fun u : FordBox k P × FordPowerSolution s k Q => u.1) hvw
  have hxy : v.1.2 = w.1.2 := by
    exact congrArg
      (fun u : FordBox k P × FordPowerSolution s k Q => u.2.1) hvw
  have hvzw := fordL_terminal_polynomial_coordinates_eq Ψ hPpr v
  have hwzw := fordL_terminal_polynomial_coordinates_eq Ψ hPpr w
  apply Subtype.ext
  rcases v with ⟨⟨⟨vz, vw⟩, vxy⟩, hv⟩
  rcases w with ⟨⟨⟨wz, ww⟩, wxy⟩, hw⟩
  change vz = wz at hz
  change vxy = wxy at hxy
  change vz = vw at hvzw
  change wz = ww at hwzw
  simp only [Prod.mk.injEq]
  exact ⟨⟨hz, hvzw.symm.trans (hz.trans hwzw)⟩, hxy⟩

/-- The terminal estimate in the first paragraph of Ford's induction. -/
theorem fordLCount_terminal_le
    {k d T s P Q p q r : ℕ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hp : 0 < p) (hq : 0 < q) (hPpr : P < p ^ r) :
    fordLCount Ψ s P Q p q r ≤
      P ^ k * fordVinogradovMomentNat s k Q := by
  have hcard :
      Nat.card (FordLSolution Ψ s P Q p q r) ≤
        Nat.card (FordBox k P × FordPowerSolution s k Q) :=
    Nat.card_le_card_of_injective _
      (fordLTerminalMap_injective Ψ hp hq hPpr)
  calc
    fordLCount Ψ s P Q p q r =
        Nat.card (FordLSolution Ψ s P Q p q r) := by
      rw [Nat.card_eq_fintype_card]
      rfl
    _ ≤ Nat.card (FordBox k P × FordPowerSolution s k Q) := hcard
    _ = P ^ k * fordVinogradovMomentNat s k Q := by
      rw [Nat.card_prod, card_fordPowerSolution]
      simp [Nat.card_eq_fintype_card]

/-- The source hypothesis on `J_{s,k}(Q)`, with Ford's exact exponent. -/
def FordVinogradovMomentBound
    (s k : ℕ) (C delta : ℝ) : Prop :=
  ∀ Q : ℕ, 1 ≤ Q →
    (fordVinogradovMomentNat s k Q : ℝ) ≤
      C * (Q : ℝ) ^ fordLambda34 s k delta

/-- Terminal (3.10), now consuming the actual moment-bound hypothesis. -/
theorem fordLCount_terminal_le_moment_bound
    {k d T s P Q p q r : ℕ} {C delta : ℝ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hp : 0 < p) (hq : 0 < q) (hPpr : P < p ^ r)
    (hQ : 1 ≤ Q) (hmoment : FordVinogradovMomentBound s k C delta) :
    (fordLCount Ψ s P Q p q r : ℝ) ≤
      C * (P : ℝ) ^ k * (Q : ℝ) ^ fordLambda34 s k delta := by
  have hterminal := fordLCount_terminal_le (s := s) (Q := Q) Ψ hp hq hPpr
  have hterminalR :
      (fordLCount Ψ s P Q p q r : ℝ) ≤
        (P : ℝ) ^ k * fordVinogradovMomentNat s k Q := by
    exact_mod_cast hterminal
  have hmomentQ := hmoment Q hQ
  calc
    (fordLCount Ψ s P Q p q r : ℝ) ≤
        (P : ℝ) ^ k * fordVinogradovMomentNat s k Q := hterminalR
    _ ≤ (P : ℝ) ^ k *
        (C * (Q : ℝ) ^ fordLambda34 s k delta) := by
      gcongr
    _ = C * (P : ℝ) ^ k *
        (Q : ℝ) ^ fordLambda34 s k delta := by ring

#print axioms fordL_terminal_polynomial_coordinates_eq
#print axioms fordL_terminal_power_solution
#print axioms fordLCount_terminal_le
#print axioms fordLCount_terminal_le_moment_bound

end

end GafniTao

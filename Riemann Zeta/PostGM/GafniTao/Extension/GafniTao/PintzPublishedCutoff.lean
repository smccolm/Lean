import GafniTao.PublishedExponentInputs

/-!
# Pintz's published near-one cells and the `23/24` cutoff

This module records Theorem 1' of Pintz (2023) in the exact exponent language
used by Gafni--Tao.  The cell inequalities are retained explicitly.  The
elementary consequence needed in Section 3 is then proved here: every cell
strictly below `eta = 1/24` has `k >= 5` and `ell >= 4`, so Pintz's coefficient
`max (3/(ell-1)) (4/(k-1))` is at most one.

`PintzTheoremOnePrime` is a source theorem interface, not an assumption hidden
inside a purported native result.  Its analytic proof is the remaining work
of this source branch.
-/

namespace GafniTao

/-- Pintz's exact two-parameter cell conditions, equations (2.3)--(2.4). -/
def PintzCell (eta : ℝ) (k ell : ℕ) : Prop :=
  4 ≤ k ∧ 3 ≤ ell ∧
  eta * k * (k - 1) < 1 ∧ 1 ≤ eta * (k + 1) * k ∧
  2 * eta * ell * (ell - 1) < 1 ∧ 1 ≤ 2 * eta * (ell + 1) * ell

private theorem exists_pintz_k
    {eta : ℝ} (heta : 0 < eta) (hetaUpper : eta < 1 / 12) :
    ∃ k : ℕ, 4 ≤ k ∧
      eta * k * (k - 1) < 1 ∧ 1 ≤ eta * (k + 1) * k := by
  let P : ℕ → Prop := fun n => 1 ≤ eta * (n + 1) * n
  have hP : ∃ n : ℕ, P n := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / eta)
    refine ⟨n, ?_⟩
    dsimp only [P]
    have hnPos : 0 < (n : ℝ) := by
      have : 0 < 1 / eta := one_div_pos.mpr heta
      exact this.trans hn
    have hetaN : 1 < eta * (n : ℝ) := by
      have h := (div_lt_iff₀ heta).mp hn
      nlinarith
    nlinarith
  let k : ℕ := Nat.find hP
  have hkLower : 1 ≤ eta * (k + 1) * k := Nat.find_spec hP
  have hkFour : 4 ≤ k := by
    by_contra hk
    have hkThree : k ≤ 3 := Nat.le_of_lt_succ (lt_of_not_ge hk)
    interval_cases k <;> norm_num at hkLower <;> nlinarith
  have hkPos : 1 ≤ k := by omega
  have hkPred : ¬ P (k - 1) :=
    Nat.find_min hP (Nat.sub_lt (by omega) (by omega))
  have hkUpperRaw : eta * ((k - 1 : ℕ) + 1) * (k - 1 : ℕ) < 1 :=
    lt_of_not_ge hkPred
  have hkUpper : eta * (k : ℝ) * ((k : ℝ) - 1) < 1 := by
    simpa [Nat.sub_add_cancel hkPos, Nat.cast_sub hkPos] using hkUpperRaw
  exact ⟨k, hkFour, hkUpper, hkLower⟩

private theorem exists_pintz_ell
    {eta : ℝ} (heta : 0 < eta) (hetaUpper : eta < 1 / 12) :
    ∃ ell : ℕ, 3 ≤ ell ∧
      2 * eta * ell * (ell - 1) < 1 ∧
      1 ≤ 2 * eta * (ell + 1) * ell := by
  let P : ℕ → Prop := fun n => 1 ≤ 2 * eta * (n + 1) * n
  have hP : ∃ n : ℕ, P n := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (2 * eta))
    refine ⟨n, ?_⟩
    dsimp only [P]
    have htwoEta : 0 < 2 * eta := mul_pos (by norm_num) heta
    have hnPos : 0 < (n : ℝ) := by
      have : 0 < 1 / (2 * eta) := one_div_pos.mpr htwoEta
      exact this.trans hn
    have hetaN : 1 < (2 * eta) * (n : ℝ) := by
      have h := (div_lt_iff₀ htwoEta).mp hn
      nlinarith
    nlinarith
  let ell : ℕ := Nat.find hP
  have hellLower : 1 ≤ 2 * eta * (ell + 1) * ell := Nat.find_spec hP
  have hellThree : 3 ≤ ell := by
    by_contra hell
    have hellTwo : ell ≤ 2 := Nat.le_of_lt_succ (lt_of_not_ge hell)
    interval_cases ell <;> norm_num at hellLower <;> nlinarith
  have hellPos : 1 ≤ ell := by omega
  have hellPred : ¬ P (ell - 1) :=
    Nat.find_min hP (Nat.sub_lt (by omega) (by omega))
  have hellUpperRaw :
      2 * eta * ((ell - 1 : ℕ) + 1) * (ell - 1 : ℕ) < 1 :=
    lt_of_not_ge hellPred
  have hellUpper : 2 * eta * (ell : ℝ) * ((ell : ℝ) - 1) < 1 := by
    simpa [Nat.sub_add_cancel hellPos, Nat.cast_sub hellPos] using hellUpperRaw
  exact ⟨ell, hellThree, hellUpper, hellLower⟩

/-- Every source parameter `0 < eta < 1/12` belongs to a unique adjacent
triangular cell in each of Pintz's two moment families.  Existence, rather
than uniqueness, is the interface needed by Theorem 1. -/
theorem exists_pintzCell
    {eta : ℝ} (heta : 0 < eta) (hetaUpper : eta < 1 / 12) :
    ∃ k ell : ℕ, PintzCell eta k ell := by
  obtain ⟨k, hkFour, hkUpper, hkLower⟩ :=
    exists_pintz_k heta hetaUpper
  obtain ⟨ell, hellThree, hellUpper, hellLower⟩ :=
    exists_pintz_ell heta hetaUpper
  exact ⟨k, ell, hkFour, hellThree, hkUpper, hkLower, hellUpper, hellLower⟩

/-- Pintz's source Proposition in Section 3 starts from the strict ordering
`k > ell`, forced by the two adjacent triangular cells. -/
theorem pintzCell_ell_lt_k
    {eta : ℝ} {k ell : ℕ} (hcell : PintzCell eta k ell) :
    ell < k := by
  rcases hcell with
    ⟨_hkFour, hellThree, _hkUpper, hkLower, hellUpper, _hellLower⟩
  have hellReal : (3 : ℝ) ≤ ell := by exact_mod_cast hellThree
  by_contra hnot
  have hkell : k ≤ ell := Nat.le_of_not_gt hnot
  have hkellReal : (k : ℝ) ≤ ell := by exact_mod_cast hkell
  have hkNonneg : (0 : ℝ) ≤ k := by positivity
  have hellNonneg : (0 : ℝ) ≤ ell := by positivity
  have hpoly : (k : ℝ) * ((k : ℝ) + 1) ≤
      (ell : ℝ) * ((ell : ℝ) + 1) := by nlinarith
  have hellCompare : (ell : ℝ) * ((ell : ℝ) + 1) ≤
      2 * (ell : ℝ) * ((ell : ℝ) - 1) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left
    (hpoly.trans hellCompare) (show 0 ≤ eta by
      by_contra heta
      have : eta < 0 := lt_of_not_ge heta
      nlinarith)]

/-- Exact source Proposition after Pintz equation (3.7): the ell-threshold
strictly exceeds the k-threshold.  This is the ordering used when the
Dirichlet polynomial is powered in equations (4.15)--(4.16). -/
theorem pintzCell_threshold_order
    {eta : ℝ} {k ell : ℕ} (hcell : PintzCell eta k ell) :
    1 / ((k : ℝ) * (1 - ((k : ℝ) - 1) * eta)) <
      1 / ((ell : ℝ) * (1 - 2 * eta * ((ell : ℝ) - 1))) := by
  have hellk : ell < k := pintzCell_ell_lt_k hcell
  rcases hcell with
    ⟨hkFour, hellThree, hkUpper, _hkLower, hellUpper, hellLower⟩
  have heta : 0 < eta := by
    have hellPos : (0 : ℝ) < ell := by exact_mod_cast (lt_of_lt_of_le (by omega) hellThree)
    have hfactor : 0 < (2 : ℝ) * (ell + 1) * ell := by positivity
    nlinarith
  have hkReal : (4 : ℝ) ≤ k := by exact_mod_cast hkFour
  have hellReal : (3 : ℝ) ≤ ell := by exact_mod_cast hellThree
  have hellkReal : (ell : ℝ) < k := by exact_mod_cast hellk
  let Dk : ℝ := (k : ℝ) * (1 - ((k : ℝ) - 1) * eta)
  let Dell : ℝ := (ell : ℝ) * (1 - 2 * eta * ((ell : ℝ) - 1))
  have hDkLower : (k : ℝ) - 1 < Dk := by
    dsimp only [Dk]
    nlinarith
  have hDellPos : 0 < Dell := by
    dsimp only [Dell]
    have hellPos : (0 : ℝ) < ell := by linarith
    have hparen : 0 < 1 - 2 * eta * ((ell : ℝ) - 1) := by
      nlinarith
    positivity
  have hDellUpper : Dell ≤ (ell : ℝ) - 1 / 2 := by
    dsimp only [Dell]
    have hfactorCompare : (ell : ℝ) + 1 ≤ 2 * ((ell : ℝ) - 1) := by
      linarith
    have htwoEtaEll : 0 ≤ 2 * eta * (ell : ℝ) := by positivity
    have hproduct := mul_le_mul_of_nonneg_left hfactorCompare htwoEtaEll
    nlinarith
  have hDen : Dell < Dk := by nlinarith
  simpa only [Dk, Dell] using one_div_lt_one_div_of_lt hDellPos hDen

/-- The slightly weakened coefficient in Pintz Theorem 1', equation (2.7). -/
noncomputable def pintzTheoremOnePrimeCoefficient (k ell : ℕ) : ℝ :=
  max (3 / ((ell : ℝ) - 1)) (4 / ((k : ℝ) - 1))

/-- The sharper coefficient in Pintz Theorem 1, equation (2.6). -/
noncomputable def pintzTheoremOneCoefficient
    (eta : ℝ) (k ell : ℕ) : ℝ :=
  max (3 / ((ell : ℝ) * (1 - 2 * ((ell : ℝ) - 1) * eta)))
    (4 / ((k : ℝ) * (1 - ((k : ℝ) - 1) * eta)))

/-- Source-faithful statement of Pintz Theorem 1. -/
def PintzTheoremOne : Prop :=
  ∀ eta : ℝ, 0 < eta → eta < 1 / 12 →
    ∃ k ell : ℕ, PintzCell eta k ell ∧
      EpsilonExponentBound
        (fun T => (zeroCount (1 - eta) T : ℝ))
        (pintzTheoremOneCoefficient eta k ell * eta)

/-- Source-faithful statement of Pintz Theorem 1'.  The count is the genuine
analytic-multiplicity zero count and the exponent is `B'(eta) * eta + eps`.
-/
def PintzTheoremOnePrime : Prop :=
  ∀ eta : ℝ, 0 < eta → eta < 1 / 12 →
    ∃ k ell : ℕ, PintzCell eta k ell ∧
      EpsilonExponentBound
        (fun T => (zeroCount (1 - eta) T : ℝ))
        (pintzTheoremOnePrimeCoefficient k ell * eta)

theorem pintzTheoremOneCoefficient_le_prime
    {eta : ℝ} {k ell : ℕ} (hcell : PintzCell eta k ell) :
    pintzTheoremOneCoefficient eta k ell ≤
      pintzTheoremOnePrimeCoefficient k ell := by
  rcases hcell with ⟨hk, hell, hkUpper, _hkLower, hellUpper, _hellLower⟩
  have hkReal : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hellReal : (3 : ℝ) ≤ ell := by exact_mod_cast hell
  have hkEta : eta * (k : ℝ) * ((k : ℝ) - 1) < 1 := by
    exact hkUpper
  have hellEta : 2 * eta * (ell : ℝ) * ((ell : ℝ) - 1) < 1 := by
    exact hellUpper
  have hkDenPos : 0 < (k : ℝ) * (1 - ((k : ℝ) - 1) * eta) := by
    have : 0 < 1 - ((k : ℝ) - 1) * eta := by
      nlinarith [show 0 < (k : ℝ) by linarith]
    positivity
  have hellDenPos :
      0 < (ell : ℝ) * (1 - 2 * ((ell : ℝ) - 1) * eta) := by
    have : 0 < 1 - 2 * ((ell : ℝ) - 1) * eta := by
      nlinarith [show 0 < (ell : ℝ) by linarith]
    positivity
  have hkPrimeDenPos : 0 < (k : ℝ) - 1 := by linarith
  have hellPrimeDenPos : 0 < (ell : ℝ) - 1 := by linarith
  unfold pintzTheoremOneCoefficient pintzTheoremOnePrimeCoefficient
  apply max_le
  · refine (show 3 / ((ell : ℝ) *
        (1 - 2 * ((ell : ℝ) - 1) * eta)) ≤ 3 / ((ell : ℝ) - 1) by
          rw [div_le_div_iff₀ hellDenPos hellPrimeDenPos]
          nlinarith).trans (le_max_left _ _)
  · refine (show 4 / ((k : ℝ) * (1 - ((k : ℝ) - 1) * eta)) ≤
        4 / ((k : ℝ) - 1) by
          rw [div_le_div_iff₀ hkDenPos hkPrimeDenPos]
          nlinarith).trans (le_max_right _ _)

/-- Pintz Theorem 1 implies the displayed Theorem 1′ by exponent
monotonicity and the two cell inequalities. -/
theorem pintzTheoremOnePrime_of_theoremOne
    (hPintz : PintzTheoremOne) : PintzTheoremOnePrime := by
  intro eta heta hetaUpper
  obtain ⟨k, ell, hcell, hEnvelope⟩ := hPintz eta heta hetaUpper
  refine ⟨k, ell, hcell, ?_⟩
  exact hEnvelope.mono_exponent
    (mul_le_mul_of_nonneg_right
      (pintzTheoremOneCoefficient_le_prime hcell) heta.le)

theorem pintzCell_k_ge_five_of_eta_lt_one_twentyFour
    {eta : ℝ} {k ell : ℕ} (heta : 0 < eta) (hetaUpper : eta < 1 / 24)
    (hcell : PintzCell eta k ell) :
    5 ≤ k := by
  rcases hcell with ⟨hk, _hell, _hkUpper, hkLower, _hellUpper, _hellLower⟩
  by_contra hnot
  have hkUpper : k ≤ 4 := Nat.le_of_lt_succ (lt_of_not_ge hnot)
  have hkEq : k = 4 := Nat.le_antisymm hkUpper hk
  subst k
  norm_num at hkLower
  nlinarith

theorem pintzCell_ell_ge_four_of_eta_lt_one_twentyFour
    {eta : ℝ} {k ell : ℕ} (hetaUpper : eta < 1 / 24)
    (hcell : PintzCell eta k ell) :
    4 ≤ ell := by
  rcases hcell with ⟨_hk, hell, _hkUpper, _hkLower, _hellUpper, hellLower⟩
  by_contra hnot
  have hellUpper : ell ≤ 3 := Nat.le_of_lt_succ (lt_of_not_ge hnot)
  have hellEq : ell = 3 := Nat.le_antisymm hellUpper hell
  subst ell
  norm_num at hellLower
  nlinarith

theorem pintzTheoremOnePrimeCoefficient_le_one
    {eta : ℝ} {k ell : ℕ} (heta : 0 < eta) (hetaUpper : eta < 1 / 24)
    (hcell : PintzCell eta k ell) :
    pintzTheoremOnePrimeCoefficient k ell ≤ 1 := by
  have hk : 5 ≤ k :=
    pintzCell_k_ge_five_of_eta_lt_one_twentyFour heta hetaUpper hcell
  have hell : 4 ≤ ell :=
    pintzCell_ell_ge_four_of_eta_lt_one_twentyFour hetaUpper hcell
  have hkReal : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hellReal : (4 : ℝ) ≤ ell := by exact_mod_cast hell
  have hkDen : 0 < (k : ℝ) - 1 := by linarith
  have hellDen : 0 < (ell : ℝ) - 1 := by linarith
  unfold pintzTheoremOnePrimeCoefficient
  apply max_le
  · rw [div_le_iff₀ hellDen]
    nlinarith
  · rw [div_le_iff₀ hkDen]
    nlinarith

/-- Pintz Theorem 1' implies exactly the strict `23/24` cutoff consumed by
the second Gafni--Tao sample. -/
theorem pintzTwentyThreeTwentyFourCutoff_of_theoremOnePrime
    (hPintz : PintzTheoremOnePrime) :
    PintzTwentyThreeTwentyFourCutoff := by
  intro sigma hsigmaLower hsigmaUpper
  let eta : ℝ := 1 - sigma
  have heta : 0 < eta := by dsimp only [eta]; linarith
  have hetaUpper : eta < 1 / 24 := by dsimp only [eta]; linarith
  have hetaTwelve : eta < 1 / 12 := by linarith
  obtain ⟨k, ell, hcell, hEnvelope⟩ := hPintz eta heta hetaTwelve
  have hCoeff : pintzTheoremOnePrimeCoefficient k ell ≤ 1 :=
    pintzTheoremOnePrimeCoefficient_le_one heta hetaUpper hcell
  unfold ZeroDensityEnvelope
  simpa only [eta, sub_sub_cancel, one_mul] using
    hEnvelope.mono_exponent
      (mul_le_mul_of_nonneg_right hCoeff heta.le)

#print axioms pintzTheoremOnePrimeCoefficient_le_one
#print axioms pintzCell_ell_lt_k
#print axioms pintzCell_threshold_order
#print axioms pintzTheoremOnePrime_of_theoremOne
#print axioms pintzTwentyThreeTwentyFourCutoff_of_theoremOnePrime

end GafniTao

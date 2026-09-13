import Tao2026.ExceptionalCharacterSelberg
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Heterogeneous exceptional-character families

This file formalizes the conductor bookkeeping in Tao's Lemma 5.1.  Every
member of the family has a primitive character of modulus `q₁ * q₂`, where
the common factor `q₁` and the varying factor `q₂` are coprime and squarefree.
The pair character is placed at the least common multiple of two such
moduli.  Its level is again squarefree and is at most `Z ^ 3.09` under Tao's
stated square-root bound for the varying factors.

The genuinely analytic input is deliberately not postulated here: a later
module must supply the Burgess prefix estimate for the nonprincipal pair
character.
-/

namespace Tao2026

open Complex
open scoped ComplexConjugate

noncomputable section

/-- The exponent `3.09` in the cubefree Burgess range used in Lemma 5.1. -/
def taoBurgessPeriodExponent : ℝ := 309 / 100

/-- The explicit saving `0.0163` in Tao's stated Burgess specialization. -/
def taoBurgessSavingExponent : ℝ := 163 / 10000

/-- The sieve level exponent `0.0001` selected in the proof of Lemma 5.1. -/
def taoExceptionalSieveLevelExponent : ℝ := 1 / 10000

/-- Exact exponent ledger behind the off-diagonal estimate:
`0.016 + 0.0001 + (1 - 0.0163) = 1 - 0.0002`. -/
theorem taoExceptionalOffDiagonalExponentLedger :
    (2 / 125 : ℝ) + taoExceptionalSieveLevelExponent +
        (1 - taoBurgessSavingExponent) =
      1 - 1 / 5000 := by
  norm_num [taoExceptionalSieveLevelExponent,
    taoBurgessSavingExponent]

/-- The `3.09` conductor exponent fits strictly below the `3.1` Burgess
range after losing the sieve exponent `0.0001` from the prefix length. -/
theorem taoExceptionalPeriodExponent_lt_burgessRange :
    taoBurgessPeriodExponent <
      (31 / 10 : ℝ) * (1 - taoExceptionalSieveLevelExponent) := by
  norm_num [taoBurgessPeriodExponent, taoExceptionalSieveLevelExponent]

/-- One member of Tao's exceptional-character family.  The common factor
`q₁` and scale `Z` are indices so that the character really has the dependent
level `q₁ * q₂`. -/
structure TaoExceptionalCharacterDatum (q₁ Z : ℕ) where
  q₂ : ℕ
  q₂_squarefree : Squarefree q₂
  q₁_coprime_q₂ : q₁.Coprime q₂
  q₂_le_sqrt :
    (q₂ : ℝ) ≤ Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ : ℝ))
  χ : DirichletCharacter ℂ (q₁ * q₂)
  χ_primitive : DirichletCharacter.IsPrimitive χ

/-- The modulus of one member of the heterogeneous family. -/
def TaoExceptionalCharacterDatum.period {q₁ Z : ℕ}
    (a : TaoExceptionalCharacterDatum q₁ Z) : ℕ :=
  q₁ * a.q₂

/-- Evaluation of a family member on a natural number. -/
def TaoExceptionalCharacterDatum.value {q₁ Z : ℕ}
    (a : TaoExceptionalCharacterDatum q₁ Z) (n : ℕ) : ℂ :=
  a.χ (n : ZMod (q₁ * a.q₂))

theorem TaoExceptionalCharacterDatum.q₂_pos {q₁ Z : ℕ}
    (a : TaoExceptionalCharacterDatum q₁ Z) :
    0 < a.q₂ :=
  Nat.pos_of_ne_zero a.q₂_squarefree.ne_zero

theorem TaoExceptionalCharacterDatum.period_pos {q₁ Z : ℕ}
    (a : TaoExceptionalCharacterDatum q₁ Z) (hq₁ : 0 < q₁) :
    0 < a.period := by
  exact Nat.mul_pos hq₁ a.q₂_pos

theorem TaoExceptionalCharacterDatum.period_squarefree {q₁ Z : ℕ}
    (a : TaoExceptionalCharacterDatum q₁ Z) (hq₁ : Squarefree q₁) :
    Squarefree a.period := by
  exact (Nat.squarefree_mul a.q₁_coprime_q₂).2
    ⟨hq₁, a.q₂_squarefree⟩

theorem TaoExceptionalCharacterDatum.norm_value_le_one {q₁ Z : ℕ}
    (a : TaoExceptionalCharacterDatum q₁ Z) (n : ℕ) :
    ‖a.value n‖ ≤ 1 := by
  exact a.χ.norm_le_one (n : ZMod (q₁ * a.q₂))

theorem TaoExceptionalCharacterDatum.value_mul {q₁ Z : ℕ}
    (a : TaoExceptionalCharacterDatum q₁ Z) (m n : ℕ) :
    a.value (m * n) = a.value m * a.value n := by
  simp only [TaoExceptionalCharacterDatum.value, Nat.cast_mul, map_mul]

/-- The lcm of two squarefree natural numbers is squarefree. -/
theorem squarefree_nat_lcm {m n : ℕ}
    (hm : Squarefree m) (hn : Squarefree n) :
    Squarefree (m.lcm n) := by
  refine Nat.squarefree_of_factorization_le_one
    (Nat.lcm_ne_zero hm.ne_zero hn.ne_zero) ?_
  intro p
  rw [Nat.factorization_lcm hm.ne_zero hn.ne_zero]
  exact sup_le (hm.natFactorization_le_one p) (hn.natFactorization_le_one p)

/-- The common level at which the quotient of two family members is a single
Dirichlet character. -/
def taoExceptionalPairPeriod {q₁ Z : ℕ}
    (a b : TaoExceptionalCharacterDatum q₁ Z) : ℕ :=
  a.period.lcm b.period

theorem taoExceptionalPairPeriod_eq_common_mul_lcm {q₁ Z : ℕ}
    (a b : TaoExceptionalCharacterDatum q₁ Z) :
    taoExceptionalPairPeriod a b = q₁ * a.q₂.lcm b.q₂ := by
  exact Nat.lcm_mul_left q₁ a.q₂ b.q₂

theorem taoExceptionalPairPeriod_pos {q₁ Z : ℕ}
    (a b : TaoExceptionalCharacterDatum q₁ Z) (hq₁ : 0 < q₁) :
    0 < taoExceptionalPairPeriod a b := by
  exact Nat.lcm_pos (a.period_pos hq₁) (b.period_pos hq₁)

theorem taoExceptionalPairPeriod_squarefree {q₁ Z : ℕ}
    (a b : TaoExceptionalCharacterDatum q₁ Z) (hq₁ : Squarefree q₁) :
    Squarefree (taoExceptionalPairPeriod a b) := by
  exact squarefree_nat_lcm (a.period_squarefree hq₁)
    (b.period_squarefree hq₁)

theorem taoExceptionalPairPeriod_le_product {q₁ Z : ℕ}
    (a b : TaoExceptionalCharacterDatum q₁ Z) :
    taoExceptionalPairPeriod a b ≤ q₁ * a.q₂ * b.q₂ := by
  rw [taoExceptionalPairPeriod_eq_common_mul_lcm]
  have hlcm : a.q₂.lcm b.q₂ ≤ a.q₂ * b.q₂ :=
    Nat.lcm_le_mul a.q₂_pos b.q₂_pos
  calc
    q₁ * a.q₂.lcm b.q₂ ≤ q₁ * (a.q₂ * b.q₂) :=
      Nat.mul_le_mul_left q₁ hlcm
    _ = q₁ * a.q₂ * b.q₂ := by simp [Nat.mul_assoc]

/-- Tao's two square-root bounds imply the required `Z ^ 3.09` bound for
the pair period. -/
theorem taoExceptionalPairPeriod_cast_le_rpow {q₁ Z : ℕ}
    (a b : TaoExceptionalCharacterDatum q₁ Z) (hq₁ : 0 < q₁) :
    (taoExceptionalPairPeriod a b : ℝ) ≤
      (Z : ℝ) ^ taoBurgessPeriodExponent := by
  let A : ℝ := (Z : ℝ) ^ taoBurgessPeriodExponent
  have hq₁Real : 0 < (q₁ : ℝ) := by exact_mod_cast hq₁
  have hquotNonneg : 0 ≤ A / (q₁ : ℝ) := by
    exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Z) _) hq₁Real.le
  have hab : (a.q₂ : ℝ) * (b.q₂ : ℝ) ≤ A / (q₁ : ℝ) := by
    calc
      (a.q₂ : ℝ) * (b.q₂ : ℝ) ≤
          Real.sqrt (A / (q₁ : ℝ)) * Real.sqrt (A / (q₁ : ℝ)) :=
        mul_le_mul a.q₂_le_sqrt b.q₂_le_sqrt
          (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      _ = A / (q₁ : ℝ) := by rw [Real.mul_self_sqrt hquotNonneg]
  have hmul : (q₁ : ℝ) * ((a.q₂ : ℝ) * (b.q₂ : ℝ)) ≤ A := by
    have := (le_div_iff₀ hq₁Real).mp hab
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  calc
    (taoExceptionalPairPeriod a b : ℝ) ≤
        ((q₁ * a.q₂ * b.q₂ : ℕ) : ℝ) := by
      exact_mod_cast taoExceptionalPairPeriod_le_product a b
    _ = (q₁ : ℝ) * ((a.q₂ : ℝ) * (b.q₂ : ℝ)) := by
      push_cast
      ring
    _ ≤ A := hmul

/-- The existence of one datum with Tao's square-root bound already implies
the source hypothesis `q₁ ≤ Z ^ 3.09`. -/
theorem taoExceptionalCommonFactor_cast_le_rpow {q₁ Z : ℕ}
    (a : TaoExceptionalCharacterDatum q₁ Z) (hq₁ : 0 < q₁) :
    (q₁ : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent := by
  calc
    (q₁ : ℝ) ≤ (a.period : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_right q₁ a.q₂_pos
    _ = (taoExceptionalPairPeriod a a : ℝ) := by
      simp [taoExceptionalPairPeriod]
    _ ≤ (Z : ℝ) ^ taoBurgessPeriodExponent :=
      taoExceptionalPairPeriod_cast_le_rpow a a hq₁

/-- Changing two character levels to their lcm and multiplying agrees on
natural inputs with multiplying their original values.  The nonunit case is
important here: a prime lost by one lift forces the other original character
value to vanish. -/
theorem dirichletCharacter_mul_apply_natCast
    {r s : ℕ} (χ : DirichletCharacter ℂ r)
    (ψ : DirichletCharacter ℂ s) (n : ℕ) :
    DirichletCharacter.mul χ ψ (n : ZMod (r.lcm s)) =
      χ (n : ZMod r) * ψ (n : ZMod s) := by
  unfold DirichletCharacter.mul
  by_cases hu : IsUnit (n : ZMod (r.lcm s))
  · let u : Units (ZMod (r.lcm s)) := hu.unit
    have huVal : (u : ZMod (r.lcm s)) = n := rfl
    rw [← huVal, MulChar.mul_apply,
      DirichletCharacter.changeLevel_eq_cast_of_dvd χ _ u,
      DirichletCharacter.changeLevel_eq_cast_of_dvd ψ _ u]
    rw [huVal, ZMod.cast_natCast (Nat.dvd_lcm_left r s) n,
      ZMod.cast_natCast (Nat.dvd_lcm_right r s) n]
  · have hnNotCoprime : ¬n.Coprime (r.lcm s) := by
      simpa only [ZMod.isUnit_iff_coprime] using hu
    have hbad : ¬n.Coprime r ∨ ¬n.Coprime s := by
      by_contra h
      push Not at h
      apply hnNotCoprime
      exact Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul r s)
        (h.1.mul_right h.2)
    rw [MulChar.mul_apply, MulChar.map_nonunit _ hu]
    rcases hbad with hr | hs
    · have hr' : ¬IsUnit (n : ZMod r) := by
        simpa only [ZMod.isUnit_iff_coprime] using hr
      simp [MulChar.map_nonunit χ hr']
    · have hs' : ¬IsUnit (n : ZMod s) := by
        simpa only [ZMod.isUnit_iff_coprime] using hs
      simp [MulChar.map_nonunit ψ hs']

/-- Complex conjugation of a Dirichlet-character value is evaluation of the
inverse character. -/
theorem dirichletCharacter_inv_apply_eq_conj
    {r : ℕ} (χ : DirichletCharacter ℂ r) (x : ZMod r) :
    χ⁻¹ x = conj (χ x) := by
  by_cases hu : IsUnit x
  · rw [MulChar.inv_apply_eq_inv', Complex.inv_eq_conj]
    simpa only [← χ.toUnitHom_eq_char' hu] using χ.unit_norm_eq_one hu.unit
  · rw [MulChar.map_nonunit χ hu, MulChar.map_nonunit χ⁻¹ hu, map_zero]

/-- The quotient character attached to an ordered pair of family members. -/
def taoExceptionalPairCharacter {q₁ Z : ℕ}
    (a b : TaoExceptionalCharacterDatum q₁ Z) :
    DirichletCharacter ℂ (taoExceptionalPairPeriod a b) :=
  DirichletCharacter.mul a.χ b.χ⁻¹

/-- The pair correlation is exactly the value of one Dirichlet character at
the lcm period. -/
theorem taoExceptionalPairCharacter_apply_natCast {q₁ Z : ℕ}
    (a b : TaoExceptionalCharacterDatum q₁ Z) (n : ℕ) :
    taoExceptionalPairCharacter a b
        (n : ZMod (taoExceptionalPairPeriod a b)) =
      a.value n * conj (b.value n) := by
  simp only [taoExceptionalPairCharacter, taoExceptionalPairPeriod,
    TaoExceptionalCharacterDatum.period]
  calc
    DirichletCharacter.mul a.χ b.χ⁻¹
        (n : ZMod ((q₁ * a.q₂).lcm (q₁ * b.q₂))) =
        a.χ (n : ZMod (q₁ * a.q₂)) *
          b.χ⁻¹ (n : ZMod (q₁ * b.q₂)) :=
      dirichletCharacter_mul_apply_natCast a.χ b.χ⁻¹ n
    _ = a.value n * conj (b.value n) := by
      unfold TaoExceptionalCharacterDatum.value
      rw [dirichletCharacter_inv_apply_eq_conj]

/-- Prefix correlations of two heterogeneous family members are ordinary
prefix sums of their single pair character. -/
theorem sum_Ioc_exceptional_value_mul_conj_eq_pairCharacter
    {q₁ Z : ℕ} (a b : TaoExceptionalCharacterDatum q₁ Z) (N : ℕ) :
    (∑ m ∈ Finset.Ioc 0 N, a.value m * conj (b.value m)) =
      ∑ m ∈ Finset.Ioc 0 N,
        taoExceptionalPairCharacter a b
          (m : ZMod (taoExceptionalPairPeriod a b)) := by
  apply Finset.sum_congr rfl
  intro m hm
  exact (taoExceptionalPairCharacter_apply_natCast a b m).symm

theorem taoExceptionalPairCharacter_conductor_dvd_period {q₁ Z : ℕ}
    (a b : TaoExceptionalCharacterDatum q₁ Z) :
    (taoExceptionalPairCharacter a b).conductor ∣
      taoExceptionalPairPeriod a b :=
  (taoExceptionalPairCharacter a b).conductor_dvd_level

/-- Unequal lifts give a nonprincipal pair character.  Separating primitive
characters into unequal lifts is an arithmetic statement proved downstream. -/
theorem taoExceptionalPairCharacter_ne_one_of_changeLevel_ne {q₁ Z : ℕ}
    (a b : TaoExceptionalCharacterDatum q₁ Z)
    (hne :
      DirichletCharacter.changeLevel
          (Nat.dvd_lcm_left a.period b.period) a.χ ≠
        DirichletCharacter.changeLevel
          (Nat.dvd_lcm_right a.period b.period) b.χ) :
    taoExceptionalPairCharacter a b ≠ 1 := by
  intro hprincipal
  apply hne
  apply mul_inv_eq_one.mp
  simpa [taoExceptionalPairCharacter, DirichletCharacter.mul, map_inv] using
    hprincipal

/-- Pairwise separation at the common lcm level.  This is the exact
nonduplication condition on a finite family needed to make every off-diagonal
quotient character nonprincipal. -/
def IsSeparatedTaoExceptionalFamily {q₁ Z : ℕ}
    (W : Finset (TaoExceptionalCharacterDatum q₁ Z)) : Prop :=
  ∀ a ∈ W, ∀ b ∈ W, b ≠ a →
    DirichletCharacter.changeLevel
        (Nat.dvd_lcm_left a.period b.period) a.χ ≠
      DirichletCharacter.changeLevel
        (Nat.dvd_lcm_right a.period b.period) b.χ

/-- The remaining analytic input to Lemma 5.1: a uniform prefix estimate for
every nonprincipal character of squarefree level in the `Z ^ 3.09` range. -/
def TaoCubefreeCharacterPrefixBound (Z : ℕ) (E : ℝ) : Prop :=
  ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (N : ℕ),
    Squarefree q →
    (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent →
    χ ≠ 1 →
    N ≤ 2 * Z →
    ‖∑ n ∈ Finset.Ioc 0 N, χ (n : ZMod q)‖ ≤ E

/-- The Selberg/BHM conclusion for a heterogeneous primitive-character
family, reduced exactly to prefix estimates for the associated pair
characters. -/
theorem sum_finiteNormalizedPrimeBandSum_sq_le_exceptionalFamily
    {q₁ R Z : ℕ} (hR : 1 < R) (hRZ : R < Z)
    (W : Finset (TaoExceptionalCharacterDatum q₁ Z)) (E : ℝ)
    (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hE : 0 ≤ E)
    (hpair : ∀ a ∈ W, ∀ b ∈ W, b ≠ a →
      ∀ d ∈ (primorial R).divisors, (d : ℝ) ≤ R →
        ‖∑ m ∈ Finset.Ioc 0 ((2 * Z - 1) / d),
            taoExceptionalPairCharacter a b
              (m : ZMod (taoExceptionalPairPeriod a b))‖ ≤ E) :
    ∑ a ∈ W,
        ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 ≤
      ((((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
          (R : ℝ) * (1 + Real.log R) ^ 3) +
        ((W.card - 1 : ℕ) : ℝ) *
          (((R : ℝ) * (1 + Real.log R) ^ 3) * E)) /
        (taoDyadicPrimeBand Z).card := by
  classical
  apply sum_finiteNormalizedPrimeBandSum_sq_le_selberg_of_baseCorrelations
    R Z hR hRZ W (fun a ↦ a.value) E hZ hE
  · intro a ha n
    exact a.norm_value_le_one n
  · intro a ha m d
    exact a.value_mul m d
  · intro a ha b hb hba d hd hdR
    rw [sum_Ioc_exceptional_value_mul_conj_eq_pairCharacter]
    exact hpair a ha b hb hba d hd hdR

/-- Complete arithmetic-and-sieve reduction of Tao's exceptional-character
family estimate to the single cubefree Burgess prefix-bound predicate. -/
theorem sum_finiteNormalizedPrimeBandSum_sq_le_exceptionalFamily_of_burgess
    {q₁ R Z : ℕ} (hR : 1 < R) (hRZ : R < Z)
    (hq₁ : Squarefree q₁)
    (W : Finset (TaoExceptionalCharacterDatum q₁ Z)) (E : ℝ)
    (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hE : 0 ≤ E)
    (hsep : IsSeparatedTaoExceptionalFamily W)
    (hburgess : TaoCubefreeCharacterPrefixBound Z E) :
    ∑ a ∈ W,
        ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 ≤
      ((((2 * Z : ℕ) : ℝ) * (2 / Real.log R) +
          (R : ℝ) * (1 + Real.log R) ^ 3) +
        ((W.card - 1 : ℕ) : ℝ) *
          (((R : ℝ) * (1 + Real.log R) ^ 3) * E)) /
        (taoDyadicPrimeBand Z).card := by
  apply sum_finiteNormalizedPrimeBandSum_sq_le_exceptionalFamily
    hR hRZ W E hZ hE
  intro a ha b hb hba d hd hdR
  apply hburgess (taoExceptionalPairPeriod a b)
    (taoExceptionalPairCharacter a b) ((2 * Z - 1) / d)
  · exact taoExceptionalPairPeriod_squarefree a b hq₁
  · exact taoExceptionalPairPeriod_cast_le_rpow a b
      (Nat.pos_of_ne_zero hq₁.ne_zero)
  · exact taoExceptionalPairCharacter_ne_one_of_changeLevel_ne a b
      (hsep a ha b hb hba)
  · exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)


end

end Tao2026

import Tao2026.BurgessWeilPrimeFourRoots

/-!
# Sharp Kummer form of the prime Burgess boundary

This file records the exact one-variable multiplicative-character estimate
used in the prime step of Burgess's argument.  For a split polynomial which
is not a nonzero scalar multiple of an `orderOf χ`-th power, its complete
character sum is bounded by one less than the number of distinct geometric
roots times `sqrt p`.

The algebraic bridge below proves that the already constructed tagged root,
whose multiplicity is not divisible by `orderOf χ`, rules out precisely that
exceptional power shape.  Thus this single sharp finite-field statement
implies the coarser split-polynomial contract used by the complete Burgess
development.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The exceptional shape excluded in the classical Kummer character-sum
estimate: a nonzero scalar multiple of a power of exponent `orderOf χ`. -/
def IsMulCharOrderScalarPower
    {p : ℕ} [NeZero p] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) : Prop :=
  ∃ c : ZMod p, c ≠ 0 ∧ ∃ Q : Polynomial (ZMod p),
    P = Polynomial.C c * Q ^ orderOf χ

/-- The distinct-root Kummer trace attached to a split polynomial. -/
def primeKummerRootCorrelation
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) : ℂ :=
  χ P.leadingCoeff *
    ∑ x : ZMod p, ∏ a ∈ P.roots.toFinset,
      χ (x - a) ^ P.rootMultiplicity a

/-- A split polynomial character sum written entirely in terms of its
distinct roots and their multiplicities.  This is the literal Kummer trace
normal form: the analytic estimate has no remaining polynomial-factorization
bookkeeping. -/
theorem primePolynomialCharacterCorrelation_eq_kummerRootCorrelation
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) :
    primePolynomialCharacterCorrelation p χ P =
      primeKummerRootCorrelation χ P := by
  unfold primeKummerRootCorrelation
  unfold primePolynomialCharacterCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [hP.eval_eq_prod_roots, map_mul,
    Finset.prod_multiset_map_count, map_prod]
  simp only [map_pow, Polynomial.count_roots]

/-- The canonical root-factor base obtained by dividing every root
multiplicity by the character order. -/
def kummerRootPowerBase
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) : Polynomial (ZMod p) :=
  ∏ a ∈ P.roots.toFinset,
    (Polynomial.X - Polynomial.C a) ^
      (P.rootMultiplicity a / orderOf χ)

/-- For a nonzero split polynomial, divisibility of every root multiplicity
by the character order constructs the exceptional scalar-power presentation.
Together with the converse below, this identifies the Kummer nondegeneracy
hypothesis exactly. -/
theorem isMulCharOrderScalarPower_of_splits_of_forall_dvd_rootMultiplicity
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) (hP : P.Splits)
    (hdiv : ∀ a ∈ P.roots.toFinset,
      orderOf χ ∣ P.rootMultiplicity a) :
    IsMulCharOrderScalarPower χ P := by
  refine ⟨P.leadingCoeff, leadingCoeff_ne_zero.mpr hP0,
    kummerRootPowerBase χ P, ?_⟩
  calc
    P = Polynomial.C P.leadingCoeff *
        (P.roots.map (Polynomial.X - Polynomial.C ·)).prod :=
      hP.eq_prod_roots
    _ = Polynomial.C P.leadingCoeff *
        kummerRootPowerBase χ P ^ orderOf χ := by
      congr 1
      rw [Finset.prod_multiset_map_count]
      simp only [Polynomial.count_roots, kummerRootPowerBase]
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro a ha
      rw [← pow_mul]
      congr 1
      exact (Nat.div_mul_cancel (hdiv a ha)).symm

/-- Exact split-polynomial specialization of the classical Kummer
multiplicative-character estimate.  Since `P.Splits`, `roots.toFinset.card`
is the number of distinct geometric roots. -/
def TaoPrimeKummerPolynomialWeilBound : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → ¬IsMulCharOrderScalarPower χ P →
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p

/-- A root multiplicity not divisible by the character order excludes a
nonzero scalar multiple of an order-th power. -/
theorem not_isMulCharOrderScalarPower_of_not_dvd_rootMultiplicity
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) (a : ZMod p)
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a) :
    ¬IsMulCharOrderScalarPower χ P := by
  rintro ⟨c, hc, Q, hP⟩
  have hP0 : P ≠ 0 := by
    intro hzero
    apply hnot
    rw [hzero, Polynomial.rootMultiplicity_zero]
    exact dvd_zero _
  have hQ0 : Q ≠ 0 := by
    intro hzero
    apply hP0
    simp [hP, hzero, zero_pow χ.orderOf_pos.ne']
  have hC0 : Polynomial.C c ≠ 0 := Polynomial.C_ne_zero.mpr hc
  have hmul : Polynomial.C c * Q ^ orderOf χ ≠ 0 :=
    mul_ne_zero hC0 (pow_ne_zero _ hQ0)
  apply hnot
  rw [hP, Polynomial.rootMultiplicity_mul hmul,
    Polynomial.rootMultiplicity_C,
    rootMultiplicity_pow_of_ne_zero Q a (orderOf χ) hQ0]
  simp only [zero_add]
  exact dvd_mul_right _ _

/-- The zero polynomial is always an exceptional scalar power. -/
theorem isMulCharOrderScalarPower_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) :
    IsMulCharOrderScalarPower χ 0 := by
  refine ⟨1, one_ne_zero, 0, ?_⟩
  simp [zero_pow χ.orderOf_pos.ne']

/-- Exact root-multiplicity characterization of Kummer nondegeneracy for a
nonzero split polynomial. -/
theorem not_isMulCharOrderScalarPower_iff_exists_not_dvd_rootMultiplicity
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP0 : P ≠ 0) (hP : P.Splits) :
    ¬IsMulCharOrderScalarPower χ P ↔
      ∃ a ∈ P.roots.toFinset,
        ¬orderOf χ ∣ P.rootMultiplicity a := by
  constructor
  · intro hnot
    by_contra hexists
    push Not at hexists
    exact hnot
      (isMulCharOrderScalarPower_of_splits_of_forall_dvd_rootMultiplicity
        χ P hP0 hP hexists)
  · rintro ⟨a, _ha, hnot⟩
    exact not_isMulCharOrderScalarPower_of_not_dvd_rootMultiplicity
      χ P a hnot

/-- The analytic Kummer estimate in its exact distinct-root trace normal
form.  All polynomial factorization and exceptional-power algebra has been
removed from this proposition. -/
def TaoPrimeKummerRootProductWeilBound : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)),
    χ ≠ 1 → P ≠ 0 → P.Splits →
    (∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a) →
    ‖primeKummerRootCorrelation χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p

/-- The sharp Kummer trace estimate is elementary for at most two distinct
roots: the one-root sum vanishes and the two-root sum is a Jacobi sum. -/
theorem primeKummerRootCorrelation_le_of_card_roots_le_two
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits)
    (hroot : ∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a)
    (hcard : P.roots.toFinset.card ≤ 2) :
    ‖primeKummerRootCorrelation χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
  rw [← primePolynomialCharacterCorrelation_eq_kummerRootCorrelation χ P hP]
  obtain ⟨a, ha, hnot⟩ := hroot
  have hcardPos : 0 < P.roots.toFinset.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hcases : P.roots.toFinset.card = 1 ∨
      P.roots.toFinset.card = 2 := by
    omega
  rcases hcases with hone | htwo
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hone
    have hac : a = c := by simpa [hc] using ha
    subst c
    rw [primeSplitPolynomialCorrelation_eq_zero_of_single_root
      p χ P a hP hnot hc, norm_zero, hone]
    norm_num
  · obtain ⟨u, v, huv, huvRoots⟩ := Finset.card_eq_two.mp htwo
    have hauv : a = u ∨ a = v := by simpa [huvRoots] using ha
    have hstrong :
        ‖primePolynomialCharacterCorrelation p χ P‖ ≤ Real.sqrt p := by
      rcases hauv with rfl | rfl
      · exact primeSplitPolynomialCorrelation_le_sqrt_of_two_roots
          p χ P a v huv hP hnot huvRoots
      · exact primeSplitPolynomialCorrelation_le_sqrt_of_two_roots
          p χ P a u huv.symm hP hnot (by
            simpa [Finset.pair_comm] using huvRoots)
    calc
      ‖primePolynomialCharacterCorrelation p χ P‖ ≤ Real.sqrt p := hstrong
      _ = ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
        rw [htwo]
        norm_num

/-- For a split polynomial, divisibility of the total degree by the character
order is equivalent to divisibility of the sum of the active-root
multiplicities.  Inactive-root multiplicities are divisible termwise. -/
theorem orderOf_dvd_natDegree_iff_dvd_sum_primeActiveRoots_count
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) :
    orderOf χ ∣ P.natDegree ↔
      orderOf χ ∣
        ∑ a ∈ primeActiveRoots p χ P, P.roots.count a := by
  constructor
  · exact orderOf_dvd_sum_primeActiveRoots_count p χ P hP
  · intro hactive
    have hdisjoint :
        Disjoint (primeActiveRoots p χ P) (primeInactiveRoots p χ P) := by
      rw [Finset.disjoint_left]
      intro a haActive haInactive
      exact (Finset.mem_filter.mp haActive).2
        (Finset.mem_filter.mp haInactive).2
    have hinactive :
        orderOf χ ∣
          ∑ a ∈ primeInactiveRoots p χ P, P.roots.count a :=
      Finset.dvd_sum fun a ha => (Finset.mem_filter.mp ha).2
    have hsum :
        (∑ a ∈ P.roots.toFinset, P.roots.count a) =
          (∑ a ∈ primeActiveRoots p χ P, P.roots.count a) +
            ∑ a ∈ primeInactiveRoots p χ P, P.roots.count a := by
      rw [← primeActiveRoots_union_primeInactiveRoots p χ P,
        Finset.sum_union hdisjoint]
    have hsumAll :
        (∑ a ∈ P.roots.toFinset, P.roots.count a) = P.natDegree := by
      rw [Multiset.toFinset_sum_count_eq, ← hP.natDegree_eq_card_roots]
    rw [← hsumAll, hsum]
    exact dvd_add hactive hinactive

/-- The canonical four-point Kummer endpoint at one prime.  The four finite
local characters and their product are all nontrivial; this is precisely the
degree-nondivisible four-active-root case that is not covered by the
projective three-point reduction. -/
def TaoPrimeFourPointHypergeometricWeilBoundAt
    (p : ℕ) [NeZero p] [Fact p.Prime] : Prop :=
  ∀ (α β γ δ : MulChar (ZMod p) ℂ) (lam mu nu : ZMod p),
    α ≠ 1 → β ≠ 1 → γ ≠ 1 → δ ≠ 1 → α * β * γ * δ ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → nu ≠ 0 →
    lam ≠ mu → lam ≠ nu → mu ≠ nu →
    ‖∑ y : ZMod p,
      α y * β (y - lam) * γ (y - mu) * δ (y - nu)‖ ≤
      3 * Real.sqrt p

/-- The global four-point Kummer endpoint. -/
def TaoPrimeFourPointHypergeometricWeilBound : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime],
    TaoPrimeFourPointHypergeometricWeilBoundAt p

/-- The source-shaped four-point endpoint: all four finite local characters
are powers of the single Burgess character. -/
def TaoPrimePowerFourPointHypergeometricWeilBoundAt
    (p : ℕ) [NeZero p] [Fact p.Prime] : Prop :=
  ∀ (χ : MulChar (ZMod p) ℂ) (m n k l : ℕ) (lam mu nu : ZMod p),
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 →
    χ ^ (m + n + k + l) ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → nu ≠ 0 →
    lam ≠ mu → lam ≠ nu → mu ≠ nu →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ k) (y - mu) *
        (χ ^ l) (y - nu)‖ ≤
      3 * Real.sqrt p

/-- Only the large-characteristic range is used by the Burgess source. -/
def TaoPrimePowerFourPointHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime],
    64 < p → TaoPrimePowerFourPointHypergeometricWeilBoundAt p

/-- Finite exponent-range form of the source-shaped four-point endpoint. -/
def TaoPrimeReducedPowerFourPointHypergeometricWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime], 64 < p →
    ∀ (χ : MulChar (ZMod p) ℂ) (m n k l : ℕ) (lam mu nu : ZMod p),
    m < orderOf χ → n < orderOf χ → k < orderOf χ → l < orderOf χ →
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 →
    χ ^ (m + n + k + l) ≠ 1 →
    lam ≠ 0 → mu ≠ 0 → nu ≠ 0 →
    lam ≠ mu → lam ≠ nu → mu ≠ nu →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ k) (y - mu) *
        (χ ^ l) (y - nu)‖ ≤
      3 * Real.sqrt p

/-- Scaling by the first marked point puts a four-point sum into the
two-parameter Legendre form with finite points `0`, `1`, `t`, and `u`. -/
theorem fourPointMulCharSum_eq_legendreForm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ : MulChar (ZMod p) ℂ) (lam mu nu : ZMod p)
    (hlam : lam ≠ 0) :
    (∑ y : ZMod p,
      α y * β (y - lam) * γ (y - mu) * δ (y - nu)) =
      (α lam * β lam * γ lam * δ lam) *
        ∑ t : ZMod p,
          α t * β (t - 1) * γ (t - mu / lam) * δ (t - nu / lam) := by
  let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ lam hlam
  calc
    (∑ y : ZMod p,
        α y * β (y - lam) * γ (y - mu) * δ (y - nu)) =
        ∑ t : ZMod p,
          α (e t) * β (e t - lam) * γ (e t - mu) * δ (e t - nu) :=
      (Equiv.sum_comp e
        (fun y : ZMod p =>
          α y * β (y - lam) * γ (y - mu) * δ (y - nu))).symm
    _ = (α lam * β lam * γ lam * δ lam) *
        ∑ t : ZMod p,
          α t * β (t - 1) * γ (t - mu / lam) * δ (t - nu / lam) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      have hsubOne : lam * t - lam = lam * (t - 1) := by ring
      have hsubMu : lam * t - mu = lam * (t - mu / lam) := by
        field_simp
      have hsubNu : lam * t - nu = lam * (t - nu / lam) := by
        field_simp
      dsimp [e]
      rw [hsubOne, hsubMu, hsubNu, map_mul, map_mul, map_mul, map_mul]
      ring

/-- The final two-parameter analytic boundary for five active roots. -/
def TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime], 64 < p →
    ∀ (χ : MulChar (ZMod p) ℂ) (m n k l : ℕ) (t u : ZMod p),
    m < orderOf χ → n < orderOf χ → k < orderOf χ → l < orderOf χ →
    χ ^ m ≠ 1 → χ ^ n ≠ 1 → χ ^ k ≠ 1 → χ ^ l ≠ 1 →
    χ ^ (m + n + k + l) ≠ 1 →
    t ≠ 0 → u ≠ 0 → t ≠ 1 → u ≠ 1 → t ≠ u →
    ‖∑ y : ZMod p,
      (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - t) *
        (χ ^ l) (y - u)‖ ≤
      3 * Real.sqrt p

theorem TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour.toFourPoint
    (hweil :
      TaoPrimeReducedPowerFourPointLegendreWeilBoundAboveSixtyFour) :
    TaoPrimeReducedPowerFourPointHypergeometricWeilBoundAboveSixtyFour := by
  intro p _ _ hp χ m n k l lam mu nu hm hn hk hl
    hpowM hpowN hpowK hpowL hpowSum hlam hmu hnu hlammu hlamnu hmunu
  let t : ZMod p := mu / lam
  let u : ZMod p := nu / lam
  have ht0 : t ≠ 0 := div_ne_zero hmu hlam
  have hu0 : u ≠ 0 := div_ne_zero hnu hlam
  have ht1 : t ≠ 1 := by
    intro heq
    apply hlammu
    dsimp [t] at heq
    rw [div_eq_one_iff_eq hlam] at heq
    exact heq.symm
  have hu1 : u ≠ 1 := by
    intro heq
    apply hlamnu
    dsimp [u] at heq
    rw [div_eq_one_iff_eq hlam] at heq
    exact heq.symm
  have htu : t ≠ u := by
    intro heq
    apply hmunu
    dsimp [t, u] at heq
    exact (div_left_inj' hlam).mp heq
  have hbound := hweil p hp χ m n k l t u hm hn hk hl
    hpowM hpowN hpowK hpowL hpowSum ht0 hu0 ht1 hu1 htu
  rw [fourPointMulCharSum_eq_legendreForm
    p (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l) lam mu nu hlam]
  simp only [norm_mul]
  have hC :
      ‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ ≤ 1 := by
    calc
      ‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖ ≤
          1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one (χ ^ m) lam
        · exact DirichletCharacter.norm_le_one (χ ^ n) lam
        · exact DirichletCharacter.norm_le_one (χ ^ k) lam
        · exact DirichletCharacter.norm_le_one (χ ^ l) lam
      _ = 1 := by norm_num
  calc
    (‖(χ ^ m) lam‖ * ‖(χ ^ n) lam‖ * ‖(χ ^ k) lam‖ * ‖(χ ^ l) lam‖) *
          ‖∑ y : ZMod p,
            (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - mu / lam) *
              (χ ^ l) (y - nu / lam)‖ ≤
        1 * ‖∑ y : ZMod p,
          (χ ^ m) y * (χ ^ n) (y - 1) * (χ ^ k) (y - mu / lam) *
            (χ ^ l) (y - nu / lam)‖ := by
      gcongr
    _ ≤ 3 * Real.sqrt p := by simpa [t, u] using hbound

theorem TaoPrimeReducedPowerFourPointHypergeometricWeilBoundAboveSixtyFour.toPower
    (hweil :
      TaoPrimeReducedPowerFourPointHypergeometricWeilBoundAboveSixtyFour) :
    TaoPrimePowerFourPointHypergeometricWeilBoundAboveSixtyFour := by
  intro p _ _ hp χ m n k l lam mu nu hpowM hpowN hpowK hpowL hpowSum
    hlam hmu hnu hlammu hlamnu hmunu
  let m' := m % orderOf χ
  let n' := n % orderOf χ
  let k' := k % orderOf χ
  let l' := l % orderOf χ
  have hord : 0 < orderOf χ := orderOf_pos χ
  have hmLt : m' < orderOf χ := Nat.mod_lt m hord
  have hnLt : n' < orderOf χ := Nat.mod_lt n hord
  have hkLt : k' < orderOf χ := Nat.mod_lt k hord
  have hlLt : l' < orderOf χ := Nat.mod_lt l hord
  have hmEq : χ ^ m' = χ ^ m := pow_mod_orderOf χ m
  have hnEq : χ ^ n' = χ ^ n := pow_mod_orderOf χ n
  have hkEq : χ ^ k' = χ ^ k := pow_mod_orderOf χ k
  have hlEq : χ ^ l' = χ ^ l := pow_mod_orderOf χ l
  have hpowM' : χ ^ m' ≠ 1 := by simpa only [hmEq] using hpowM
  have hpowN' : χ ^ n' ≠ 1 := by simpa only [hnEq] using hpowN
  have hpowK' : χ ^ k' ≠ 1 := by simpa only [hkEq] using hpowK
  have hpowL' : χ ^ l' ≠ 1 := by simpa only [hlEq] using hpowL
  have hsumEq : χ ^ (m' + n' + k' + l') = χ ^ (m + n + k + l) := by
    rw [pow_add, pow_add, pow_add, pow_add, pow_add, pow_add,
      hmEq, hnEq, hkEq, hlEq]
  have hpowSum' : χ ^ (m' + n' + k' + l') ≠ 1 := by
    simpa only [hsumEq] using hpowSum
  have hbound := hweil p hp χ m' n' k' l' lam mu nu
    hmLt hnLt hkLt hlLt hpowM' hpowN' hpowK' hpowL' hpowSum'
      hlam hmu hnu hlammu hlamnu hmunu
  simpa only [hmEq, hnEq, hkEq, hlEq] using hbound

/-- Translation of a three-root character sum to the three-point form used by
the hypergeometric endpoint. -/
theorem threeRootMulCharSum_eq_threePointTranslate
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ : MulChar (ZMod p) ℂ) (a b c : ZMod p) :
    (∑ x : ZMod p, α (x - a) * β (x - b) * γ (x - c)) =
      ∑ y : ZMod p,
        α y * β (y - (b - a)) * γ (y - (c - a)) := by
  let e : ZMod p ≃ ZMod p := Equiv.addRight a
  calc
    (∑ x : ZMod p, α (x - a) * β (x - b) * γ (x - c)) =
        ∑ y : ZMod p,
          α (e y - a) * β (e y - b) * γ (e y - c) :=
      (Equiv.sum_comp e
        (fun x : ZMod p => α (x - a) * β (x - b) * γ (x - c))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _hy
      have hfirst : e y - a = y := by simp [e]
      have hsecond : e y - b = y - (b - a) := by
        dsimp [e]
        ring
      have hthird : e y - c = y - (c - a) := by
        dsimp [e]
        ring
      rw [hfirst, hsecond, hthird]

/-- Translation of a four-root character sum to the canonical finite points
`0`, `b-a`, `c-a`, and `d-a`. -/
theorem fourRootMulCharSum_eq_fourPointTranslate
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ : MulChar (ZMod p) ℂ) (a b c d : ZMod p) :
    (∑ x : ZMod p,
      α (x - a) * β (x - b) * γ (x - c) * δ (x - d)) =
      ∑ y : ZMod p,
        α y * β (y - (b - a)) * γ (y - (c - a)) *
          δ (y - (d - a)) := by
  let e : ZMod p ≃ ZMod p := Equiv.addRight a
  calc
    (∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d)) =
        ∑ y : ZMod p,
          α (e y - a) * β (e y - b) * γ (e y - c) * δ (e y - d) :=
      (Equiv.sum_comp e
        (fun x : ZMod p =>
          α (x - a) * β (x - b) * γ (x - c) * δ (x - d))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _hy
      have hfirst : e y - a = y := by simp [e]
      have hsecond : e y - b = y - (b - a) := by
        dsimp [e]
        ring
      have hthird : e y - c = y - (c - a) := by
        dsimp [e]
        ring
      have hfourth : e y - d = y - (d - a) := by
        dsimp [e]
        ring
      rw [hfirst, hsecond, hthird, hfourth]

set_option maxHeartbeats 1000000 in
/-- Pointwise five-root Möbius reduction away from the single deleted point.
When the five local characters multiply to one, sending the third root to
infinity leaves a four-point finite character product. -/
theorem fiveRootMobius_term
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε = 1)
    (a b c d e : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c) (hec : e ≠ c)
    (y : ZMod p) (hy : y ≠ 1) :
    let mob := threeRootMobiusEquiv p a c hac
    let lam := (a - b) / (c - b)
    let mu := (a - d) / (c - d)
    let nu := (a - e) / (c - e)
    α (mob.symm y - a) * β (mob.symm y - b) * γ (mob.symm y - c) *
        δ (mob.symm y - d) * ε (mob.symm y - e) =
      (α (c - a) * β (c - b) * γ (c - a) * δ (c - d) * ε (c - e)) *
        (α y * β (y - lam) * δ (y - mu) * ε (y - nu)) := by
  dsimp only
  rw [threeRootMobiusEquiv_symm_apply, if_neg hy]
  have hden : y - 1 ≠ 0 := sub_ne_zero.mpr hy
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
  have hcd : c - d ≠ 0 := sub_ne_zero.mpr hdc.symm
  have hce : c - e ≠ 0 := sub_ne_zero.mpr hec.symm
  have hxa : (y * c - a) / (y - 1) - a =
      y * (c - a) / (y - 1) := by field_simp; ring
  have hxb : (y * c - a) / (y - 1) - b =
      (c - b) * (y - (a - b) / (c - b)) / (y - 1) := by
    field_simp
    ring
  have hxc : (y * c - a) / (y - 1) - c =
      (c - a) / (y - 1) := by field_simp; ring
  have hxd : (y * c - a) / (y - 1) - d =
      (c - d) * (y - (a - d) / (c - d)) / (y - 1) := by
    field_simp
    ring
  have hxe : (y * c - a) / (y - 1) - e =
      (c - e) * (y - (a - e) / (c - e)) / (y - 1) := by
    field_simp
    ring
  rw [hxa, hxb, hxc, hxd, hxe]
  have hmapdivα (u v : ZMod p) : α (u / v) = α u / α v := by
    exact map_div₀ α.toMonoidWithZeroHom u v
  have hmapdivβ (u v : ZMod p) : β (u / v) = β u / β v := by
    exact map_div₀ β.toMonoidWithZeroHom u v
  have hmapdivγ (u v : ZMod p) : γ (u / v) = γ u / γ v := by
    exact map_div₀ γ.toMonoidWithZeroHom u v
  have hmapdivδ (u v : ZMod p) : δ (u / v) = δ u / δ v := by
    exact map_div₀ δ.toMonoidWithZeroHom u v
  have hmapdivε (u v : ZMod p) : ε (u / v) = ε u / ε v := by
    exact map_div₀ ε.toMonoidWithZeroHom u v
  rw [hmapdivα, map_mul, hmapdivβ, map_mul, hmapdivγ,
    hmapdivδ, map_mul, hmapdivε, map_mul]
  have hcancel :
      α (y - 1) * β (y - 1) * γ (y - 1) * δ (y - 1) * ε (y - 1) = 1 := by
    rw [← MulChar.mul_apply, ← MulChar.mul_apply, ← MulChar.mul_apply,
      ← MulChar.mul_apply, hprod]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hden)
  have hα : α (y - 1) ≠ 0 := by
    intro h
    rw [h, zero_mul, zero_mul, zero_mul, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hβ : β (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul, zero_mul, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hγ : γ (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hδ : δ (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hε : ε (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcancel
    exact zero_ne_one hcancel
  field_simp [hα, hβ, hγ, hδ, hε]
  linear_combination
    -(α y * α (c - a) * β (c - b) *
      β ((y * (c - b) - (a - b)) / (c - b)) * γ (c - a) *
      δ (c - d) * δ ((y * (c - d) - (a - d)) / (c - d)) *
      ε (c - e) * ε ((y * (c - e) - (a - e)) / (c - e))) * hcancel

/-- A degree-balanced five-root character sum is a canonical four-point sum
with one deleted projective point, up to a character-valued constant. -/
theorem fiveRootMulCharSum_eq_fourPointSum_sub
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β γ δ ε : MulChar (ZMod p) ℂ)
    (hprod : α * β * γ * δ * ε = 1)
    (a b c d e : ZMod p)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c) (hec : e ≠ c) :
    let lam := (a - b) / (c - b)
    let mu := (a - d) / (c - d)
    let nu := (a - e) / (c - e)
    (∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
          ε (x - e)) =
      (α (c - a) * β (c - b) * γ (c - a) * δ (c - d) * ε (c - e)) *
        ((∑ y : ZMod p,
            α y * β (y - lam) * δ (y - mu) * ε (y - nu)) -
          β (1 - lam) * δ (1 - mu) * ε (1 - nu)) := by
  dsimp only
  let mob := threeRootMobiusEquiv p a c hac
  let f : ZMod p → ℂ := fun x =>
    α (x - a) * β (x - b) * γ (x - c) * δ (x - d) * ε (x - e)
  let g : ZMod p → ℂ := fun y =>
    α y * β (y - (a - b) / (c - b)) *
      δ (y - (a - d) / (c - d)) * ε (y - (a - e) / (c - e))
  let C : ℂ :=
    α (c - a) * β (c - b) * γ (c - a) * δ (c - d) * ε (c - e)
  have hone : f (mob.symm 1) = 0 := by
    simp [f, mob, γ.map_zero]
  have hterm (y : ZMod p) (hy : y ∈ Finset.univ.erase 1) :
      f (mob.symm y) = C * g y := by
    have hyOne : y ≠ 1 := by simpa using hy
    simpa [f, g, C, mob] using
      fiveRootMobius_term p α β γ δ ε hprod a b c d e
        hac hbc hdc hec y hyOne
  calc
    (∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
          ε (x - e)) = ∑ x : ZMod p, f x := by rfl
    _ = ∑ y : ZMod p, f (mob.symm y) :=
      (Equiv.sum_comp mob.symm f).symm
    _ = ∑ y ∈ Finset.univ.erase 1, f (mob.symm y) := by
      exact (Finset.sum_erase (s := Finset.univ)
        (f := fun y => f (mob.symm y)) hone).symm
    _ = C * ∑ y ∈ Finset.univ.erase 1, g y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      exact hterm
    _ = C * ((∑ y : ZMod p, g y) - g 1) := by
      congr 1
      have h := Finset.sum_erase_add Finset.univ g
        (Finset.mem_univ (1 : ZMod p))
      linear_combination h
    _ = _ := by simp [C, g, MulChar.map_one]

/-- The four-point endpoint gives the sharp projective estimate for five
distinct roots whose local characters multiply to one. -/
theorem norm_fiveRootMulCharSum_le_three_mul_sqrt_add_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimeFourPointHypergeometricWeilBoundAt p)
    (α β γ δ ε : MulChar (ZMod p) ℂ)
    (hα : α ≠ 1) (hβ : β ≠ 1) (hγ : γ ≠ 1)
    (hδ : δ ≠ 1) (hε : ε ≠ 1)
    (hprod : α * β * γ * δ * ε = 1)
    (a b c d e : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hdc : d ≠ c) (hec : e ≠ c) (hde : d ≠ e) :
    ‖∑ x : ZMod p,
        α (x - a) * β (x - b) * γ (x - c) * δ (x - d) *
          ε (x - e)‖ ≤
      3 * Real.sqrt p + 1 := by
  let lam : ZMod p := (a - b) / (c - b)
  let mu : ZMod p := (a - d) / (c - d)
  let nu : ZMod p := (a - e) / (c - e)
  have hlam : lam ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hbc.symm)
  have hmu : mu ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr had) (sub_ne_zero.mpr hdc.symm)
  have hnu : nu ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hae) (sub_ne_zero.mpr hec.symm)
  have hlammu : lam ≠ mu := by
    intro heq
    have hcb : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
    have hcd : c - d ≠ 0 := sub_ne_zero.mpr hdc.symm
    dsimp [lam, mu] at heq
    rw [div_eq_div_iff hcb hcd] at heq
    have hzero : (a - c) * (b - d) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hzero with hac' | hbd'
    · exact hac (sub_eq_zero.mp hac')
    · exact hbd (sub_eq_zero.mp hbd')
  have hlamnu : lam ≠ nu := by
    intro heq
    have hcb : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
    have hce : c - e ≠ 0 := sub_ne_zero.mpr hec.symm
    dsimp [lam, nu] at heq
    rw [div_eq_div_iff hcb hce] at heq
    have hzero : (a - c) * (b - e) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hzero with hac' | hbe'
    · exact hac (sub_eq_zero.mp hac')
    · exact hbe (sub_eq_zero.mp hbe')
  have hmunu : mu ≠ nu := by
    intro heq
    have hcd : c - d ≠ 0 := sub_ne_zero.mpr hdc.symm
    have hce : c - e ≠ 0 := sub_ne_zero.mpr hec.symm
    dsimp [mu, nu] at heq
    rw [div_eq_div_iff hcd hce] at heq
    have hzero : (a - c) * (d - e) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hzero with hac' | hde'
    · exact hac (sub_eq_zero.mp hac')
    · exact hde (sub_eq_zero.mp hde')
  have hfiniteProd : α * β * δ * ε ≠ 1 := by
    intro heq
    apply hγ
    calc
      γ = 1 * γ := by simp
      _ = (α * β * δ * ε) * γ := by rw [heq]
      _ = α * β * γ * δ * ε := by ac_rfl
      _ = 1 := hprod
  have hfour :
      ‖∑ y : ZMod p,
        α y * β (y - lam) * δ (y - mu) * ε (y - nu)‖ ≤
          3 * Real.sqrt p :=
    hweil α β δ ε lam mu nu hα hβ hδ hε hfiniteProd
      hlam hmu hnu hlammu hlamnu hmunu
  rw [fiveRootMulCharSum_eq_fourPointSum_sub
    p α β γ δ ε hprod a b c d e hac hbc hdc hec]
  simp only [norm_mul]
  have hC :
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ *
          ‖δ (c - d)‖ * ‖ε (c - e)‖ ≤ 1 := by
    calc
      ‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ *
            ‖δ (c - d)‖ * ‖ε (c - e)‖ ≤ 1 * 1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one α (c - a)
        · exact DirichletCharacter.norm_le_one β (c - b)
        · exact DirichletCharacter.norm_le_one γ (c - a)
        · exact DirichletCharacter.norm_le_one δ (c - d)
        · exact DirichletCharacter.norm_le_one ε (c - e)
      _ = 1 := by norm_num
  have hdeleted :
      ‖β (1 - lam) * δ (1 - mu) * ε (1 - nu)‖ ≤ 1 := by
    simp only [norm_mul]
    calc
      ‖β (1 - lam)‖ * ‖δ (1 - mu)‖ * ‖ε (1 - nu)‖ ≤
          1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one β _
        · exact DirichletCharacter.norm_le_one δ _
        · exact DirichletCharacter.norm_le_one ε _
      _ = 1 := by norm_num
  calc
    (‖α (c - a)‖ * ‖β (c - b)‖ * ‖γ (c - a)‖ *
          ‖δ (c - d)‖ * ‖ε (c - e)‖) *
        ‖(∑ y : ZMod p,
            α y * β (y - lam) * δ (y - mu) * ε (y - nu)) -
          β (1 - lam) * δ (1 - mu) * ε (1 - nu)‖ ≤
      1 * ‖(∑ y : ZMod p,
            α y * β (y - lam) * δ (y - mu) * ε (y - nu)) -
          β (1 - lam) * δ (1 - mu) * ε (1 - nu)‖ := by
      gcongr
    _ ≤ ‖∑ y : ZMod p,
          α y * β (y - lam) * δ (y - mu) * ε (y - nu)‖ +
        ‖β (1 - lam) * δ (1 - mu) * ε (1 - nu)‖ := by
      simpa using norm_sub_le
        (∑ y : ZMod p,
          α y * β (y - lam) * δ (y - mu) * ε (y - nu))
        (β (1 - lam) * δ (1 - mu) * ε (1 - nu))
    _ ≤ 3 * Real.sqrt p + 1 := add_le_add hfour hdeleted

/-- Source-shaped specialization of the five-root projective estimate.  The
four finite local characters produced by the Möbius reduction remain powers
of the single input character. -/
theorem norm_fiveRootMulCharPowerSum_le_three_mul_sqrt_add_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerFourPointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (m n k l s : ℕ)
    (hpowM : χ ^ m ≠ 1) (hpowN : χ ^ n ≠ 1) (hpowK : χ ^ k ≠ 1)
    (hpowL : χ ^ l ≠ 1) (hpowS : χ ^ s ≠ 1)
    (hprod : (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) = 1)
    (a b c d e : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hdc : d ≠ c) (hec : e ≠ c) (hde : d ≠ e) :
    ‖∑ x : ZMod p,
        (χ ^ m) (x - a) * (χ ^ n) (x - b) * (χ ^ k) (x - c) *
          (χ ^ l) (x - d) * (χ ^ s) (x - e)‖ ≤
      3 * Real.sqrt p + 1 := by
  let lam : ZMod p := (a - b) / (c - b)
  let mu : ZMod p := (a - d) / (c - d)
  let nu : ZMod p := (a - e) / (c - e)
  have hlam : lam ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hbc.symm)
  have hmu : mu ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr had) (sub_ne_zero.mpr hdc.symm)
  have hnu : nu ≠ 0 := div_ne_zero
    (sub_ne_zero.mpr hae) (sub_ne_zero.mpr hec.symm)
  have hlammu : lam ≠ mu := by
    intro heq
    have hcb : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
    have hcd : c - d ≠ 0 := sub_ne_zero.mpr hdc.symm
    dsimp [lam, mu] at heq
    rw [div_eq_div_iff hcb hcd] at heq
    have hzero : (a - c) * (b - d) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hzero with hac' | hbd'
    · exact hac (sub_eq_zero.mp hac')
    · exact hbd (sub_eq_zero.mp hbd')
  have hlamnu : lam ≠ nu := by
    intro heq
    have hcb : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
    have hce : c - e ≠ 0 := sub_ne_zero.mpr hec.symm
    dsimp [lam, nu] at heq
    rw [div_eq_div_iff hcb hce] at heq
    have hzero : (a - c) * (b - e) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hzero with hac' | hbe'
    · exact hac (sub_eq_zero.mp hac')
    · exact hbe (sub_eq_zero.mp hbe')
  have hmunu : mu ≠ nu := by
    intro heq
    have hcd : c - d ≠ 0 := sub_ne_zero.mpr hdc.symm
    have hce : c - e ≠ 0 := sub_ne_zero.mpr hec.symm
    dsimp [mu, nu] at heq
    rw [div_eq_div_iff hcd hce] at heq
    have hzero : (a - c) * (d - e) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp hzero with hac' | hde'
    · exact hac (sub_eq_zero.mp hac')
    · exact hde (sub_eq_zero.mp hde')
  have hfiniteProd : χ ^ (m + n + l + s) ≠ 1 := by
    intro heq
    apply hpowK
    calc
      χ ^ k = 1 * χ ^ k := by simp
      _ = χ ^ (m + n + l + s) * χ ^ k := by rw [heq]
      _ = (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) := by
        simp only [pow_add]
        ac_rfl
      _ = 1 := hprod
  have hfour :
      ‖∑ y : ZMod p,
        (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ l) (y - mu) *
          (χ ^ s) (y - nu)‖ ≤
          3 * Real.sqrt p :=
    hweil χ m n l s lam mu nu hpowM hpowN hpowL hpowS hfiniteProd
      hlam hmu hnu hlammu hlamnu hmunu
  rw [fiveRootMulCharSum_eq_fourPointSum_sub
    p (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l) (χ ^ s) hprod
      a b c d e hac hbc hdc hec]
  simp only [norm_mul]
  have hC :
      ‖(χ ^ m) (c - a)‖ * ‖(χ ^ n) (c - b)‖ * ‖(χ ^ k) (c - a)‖ *
          ‖(χ ^ l) (c - d)‖ * ‖(χ ^ s) (c - e)‖ ≤ 1 := by
    calc
      ‖(χ ^ m) (c - a)‖ * ‖(χ ^ n) (c - b)‖ * ‖(χ ^ k) (c - a)‖ *
            ‖(χ ^ l) (c - d)‖ * ‖(χ ^ s) (c - e)‖ ≤ 1 * 1 * 1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one (χ ^ m) (c - a)
        · exact DirichletCharacter.norm_le_one (χ ^ n) (c - b)
        · exact DirichletCharacter.norm_le_one (χ ^ k) (c - a)
        · exact DirichletCharacter.norm_le_one (χ ^ l) (c - d)
        · exact DirichletCharacter.norm_le_one (χ ^ s) (c - e)
      _ = 1 := by norm_num
  have hdeleted :
      ‖(χ ^ n) (1 - lam) * (χ ^ l) (1 - mu) * (χ ^ s) (1 - nu)‖ ≤ 1 := by
    simp only [norm_mul]
    calc
      ‖(χ ^ n) (1 - lam)‖ * ‖(χ ^ l) (1 - mu)‖ * ‖(χ ^ s) (1 - nu)‖ ≤
          1 * 1 * 1 := by
        gcongr
        · exact DirichletCharacter.norm_le_one (χ ^ n) _
        · exact DirichletCharacter.norm_le_one (χ ^ l) _
        · exact DirichletCharacter.norm_le_one (χ ^ s) _
      _ = 1 := by norm_num
  calc
    (‖(χ ^ m) (c - a)‖ * ‖(χ ^ n) (c - b)‖ * ‖(χ ^ k) (c - a)‖ *
          ‖(χ ^ l) (c - d)‖ * ‖(χ ^ s) (c - e)‖) *
        ‖(∑ y : ZMod p,
            (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ l) (y - mu) *
              (χ ^ s) (y - nu)) -
          (χ ^ n) (1 - lam) * (χ ^ l) (1 - mu) * (χ ^ s) (1 - nu)‖ ≤
      1 * ‖(∑ y : ZMod p,
            (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ l) (y - mu) *
              (χ ^ s) (y - nu)) -
          (χ ^ n) (1 - lam) * (χ ^ l) (1 - mu) * (χ ^ s) (1 - nu)‖ := by
      gcongr
    _ ≤ ‖∑ y : ZMod p,
          (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ l) (y - mu) *
            (χ ^ s) (y - nu)‖ +
        ‖(χ ^ n) (1 - lam) * (χ ^ l) (1 - mu) * (χ ^ s) (1 - nu)‖ := by
      simpa using norm_sub_le
        (∑ y : ZMod p,
          (χ ^ m) y * (χ ^ n) (y - lam) * (χ ^ l) (y - mu) *
            (χ ^ s) (y - nu))
        ((χ ^ n) (1 - lam) * (χ ^ l) (1 - mu) * (χ ^ s) (1 - nu))
    _ ≤ 3 * Real.sqrt p + 1 := add_le_add hfour hdeleted

/-- When exactly three roots are active and their total multiplicity is not
divisible by the character order, the active-root sum is literally an
instance of the three-point hypergeometric endpoint. -/
theorem norm_primeActiveRootCharacterSum_le_two_mul_sqrt_of_card_eq_three_degree_not_dvd
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hhyper : TaoPrimeThreePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : ¬orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 3) :
    ‖primeActiveRootCharacterSum p χ P‖ ≤ 2 * Real.sqrt p := by
  obtain ⟨u, v, w, huv, huw, hvw, hroots⟩ := Finset.card_eq_three.mp hcard
  have huActive : u ∈ primeActiveRoots p χ P := by simp [hroots]
  have hvActive : v ∈ primeActiveRoots p χ P := by simp [hroots]
  have hwActive : w ∈ primeActiveRoots p χ P := by simp [hroots]
  have huRoot : u ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P huActive
  have hvRoot : v ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hvActive
  have hwRoot : w ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hwActive
  let m := P.roots.count u
  let n := P.roots.count v
  let k := P.roots.count w
  have hm : m ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp huRoot)).ne'
  have hn : n ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hvRoot)).ne'
  have hk : k ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hwRoot)).ne'
  have hpowM : χ ^ m ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp huActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowN : χ ^ n ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hvActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowK : χ ^ k ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hwActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hsumNot :
      ¬orderOf χ ∣
        ∑ a ∈ primeActiveRoots p χ P, P.roots.count a := by
    intro hsum
    exact hdegree
      ((orderOf_dvd_natDegree_iff_dvd_sum_primeActiveRoots_count
        p χ P hP).2 hsum)
  have hmnkNot : ¬orderOf χ ∣ m + n + k := by
    simpa [hroots, huv, huw, hvw, m, n, k, add_assoc, add_comm,
      add_left_comm] using hsumNot
  have hpowSum : χ ^ (m + n + k) ≠ 1 := by
    intro heq
    exact hmnkNot (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hprod : (χ ^ m) * (χ ^ n) * (χ ^ k) ≠ 1 := by
    simpa [pow_add] using hpowSum
  have hlam : v - u ≠ 0 := sub_ne_zero.mpr huv.symm
  have hmu : w - u ≠ 0 := sub_ne_zero.mpr huw.symm
  have hlammu : v - u ≠ w - u := by
    intro heq
    exact hvw (sub_left_inj.mp heq)
  have hthree := hhyper (χ ^ m) (χ ^ n) (χ ^ k)
    (v - u) (w - u) hpowM hpowN hpowK hprod hlam hmu hlammu
  rw [← threeRootMulCharSum_eq_threePointTranslate
    p (χ ^ m) (χ ^ n) (χ ^ k) u v w] at hthree
  unfold primeActiveRootCharacterSum
  rw [hroots]
  convert hthree using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro x _hx
  simp [huv, huw, hvw]
  rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn,
    MulChar.pow_apply' χ hk]
  simp [m, n, k, Polynomial.count_roots]
  ac_rfl

/-- Four active roots of degree nondivisible by the character order are
literally an instance of the four-point Kummer endpoint. -/
theorem norm_primeActiveRootCharacterSum_le_three_mul_sqrt_of_card_eq_four_degree_not_dvd
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hhyper : TaoPrimeFourPointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : ¬orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 4) :
    ‖primeActiveRootCharacterSum p χ P‖ ≤ 3 * Real.sqrt p := by
  obtain ⟨u, v, w, z, huv, huw, huz, hvw, hvz, hwz, hroots⟩ :=
    Finset.card_eq_four.mp hcard
  have huActive : u ∈ primeActiveRoots p χ P := by simp [hroots]
  have hvActive : v ∈ primeActiveRoots p χ P := by simp [hroots]
  have hwActive : w ∈ primeActiveRoots p χ P := by simp [hroots]
  have hzActive : z ∈ primeActiveRoots p χ P := by simp [hroots]
  have huRoot : u ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P huActive
  have hvRoot : v ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hvActive
  have hwRoot : w ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hwActive
  have hzRoot : z ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hzActive
  let m := P.roots.count u
  let n := P.roots.count v
  let k := P.roots.count w
  let l := P.roots.count z
  have hm : m ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp huRoot)).ne'
  have hn : n ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hvRoot)).ne'
  have hk : k ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hwRoot)).ne'
  have hl : l ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hzRoot)).ne'
  have hpowM : χ ^ m ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp huActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowN : χ ^ n ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hvActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowK : χ ^ k ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hwActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowL : χ ^ l ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hzActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hsumNot :
      ¬orderOf χ ∣
        ∑ a ∈ primeActiveRoots p χ P, P.roots.count a := by
    intro hsum
    exact hdegree
      ((orderOf_dvd_natDegree_iff_dvd_sum_primeActiveRoots_count
        p χ P hP).2 hsum)
  have hmnklNot : ¬orderOf χ ∣ m + n + k + l := by
    simpa [hroots, huv, huw, huz, hvw, hvz, hwz, m, n, k, l,
      add_assoc, add_comm, add_left_comm] using hsumNot
  have hpowSum : χ ^ (m + n + k + l) ≠ 1 := by
    intro heq
    exact hmnklNot (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hprod : (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) ≠ 1 := by
    simpa [pow_add] using hpowSum
  have hlam : v - u ≠ 0 := sub_ne_zero.mpr huv.symm
  have hmu : w - u ≠ 0 := sub_ne_zero.mpr huw.symm
  have hnu : z - u ≠ 0 := sub_ne_zero.mpr huz.symm
  have hlammu : v - u ≠ w - u := by
    intro heq
    exact hvw (sub_left_inj.mp heq)
  have hlamnu : v - u ≠ z - u := by
    intro heq
    exact hvz (sub_left_inj.mp heq)
  have hmunu : w - u ≠ z - u := by
    intro heq
    exact hwz (sub_left_inj.mp heq)
  have hfour := hhyper (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l)
    (v - u) (w - u) (z - u) hpowM hpowN hpowK hpowL hprod
      hlam hmu hnu hlammu hlamnu hmunu
  rw [← fourRootMulCharSum_eq_fourPointTranslate
    p (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l) u v w z] at hfour
  unfold primeActiveRootCharacterSum
  rw [hroots]
  convert hfour using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro x _hx
  simp [huv, huw, huz, hvw, hvz, hwz]
  rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn,
    MulChar.pow_apply' χ hk, MulChar.pow_apply' χ hl]
  simp [m, n, k, l, Polynomial.count_roots]
  ac_rfl

/-- Exactly five active roots of character-order-divisible degree reduce to
the four-point endpoint, with one deleted projective point. -/
theorem norm_primeActiveRootCharacterSum_le_three_mul_sqrt_add_one_of_card_eq_five_degree
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimeFourPointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 5) :
    ‖primeActiveRootCharacterSum p χ P‖ ≤ 3 * Real.sqrt p + 1 := by
  obtain ⟨u, huActive⟩ : (primeActiveRoots p χ P).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardErase : ((primeActiveRoots p χ P).erase u).card = 4 := by
    rw [Finset.card_erase_of_mem huActive, hcard]
  obtain ⟨v, w, z, t, hvw, hvz, hvt, hwz, hwt, hzt, hrest⟩ :=
    Finset.card_eq_four.mp hcardErase
  have hvErase : v ∈ (primeActiveRoots p χ P).erase u := by simp [hrest]
  have hwErase : w ∈ (primeActiveRoots p χ P).erase u := by simp [hrest]
  have hzErase : z ∈ (primeActiveRoots p χ P).erase u := by simp [hrest]
  have htErase : t ∈ (primeActiveRoots p χ P).erase u := by simp [hrest]
  have huv : u ≠ v := (Finset.mem_erase.mp hvErase).1.symm
  have huw : u ≠ w := (Finset.mem_erase.mp hwErase).1.symm
  have huz : u ≠ z := (Finset.mem_erase.mp hzErase).1.symm
  have hut : u ≠ t := (Finset.mem_erase.mp htErase).1.symm
  have hvActive : v ∈ primeActiveRoots p χ P :=
    (Finset.mem_erase.mp hvErase).2
  have hwActive : w ∈ primeActiveRoots p χ P :=
    (Finset.mem_erase.mp hwErase).2
  have hzActive : z ∈ primeActiveRoots p χ P :=
    (Finset.mem_erase.mp hzErase).2
  have htActive : t ∈ primeActiveRoots p χ P :=
    (Finset.mem_erase.mp htErase).2
  have hroots : primeActiveRoots p χ P = {u, v, w, z, t} := by
    calc
      primeActiveRoots p χ P =
          insert u ((primeActiveRoots p χ P).erase u) :=
        (Finset.insert_erase huActive).symm
      _ = {u, v, w, z, t} := by rw [hrest]
  have huRoot : u ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P huActive
  have hvRoot : v ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hvActive
  have hwRoot : w ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hwActive
  have hzRoot : z ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hzActive
  have htRoot : t ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P htActive
  let m := P.roots.count u
  let n := P.roots.count v
  let k := P.roots.count w
  let l := P.roots.count z
  let s := P.roots.count t
  have hm : m ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp huRoot)).ne'
  have hn : n ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hvRoot)).ne'
  have hk : k ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hwRoot)).ne'
  have hl : l ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hzRoot)).ne'
  have hs : s ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp htRoot)).ne'
  have hpowM : χ ^ m ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp huActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowN : χ ^ n ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hvActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowK : χ ^ k ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hwActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowL : χ ^ l ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hzActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowS : χ ^ s ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp htActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hsum := orderOf_dvd_sum_primeActiveRoots_count
    p χ P hP hdegree
  have hmnkls : orderOf χ ∣ m + n + k + l + s := by
    simpa [hroots, huv, huw, huz, hut, hvw, hvz, hvt, hwz, hwt, hzt,
      m, n, k, l, s, add_assoc, add_comm, add_left_comm] using hsum
  have hprod :
      (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    exact orderOf_dvd_iff_pow_eq_one.mp hmnkls
  have hfive := norm_fiveRootMulCharSum_le_three_mul_sqrt_add_one
    p hweil (χ ^ m) (χ ^ n) (χ ^ k) (χ ^ l) (χ ^ s)
      hpowM hpowN hpowK hpowL hpowS hprod u v w z t
      huv huw huz hut hvw hvz hvt hwz.symm hwt.symm hzt
  unfold primeActiveRootCharacterSum
  rw [hroots]
  convert hfive using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro x _hx
  simp [huv, huw, huz, hut, hvw, hvz, hvt, hwz, hwt, hzt]
  rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn,
    MulChar.pow_apply' χ hk, MulChar.pow_apply' χ hl,
    MulChar.pow_apply' χ hs]
  simp [m, n, k, l, s, Polynomial.count_roots]
  ac_rfl

/-- Source-shaped version of the exactly-five-active-root reduction. -/
theorem norm_primeActiveRootCharacterSum_le_three_mul_sqrt_add_one_of_card_eq_five_degree_power
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerFourPointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 5) :
    ‖primeActiveRootCharacterSum p χ P‖ ≤ 3 * Real.sqrt p + 1 := by
  obtain ⟨u, huActive⟩ : (primeActiveRoots p χ P).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hcardErase : ((primeActiveRoots p χ P).erase u).card = 4 := by
    rw [Finset.card_erase_of_mem huActive, hcard]
  obtain ⟨v, w, z, t, hvw, hvz, hvt, hwz, hwt, hzt, hrest⟩ :=
    Finset.card_eq_four.mp hcardErase
  have hvErase : v ∈ (primeActiveRoots p χ P).erase u := by simp [hrest]
  have hwErase : w ∈ (primeActiveRoots p χ P).erase u := by simp [hrest]
  have hzErase : z ∈ (primeActiveRoots p χ P).erase u := by simp [hrest]
  have htErase : t ∈ (primeActiveRoots p χ P).erase u := by simp [hrest]
  have huv : u ≠ v := (Finset.mem_erase.mp hvErase).1.symm
  have huw : u ≠ w := (Finset.mem_erase.mp hwErase).1.symm
  have huz : u ≠ z := (Finset.mem_erase.mp hzErase).1.symm
  have hut : u ≠ t := (Finset.mem_erase.mp htErase).1.symm
  have hvActive : v ∈ primeActiveRoots p χ P :=
    (Finset.mem_erase.mp hvErase).2
  have hwActive : w ∈ primeActiveRoots p χ P :=
    (Finset.mem_erase.mp hwErase).2
  have hzActive : z ∈ primeActiveRoots p χ P :=
    (Finset.mem_erase.mp hzErase).2
  have htActive : t ∈ primeActiveRoots p χ P :=
    (Finset.mem_erase.mp htErase).2
  have hroots : primeActiveRoots p χ P = {u, v, w, z, t} := by
    calc
      primeActiveRoots p χ P =
          insert u ((primeActiveRoots p χ P).erase u) :=
        (Finset.insert_erase huActive).symm
      _ = {u, v, w, z, t} := by rw [hrest]
  have huRoot : u ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P huActive
  have hvRoot : v ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hvActive
  have hwRoot : w ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hwActive
  have hzRoot : z ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P hzActive
  have htRoot : t ∈ P.roots.toFinset :=
    primeActiveRoots_subset_roots p χ P htActive
  let m := P.roots.count u
  let n := P.roots.count v
  let k := P.roots.count w
  let l := P.roots.count z
  let s := P.roots.count t
  have hm : m ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp huRoot)).ne'
  have hn : n ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hvRoot)).ne'
  have hk : k ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hwRoot)).ne'
  have hl : l ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hzRoot)).ne'
  have hs : s ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp htRoot)).ne'
  have hpowM : χ ^ m ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp huActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowN : χ ^ n ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hvActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowK : χ ^ k ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hwActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowL : χ ^ l ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp hzActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpowS : χ ^ s ≠ 1 := by
    intro heq
    exact (Finset.mem_filter.mp htActive).2
      (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hsum := orderOf_dvd_sum_primeActiveRoots_count
    p χ P hP hdegree
  have hmnkls : orderOf χ ∣ m + n + k + l + s := by
    simpa [hroots, huv, huw, huz, hut, hvw, hvz, hvt, hwz, hwt, hzt,
      m, n, k, l, s, add_assoc, add_comm, add_left_comm] using hsum
  have hprod :
      (χ ^ m) * (χ ^ n) * (χ ^ k) * (χ ^ l) * (χ ^ s) = 1 := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    exact orderOf_dvd_iff_pow_eq_one.mp hmnkls
  have hfive := norm_fiveRootMulCharPowerSum_le_three_mul_sqrt_add_one
    p hweil χ m n k l s hpowM hpowN hpowK hpowL hpowS hprod
      u v w z t huv huw huz hut hvw hvz hvt hwz.symm hwt.symm hzt
  unfold primeActiveRootCharacterSum
  rw [hroots]
  convert hfive using 1
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro x _hx
  simp [huv, huw, huz, hut, hvw, hvz, hvt, hwz, hwt, hzt]
  rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn,
    MulChar.pow_apply' χ hk, MulChar.pow_apply' χ hl,
    MulChar.pow_apply' χ hs]
  simp [m, n, k, l, s, Polynomial.count_roots]
  ac_rfl

/-- Deleting the inactive roots from a complete active-root sum costs at
most one unit per deleted point. -/
theorem norm_filter_primeActiveRootProduct_le_of_activeRootCharacterSum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) (B : ℝ)
    (hbound : ‖primeActiveRootCharacterSum p χ P‖ ≤ B) :
    ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
        x ∉ primeInactiveRoots p χ P),
      ∏ b ∈ primeActiveRoots p χ P,
        χ (x - b) ^ P.roots.count b‖ ≤
      B + (primeInactiveRoots p χ P).card := by
  let f : ZMod p → ℂ := fun x =>
    ∏ b ∈ primeActiveRoots p χ P,
      χ (x - b) ^ P.roots.count b
  let I := primeInactiveRoots p χ P
  have hsplit :
      (∑ x ∈ I, f x) +
          (∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x) =
        ∑ x : ZMod p, f x := by
    simpa [I] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x : ZMod p => x ∈ I) f)
  have hrewrite :
      (∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x) =
        (∑ x : ZMod p, f x) - ∑ x ∈ I, f x := by
    linear_combination hsplit
  have htotal : ‖∑ x : ZMod p, f x‖ ≤ B := by
    simpa [f, primeActiveRootCharacterSum] using hbound
  have hbad : ‖∑ x ∈ I, f x‖ ≤ I.card := by
    calc
      ‖∑ x ∈ I, f x‖ ≤ ∑ x ∈ I, ‖f x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ I, (1 : ℝ) := by
        exact Finset.sum_le_sum fun x hx => by
          simpa [f] using norm_primeActiveRootProduct_le_one p χ P x
      _ = I.card := by simp
  change ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x‖ ≤ _
  rw [hrewrite]
  exact (norm_sub_le _ _).trans (add_le_add htotal hbad)

/-- The four-point endpoint discharges the existing split-polynomial Weil
target whenever there are exactly five active roots and the degree is
character-order divisible. -/
theorem primeSplitPolynomialWeilBound_of_card_activeRoots_eq_five_degree
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimeFourPointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (_a : ZMod p) (_hχ : χ ≠ 1) (hP : P.Splits)
    (_hnot : ¬orderOf χ ∣ P.rootMultiplicity _a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 5) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hactive :=
    norm_primeActiveRootCharacterSum_le_three_mul_sqrt_add_one_of_card_eq_five_degree
      p hweil χ P hP hdegree hcard
  have hrestricted :=
    norm_filter_primeActiveRootProduct_le_of_activeRootCharacterSum
      p χ P (3 * Real.sqrt p + 1) hactive
  have hrootCard : 5 ≤ P.roots.toFinset.card := by
    rw [← hcard]
    exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
  have hInactiveCard :
      (primeInactiveRoots p χ P).card ≤ P.roots.toFinset.card :=
    Finset.card_le_card (primeInactiveRoots_subset_roots p χ P)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hroom :
      3 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
    have hInactiveCard' :
        ((primeInactiveRoots p χ P).card : ℝ) ≤
          (P.roots.toFinset.card : ℝ) := by exact_mod_cast hInactiveCard
    have hrootCard' : (5 : ℝ) ≤ P.roots.toFinset.card := by
      exact_mod_cast hrootCard
    push_cast
    nlinarith [Real.sqrt_nonneg (p : ℝ)]
  rw [primePolynomialCharacterCorrelation_eq_rootProduct p χ P hP,
    hsum, norm_mul]
  calc
    ‖χ P.leadingCoeff‖ *
          ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ ≤
        1 * ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ := by
      gcongr
      exact DirichletCharacter.norm_le_one χ P.leadingCoeff
    _ ≤ 3 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card := by
      simpa using hrestricted
    _ ≤ ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := hroom

/-- Source-shaped counterpart of the exactly-five-active-root
split-polynomial estimate. -/
theorem primeSplitPolynomialWeilBound_of_card_activeRoots_eq_five_degree_power
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hweil : TaoPrimePowerFourPointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (_a : ZMod p) (_hχ : χ ≠ 1) (hP : P.Splits)
    (_hnot : ¬orderOf χ ∣ P.rootMultiplicity _a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : (primeActiveRoots p χ P).card = 5) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hactive :=
    norm_primeActiveRootCharacterSum_le_three_mul_sqrt_add_one_of_card_eq_five_degree_power
      p hweil χ P hP hdegree hcard
  have hrestricted :=
    norm_filter_primeActiveRootProduct_le_of_activeRootCharacterSum
      p χ P (3 * Real.sqrt p + 1) hactive
  have hrootCard : 5 ≤ P.roots.toFinset.card := by
    rw [← hcard]
    exact Finset.card_le_card (primeActiveRoots_subset_roots p χ P)
  have hInactiveCard :
      (primeInactiveRoots p χ P).card ≤ P.roots.toFinset.card :=
    Finset.card_le_card (primeInactiveRoots_subset_roots p χ P)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hroom :
      3 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
    have hInactiveCard' :
        ((primeInactiveRoots p χ P).card : ℝ) ≤
          (P.roots.toFinset.card : ℝ) := by exact_mod_cast hInactiveCard
    have hrootCard' : (5 : ℝ) ≤ P.roots.toFinset.card := by
      exact_mod_cast hrootCard
    push_cast
    nlinarith [Real.sqrt_nonneg (p : ℝ)]
  rw [primePolynomialCharacterCorrelation_eq_rootProduct p χ P hP,
    hsum, norm_mul]
  calc
    ‖χ P.leadingCoeff‖ *
          ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ ≤
        1 * ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ := by
      gcongr
      exact DirichletCharacter.norm_le_one χ P.leadingCoeff
    _ ≤ 3 * Real.sqrt p + 1 + (primeInactiveRoots p χ P).card := by
      simpa using hrestricted
    _ ≤ ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := hroom

/-- If the character order divides the degree, the sharp three-root Kummer
bound is elementary.  After removing order-divisible roots, either two active
roots remain and the sum is a Jacobi sum with one deleted point, or all three
roots remain and the product of their characters is trivial, so a projective
change again reduces the sum to a Jacobi sum with one deleted point. -/
theorem primePolynomialCharacterCorrelation_le_two_mul_sqrt_of_card_roots_eq_three_of_degree_dvd
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p) (hP : P.Splits)
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : P.roots.toFinset.card = 3) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤ 2 * Real.sqrt p := by
  have hnot' : ¬orderOf χ ∣ P.roots.count a := by
    intro hdvd
    exact hnot ((Polynomial.count_roots P) ▸ hdvd)
  have hcountA : P.roots.count a ≠ 0 := by
    intro hzero
    apply hnot'
    rw [hzero]
    exact dvd_zero _
  have haRoot : a ∈ P.roots.toFinset :=
    Multiset.mem_toFinset.mpr
      (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcountA))
  have haActive : a ∈ primeActiveRoots p χ P :=
    Finset.mem_filter.mpr ⟨haRoot, hnot'⟩
  have hactivePos : 0 < (primeActiveRoots p χ P).card :=
    Finset.card_pos.mpr ⟨a, haActive⟩
  have hactiveTwo : 2 ≤ (primeActiveRoots p χ P).card := by
    by_contra hlt
    have hone : (primeActiveRoots p χ P).card = 1 := by omega
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hone
    have huActive : u ∈ primeActiveRoots p χ P := by simp [hu]
    have hnotU : ¬orderOf χ ∣ P.roots.count u :=
      (Finset.mem_filter.mp huActive).2
    apply hnotU
    have hsum := orderOf_dvd_sum_primeActiveRoots_count
      p χ P hP hdegree
    simpa [hu] using hsum
  have hdisjoint :
      Disjoint (primeActiveRoots p χ P) (primeInactiveRoots p χ P) := by
    rw [Finset.disjoint_left]
    intro u huActive huInactive
    exact (Finset.mem_filter.mp huActive).2
      (Finset.mem_filter.mp huInactive).2
  have hcardParts :
      (primeActiveRoots p χ P).card +
          (primeInactiveRoots p χ P).card = 3 := by
    have hunion := congrArg Finset.card
      (primeActiveRoots_union_primeInactiveRoots p χ P)
    rw [Finset.card_union_of_disjoint hdisjoint, hcard] at hunion
    exact hunion
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hrestricted :
      ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
          x ∉ primeInactiveRoots p χ P),
        ∏ b ∈ primeActiveRoots p χ P,
          χ (x - b) ^ P.roots.count b‖ ≤ Real.sqrt p + 1 := by
    by_cases hactiveLe : (primeActiveRoots p χ P).card ≤ 2
    · have hactiveEq : (primeActiveRoots p χ P).card = 2 := by omega
      have hinactiveEq : (primeInactiveRoots p χ P).card = 1 := by omega
      simpa [hinactiveEq] using
        (norm_filter_primeActiveRootProduct_le
          p χ P a hnot hactiveLe)
    · have hactiveEq : (primeActiveRoots p χ P).card = 3 := by
        have hsubset := Finset.card_le_card
          (primeActiveRoots_subset_roots p χ P)
        omega
      have hinactiveEq : (primeInactiveRoots p χ P).card = 0 := by omega
      simpa [hinactiveEq] using
        (norm_filter_primeActiveRootProduct_le_of_card_eq_three_degree
          p χ P hP hdegree hactiveEq)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  rw [primePolynomialCharacterCorrelation_eq_rootProduct p χ P hP,
    hsum, norm_mul]
  calc
    ‖χ P.leadingCoeff‖ *
          ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ ≤
        1 * ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ := by
      gcongr
      exact DirichletCharacter.norm_le_one χ P.leadingCoeff
    _ ≤ Real.sqrt p + 1 := by simpa using hrestricted
    _ ≤ 2 * Real.sqrt p := by linarith

/-- Sharp Kummer trace form of the degree-divisible three-root theorem. -/
theorem primeKummerRootCorrelation_le_of_card_roots_eq_three_of_degree_dvd
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits)
    (hroot : ∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : P.roots.toFinset.card = 3) :
    ‖primeKummerRootCorrelation χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
  obtain ⟨a, _ha, hnot⟩ := hroot
  rw [← primePolynomialCharacterCorrelation_eq_kummerRootCorrelation χ P hP]
  have hbound :=
    primePolynomialCharacterCorrelation_le_two_mul_sqrt_of_card_roots_eq_three_of_degree_dvd
      p χ P a hP hnot hdegree hcard
  simpa [hcard] using hbound

/-- The remaining degree-nondivisible three-root Kummer trace is exactly the
three-point hypergeometric endpoint.  Cases with fewer than three active
roots are elementary after deleting inactive roots; small characteristics
are covered by the trivial complete-sum estimate. -/
theorem primeKummerRootCorrelation_le_of_card_roots_eq_three_of_degree_not_dvd
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hhyper : TaoPrimeThreePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits)
    (hroot : ∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a)
    (hdegree : ¬orderOf χ ∣ P.natDegree)
    (hcard : P.roots.toFinset.card = 3) :
    ‖primeKummerRootCorrelation χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
  rw [← primePolynomialCharacterCorrelation_eq_kummerRootCorrelation χ P hP]
  by_cases hpSmall : p ≤ 4
  · have hp0 : (0 : ℝ) ≤ p := by positivity
    have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt hp0
    have hsqrtOne : (1 : ℝ) ≤ Real.sqrt p := by
      rw [Real.one_le_sqrt]
      exact_mod_cast (Fact.out : p.Prime).one_le
    have hpFour : (p : ℝ) ≤ 4 := by exact_mod_cast hpSmall
    calc
      ‖primePolynomialCharacterCorrelation p χ P‖ ≤ p :=
        norm_primePolynomialCharacterCorrelation_le_prime p χ P
      _ ≤ 2 * Real.sqrt p := by nlinarith
      _ = ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
        rw [hcard]
        norm_num
  · obtain ⟨a, haRoot, hnot⟩ := hroot
    have hnot' : ¬orderOf χ ∣ P.roots.count a := by
      intro hdvd
      exact hnot ((Polynomial.count_roots P) ▸ hdvd)
    have haActive : a ∈ primeActiveRoots p χ P :=
      Finset.mem_filter.mpr ⟨haRoot, hnot'⟩
    have hactivePos : 0 < (primeActiveRoots p χ P).card :=
      Finset.card_pos.mpr ⟨a, haActive⟩
    have hdisjoint :
        Disjoint (primeActiveRoots p χ P) (primeInactiveRoots p χ P) := by
      rw [Finset.disjoint_left]
      intro u huActive huInactive
      exact (Finset.mem_filter.mp huActive).2
        (Finset.mem_filter.mp huInactive).2
    have hcardParts :
        (primeActiveRoots p χ P).card +
            (primeInactiveRoots p χ P).card = 3 := by
      have hunion := congrArg Finset.card
        (primeActiveRoots_union_primeInactiveRoots p χ P)
      rw [Finset.card_union_of_disjoint hdisjoint, hcard] at hunion
      exact hunion
    have hsqrtTwo : (2 : ℝ) ≤ Real.sqrt p := by
      have hp0 : (0 : ℝ) ≤ p := by positivity
      have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt hp0
      have hpFive : (5 : ℝ) ≤ p := by exact_mod_cast (by omega : 5 ≤ p)
      nlinarith [Real.sqrt_nonneg (p : ℝ)]
    have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
    have hrestricted :
        ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
            x ∉ primeInactiveRoots p χ P),
          ∏ b ∈ primeActiveRoots p χ P,
            χ (x - b) ^ P.roots.count b‖ ≤ 2 * Real.sqrt p := by
      by_cases hactiveLe : (primeActiveRoots p χ P).card ≤ 2
      · have hinactiveLe : (primeInactiveRoots p χ P).card ≤ 2 := by omega
        have hlow := norm_filter_primeActiveRootProduct_le
          p χ P a hnot hactiveLe
        have hinactiveReal :
            ((primeInactiveRoots p χ P).card : ℝ) ≤ 2 := by
          exact_mod_cast hinactiveLe
        exact hlow.trans (by linarith)
      · have hactiveEq : (primeActiveRoots p χ P).card = 3 := by
          have hsubset := Finset.card_le_card
            (primeActiveRoots_subset_roots p χ P)
          omega
        have hinactiveEq : (primeInactiveRoots p χ P).card = 0 := by omega
        have hinactiveEmpty : primeInactiveRoots p χ P = ∅ :=
          Finset.card_eq_zero.mp hinactiveEq
        simpa [hinactiveEmpty, primeActiveRootCharacterSum] using
          (norm_primeActiveRootCharacterSum_le_two_mul_sqrt_of_card_eq_three_degree_not_dvd
            p hhyper χ P hP hdegree hactiveEq)
    rw [primePolynomialCharacterCorrelation_eq_rootProduct p χ P hP,
      hsum, norm_mul]
    calc
      ‖χ P.leadingCoeff‖ *
            ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
                x ∉ primeInactiveRoots p χ P),
              ∏ b ∈ primeActiveRoots p χ P,
                χ (x - b) ^ P.roots.count b‖ ≤
          1 * ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
                x ∉ primeInactiveRoots p χ P),
              ∏ b ∈ primeActiveRoots p χ P,
                χ (x - b) ^ P.roots.count b‖ := by
        gcongr
        exact DirichletCharacter.norm_le_one χ P.leadingCoeff
      _ ≤ 2 * Real.sqrt p := by simpa using hrestricted
      _ = ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
        rw [hcard]
        norm_num

/-- Assuming the three-point hypergeometric estimate, every degree-divisible
four-root Kummer trace satisfies the sharp `3 * sqrt p` bound.  The exact
active-root split covers two, three, and four active roots, with the omitted
inactive points absorbed by the available square-root units. -/
theorem primeKummerRootCorrelation_le_of_card_roots_eq_four_of_degree_dvd
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hhyper : TaoPrimeThreePointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits)
    (hroot : ∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : P.roots.toFinset.card = 4) :
    ‖primeKummerRootCorrelation χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
  rw [← primePolynomialCharacterCorrelation_eq_kummerRootCorrelation χ P hP]
  obtain ⟨a, haRoot, hnot⟩ := hroot
  have hnot' : ¬orderOf χ ∣ P.roots.count a := by
    intro hdvd
    exact hnot ((Polynomial.count_roots P) ▸ hdvd)
  have haActive : a ∈ primeActiveRoots p χ P :=
    Finset.mem_filter.mpr ⟨haRoot, hnot'⟩
  have hactivePos : 0 < (primeActiveRoots p χ P).card :=
    Finset.card_pos.mpr ⟨a, haActive⟩
  have hactiveTwo : 2 ≤ (primeActiveRoots p χ P).card := by
    by_contra hlt
    have hone : (primeActiveRoots p χ P).card = 1 := by omega
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hone
    have huActive : u ∈ primeActiveRoots p χ P := by simp [hu]
    have hnotU : ¬orderOf χ ∣ P.roots.count u :=
      (Finset.mem_filter.mp huActive).2
    apply hnotU
    have hsum := orderOf_dvd_sum_primeActiveRoots_count
      p χ P hP hdegree
    simpa [hu] using hsum
  have hdisjoint :
      Disjoint (primeActiveRoots p χ P) (primeInactiveRoots p χ P) := by
    rw [Finset.disjoint_left]
    intro u huActive huInactive
    exact (Finset.mem_filter.mp huActive).2
      (Finset.mem_filter.mp huInactive).2
  have hcardParts :
      (primeActiveRoots p χ P).card +
          (primeInactiveRoots p χ P).card = 4 := by
    have hunion := congrArg Finset.card
      (primeActiveRoots_union_primeInactiveRoots p χ P)
    rw [Finset.card_union_of_disjoint hdisjoint, hcard] at hunion
    exact hunion
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hrestricted :
      ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
          x ∉ primeInactiveRoots p χ P),
        ∏ b ∈ primeActiveRoots p χ P,
          χ (x - b) ^ P.roots.count b‖ ≤ 3 * Real.sqrt p := by
    by_cases hactiveTwoLe : (primeActiveRoots p χ P).card ≤ 2
    · have hactiveEq : (primeActiveRoots p χ P).card = 2 := by omega
      have hinactiveEq : (primeInactiveRoots p χ P).card = 2 := by omega
      have hlow := norm_filter_primeActiveRootProduct_le
        p χ P a hnot hactiveTwoLe
      have hroom :
          Real.sqrt p + ((primeInactiveRoots p χ P).card : ℝ) ≤
            3 * Real.sqrt p := by
        rw [hinactiveEq]
        norm_num
        linarith
      exact hlow.trans hroom
    · by_cases hactiveThree : (primeActiveRoots p χ P).card = 3
      · have hinactiveEq : (primeInactiveRoots p χ P).card = 1 := by omega
        have hthree :=
          norm_filter_primeActiveRootProduct_le_of_card_eq_three_degree
            p χ P hP hdegree hactiveThree
        have hroom :
            Real.sqrt p + 1 + ((primeInactiveRoots p χ P).card : ℝ) ≤
              3 * Real.sqrt p := by
          rw [hinactiveEq]
          norm_num
          linarith
        exact hthree.trans hroom
      · have hactiveFour : (primeActiveRoots p χ P).card = 4 := by
          have hsubset := Finset.card_le_card
            (primeActiveRoots_subset_roots p χ P)
          omega
        have hinactiveEq : (primeInactiveRoots p χ P).card = 0 := by omega
        have hfour :=
          norm_filter_primeActiveRootProduct_le_of_card_eq_four_degree
            p hhyper χ P hP hdegree hactiveFour
        have hroom :
            2 * Real.sqrt p + 1 +
                ((primeInactiveRoots p χ P).card : ℝ) ≤
              3 * Real.sqrt p := by
          rw [hinactiveEq]
          norm_num
          linarith
        exact hfour.trans hroom
  rw [primePolynomialCharacterCorrelation_eq_rootProduct p χ P hP,
    hsum, norm_mul]
  calc
    ‖χ P.leadingCoeff‖ *
          ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ ≤
        1 * ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ := by
      gcongr
      exact DirichletCharacter.norm_le_one χ P.leadingCoeff
    _ ≤ 3 * Real.sqrt p := by simpa using hrestricted
    _ = ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
      rw [hcard]
      norm_num

/-- Assuming the three- and four-point endpoints, every degree-nondivisible
four-root Kummer trace satisfies the sharp `3 * sqrt p` bound.  The cases
with fewer active roots are obtained by deleting the inactive points. -/
theorem primeKummerRootCorrelation_le_of_card_roots_eq_four_of_degree_not_dvd
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hthree : TaoPrimeThreePointHypergeometricWeilBoundAt p)
    (hfour : TaoPrimeFourPointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits)
    (hroot : ∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a)
    (hdegree : ¬orderOf χ ∣ P.natDegree)
    (hcard : P.roots.toFinset.card = 4) :
    ‖primeKummerRootCorrelation χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
  rw [← primePolynomialCharacterCorrelation_eq_kummerRootCorrelation χ P hP]
  obtain ⟨a, haRoot, hnot⟩ := hroot
  have hnot' : ¬orderOf χ ∣ P.roots.count a := by
    intro hdvd
    exact hnot ((Polynomial.count_roots P) ▸ hdvd)
  have haActive : a ∈ primeActiveRoots p χ P :=
    Finset.mem_filter.mpr ⟨haRoot, hnot'⟩
  have hactivePos : 0 < (primeActiveRoots p χ P).card :=
    Finset.card_pos.mpr ⟨a, haActive⟩
  have hdisjoint :
      Disjoint (primeActiveRoots p χ P) (primeInactiveRoots p χ P) := by
    rw [Finset.disjoint_left]
    intro u huActive huInactive
    exact (Finset.mem_filter.mp huActive).2
      (Finset.mem_filter.mp huInactive).2
  have hcardParts :
      (primeActiveRoots p χ P).card +
          (primeInactiveRoots p χ P).card = 4 := by
    have hunion := congrArg Finset.card
      (primeActiveRoots_union_primeInactiveRoots p χ P)
    rw [Finset.card_union_of_disjoint hdisjoint, hcard] at hunion
    exact hunion
  have hpFour : 4 ≤ p := by
    have hle : P.roots.toFinset.card ≤ Fintype.card (ZMod p) :=
      Finset.card_le_univ _
    simpa [hcard] using hle
  have hsqrtTwo : (2 : ℝ) ≤ Real.sqrt p := by
    have hp0 : (0 : ℝ) ≤ p := by positivity
    have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt hp0
    have hpFourReal : (4 : ℝ) ≤ p := by exact_mod_cast hpFour
    nlinarith [Real.sqrt_nonneg (p : ℝ)]
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hrestricted :
      ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
          x ∉ primeInactiveRoots p χ P),
        ∏ b ∈ primeActiveRoots p χ P,
          χ (x - b) ^ P.roots.count b‖ ≤ 3 * Real.sqrt p := by
    by_cases hactiveLe : (primeActiveRoots p χ P).card ≤ 2
    · have hinactiveLe : (primeInactiveRoots p χ P).card ≤ 3 := by omega
      have hlow := norm_filter_primeActiveRootProduct_le
        p χ P a hnot hactiveLe
      have hinactiveReal :
          ((primeInactiveRoots p χ P).card : ℝ) ≤ 3 := by
        exact_mod_cast hinactiveLe
      exact hlow.trans (by linarith)
    · by_cases hactiveThree : (primeActiveRoots p χ P).card = 3
      · have hinactiveEq : (primeInactiveRoots p χ P).card = 1 := by omega
        have hactive :=
          norm_primeActiveRootCharacterSum_le_two_mul_sqrt_of_card_eq_three_degree_not_dvd
            p hthree χ P hP hdegree hactiveThree
        have hfiltered :=
          norm_filter_primeActiveRootProduct_le_of_activeRootCharacterSum
            p χ P (2 * Real.sqrt p) hactive
        have hroom :
            2 * Real.sqrt p +
                ((primeInactiveRoots p χ P).card : ℝ) ≤
              3 * Real.sqrt p := by
          rw [hinactiveEq]
          norm_num
          linarith
        exact hfiltered.trans hroom
      · have hactiveFour : (primeActiveRoots p χ P).card = 4 := by
          have hsubset := Finset.card_le_card
            (primeActiveRoots_subset_roots p χ P)
          omega
        have hinactiveEq : (primeInactiveRoots p χ P).card = 0 := by omega
        have hactive :=
          norm_primeActiveRootCharacterSum_le_three_mul_sqrt_of_card_eq_four_degree_not_dvd
            p hfour χ P hP hdegree hactiveFour
        have hfiltered :=
          norm_filter_primeActiveRootProduct_le_of_activeRootCharacterSum
            p χ P (3 * Real.sqrt p) hactive
        simpa [hinactiveEq] using hfiltered
  rw [primePolynomialCharacterCorrelation_eq_rootProduct p χ P hP,
    hsum, norm_mul]
  calc
    ‖χ P.leadingCoeff‖ *
          ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ ≤
        1 * ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ := by
      gcongr
      exact DirichletCharacter.norm_le_one χ P.leadingCoeff
    _ ≤ 3 * Real.sqrt p := by simpa using hrestricted
    _ = ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
      rw [hcard]
      norm_num

/-- Assuming the three- and four-point endpoints, every degree-divisible
five-root Kummer trace satisfies the sharp `4 * sqrt p` bound. -/
theorem primeKummerRootCorrelation_le_of_card_roots_eq_five_of_degree_dvd
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (hthree : TaoPrimeThreePointHypergeometricWeilBoundAt p)
    (hfour : TaoPrimeFourPointHypergeometricWeilBoundAt p)
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits)
    (hroot : ∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : P.roots.toFinset.card = 5) :
    ‖primeKummerRootCorrelation χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
  rw [← primePolynomialCharacterCorrelation_eq_kummerRootCorrelation χ P hP]
  obtain ⟨a, haRoot, hnot⟩ := hroot
  have hnot' : ¬orderOf χ ∣ P.roots.count a := by
    intro hdvd
    exact hnot ((Polynomial.count_roots P) ▸ hdvd)
  have haActive : a ∈ primeActiveRoots p χ P :=
    Finset.mem_filter.mpr ⟨haRoot, hnot'⟩
  have hactivePos : 0 < (primeActiveRoots p χ P).card :=
    Finset.card_pos.mpr ⟨a, haActive⟩
  have hactiveTwo : 2 ≤ (primeActiveRoots p χ P).card := by
    by_contra hlt
    have hone : (primeActiveRoots p χ P).card = 1 := by omega
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hone
    have huActive : u ∈ primeActiveRoots p χ P := by simp [hu]
    have hnotU : ¬orderOf χ ∣ P.roots.count u :=
      (Finset.mem_filter.mp huActive).2
    apply hnotU
    have hsum := orderOf_dvd_sum_primeActiveRoots_count
      p χ P hP hdegree
    simpa [hu] using hsum
  have hdisjoint :
      Disjoint (primeActiveRoots p χ P) (primeInactiveRoots p χ P) := by
    rw [Finset.disjoint_left]
    intro u huActive huInactive
    exact (Finset.mem_filter.mp huActive).2
      (Finset.mem_filter.mp huInactive).2
  have hcardParts :
      (primeActiveRoots p χ P).card +
          (primeInactiveRoots p χ P).card = 5 := by
    have hunion := congrArg Finset.card
      (primeActiveRoots_union_primeInactiveRoots p χ P)
    rw [Finset.card_union_of_disjoint hdisjoint, hcard] at hunion
    exact hunion
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hsum := sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P
  have hrestricted :
      ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
          x ∉ primeInactiveRoots p χ P),
        ∏ b ∈ primeActiveRoots p χ P,
          χ (x - b) ^ P.roots.count b‖ ≤ 4 * Real.sqrt p := by
    by_cases hactiveTwoLe : (primeActiveRoots p χ P).card ≤ 2
    · have hactiveEq : (primeActiveRoots p χ P).card = 2 := by omega
      have hinactiveEq : (primeInactiveRoots p χ P).card = 3 := by omega
      have hlow := norm_filter_primeActiveRootProduct_le
        p χ P a hnot hactiveTwoLe
      have hroom :
          Real.sqrt p + ((primeInactiveRoots p χ P).card : ℝ) ≤
            4 * Real.sqrt p := by
        rw [hinactiveEq]
        norm_num
        linarith
      exact hlow.trans hroom
    · by_cases hactiveThree : (primeActiveRoots p χ P).card = 3
      · have hinactiveEq : (primeInactiveRoots p χ P).card = 2 := by omega
        have hthreeBound :=
          norm_filter_primeActiveRootProduct_le_of_card_eq_three_degree
            p χ P hP hdegree hactiveThree
        have hroom :
            Real.sqrt p + 1 +
                ((primeInactiveRoots p χ P).card : ℝ) ≤
              4 * Real.sqrt p := by
          rw [hinactiveEq]
          norm_num
          linarith
        exact hthreeBound.trans hroom
      · by_cases hactiveFour : (primeActiveRoots p χ P).card = 4
        · have hinactiveEq : (primeInactiveRoots p χ P).card = 1 := by omega
          have hfourBound :=
            norm_filter_primeActiveRootProduct_le_of_card_eq_four_degree
              p hthree χ P hP hdegree hactiveFour
          have hroom :
              2 * Real.sqrt p + 1 +
                  ((primeInactiveRoots p χ P).card : ℝ) ≤
                4 * Real.sqrt p := by
            rw [hinactiveEq]
            norm_num
            linarith
          exact hfourBound.trans hroom
        · have hactiveFive : (primeActiveRoots p χ P).card = 5 := by
            have hsubset := Finset.card_le_card
              (primeActiveRoots_subset_roots p χ P)
            omega
          have hinactiveEq : (primeInactiveRoots p χ P).card = 0 := by omega
          have hactive :=
            norm_primeActiveRootCharacterSum_le_three_mul_sqrt_add_one_of_card_eq_five_degree
              p hfour χ P hP hdegree hactiveFive
          have hfiltered :=
            norm_filter_primeActiveRootProduct_le_of_activeRootCharacterSum
              p χ P (3 * Real.sqrt p + 1) hactive
          have hroom :
              3 * Real.sqrt p + 1 +
                  ((primeInactiveRoots p χ P).card : ℝ) ≤
                4 * Real.sqrt p := by
            rw [hinactiveEq]
            norm_num
            linarith
          exact hfiltered.trans hroom
  rw [primePolynomialCharacterCorrelation_eq_rootProduct p χ P hP,
    hsum, norm_mul]
  calc
    ‖χ P.leadingCoeff‖ *
          ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ ≤
        1 * ‖∑ x ∈ (Finset.univ.filter fun x : ZMod p =>
              x ∉ primeInactiveRoots p χ P),
            ∏ b ∈ primeActiveRoots p χ P,
              χ (x - b) ^ P.roots.count b‖ := by
      gcongr
      exact DirichletCharacter.norm_le_one χ P.leadingCoeff
    _ ≤ 4 * Real.sqrt p := by simpa using hrestricted
    _ = ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p := by
      rw [hcard]
      norm_num
/-- The genuine Kummer trace boundary after the elementary one- and two-root
cases have been removed. -/
def TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)),
    χ ≠ 1 → P ≠ 0 → P.Splits →
    (∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a) →
    3 ≤ P.roots.toFinset.card →
    ‖primeKummerRootCorrelation χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p

/-- A Kummer trace estimate restricted to at least three distinct roots
supplies the full sharp trace endpoint. -/
theorem TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore.toFull
    (hweil : TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore) :
    TaoPrimeKummerRootProductWeilBound := by
  intro p _ _ χ P hχ hP0 hP hroot
  by_cases hcard : P.roots.toFinset.card ≤ 2
  · exact primeKummerRootCorrelation_le_of_card_roots_le_two
      p χ P hP hroot hcard
  · exact hweil p χ P hχ hP0 hP hroot (by omega)

/-- The full sharp Kummer trace estimate is equivalent to its restriction to
polynomials with at least three distinct roots. -/
theorem taoPrimeKummerRootProductWeilBound_iff_threeRootsOrMore :
    TaoPrimeKummerRootProductWeilBound ↔
      TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore := by
  constructor
  · intro hweil p _ _ χ P hχ hP0 hP hroot _hcard
    exact hweil p χ P hχ hP0 hP hroot
  · exact TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore.toFull

/-- After the degree-divisible three-root theorem, the exact general Kummer
residual consists only of four-or-more-root traces and three-root traces whose
total degree is not divisible by the character order. -/
def TaoPrimeKummerRootProductWeilBoundFourRootsOrThreeDegreeNondivisible : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)),
    χ ≠ 1 → P ≠ 0 → P.Splits →
    (∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a) →
    (4 ≤ P.roots.toFinset.card ∨
      (P.roots.toFinset.card = 3 ∧ ¬orderOf χ ∣ P.natDegree)) →
    ‖primeKummerRootCorrelation χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p

/-- The refined four-root-or-degree-nondivisible residual supplies the full
sharp Kummer trace theorem. -/
theorem TaoPrimeKummerRootProductWeilBoundFourRootsOrThreeDegreeNondivisible.toFull
    (hweil :
      TaoPrimeKummerRootProductWeilBoundFourRootsOrThreeDegreeNondivisible) :
    TaoPrimeKummerRootProductWeilBound := by
  intro p _ _ χ P hχ hP0 hP hroot
  by_cases hcardTwo : P.roots.toFinset.card ≤ 2
  · exact primeKummerRootCorrelation_le_of_card_roots_le_two
      p χ P hP hroot hcardTwo
  · by_cases hcardThree : P.roots.toFinset.card = 3
    · by_cases hdegree : orderOf χ ∣ P.natDegree
      · exact primeKummerRootCorrelation_le_of_card_roots_eq_three_of_degree_dvd
          p χ P hP hroot hdegree hcardThree
      · exact hweil p χ P hχ hP0 hP hroot
          (Or.inr ⟨hcardThree, hdegree⟩)
    · exact hweil p χ P hχ hP0 hP hroot (Or.inl (by omega))

/-- Exact equivalence between the full Kummer theorem and the refined
four-root-or-degree-nondivisible residual. -/
theorem taoPrimeKummerRootProductWeilBound_iff_fourRootsOrThreeDegreeNondivisible :
    TaoPrimeKummerRootProductWeilBound ↔
      TaoPrimeKummerRootProductWeilBoundFourRootsOrThreeDegreeNondivisible := by
  constructor
  · intro hweil p _ _ χ P hχ hP0 hP hroot _hshape
    exact hweil p χ P hχ hP0 hP hroot
  · exact
      TaoPrimeKummerRootProductWeilBoundFourRootsOrThreeDegreeNondivisible.toFull

/-- The pure four-or-more-root Kummer trace residual.  All smaller root counts
are elementary except for the separately normalized three-point
hypergeometric endpoint. -/
def TaoPrimeKummerRootProductWeilBoundFourRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)),
    χ ≠ 1 → P ≠ 0 → P.Splits →
    (∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a) →
    4 ≤ P.roots.toFinset.card →
    ‖primeKummerRootCorrelation χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p

/-- The global three-point hypergeometric estimate and the four-or-more-root
Kummer residual supply the full sharp Kummer theorem. -/
theorem TaoPrimeKummerRootProductWeilBoundFourRootsOrMore.toFull
    (hhyper : TaoPrimeThreePointHypergeometricWeilBound)
    (hweil : TaoPrimeKummerRootProductWeilBoundFourRootsOrMore) :
    TaoPrimeKummerRootProductWeilBound := by
  intro p _ _ χ P hχ hP0 hP hroot
  by_cases hcardTwo : P.roots.toFinset.card ≤ 2
  · exact primeKummerRootCorrelation_le_of_card_roots_le_two
      p χ P hP hroot hcardTwo
  · by_cases hcardThree : P.roots.toFinset.card = 3
    · by_cases hdegree : orderOf χ ∣ P.natDegree
      · exact primeKummerRootCorrelation_le_of_card_roots_eq_three_of_degree_dvd
          p χ P hP hroot hdegree hcardThree
      · exact
          primeKummerRootCorrelation_le_of_card_roots_eq_three_of_degree_not_dvd
            p (hhyper p) χ P hP hroot hdegree hcardThree
    · exact hweil p χ P hχ hP0 hP hroot (by omega)

/-- Under the three-point hypergeometric estimate, the full sharp Kummer
theorem is equivalent to its restriction to at least four roots. -/
theorem taoPrimeKummerRootProductWeilBound_iff_fourRootsOrMore
    (hhyper : TaoPrimeThreePointHypergeometricWeilBound) :
    TaoPrimeKummerRootProductWeilBound ↔
      TaoPrimeKummerRootProductWeilBoundFourRootsOrMore := by
  constructor
  · intro hweil p _ _ χ P hχ hP0 hP hroot _hcard
    exact hweil p χ P hχ hP0 hP hroot
  · exact TaoPrimeKummerRootProductWeilBoundFourRootsOrMore.toFull hhyper

/-- After the degree-divisible four-root closure, the exact residual consists
of five-or-more-root traces and degree-nondivisible four-root traces. -/
def TaoPrimeKummerRootProductWeilBoundFiveRootsOrFourDegreeNondivisible : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)),
    χ ≠ 1 → P ≠ 0 → P.Splits →
    (∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a) →
    (5 ≤ P.roots.toFinset.card ∨
      (P.roots.toFinset.card = 4 ∧ ¬orderOf χ ∣ P.natDegree)) →
    ‖primeKummerRootCorrelation χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p

/-- The three-point hypergeometric estimate upgrades the refined five-root
residual to the pure four-or-more-root Kummer theorem. -/
theorem TaoPrimeKummerRootProductWeilBoundFiveRootsOrFourDegreeNondivisible.toFourRootsOrMore
    (hhyper : TaoPrimeThreePointHypergeometricWeilBound)
    (hweil :
      TaoPrimeKummerRootProductWeilBoundFiveRootsOrFourDegreeNondivisible) :
    TaoPrimeKummerRootProductWeilBoundFourRootsOrMore := by
  intro p _ _ χ P hχ hP0 hP hroot hcardFour
  by_cases hcardEq : P.roots.toFinset.card = 4
  · by_cases hdegree : orderOf χ ∣ P.natDegree
    · exact primeKummerRootCorrelation_le_of_card_roots_eq_four_of_degree_dvd
        p (hhyper p) χ P hP hroot hdegree hcardEq
    · exact hweil p χ P hχ hP0 hP hroot (Or.inr ⟨hcardEq, hdegree⟩)
  · exact hweil p χ P hχ hP0 hP hroot (Or.inl (by omega))

/-- Under the three-point hypergeometric theorem, the full Kummer theorem is
equivalent to the five-root-or-degree-nondivisible-four-root residual. -/
theorem taoPrimeKummerRootProductWeilBound_iff_fiveRootsOrFourDegreeNondivisible
    (hhyper : TaoPrimeThreePointHypergeometricWeilBound) :
    TaoPrimeKummerRootProductWeilBound ↔
      TaoPrimeKummerRootProductWeilBoundFiveRootsOrFourDegreeNondivisible := by
  constructor
  · intro hfull p _ _ χ P hχ hP0 hP hroot _hshape
    exact hfull p χ P hχ hP0 hP hroot
  · intro hweil
    exact (hweil.toFourRootsOrMore hhyper).toFull hhyper

/-- The pure five-or-more-root Kummer residual.  The three- and four-point
endpoints close every smaller distinct-root case. -/
def TaoPrimeKummerRootProductWeilBoundFiveRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)),
    χ ≠ 1 → P ≠ 0 → P.Splits →
    (∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a) →
    5 ≤ P.roots.toFinset.card →
    ‖primeKummerRootCorrelation χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p

/-- The three- and four-point endpoints upgrade the pure five-root residual
to the preceding refined residual. -/
theorem TaoPrimeKummerRootProductWeilBoundFiveRootsOrMore.toFiveRootsOrFourDegreeNondivisible
    (hthree : TaoPrimeThreePointHypergeometricWeilBound)
    (hfour : TaoPrimeFourPointHypergeometricWeilBound)
    (hweil : TaoPrimeKummerRootProductWeilBoundFiveRootsOrMore) :
    TaoPrimeKummerRootProductWeilBoundFiveRootsOrFourDegreeNondivisible := by
  intro p _ _ χ P hχ hP0 hP hroot hshape
  rcases hshape with hcardFive | ⟨hcardFour, hdegree⟩
  · exact hweil p χ P hχ hP0 hP hroot hcardFive
  · exact
      primeKummerRootCorrelation_le_of_card_roots_eq_four_of_degree_not_dvd
        p (hthree p) (hfour p) χ P hP hroot hdegree hcardFour

/-- Under the three- and four-point endpoints, the full Kummer theorem is
equivalent to the pure five-or-more-root residual. -/
theorem taoPrimeKummerRootProductWeilBound_iff_fiveRootsOrMore
    (hthree : TaoPrimeThreePointHypergeometricWeilBound)
    (hfour : TaoPrimeFourPointHypergeometricWeilBound) :
    TaoPrimeKummerRootProductWeilBound ↔
      TaoPrimeKummerRootProductWeilBoundFiveRootsOrMore := by
  constructor
  · intro hfull p _ _ χ P hχ hP0 hP hroot _hcard
    exact hfull p χ P hχ hP0 hP hroot
  · intro hweil
    exact
      (taoPrimeKummerRootProductWeilBound_iff_fiveRootsOrFourDegreeNondivisible
        hthree).2
        (hweil.toFiveRootsOrFourDegreeNondivisible hthree hfour)

/-- After the degree-divisible five-root closure, the exact residual consists
of six-or-more-root traces and degree-nondivisible five-root traces. -/
def TaoPrimeKummerRootProductWeilBoundSixRootsOrFiveDegreeNondivisible : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)),
    χ ≠ 1 → P ≠ 0 → P.Splits →
    (∃ a ∈ P.roots.toFinset,
      ¬orderOf χ ∣ P.rootMultiplicity a) →
    (6 ≤ P.roots.toFinset.card ∨
      (P.roots.toFinset.card = 5 ∧ ¬orderOf χ ∣ P.natDegree)) →
    ‖primeKummerRootCorrelation χ P‖ ≤
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) * Real.sqrt p

/-- The three- and four-point endpoints upgrade the refined six-root residual
to the pure five-or-more-root theorem. -/
theorem TaoPrimeKummerRootProductWeilBoundSixRootsOrFiveDegreeNondivisible.toFiveRootsOrMore
    (hthree : TaoPrimeThreePointHypergeometricWeilBound)
    (hfour : TaoPrimeFourPointHypergeometricWeilBound)
    (hweil :
      TaoPrimeKummerRootProductWeilBoundSixRootsOrFiveDegreeNondivisible) :
    TaoPrimeKummerRootProductWeilBoundFiveRootsOrMore := by
  intro p _ _ χ P hχ hP0 hP hroot hcardFive
  by_cases hcardEq : P.roots.toFinset.card = 5
  · by_cases hdegree : orderOf χ ∣ P.natDegree
    · exact primeKummerRootCorrelation_le_of_card_roots_eq_five_of_degree_dvd
        p (hthree p) (hfour p) χ P hP hroot hdegree hcardEq
    · exact hweil p χ P hχ hP0 hP hroot (Or.inr ⟨hcardEq, hdegree⟩)
  · exact hweil p χ P hχ hP0 hP hroot (Or.inl (by omega))

/-- Under the three- and four-point endpoints, the full Kummer theorem is
equivalent to the six-root-or-degree-nondivisible-five-root residual. -/
theorem taoPrimeKummerRootProductWeilBound_iff_sixRootsOrFiveDegreeNondivisible
    (hthree : TaoPrimeThreePointHypergeometricWeilBound)
    (hfour : TaoPrimeFourPointHypergeometricWeilBound) :
    TaoPrimeKummerRootProductWeilBound ↔
      TaoPrimeKummerRootProductWeilBoundSixRootsOrFiveDegreeNondivisible := by
  constructor
  · intro hfull p _ _ χ P hχ hP0 hP hroot _hshape
    exact hfull p χ P hχ hP0 hP hroot
  · intro hweil
    exact (taoPrimeKummerRootProductWeilBound_iff_fiveRootsOrMore
      hthree hfour).2 (hweil.toFiveRootsOrMore hthree hfour)

/-- The polynomial and distinct-root trace formulations of the sharp Kummer
estimate are equivalent. -/
theorem taoPrimeKummerPolynomialWeilBound_iff_rootProduct :
    TaoPrimeKummerPolynomialWeilBound ↔
      TaoPrimeKummerRootProductWeilBound := by
  constructor
  · intro hweil p _ _ χ P hχ hP0 hP hroot
    rw [← primePolynomialCharacterCorrelation_eq_kummerRootCorrelation χ P hP]
    exact hweil p χ P hχ hP
      ((not_isMulCharOrderScalarPower_iff_exists_not_dvd_rootMultiplicity
        χ P hP0 hP).2 hroot)
  · intro hweil p _ _ χ P hχ hP hnot
    have hP0 : P ≠ 0 := by
      intro hzero
      subst P
      exact hnot (isMulCharOrderScalarPower_zero χ)
    have hroot :=
      (not_isMulCharOrderScalarPower_iff_exists_not_dvd_rootMultiplicity
        χ P hP0 hP).1 hnot
    rw [primePolynomialCharacterCorrelation_eq_kummerRootCorrelation χ P hP]
    exact hweil p χ P hχ hP0 hP hroot

/-- The sharp split-polynomial Kummer theorem is exactly equivalent to the
distinct-root trace estimate restricted to at least three roots. -/
theorem taoPrimeKummerPolynomialWeilBound_iff_threeRootsOrMore :
    TaoPrimeKummerPolynomialWeilBound ↔
      TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore :=
  taoPrimeKummerPolynomialWeilBound_iff_rootProduct.trans
    taoPrimeKummerRootProductWeilBound_iff_threeRootsOrMore

/-- Polynomial formulation of the exact refined Kummer residual. -/
theorem taoPrimeKummerPolynomialWeilBound_iff_fourRootsOrThreeDegreeNondivisible :
    TaoPrimeKummerPolynomialWeilBound ↔
      TaoPrimeKummerRootProductWeilBoundFourRootsOrThreeDegreeNondivisible :=
  taoPrimeKummerPolynomialWeilBound_iff_rootProduct.trans
    taoPrimeKummerRootProductWeilBound_iff_fourRootsOrThreeDegreeNondivisible

/-- Under the three-point hypergeometric estimate, the polynomial Kummer
theorem is equivalent to the pure four-or-more-root trace residual. -/
theorem taoPrimeKummerPolynomialWeilBound_iff_fourRootsOrMore
    (hhyper : TaoPrimeThreePointHypergeometricWeilBound) :
    TaoPrimeKummerPolynomialWeilBound ↔
      TaoPrimeKummerRootProductWeilBoundFourRootsOrMore :=
  taoPrimeKummerPolynomialWeilBound_iff_rootProduct.trans
    (taoPrimeKummerRootProductWeilBound_iff_fourRootsOrMore hhyper)

/-- Polynomial formulation of the refined five-root Kummer residual. -/
theorem taoPrimeKummerPolynomialWeilBound_iff_fiveRootsOrFourDegreeNondivisible
    (hhyper : TaoPrimeThreePointHypergeometricWeilBound) :
    TaoPrimeKummerPolynomialWeilBound ↔
      TaoPrimeKummerRootProductWeilBoundFiveRootsOrFourDegreeNondivisible :=
  taoPrimeKummerPolynomialWeilBound_iff_rootProduct.trans
    (taoPrimeKummerRootProductWeilBound_iff_fiveRootsOrFourDegreeNondivisible
      hhyper)

/-- Under the three- and four-point endpoints, the polynomial Kummer theorem
is equivalent to the pure five-or-more-root trace residual. -/
theorem taoPrimeKummerPolynomialWeilBound_iff_fiveRootsOrMore
    (hthree : TaoPrimeThreePointHypergeometricWeilBound)
    (hfour : TaoPrimeFourPointHypergeometricWeilBound) :
    TaoPrimeKummerPolynomialWeilBound ↔
      TaoPrimeKummerRootProductWeilBoundFiveRootsOrMore :=
  taoPrimeKummerPolynomialWeilBound_iff_rootProduct.trans
    (taoPrimeKummerRootProductWeilBound_iff_fiveRootsOrMore hthree hfour)

/-- Polynomial formulation of the refined six-root residual. -/
theorem taoPrimeKummerPolynomialWeilBound_iff_sixRootsOrFiveDegreeNondivisible
    (hthree : TaoPrimeThreePointHypergeometricWeilBound)
    (hfour : TaoPrimeFourPointHypergeometricWeilBound) :
    TaoPrimeKummerPolynomialWeilBound ↔
      TaoPrimeKummerRootProductWeilBoundSixRootsOrFiveDegreeNondivisible :=
  taoPrimeKummerPolynomialWeilBound_iff_rootProduct.trans
    (taoPrimeKummerRootProductWeilBound_iff_sixRootsOrFiveDegreeNondivisible
      hthree hfour)

/-- The restricted three-or-more-root Kummer trace theorem supplies the
polynomial formulation. -/
theorem TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore.toPolynomial
    (hweil : TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore) :
    TaoPrimeKummerPolynomialWeilBound :=
  taoPrimeKummerPolynomialWeilBound_iff_threeRootsOrMore.mpr hweil

/-- The sharp Kummer estimate supplies the coarser split-polynomial contract
used by the Burgess prime-to-composite chain. -/
theorem TaoPrimeKummerPolynomialWeilBound.toSplitPolynomial
    (hweil : TaoPrimeKummerPolynomialWeilBound) :
    TaoPrimeSplitPolynomialWeilBound := by
  intro p _ _ χ P a hχ hP hnot
  have hsharp := hweil p χ P hχ hP
    (not_isMulCharOrderScalarPower_of_not_dvd_rootMultiplicity χ P a hnot)
  have hcardPos : 0 < P.roots.toFinset.card := by
    have hmult : 0 < P.rootMultiplicity a := by
      by_contra hz
      apply hnot
      have heq : P.rootMultiplicity a = 0 := Nat.eq_zero_of_not_pos hz
      rw [heq]
      exact dvd_zero _
    have ha : a ∈ P.roots.toFinset := by
      rw [Multiset.mem_toFinset, ← Multiset.count_pos,
        Polynomial.count_roots]
      exact hmult
    exact Finset.card_pos.mpr ⟨a, ha⟩
  have hnat : P.roots.toFinset.card - 1 ≤ 2 * P.roots.toFinset.card := by
    omega
  have hreal :
      ((P.roots.toFinset.card - 1 : ℕ) : ℝ) ≤
        ((2 * P.roots.toFinset.card : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hsharp.trans
    (mul_le_mul_of_nonneg_right hreal (Real.sqrt_nonneg p))

theorem TaoPrimeKummerPolynomialWeilBound.toLinearQuotient
    (hweil : TaoPrimeKummerPolynomialWeilBound) :
    TaoPrimeLinearQuotientWeilBound :=
  hweil.toSplitPolynomial.toLinearQuotient

theorem TaoPrimeKummerPolynomialWeilBound.toComposite
    (hweil : TaoPrimeKummerPolynomialWeilBound) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  hweil.toSplitPolynomial.toComposite

/-- Direct downstream bridge from the genuine three-or-more-root Kummer
trace boundary to the complete cubefree Burgess estimate. -/
theorem TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore.toComposite
    (hweil : TaoPrimeKummerRootProductWeilBoundThreeRootsOrMore) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  hweil.toPolynomial.toComposite

/-- Direct downstream bridge from the refined Kummer residual to the complete
cubefree Burgess estimate. -/
theorem TaoPrimeKummerRootProductWeilBoundFourRootsOrThreeDegreeNondivisible.toComposite
    (hweil :
      TaoPrimeKummerRootProductWeilBoundFourRootsOrThreeDegreeNondivisible) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (taoPrimeKummerPolynomialWeilBound_iff_fourRootsOrThreeDegreeNondivisible.mpr
    hweil).toComposite

/-- Direct composite Burgess bridge from the pure four-or-more-root Kummer
residual and the three-point hypergeometric estimate. -/
theorem TaoPrimeKummerRootProductWeilBoundFourRootsOrMore.toComposite
    (hhyper : TaoPrimeThreePointHypergeometricWeilBound)
    (hweil : TaoPrimeKummerRootProductWeilBoundFourRootsOrMore) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (taoPrimeKummerPolynomialWeilBound_iff_fourRootsOrMore hhyper).2 hweil |>.toComposite

/-- Direct composite Burgess bridge from the refined five-root Kummer
residual and the three-point hypergeometric estimate. -/
theorem TaoPrimeKummerRootProductWeilBoundFiveRootsOrFourDegreeNondivisible.toComposite
    (hhyper : TaoPrimeThreePointHypergeometricWeilBound)
    (hweil :
      TaoPrimeKummerRootProductWeilBoundFiveRootsOrFourDegreeNondivisible) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (taoPrimeKummerPolynomialWeilBound_iff_fiveRootsOrFourDegreeNondivisible
    hhyper).2 hweil |>.toComposite

/-- Direct composite Burgess bridge from the pure five-or-more-root Kummer
residual and the three- and four-point endpoints. -/
theorem TaoPrimeKummerRootProductWeilBoundFiveRootsOrMore.toComposite
    (hthree : TaoPrimeThreePointHypergeometricWeilBound)
    (hfour : TaoPrimeFourPointHypergeometricWeilBound)
    (hweil : TaoPrimeKummerRootProductWeilBoundFiveRootsOrMore) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (taoPrimeKummerPolynomialWeilBound_iff_fiveRootsOrMore hthree hfour).2 hweil
    |>.toComposite

/-- Direct composite Burgess bridge from the refined six-root residual and
the three- and four-point endpoints. -/
theorem TaoPrimeKummerRootProductWeilBoundSixRootsOrFiveDegreeNondivisible.toComposite
    (hthree : TaoPrimeThreePointHypergeometricWeilBound)
    (hfour : TaoPrimeFourPointHypergeometricWeilBound)
    (hweil :
      TaoPrimeKummerRootProductWeilBoundSixRootsOrFiveDegreeNondivisible) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  (taoPrimeKummerPolynomialWeilBound_iff_sixRootsOrFiveDegreeNondivisible
    hthree hfour).2 hweil |>.toComposite

end

end Tao2026

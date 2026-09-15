import Tao2026.ErdosSelfridgePowerFree

/-!
# Product separation in the Erdős--Selfridge setup

This file formalizes equations (2) and (4) on journal page 293 of
Erdős--Selfridge (1975).  A counterexample, together with the
Sylvester--Schur large-prime input, forces `H ^ l < N`.  At that scale,
different equally sized subfamilies of `[N+1, N+H]` have different products.

The stronger final clause of source Lemma 1—that the ratio of two such
products cannot be an `l`-th power in the rationals—remains the next step.
-/

namespace Tao2026

/-- Gcd is submultiplicative over a finite product, in divisibility form. -/
theorem gcd_finsetProduct_dvd_product_gcd {ι : Type*} [DecidableEq ι]
    (q : ℕ) (s : Finset ι) (f : ι → ℕ) :
    Nat.gcd q (∏ i ∈ s, f i) ∣ ∏ i ∈ s, Nat.gcd q (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact (gcd_mul_dvd_mul_gcd q (f i) (∏ j ∈ s, f j)).trans
        (mul_dvd_mul_left (Nat.gcd q (f i)) ih)

/-- If `q` divides a finite product, it divides the product of its gcds with
the individual factors. -/
theorem dvd_product_gcd_of_dvd_finsetProduct {ι : Type*} [DecidableEq ι]
    {q : ℕ} {s : Finset ι} {f : ι → ℕ}
    (h : q ∣ ∏ i ∈ s, f i) :
    q ∣ ∏ i ∈ s, Nat.gcd q (f i) := by
  calc
    q = Nat.gcd q (∏ i ∈ s, f i) :=
      (Nat.gcd_eq_left_iff_dvd.mpr h).symm
    _ ∣ ∏ i ∈ s, Nat.gcd q (f i) :=
      gcd_finsetProduct_dvd_product_gcd q s f

/-- Two distinct members of an interval of length `H` have gcd strictly
smaller than `H`. -/
theorem gcd_lt_length_of_mem_consecutiveInterval
    {N H m b : ℕ} (hm : m ∈ consecutiveInterval N H)
    (hb : b ∈ consecutiveInterval N H) (hmb : m ≠ b) :
    Nat.gcd m b < H := by
  have hdistPos : 0 < Nat.dist m b := Nat.dist_pos_of_ne hmb
  have hgdist : Nat.gcd m b ∣ Nat.dist m b := by
    rcases le_total m b with hle | hle
    · rw [Nat.dist_eq_sub_of_le hle]
      exact Nat.dvd_sub (Nat.gcd_dvd_right m b) (Nat.gcd_dvd_left m b)
    · rw [Nat.dist_eq_sub_of_le_right hle]
      exact Nat.dvd_sub (Nat.gcd_dvd_left m b) (Nat.gcd_dvd_right m b)
  have hgLeDist : Nat.gcd m b ≤ Nat.dist m b :=
    Nat.le_of_dvd hdistPos hgdist
  have hdistLt : Nat.dist m b < H := by
    rcases le_total m b with hle | hle
    · rw [Nat.dist_eq_sub_of_le hle]
      have hmLower := (Finset.mem_Ioc.mp hm).1
      have hbUpper := (Finset.mem_Ioc.mp hb).2
      omega
    · rw [Nat.dist_eq_sub_of_le_right hle]
      have hbLower := (Finset.mem_Ioc.mp hb).1
      have hmUpper := (Finset.mem_Ioc.mp hm).2
      omega
  exact hgLeDist.trans_lt hdistLt

/-- The elementary binomial margin used to pass from
`(H+1)^l ≤ N+H` to `H^l < N`. -/
theorem pow_add_length_lt_add_one_pow {H l : ℕ}
    (hH : 1 ≤ H) (hl : 2 ≤ l) : H ^ l + H < (H + 1) ^ l := by
  have hpowH : H ≤ H ^ (l - 1) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < H) (by omega : 1 ≤ l - 1)
  have hbase : H ^ (l - 1) < (H + 1) ^ (l - 1) :=
    Nat.pow_lt_pow_left (by omega) (by omega)
  have hHpow : H ^ l = H * H ^ (l - 1) := by
    conv_lhs => rw [show l = (l - 1) + 1 by omega, pow_succ']
  have hHonePow : (H + 1) ^ l = (H + 1) * (H + 1) ^ (l - 1) := by
    conv_lhs => rw [show l = (l - 1) + 1 by omega, pow_succ']
  calc
    H ^ l + H ≤ H ^ l + H ^ (l - 1) := Nat.add_le_add_left hpowH _
    _ = (H + 1) * H ^ (l - 1) := by
      rw [hHpow, Nat.add_mul, one_mul]
    _ < (H + 1) * (H + 1) ^ (l - 1) :=
      (Nat.mul_lt_mul_left (by omega)).mpr hbase
    _ = (H + 1) ^ l := hHonePow.symm

/-- Equation (2), with the precise large-prime witness exposed: a prime
larger than `H` in the interval product must occur to exponent at least `l`
under failure of the source conclusion, forcing `H^l < N`. -/
theorem erdosSelfridge_pow_lt_start_of_failure_of_largePrime
    {N H l p : ℕ} (hH : 3 ≤ H) (hl : 2 ≤ l)
    (hp : p.Prime) (hHp : H < p) (hpProduct : p ∣ consecutiveProduct N H)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H l) :
    H ^ l < N := by
  have hpProduct' : p ∣ ∏ m ∈ consecutiveInterval N H, m := by
    simpa [consecutiveProduct] using hpProduct
  obtain ⟨m, hm, hpm⟩ :=
    (hp.prime.dvd_finsetProd_iff id).mp hpProduct'
  have hmPos : 0 < m := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  have hfacEq : (consecutiveProduct N H).factorization p =
      m.factorization p :=
    factorization_consecutiveProduct_eq_intervalElement_of_length_le
      hm hp hHp.le hpm
  have hlDvd : l ∣ m.factorization p := by
    rw [← hfacEq]
    exact hfail p hHp.le hp
  have hfacPos : 0 < m.factorization p :=
    (hp.dvd_iff_one_le_factorization hmPos.ne').mp hpm
  have hlFac : l ≤ m.factorization p := Nat.le_of_dvd hfacPos hlDvd
  have hpPowDvd : p ^ l ∣ m :=
    (hp.pow_dvd_iff_le_factorization hmPos.ne').mpr hlFac
  have hpPowLeM : p ^ l ≤ m := Nat.le_of_dvd hmPos hpPowDvd
  have hmUpper : m ≤ N + H := (Finset.mem_Ioc.mp hm).2
  have hbase : H + 1 ≤ p := by omega
  have hHpPow : (H + 1) ^ l ≤ p ^ l := Nat.pow_le_pow_left hbase l
  have hsum : H ^ l + H < N + H :=
    (pow_add_length_lt_add_one_pow (by omega) hl).trans_le
      (hHpPow.trans (hpPowLeM.trans hmUpper))
  omega

/-- Source equation (2), conditional only on the classical
Sylvester--Schur theorem used at this point of the paper. -/
theorem erdosSelfridge_pow_lt_start_of_failure
    (hSS : SylvesterSchurConclusion) {N H l : ℕ}
    (hH : 3 ≤ H) (hl : 2 ≤ l) (hHN : H < N)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H l) :
    H ^ l < N := by
  obtain ⟨p, hp, hHp, hpProduct⟩ := hSS (by omega) hHN
  exact erdosSelfridge_pow_lt_start_of_failure_of_largePrime
    hH hl hp hHp hpProduct hfail

/-- Source equation (4): below the exponent `l`, a product remembers exactly
which interval factors were selected once `H^l < N`. -/
theorem consecutiveSubproduct_injective_of_pow_lt_start
    {N H l r : ℕ} (hH : 2 ≤ H) (hpow : H ^ l < N) (hr : r < l)
    {S T : Finset ℕ} (hS : S ⊆ consecutiveInterval N H)
    (hT : T ⊆ consecutiveInterval N H) (hScard : S.card = r)
    (hTcard : T.card = r)
    (hprod : (∏ m ∈ S, m) = ∏ m ∈ T, m) : S = T := by
  by_contra hne
  have hnotSubset : ¬S ⊆ T := by
    intro hsub
    apply hne
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  obtain ⟨m, hmS, hmT⟩ := Finset.not_subset.mp hnotSubset
  have hmInterval : m ∈ consecutiveInterval N H := hS hmS
  have hmDvdT : m ∣ ∏ b ∈ T, b := by
    rw [← hprod]
    exact Finset.dvd_prod_of_mem id hmS
  have hmDvdGcd : m ∣ ∏ b ∈ T, Nat.gcd m b :=
    dvd_product_gcd_of_dvd_finsetProduct hmDvdT
  have hgcdLe : ∏ b ∈ T, Nat.gcd m b ≤ H ^ T.card := by
    apply Finset.prod_le_pow_card
    intro b hb
    exact (gcd_lt_length_of_mem_consecutiveInterval hmInterval (hT hb)
      (by exact fun h => hmT (h ▸ hb))).le
  have hmLePow : m ≤ H ^ r := by
    rw [← hTcard]
    exact (Nat.le_of_dvd (Finset.prod_pos fun b hb =>
      Nat.gcd_pos_of_pos_left b (by
        have := (Finset.mem_Ioc.mp hmInterval).1
        omega)) hmDvdGcd).trans hgcdLe
  have hpowLt : H ^ r < H ^ l := Nat.pow_lt_pow_right (by omega) hr
  have hmGtN : N < m := (Finset.mem_Ioc.mp hmInterval).1
  omega

/-- Negated form of equation (4), convenient for the rational-power-ratio
step in source Lemma 1. -/
theorem consecutiveSubproduct_ne_of_pow_lt_start
    {N H l r : ℕ} (hH : 2 ≤ H) (hpow : H ^ l < N) (hr : r < l)
    {S T : Finset ℕ} (hS : S ⊆ consecutiveInterval N H)
    (hT : T ⊆ consecutiveInterval N H) (hScard : S.card = r)
    (hTcard : T.card = r) (hne : S ≠ T) :
    (∏ m ∈ S, m) ≠ ∏ m ∈ T, m := by
  intro hprod
  exact hne (consecutiveSubproduct_injective_of_pow_lt_start
    hH hpow hr hS hT hScard hTcard hprod)

/-- Multiplicative form of equation (3) over an arbitrary positive finite
family.  This is the exact algebra used when passing from coefficient ratios
to ratios of interval subproducts. -/
theorem product_powerFreePart_mul_product_powerRootPart_pow
    {l : ℕ} {S : Finset ℕ} (hpos : ∀ m ∈ S, m ≠ 0) :
    (∏ m ∈ S, powerFreePart l m) *
        (∏ m ∈ S, powerRootPart l m) ^ l =
      ∏ m ∈ S, m := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro m hm
  exact powerFreePart_mul_powerRootPart_pow (hpos m hm)

/-- Equation (5), before its final gap contradiction: if two products of
canonical coefficients differ by the `l`-th power of a rational `u/v`, then
the corresponding interval subproducts differ by an `l`-th power as well. -/
theorem consecutiveSubproduct_crossPower_eq_of_powerFreePart_crossPower_eq
    {l u v : ℕ} {S T : Finset ℕ}
    (hSpos : ∀ m ∈ S, m ≠ 0) (hTpos : ∀ m ∈ T, m ≠ 0)
    (hratio :
      (∏ m ∈ S, powerFreePart l m) * v ^ l =
        (∏ m ∈ T, powerFreePart l m) * u ^ l) :
    (∏ m ∈ S, m) *
        (v * ∏ m ∈ T, powerRootPart l m) ^ l =
      (∏ m ∈ T, m) *
        (u * ∏ m ∈ S, powerRootPart l m) ^ l := by
  rw [← product_powerFreePart_mul_product_powerRootPart_pow hSpos,
    ← product_powerFreePart_mul_product_powerRootPart_pow hTpos, mul_pow,
    mul_pow]
  calc
    ((∏ m ∈ S, powerFreePart l m) *
          (∏ m ∈ S, powerRootPart l m) ^ l) *
        (v ^ l * (∏ m ∈ T, powerRootPart l m) ^ l) =
      ((∏ m ∈ S, powerFreePart l m) * v ^ l) *
        ((∏ m ∈ S, powerRootPart l m) ^ l *
          (∏ m ∈ T, powerRootPart l m) ^ l) := by ring
    _ = ((∏ m ∈ T, powerFreePart l m) * u ^ l) *
        ((∏ m ∈ S, powerRootPart l m) ^ l *
          (∏ m ∈ T, powerRootPart l m) ^ l) := by rw [hratio]
    _ = ((∏ m ∈ T, powerFreePart l m) *
          (∏ m ∈ T, powerRootPart l m) ^ l) *
        (u ^ l * (∏ m ∈ S, powerRootPart l m) ^ l) := by ring

end Tao2026

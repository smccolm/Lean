import Tao2026.ErdosSelfridgePowerFree

/-!
# Product separation in the Erdős--Selfridge setup

This file formalizes equations (2) and (4) on journal page 293 of
Erdős--Selfridge (1975).  A counterexample, together with the
Sylvester--Schur large-prime input, forces `H ^ l < N`.  At that scale,
different equally sized subfamilies of `[N+1, N+H]` have different products.

The stronger final clause of source Lemma 1—that the ratio of two such
products cannot be an `l`-th power in the rationals—is proved below.  The
next source step is Lemma 2's maximal-valuation deletion argument.
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

/-! ## The source gap estimate -/

/-- First-order expansion bound with an explicit geometric remainder. -/
theorem addPow_succ_le {N H s : ℕ} (hHN : H ≤ N) :
    (N + H) ^ (s + 1) ≤
      N ^ (s + 1) + (2 ^ (s + 1) - 1) * H * N ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hdouble : N + H ≤ 2 * N := by omega
      have hpowDouble : (N + H) ^ (s + 1) ≤
          2 ^ (s + 1) * N ^ (s + 1) := by
        calc
          (N + H) ^ (s + 1) ≤ (2 * N) ^ (s + 1) :=
            Nat.pow_le_pow_left hdouble _
          _ = 2 ^ (s + 1) * N ^ (s + 1) := mul_pow 2 N (s + 1)
      have hfirst := Nat.mul_le_mul_left N ih
      have hsecond := Nat.mul_le_mul_left H hpowDouble
      calc
        (N + H) ^ (s + 1 + 1) =
            N * (N + H) ^ (s + 1) + H * (N + H) ^ (s + 1) := by
              rw [pow_succ']
              ring
        _ ≤ N * (N ^ (s + 1) + (2 ^ (s + 1) - 1) * H * N ^ s) +
            H * (2 ^ (s + 1) * N ^ (s + 1)) :=
              Nat.add_le_add hfirst hsecond
        _ = N ^ (s + 1 + 1) +
            (2 ^ (s + 1 + 1) - 1) * H * N ^ (s + 1) := by
              have hpowN : N ^ (s + 1) = N * N ^ s := by rw [pow_succ']
              have hpowN' : N ^ (s + 1 + 1) = N * N ^ (s + 1) := by
                rw [pow_succ']
              have hpowTwo : 2 ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := by
                rw [pow_succ']
              calc
                N * (N ^ (s + 1) + (2 ^ (s + 1) - 1) * H * N ^ s) +
                    H * (2 ^ (s + 1) * N ^ (s + 1)) =
                  N ^ (s + 1 + 1) +
                    ((2 ^ (s + 1) - 1) + 2 ^ (s + 1)) * H *
                      N ^ (s + 1) := by
                        rw [hpowN, hpowN']
                        ring
                _ = N ^ (s + 1 + 1) +
                    (2 ^ (s + 1 + 1) - 1) * H * N ^ (s + 1) := by
                      have htwoPos : 0 < 2 ^ (s + 1) := pow_pos (by omega) _
                      have hcoeff :
                          (2 ^ (s + 1) - 1) + 2 ^ (s + 1) =
                            2 ^ (s + 1 + 1) - 1 := by
                        omega
                      rw [hcoeff]

/-- Mean-value upper bound for a natural-number power difference. -/
theorem addPow_sub_pow_le (N H r : ℕ) :
    (N + H) ^ r - N ^ r ≤ H * r * (N + H) ^ (r - 1) := by
  have h := abs_pow_sub_pow_le (a := ((N + H : ℕ) : ℝ))
    (b := (N : ℝ)) r
  have hsub : (0 : ℝ) ≤ ((N + H : ℕ) : ℝ) ^ r - (N : ℝ) ^ r := by
    apply sub_nonneg.mpr
    gcongr
    omega
  have hdiff : (0 : ℝ) ≤ ((N + H : ℕ) : ℝ) - N := by
    norm_num
  rw [abs_of_nonneg hsub, abs_of_nonneg hdiff,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((N + H : ℕ) : ℝ)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ N),
    max_eq_left (by norm_num)] at h
  norm_num at h
  have hnat : (N + H) ^ r ≤
      H * r * (N + H) ^ (r - 1) + N ^ r := by
    exact_mod_cast (show (((N + H) ^ r : ℕ) : ℝ) ≤
      (H * r * (N + H) ^ (r - 1) + N ^ r : ℕ) by
        push_cast
        nlinarith)
  omega

/-- Elementary coefficient inequality controlling the geometric remainder. -/
theorem succ_mul_two_pow_lt_three_pow_succ (n : ℕ) :
    (n + 1) * 2 ^ n < 3 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        norm_num
      · have hnPos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hcoeff : 2 * (n + 2) ≤ 3 * (n + 1) := by omega
        calc
          (n + 1 + 1) * 2 ^ (n + 1) =
              (2 * (n + 2)) * 2 ^ n := by rw [pow_succ']; ring
          _ ≤ (3 * (n + 1)) * 2 ^ n :=
            Nat.mul_le_mul_right _ hcoeff
          _ < 3 * 3 ^ (n + 1) := by
            rw [mul_assoc]
            exact (Nat.mul_lt_mul_left (by omega)).mpr ih
          _ = 3 ^ (n + 1 + 1) := by
            rw [pow_succ', pow_succ']
            ring

theorem r_mul_two_pow_sub_one_lt_pow
    {H r : ℕ} (hH : 3 ≤ H) (hr : 1 ≤ r) :
    r * (2 ^ (r - 1) - 1) < H ^ r := by
  have hmain : r * 2 ^ (r - 1) < 3 ^ r := by
    have h := succ_mul_two_pow_lt_three_pow_succ (r - 1)
    have hrEq : r - 1 + 1 = r := by omega
    rwa [hrEq] at h
  have hthree : 3 ^ r ≤ H ^ r := Nat.pow_le_pow_left hH r
  exact (Nat.mul_le_mul_left r (Nat.sub_le _ _)).trans_lt
    (hmain.trans_le hthree)

/-- The source's sharp upper gap: at scale `H^(r+1)<N`, the endpoint power
difference costs fewer than `r+1` linear increments. -/
theorem intervalPowerGap_upper
    {N H r : ℕ} (hH : 3 ≤ H) (hr : 1 ≤ r)
    (hscale : H ^ (r + 1) < N) :
    (N + H) ^ r - N ^ r < (r + 1) * H * N ^ (r - 1) := by
  rcases eq_or_lt_of_le hr with rfl | hrTwo
  · simp
    omega
  have hHN : H ≤ N := by
    have hHpow : H ≤ H ^ (r + 1) := Nat.le_pow (by omega : 0 < r + 1)
    omega
  have hmean := addPow_sub_pow_le N H r
  have happrox : (N + H) ^ (r - 1) ≤
      N ^ (r - 1) + (2 ^ (r - 1) - 1) * H * N ^ (r - 2) := by
    have h := addPow_succ_le (s := r - 2) hHN
    have hexp : r - 2 + 1 = r - 1 := by omega
    rwa [hexp] at h
  have hcoef := r_mul_two_pow_sub_one_lt_pow hH hr
  have hcoefH : r * (2 ^ (r - 1) - 1) * H < N := by
    calc
      r * (2 ^ (r - 1) - 1) * H < H ^ r * H :=
        (Nat.mul_lt_mul_right (by omega : 0 < H)).mpr hcoef
      _ = H ^ (r + 1) := by rw [pow_succ]
      _ < N := hscale
  have hNpos : 0 < N := by omega
  have hfactorPos : 0 < H * N ^ (r - 2) := by positivity
  have hremainder :
      H * r * ((2 ^ (r - 1) - 1) * H * N ^ (r - 2)) <
        H * N ^ (r - 1) := by
    have hmul := (Nat.mul_lt_mul_right hfactorPos).mpr hcoefH
    have hNpow : N ^ (r - 1) = N * N ^ (r - 2) := by
      rw [show r - 1 = (r - 2) + 1 by omega, pow_succ']
    rw [hNpow]
    convert hmul using 1 <;> ring
  calc
    (N + H) ^ r - N ^ r ≤ H * r * (N + H) ^ (r - 1) := hmean
    _ ≤ H * r *
        (N ^ (r - 1) + (2 ^ (r - 1) - 1) * H * N ^ (r - 2)) :=
      Nat.mul_le_mul_left _ happrox
    _ = H * r * N ^ (r - 1) +
        H * r * ((2 ^ (r - 1) - 1) * H * N ^ (r - 2)) := by ring
    _ < H * r * N ^ (r - 1) + H * N ^ (r - 1) :=
      Nat.add_lt_add_left hremainder _
    _ = (r + 1) * H * N ^ (r - 1) := by ring

/-- Powered upper gap in exactly the exponent ledger needed for Lemma 1. -/
theorem intervalPowerGap_pow_upper
    {N H l r : ℕ} (hH : 3 ≤ H) (hl : 2 ≤ l)
    (hr : 1 ≤ r) (hrl : r < l) (hscale : H ^ l < N) :
    ((N + H) ^ r - N ^ r) ^ l < l ^ l * N ^ (r * (l - 1)) := by
  have hrSuccLe : r + 1 ≤ l := by omega
  have hscaleR : H ^ (r + 1) < N :=
    (Nat.pow_le_pow_right (by omega : 0 < H) hrSuccLe).trans_lt hscale
  have hgap := intervalPowerGap_upper hH hr hscaleR
  have hHpower : H ≤ H ^ (l - r) := Nat.le_pow (by omega)
  have hfactor : (r + 1) * H ≤ l * H ^ (l - r) :=
    Nat.mul_le_mul hrSuccLe hHpower
  have hgap' : (N + H) ^ r - N ^ r <
      l * H ^ (l - r) * N ^ (r - 1) :=
    hgap.trans_le (Nat.mul_le_mul_right _ hfactor)
  have hscalePow : H ^ (l * (l - r)) < N ^ (l - r) := by
    rw [pow_mul]
    exact Nat.pow_lt_pow_left hscale (by omega)
  have hNpos : 0 < N := by omega
  calc
    ((N + H) ^ r - N ^ r) ^ l <
        (l * H ^ (l - r) * N ^ (r - 1)) ^ l :=
      Nat.pow_lt_pow_left hgap' (by omega)
    _ = l ^ l * H ^ (l * (l - r)) * N ^ (l * (r - 1)) := by
      simp only [mul_pow, pow_mul]
      ring
    _ < l ^ l * N ^ (l - r) * N ^ (l * (r - 1)) := by
      exact (Nat.mul_lt_mul_right (pow_pos hNpos _)).mpr
        ((Nat.mul_lt_mul_left (pow_pos (by omega : 0 < l) _)).mpr hscalePow)
    _ = l ^ l * N ^ (r * (l - 1)) := by
      have hexp : (l - r) + l * (r - 1) = r * (l - 1) := by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrl.le
        have hdiff : r + d - r = d := by omega
        have hpred : r + d - 1 = (r - 1) + d := by omega
        rw [hdiff, hpred]
        have hdmul : d + d * (r - 1) = d * r := by
          calc
            d + d * (r - 1) = d * ((r - 1) + 1) := by ring
            _ = d * r := by rw [Nat.sub_add_cancel hr]
        calc
          d + (r + d) * (r - 1) =
              r * (r - 1) + (d + d * (r - 1)) := by ring
          _ = r * (r - 1) + d * r := by rw [hdmul]
          _ = r * ((r - 1) + d) := by ring
      rw [mul_assoc, ← pow_add, hexp]

/-- A rational `l`-th-power ratio forces a lower gap incompatible with the
preceding powered upper bound. -/
theorem rationalPowerRatio_gap_pow_lower
    {P Q x y l : ℕ} (hl : 1 ≤ l) (hQ : 0 < Q)
    (hy : 0 < y) (hcop : x.Coprime y)
    (hcross : P * y ^ l = Q * x ^ l) (hQP : Q < P) :
    l ^ l * Q ^ (l - 1) ≤ (P - Q) ^ l := by
  have hyPowDvdQ : y ^ l ∣ Q := by
    apply (hcop.symm.pow l l).dvd_of_dvd_mul_right
    rw [← hcross]
    exact ⟨P, by ring⟩
  let A : ℕ := Q / y ^ l
  have hQeq : Q = A * y ^ l := (Nat.div_mul_cancel hyPowDvdQ).symm
  have hApos : 0 < A :=
    Nat.div_pos (Nat.le_of_dvd hQ hyPowDvdQ) (pow_pos hy l)
  have hPeq : P = A * x ^ l := by
    apply Nat.mul_right_cancel (pow_pos hy l)
    calc
      P * y ^ l = Q * x ^ l := hcross
      _ = (A * x ^ l) * y ^ l := by rw [hQeq]; ring
  have hyx : y < x := by
    have hxpow : y ^ l < x ^ l := by
      apply (Nat.mul_lt_mul_left hApos).mp
      calc
        A * y ^ l = Q := hQeq.symm
        _ < P := hQP
        _ = A * x ^ l := hPeq
    exact (Nat.pow_lt_pow_iff_left (by omega)).mp hxpow
  have hbern : y ^ l + l * y ^ (l - 1) ≤ (y + 1) ^ l := by
    simpa using (pow_add_mul_le_add_pow (R := ℕ) (a := y) (b := 1)
      (by omega) (by omega) l)
  have hbase : l * y ^ (l - 1) ≤ x ^ l - y ^ l := by
    have hpowMono : (y + 1) ^ l ≤ x ^ l := Nat.pow_le_pow_left (by omega) l
    omega
  have hgap : A * (l * y ^ (l - 1)) ≤ P - Q := by
    rw [hPeq, hQeq, ← Nat.mul_sub_left_distrib]
    exact Nat.mul_le_mul_left A hbase
  have hgapPow : (A * (l * y ^ (l - 1))) ^ l ≤ (P - Q) ^ l :=
    Nat.pow_le_pow_left hgap l
  have hfactorization :
      (A * (l * y ^ (l - 1))) ^ l =
        A * (l ^ l * Q ^ (l - 1)) := by
    rw [hQeq]
    simp only [mul_pow]
    have hyPow : (y ^ (l - 1)) ^ l = (y ^ l) ^ (l - 1) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    have hApow : A ^ l = A * A ^ (l - 1) := by
      conv_lhs => rw [show l = (l - 1) + 1 by omega, pow_succ']
    rw [hApow, hyPow]
    ring
  calc
    l ^ l * Q ^ (l - 1) ≤ A * (l ^ l * Q ^ (l - 1)) := by
      simpa using Nat.mul_le_mul_right (l ^ l * Q ^ (l - 1)) hApos
    _ = (A * (l * y ^ (l - 1))) ^ l := hfactorization.symm
    _ ≤ (P - Q) ^ l := hgapPow

/-- Every nonempty interval subproduct lies strictly above `N^r`. -/
theorem start_pow_lt_consecutiveSubproduct
    {N H r : ℕ} (hr : 1 ≤ r) {S : Finset ℕ}
    (hS : S ⊆ consecutiveInterval N H) (hScard : S.card = r) :
    N ^ r < ∏ m ∈ S, m := by
  have hLower : (N + 1) ^ S.card ≤ ∏ m ∈ S, m := by
    apply Finset.pow_card_le_prod
    intro m hm
    have := (Finset.mem_Ioc.mp (hS hm)).1
    omega
  calc
    N ^ r < (N + 1) ^ r := Nat.pow_lt_pow_left (by omega) (by omega)
    _ = (N + 1) ^ S.card := by rw [hScard]
    _ ≤ ∏ m ∈ S, m := hLower

/-- Every interval subproduct lies below the corresponding endpoint power. -/
theorem consecutiveSubproduct_le_endpoint_pow
    {N H r : ℕ} {S : Finset ℕ}
    (hS : S ⊆ consecutiveInterval N H) (hScard : S.card = r) :
    (∏ m ∈ S, m) ≤ (N + H) ^ r := by
  calc
    (∏ m ∈ S, m) ≤ (N + H) ^ S.card := by
      apply Finset.prod_le_pow_card
      intro m hm
      exact (Finset.mem_Ioc.mp (hS hm)).2
    _ = (N + H) ^ r := by rw [hScard]

/-- Coprime numerator/denominator form of the source rational-power-ratio
contradiction. -/
theorem consecutiveSubproduct_not_coprimeRationalPowerRatio
    {N H l r u v : ℕ} (hH : 3 ≤ H) (hl : 2 ≤ l)
    (hr : 1 ≤ r) (hrl : r < l) (hscale : H ^ l < N)
    {S T : Finset ℕ} (hS : S ⊆ consecutiveInterval N H)
    (hT : T ⊆ consecutiveInterval N H) (hScard : S.card = r)
    (hTcard : T.card = r) (hST : S ≠ T)
    (hu : 0 < u) (hv : 0 < v) (hcop : u.Coprime v) :
    (∏ m ∈ S, m) * v ^ l ≠ (∏ m ∈ T, m) * u ^ l := by
  intro hcross
  let P := ∏ m ∈ S, m
  let Q := ∏ m ∈ T, m
  have hPpos : 0 < P := Finset.prod_pos fun m hm => by
    have := (Finset.mem_Ioc.mp (hS hm)).1
    omega
  have hQpos : 0 < Q := Finset.prod_pos fun m hm => by
    have := (Finset.mem_Ioc.mp (hT hm)).1
    omega
  have hPneQ : P ≠ Q := by
    intro hEq
    exact hST (consecutiveSubproduct_injective_of_pow_lt_start
      (by omega) hscale hrl hS hT hScard hTcard hEq)
  have hcrossPQ : P * v ^ l = Q * u ^ l := hcross
  have hPupper : P ≤ (N + H) ^ r :=
    consecutiveSubproduct_le_endpoint_pow hS hScard
  have hQupper : Q ≤ (N + H) ^ r :=
    consecutiveSubproduct_le_endpoint_pow hT hTcard
  have hPlower : N ^ r < P := start_pow_lt_consecutiveSubproduct hr hS hScard
  have hQlower : N ^ r < Q := start_pow_lt_consecutiveSubproduct hr hT hTcard
  have hscalar := intervalPowerGap_pow_upper hH hl hr hrl hscale
  rcases lt_or_gt_of_ne hPneQ with hPQ | hQP
  · have hlower := rationalPowerRatio_gap_pow_lower (l := l) (x := v) (y := u)
        (by omega) hPpos hu hcop.symm hcrossPQ.symm hPQ
    have hgapLt : Q - P < (N + H) ^ r - N ^ r := by omega
    have hgapPowLt : (Q - P) ^ l < ((N + H) ^ r - N ^ r) ^ l :=
      Nat.pow_lt_pow_left hgapLt (by omega)
    have hbasePow : N ^ (r * (l - 1)) < P ^ (l - 1) := by
      rw [pow_mul]
      exact Nat.pow_lt_pow_left hPlower (by omega)
    have hweighted : l ^ l * N ^ (r * (l - 1)) <
        l ^ l * P ^ (l - 1) :=
      (Nat.mul_lt_mul_left (pow_pos (by omega : 0 < l) _)).mpr hbasePow
    omega
  · have hlower := rationalPowerRatio_gap_pow_lower (l := l) (x := u) (y := v)
        (by omega) hQpos hv hcop hcrossPQ hQP
    have hgapLt : P - Q < (N + H) ^ r - N ^ r := by omega
    have hgapPowLt : (P - Q) ^ l < ((N + H) ^ r - N ^ r) ^ l :=
      Nat.pow_lt_pow_left hgapLt (by omega)
    have hbasePow : N ^ (r * (l - 1)) < Q ^ (l - 1) := by
      rw [pow_mul]
      exact Nat.pow_lt_pow_left hQlower (by omega)
    have hweighted : l ^ l * N ^ (r * (l - 1)) <
        l ^ l * Q ^ (l - 1) :=
      (Nat.mul_lt_mul_left (pow_pos (by omega : 0 < l) _)).mpr hbasePow
    omega

/-- The coprimality restriction is removed by cancelling the common gcd of
the rational numerator and denominator. -/
theorem consecutiveSubproduct_not_rationalPowerRatio
    {N H l r u v : ℕ} (hH : 3 ≤ H) (hl : 2 ≤ l)
    (hr : 1 ≤ r) (hrl : r < l) (hscale : H ^ l < N)
    {S T : Finset ℕ} (hS : S ⊆ consecutiveInterval N H)
    (hT : T ⊆ consecutiveInterval N H) (hScard : S.card = r)
    (hTcard : T.card = r) (hST : S ≠ T)
    (hu : 0 < u) (hv : 0 < v) :
    (∏ m ∈ S, m) * v ^ l ≠ (∏ m ∈ T, m) * u ^ l := by
  let g := Nat.gcd u v
  let u₀ := u / g
  let v₀ := v / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left v hu
  have hgu : g ∣ u := Nat.gcd_dvd_left u v
  have hgv : g ∣ v := Nat.gcd_dvd_right u v
  have huEq : u = u₀ * g := (Nat.div_mul_cancel hgu).symm
  have hvEq : v = v₀ * g := (Nat.div_mul_cancel hgv).symm
  have hu₀ : 0 < u₀ := Nat.div_pos (Nat.le_of_dvd hu hgu) hg
  have hv₀ : 0 < v₀ := Nat.div_pos (Nat.le_of_dvd hv hgv) hg
  have hcop : u₀.Coprime v₀ := Nat.coprime_div_gcd_div_gcd hg
  intro hcross
  have hcross₀ : (∏ m ∈ S, m) * v₀ ^ l =
      (∏ m ∈ T, m) * u₀ ^ l := by
    apply Nat.mul_right_cancel (pow_pos hg l)
    calc
      ((∏ m ∈ S, m) * v₀ ^ l) * g ^ l =
          (∏ m ∈ S, m) * (v₀ * g) ^ l := by rw [mul_pow]; ring
      _ = (∏ m ∈ S, m) * v ^ l := by rw [hvEq]
      _ = (∏ m ∈ T, m) * u ^ l := hcross
      _ = (∏ m ∈ T, m) * (u₀ * g) ^ l := by rw [huEq]
      _ = ((∏ m ∈ T, m) * u₀ ^ l) * g ^ l := by rw [mul_pow]; ring
  exact consecutiveSubproduct_not_coprimeRationalPowerRatio
    hH hl hr hrl hscale hS hT hScard hTcard hST hu₀ hv₀ hcop hcross₀

/-! ## Erdős--Selfridge Lemma 1 -/

/-- Full source Lemma 1 in canonical coefficient form: the ratio of products
of two distinct `r`-subfamilies, for `1 ≤ r < l`, cannot be an `l`-th power
in the positive rationals. -/
theorem powerFreePart_subproduct_not_rationalPowerRatio
    {N H l r u v : ℕ} (hH : 3 ≤ H) (hl : 2 ≤ l)
    (hr : 1 ≤ r) (hrl : r < l) (hscale : H ^ l < N)
    {S T : Finset ℕ} (hS : S ⊆ consecutiveInterval N H)
    (hT : T ⊆ consecutiveInterval N H) (hScard : S.card = r)
    (hTcard : T.card = r) (hST : S ≠ T)
    (hu : 0 < u) (hv : 0 < v) :
    (∏ m ∈ S, powerFreePart l m) * v ^ l ≠
      (∏ m ∈ T, powerFreePart l m) * u ^ l := by
  intro hratio
  have hSpos : ∀ m ∈ S, m ≠ 0 := by
    intro m hm
    have := (Finset.mem_Ioc.mp (hS hm)).1
    omega
  have hTpos : ∀ m ∈ T, m ≠ 0 := by
    intro m hm
    have := (Finset.mem_Ioc.mp (hT hm)).1
    omega
  have hcross :=
    consecutiveSubproduct_crossPower_eq_of_powerFreePart_crossPower_eq
      hSpos hTpos hratio
  exact consecutiveSubproduct_not_rationalPowerRatio hH hl hr hrl hscale
    hS hT hScard hTcard hST
      (Nat.mul_pos hu (Finset.prod_pos fun m _hm =>
        Nat.pos_of_ne_zero (powerRootPart_ne_zero l m)))
      (Nat.mul_pos hv (Finset.prod_pos fun m _hm =>
        Nat.pos_of_ne_zero (powerRootPart_ne_zero l m)))
      hcross

/-- The displayed distinctness conclusion of Lemma 1. -/
theorem powerFreePart_subproduct_injective
    {N H l r : ℕ} (hH : 3 ≤ H) (hl : 2 ≤ l)
    (hr : 1 ≤ r) (hrl : r < l) (hscale : H ^ l < N)
    {S T : Finset ℕ} (hS : S ⊆ consecutiveInterval N H)
    (hT : T ⊆ consecutiveInterval N H) (hScard : S.card = r)
    (hTcard : T.card = r)
    (hprod : (∏ m ∈ S, powerFreePart l m) =
      ∏ m ∈ T, powerFreePart l m) : S = T := by
  by_contra hST
  apply powerFreePart_subproduct_not_rationalPowerRatio hH hl hr hrl hscale
    hS hT hScard hTcard hST (by norm_num : 0 < (1 : ℕ))
      (by norm_num : 0 < (1 : ℕ))
  simpa using hprod

/-- Source-facing package: failure of Theorem 2 and Sylvester--Schur imply
all of Lemma 1, including its stronger rational-ratio assertion. -/
theorem erdosSelfridgeLemmaOne_of_failure
    (hSS : SylvesterSchurConclusion) {N H l r u v : ℕ}
    (hH : 3 ≤ H) (hl : 2 ≤ l) (hHN : H < N)
    (hfail : ErdosSelfridgePrimeMultiplicityFailureAt N H l)
    (hr : 1 ≤ r) (hrl : r < l)
    {S T : Finset ℕ} (hS : S ⊆ consecutiveInterval N H)
    (hT : T ⊆ consecutiveInterval N H) (hScard : S.card = r)
    (hTcard : T.card = r) (hST : S ≠ T)
    (hu : 0 < u) (hv : 0 < v) :
    (∏ m ∈ S, powerFreePart l m) * v ^ l ≠
      (∏ m ∈ T, powerFreePart l m) * u ^ l := by
  exact powerFreePart_subproduct_not_rationalPowerRatio hH hl hr hrl
    (erdosSelfridge_pow_lt_start_of_failure hSS hH hl hHN hfail)
    hS hT hScard hTcard hST hu hv

end Tao2026

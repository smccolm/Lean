import RiemannZeta.GuthMaynard.HughesYoungEquation98
import RiemannZeta.GuthMaynard.DFIDivisorEpsilon

open Complex Finset
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

theorem norm_geomSum_le_card {x : ℂ} (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ‖∑ j ∈ Finset.range n, x ^ j‖ ≤ n := by
  calc
    ‖∑ j ∈ Finset.range n, x ^ j‖ ≤
        ∑ j ∈ Finset.range n, ‖x ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg x) hx
    _ = n := by simp

theorem norm_prime_cpow_neg_two_mul_le_one
    (p : Nat.Primes) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(p : ℂ) ^ (-2 * s)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos]
  have hpOne : (1 : ℝ) ≤ (p : ℕ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr p.2.ne_zero)
  have hexp : (-2 * s).re = -2 * s.re := by norm_num
  calc
    ((p : ℕ) : ℝ) ^ (-2 * s).re ≤
        ((p : ℕ) : ℝ) ^ (0 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hpOne
      rw [hexp]
      linarith
    _ = 1 := by simp

theorem norm_prime_cpow_neg_two_mul_lt_one
    (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    ‖(p : ℂ) ^ (-2 * s)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos]
  have hpOne : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.two_le
  have hexp : (-2 * s).re = -2 * s.re := by norm_num
  apply Real.rpow_lt_one_of_one_lt_of_neg hpOne
  rw [hexp]
  linarith

theorem norm_prime_cpow_neg_natCast_le_one
    (p : Nat.Primes) (n : ℕ) :
    ‖(p : ℂ) ^ (-(n : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos]
  have hpOne : (1 : ℝ) ≤ (p : ℕ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr p.2.ne_zero)
  have hexp : (-(n : ℂ)).re = -(n : ℝ) := by norm_num
  calc
    ((p : ℕ) : ℝ) ^ (-(n : ℂ)).re ≤
        ((p : ℕ) : ℝ) ^ (0 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hpOne
      rw [hexp]
      exact neg_nonpos.mpr (Nat.cast_nonneg n)
    _ = 1 := by simp

theorem prime_cpow_neg_two_eq_inv_sq (p : Nat.Primes) :
    (p : ℂ) ^ (-2 : ℂ) = ((p : ℂ) ^ 2)⁻¹ := by
  rw [show (-2 : ℂ) = -(2 : ℂ) by norm_num, Complex.cpow_neg]
  exact congrArg Inv.inv (Complex.cpow_natCast (p : ℂ) 2)

theorem half_le_norm_one_sub_prime_cpow_neg_two (p : Nat.Primes) :
    (1 / 2 : ℝ) ≤ ‖1 - (p : ℂ) ^ (-2 : ℂ)‖ := by
  rw [prime_cpow_neg_two_eq_inv_sq]
  have hreal : ((p : ℂ) ^ 2)⁻¹ = (((p : ℝ) ^ 2)⁻¹ : ℝ) := by
    rw [Complex.ofReal_inv]
    apply congrArg Inv.inv
    norm_cast
  rw [hreal, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  have hpSq : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  have hpSqPos : 0 < (p : ℝ) ^ 2 := by positivity
  have hinv : ((p : ℝ) ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [inv_le_comm₀ hpSqPos (by norm_num)]
    norm_num
    exact hpSq
  have hnonneg : 0 ≤ 1 - ((p : ℝ) ^ 2)⁻¹ := by
    have : ((p : ℝ) ^ 2)⁻¹ ≤ 1 := hinv.trans (by norm_num)
    linarith
  rw [abs_of_nonneg hnonneg]
  linarith

def hughesYoungCPrimeZeroRegularized
    (e p : ℕ) (x : ℂ) : ℂ :=
  ((∑ j ∈ Finset.range (e + 1), x ^ j) -
      (p : ℂ) ^ (-1 : ℂ) * (1 + x) *
        (∑ j ∈ Finset.range e, x ^ j) +
      (p : ℂ) ^ (-2 : ℂ) * x *
        (∑ j ∈ Finset.range (e - 1), x ^ j)) /
    (1 - (p : ℂ) ^ (-2 : ℂ))

theorem norm_hughesYoungCPrimeZeroRegularized_le
    {e : ℕ} (p : Nat.Primes) {x : ℂ} (hx : ‖x‖ ≤ 1) :
    ‖hughesYoungCPrimeZeroRegularized e p x‖ ≤
      8 * ((e + 1 : ℕ) : ℝ) := by
  let A : ℂ := ∑ j ∈ Finset.range (e + 1), x ^ j
  let B : ℂ := ∑ j ∈ Finset.range e, x ^ j
  let C : ℂ := ∑ j ∈ Finset.range (e - 1), x ^ j
  let E : ℝ := ((e + 1 : ℕ) : ℝ)
  have hA : ‖A‖ ≤ E := by
    dsimp only [A, E]
    exact norm_geomSum_le_card hx (e + 1)
  have hBraw := norm_geomSum_le_card hx e
  have hB : ‖B‖ ≤ E := by
    dsimp only [B, E]
    exact hBraw.trans (by exact_mod_cast Nat.le_add_right e 1)
  have hCraw := norm_geomSum_le_card hx (e - 1)
  have hC : ‖C‖ ≤ E := by
    dsimp only [C, E]
    exact hCraw.trans (by exact_mod_cast (show e - 1 ≤ e + 1 by omega))
  have hOneX : ‖1 + x‖ ≤ 2 := by
    exact (norm_add_le 1 x).trans (by norm_num; linarith)
  have hp1 : ‖(p : ℂ) ^ (-1 : ℂ)‖ ≤ 1 := by
    simpa using norm_prime_cpow_neg_natCast_le_one p 1
  have hp2 : ‖(p : ℂ) ^ (-2 : ℂ)‖ ≤ 1 := by
    simpa using norm_prime_cpow_neg_natCast_le_one p 2
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hnum :
      ‖A - (p : ℂ) ^ (-1 : ℂ) * (1 + x) * B +
          (p : ℂ) ^ (-2 : ℂ) * x * C‖ ≤ 4 * E := by
    calc
      _ ≤ ‖A‖ + ‖(p : ℂ) ^ (-1 : ℂ)‖ * ‖1 + x‖ * ‖B‖ +
          ‖(p : ℂ) ^ (-2 : ℂ)‖ * ‖x‖ * ‖C‖ := by
        calc
          _ ≤ ‖A - (p : ℂ) ^ (-1 : ℂ) * (1 + x) * B‖ +
              ‖(p : ℂ) ^ (-2 : ℂ) * x * C‖ := norm_add_le _ _
          _ ≤ (‖A‖ + ‖(p : ℂ) ^ (-1 : ℂ) * (1 + x) * B‖) +
              ‖(p : ℂ) ^ (-2 : ℂ) * x * C‖ := by
            gcongr
            exact norm_sub_le _ _
          _ = _ := by simp only [norm_mul]
      _ ≤ E + 1 * 2 * E + 1 * 1 * E := by gcongr
      _ = 4 * E := by ring
  have hden := half_le_norm_one_sub_prime_cpow_neg_two p
  unfold hughesYoungCPrimeZeroRegularized
  change ‖(A - (p : ℂ) ^ (-1 : ℂ) * (1 + x) * B +
      (p : ℂ) ^ (-2 : ℂ) * x * C) /
      (1 - (p : ℂ) ^ (-2 : ℂ))‖ ≤ _
  rw [norm_div]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)).2
  change ‖A - (p : ℂ) ^ (-1 : ℂ) * (1 + x) * B +
      (p : ℂ) ^ (-2 : ℂ) * x * C‖ ≤
        (8 * E) * ‖1 - (p : ℂ) ^ (-2 : ℂ)‖
  nlinarith

theorem hughesYoungCPrimeNumerator_zero_eq_one_sub_mul_regularizedNumerator
    {e : ℕ} (he : 0 < e) (p : ℕ) (s : ℂ) :
    hughesYoungCPrimeNumerator e p 0 0 0 0 s =
      (1 - (p : ℂ) ^ (-2 * s)) *
        ((∑ j ∈ Finset.range (e + 1), ((p : ℂ) ^ (-2 * s)) ^ j) -
          (p : ℂ) ^ (-1 : ℂ) * (1 + (p : ℂ) ^ (-2 * s)) *
            (∑ j ∈ Finset.range e, ((p : ℂ) ^ (-2 * s)) ^ j) +
          (p : ℂ) ^ (-2 : ℂ) * (p : ℂ) ^ (-2 * s) *
            (∑ j ∈ Finset.range (e - 1), ((p : ℂ) ^ (-2 * s)) ^ j)) := by
  let x : ℂ := (p : ℂ) ^ (-2 * s)
  have heq : e - 1 + 1 = e := Nat.sub_add_cancel he
  have h0 : (1 - x) * (∑ j ∈ Finset.range (e + 1), x ^ j) =
      1 - x ^ (e + 1) := mul_neg_geom_sum x (e + 1)
  have h1 : (1 - x) * (∑ j ∈ Finset.range e, x ^ j) =
      1 - x ^ e := mul_neg_geom_sum x e
  have h2 : (1 - x) * (x * (∑ j ∈ Finset.range (e - 1), x ^ j)) =
      x - x ^ e := by
    calc
      (1 - x) * (x * (∑ j ∈ Finset.range (e - 1), x ^ j)) =
          x * ((1 - x) * (∑ j ∈ Finset.range (e - 1), x ^ j)) := by ring
      _ = x * (1 - x ^ (e - 1)) := by rw [mul_neg_geom_sum]
      _ = x - x ^ e := by
        rw [mul_sub, mul_one, mul_comm x, ← pow_succ]
        simp only [heq]
  unfold hughesYoungCPrimeNumerator hughesYoungC0 hughesYoungC1 hughesYoungC2
  dsimp only
  simp only [zero_sub, zero_add, sub_zero, neg_zero, Complex.cpow_zero, one_mul]
  rw [show -(2 * s) = -2 * s by ring]
  change 1 - x ^ (1 + e) - (p : ℂ) ^ (-1 : ℂ) *
      ((1 + x) * (1 - x ^ e)) +
      (p : ℂ) ^ (-2 : ℂ) * (x - x ^ e) = _
  rw [Nat.add_comm 1 e]
  rw [← h0, ← h1, ← h2]
  ring

theorem hughesYoungCPrimeFactor_zero_eq_regularized
    {e p : ℕ} (he : 0 < e) (s : ℂ)
    (hx : 1 - (p : ℂ) ^ (-2 * s) ≠ 0) :
    hughesYoungCPrimeFactor e p 0 0 0 0 s =
      hughesYoungCPrimeZeroRegularized e p ((p : ℂ) ^ (-2 * s)) := by
  have hx' : 1 - (p : ℂ) ^ (-(2 * s)) ≠ 0 := by
    rw [show -(2 * s) = -2 * s by ring]
    exact hx
  rw [hughesYoungCPrimeFactor, hughesYoungCPrimeZeroRegularized,
    hughesYoungCPrimeNumerator_zero_eq_one_sub_mul_regularizedNumerator he]
  simp only [zero_sub, sub_zero, neg_zero]
  rw [show (-2 + (0 : ℂ) + 0) = (-2 : ℂ) by ring]
  field_simp [hx']

theorem hughesYoungCPrimeFactor_zero_ne_singular
    (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    1 - (p : ℂ) ^ (-2 * s) ≠ 0 := by
  intro hzero
  have hone : (p : ℂ) ^ (-2 * s) = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm : ‖(p : ℂ) ^ (-2 * s)‖ = 1 := by rw [hone, norm_one]
  linarith [norm_prime_cpow_neg_two_mul_lt_one p hs]

theorem norm_hughesYoungCPrimeFactor_zero_le
    {e : ℕ} (he : 0 < e) (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    ‖hughesYoungCPrimeFactor e p 0 0 0 0 s‖ ≤
      8 * ((e + 1 : ℕ) : ℝ) := by
  rw [hughesYoungCPrimeFactor_zero_eq_regularized he s
    (hughesYoungCPrimeFactor_zero_ne_singular p hs)]
  exact norm_hughesYoungCPrimeZeroRegularized_le p
    (norm_prime_cpow_neg_two_mul_le_one p hs.le)

noncomputable def hughesYoungCZeroMajorant (h : ℕ) : ℝ :=
  ∏ p ∈ hughesYoungPrimeFactors h,
    8 * (((h.factorization p : ℕ) + 1 : ℕ) : ℝ)

theorem hughesYoungCZeroMajorant_eq_primeFactors (h : ℕ) :
    hughesYoungCZeroMajorant h =
      ∏ p ∈ h.primeFactors,
        8 * (((h.factorization p : ℕ) + 1 : ℕ) : ℝ) := by
  unfold hughesYoungCZeroMajorant hughesYoungPrimeFactors
  rw [prod_map]
  simpa using (Finset.prod_attach h.primeFactors
    (fun p => (8 : ℝ) * (((h.factorization p : ℕ) + 1 : ℕ) : ℝ)))

theorem hughesYoungCZeroMajorant_le_divisorsCard_pow_four
    {h : ℕ} (hh : h ≠ 0) :
    hughesYoungCZeroMajorant h ≤ ((h.divisors.card : ℝ) ^ 4) := by
  rw [hughesYoungCZeroMajorant_eq_primeFactors]
  calc
    (∏ p ∈ h.primeFactors,
        8 * (((h.factorization p : ℕ) + 1 : ℕ) : ℝ)) ≤
      ∏ p ∈ h.primeFactors,
        (((h.factorization p : ℕ) + 1 : ℕ) : ℝ) ^ 4 := by
      apply Finset.prod_le_prod
      · intro p _hp
        positivity
      · intro p hp
        have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpdvd : p ∣ h := Nat.dvd_of_mem_primeFactors hp
        have hfac : 1 ≤ h.factorization p :=
          (hpPrime.dvd_iff_one_le_factorization hh).mp hpdvd
        have ha : (2 : ℝ) ≤ ((h.factorization p + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ hfac
        nlinarith [sq_nonneg (((h.factorization p + 1 : ℕ) : ℝ) - 2)]
    _ = (∏ p ∈ h.primeFactors,
          (((h.factorization p : ℕ) + 1 : ℕ) : ℝ)) ^ 4 := by
      rw [Finset.prod_pow]
    _ = ((h.divisors.card : ℝ) ^ 4) := by
      rw [Nat.card_divisors hh]
      norm_cast

theorem norm_hughesYoungC_zero_le_majorant
    {h : ℕ} (hh : 0 < h) {s : ℂ} (hs : 0 < s.re) :
    ‖hughesYoungC h 0 0 0 0 s‖ ≤ hughesYoungCZeroMajorant h := by
  unfold hughesYoungC hughesYoungCZeroMajorant
  rw [norm_prod]
  apply Finset.prod_le_prod
  · intro p _hp
    exact norm_nonneg _
  · intro p hp
    have hpdvd : (p : ℕ) ∣ h :=
      Nat.dvd_of_mem_primeFactors (mem_hughesYoungPrimeFactors.mp hp)
    have he : 0 < h.factorization p := by
      apply Nat.pos_of_ne_zero
      intro he0
      have hcases := (Nat.factorization_eq_zero_iff h p).mp he0
      rcases hcases with hnp | hnd | hh0
      · exact hnp p.2
      · exact hnd hpdvd
      · exact hh.ne' hh0
    exact norm_hughesYoungCPrimeFactor_zero_le he p hs

theorem norm_hughesYoungC_zero_le_divisorsCard_pow_four
    {h : ℕ} (hh : 0 < h) {s : ℂ} (hs : 0 < s.re) :
    ‖hughesYoungC h 0 0 0 0 s‖ ≤ ((h.divisors.card : ℝ) ^ 4) := by
  exact (norm_hughesYoungC_zero_le_majorant hh hs).trans
    (hughesYoungCZeroMajorant_le_divisorsCard_pow_four hh.ne')

theorem norm_hughesYoungC_zero_le_const_mul_rpow
    {ε : ℝ} (hε : 0 < ε) {h : ℕ} (hh : 0 < h)
    {s : ℂ} (hs : 0 < s.re) :
    ‖hughesYoungC h 0 0 0 0 s‖ ≤
      (divisorEpsilonConstant (ε / 4)) ^ 4 * (h : ℝ) ^ ε := by
  have hε4 : 0 < ε / 4 := by positivity
  have hdiv := card_divisors_le_const_mul_rpow hε4 hh.ne'
  have hpow : ((h.divisors.card : ℝ) ^ 4) ≤
      (divisorEpsilonConstant (ε / 4) * (h : ℝ) ^ (ε / 4)) ^ 4 := by
    exact pow_le_pow_left₀ (by positivity) hdiv 4
  calc
    ‖hughesYoungC h 0 0 0 0 s‖ ≤ ((h.divisors.card : ℝ) ^ 4) :=
      norm_hughesYoungC_zero_le_divisorsCard_pow_four hh hs
    _ ≤ (divisorEpsilonConstant (ε / 4) * (h : ℝ) ^ (ε / 4)) ^ 4 := hpow
    _ = (divisorEpsilonConstant (ε / 4)) ^ 4 * (h : ℝ) ^ ε := by
      rw [mul_pow]
      have hh0 : 0 ≤ (h : ℝ) := by positivity
      have hbase : ((h : ℝ) ^ (ε / 4)) ^ (4 : ℕ) = (h : ℝ) ^ ε := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hh0]
        congr 1
        norm_num
      rw [hbase]

theorem hughesYoungEquation98_zeroShifts
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : Nat.Coprime h k)
    {s : ℂ} (hs : (1 / 2 : ℝ) < s.re) :
    hughesYoungEquation96 h k 1 1 (2 * s) =
      (riemannZeta (2 * s) * riemannZeta (1 + 2 * s) /
          riemannZeta 2) *
        (hughesYoungC h 0 0 0 0 s * hughesYoungC k 0 0 0 0 s) := by
  have hs0 : 0 < s.re := by linarith
  have hshift : 0 < ((0 : ℂ) + 0 + 2 * s - 1).re := by
    norm_num
    linarith
  have hhx : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-(0 : ℂ) - 0 - 2 * s) ≠ 0 := by
    intro p _hp
    simpa only [neg_zero, zero_sub, sub_zero, neg_mul] using
      hughesYoungCPrimeFactor_zero_ne_singular p hs0
  have hkx : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-(0 : ℂ) - 0 - 2 * s) ≠ 0 := by
    intro p _hp
    simpa only [neg_zero, zero_sub, sub_zero, neg_mul] using
      hughesYoungCPrimeFactor_zero_ne_singular p hs0
  simpa only [sub_zero, zero_add, add_zero] using
    (hughesYoungEquation98 hh hk hhk
      (alpha := 0) (beta := 0) (gamma := 0) (delta := 0) (s := s)
      (by norm_num) hshift hhx hkx)

end RiemannZeta.GuthMaynard

import RiemannZeta.GuthMaynard.HughesYoungCFunctionalEquation
import RiemannZeta.GuthMaynard.HughesYoungZFactors
open Complex
open Finset
open scoped BigOperators

example {e : ℕ} {x : ℂ} (hx : x ≠ 0) (hx1 : 1 - x ≠ 0) :
    (1 - x ^ (1 + e)) / (1-x) =
      x^e * ((1-(x⁻¹)^(1+e))/(1-x⁻¹)) := by
  have hden : 1 - x⁻¹ = (x - 1) / x := by field_simp [hx]
  have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hx1))
  have hdiv (A : ℂ) : A / ((x - 1) / x) = A * x / (x - 1) := by
    field_simp [hx]
  rw [hden, hdiv]
  rw [Nat.one_add]
  simp only [pow_succ, inv_pow]
  field_simp [hx, hx1, hxm, pow_ne_zero]
  ring

example {e : ℕ} {x u v : ℂ} (hx : x ≠ 0) (hx1 : 1 - x ≠ 0) :
    ((u+v*x)*(1-x^e))/(1-x) =
      x^e * (((v+u*x⁻¹)*(1-(x⁻¹)^e))/(1-x⁻¹)) := by
  have hden : 1 - x⁻¹ = (x - 1) / x := by field_simp [hx]
  have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hx1))
  have hdiv (A : ℂ) : A / ((x - 1) / x) = A * x / (x - 1) := by
    field_simp [hx]
  rw [hden, hdiv]
  simp only [inv_pow]
  field_simp [hx, hx1, hxm, pow_ne_zero]
  ring

example {e : ℕ} {x : ℂ} (hx : x ≠ 0) (hx1 : 1 - x ≠ 0) :
    (x-x^e)/(1-x) = x^e*((x⁻¹-(x⁻¹)^e)/(1-x⁻¹)) := by
  have hden : 1 - x⁻¹ = (x - 1) / x := by field_simp [hx]
  have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hx1))
  have hdiv (A : ℂ) : A / ((x - 1) / x) = A * x / (x - 1) := by
    field_simp [hx]
  rw [hden, hdiv]
  simp only [inv_pow]
  field_simp [hx, hx1, hxm, pow_ne_zero]
  ring

#check Complex.cpow_ne_zero_iff
#check Complex.cpow_add
#check Complex.cpow_mul_nat
#check Complex.cpow_nat_mul
#check Complex.cpow_natCast
#check Nat.prod_factorization_pow_eq_self
#check Finsupp.prod
#check Finset.prod_attach
#check Complex.natCast_mul_natCast_cpow
#check Complex.ofReal_cpow

open RiemannZeta.GuthMaynard

example {h : ℕ} (hh : h ≠ 0) :
    ∏ p ∈ hughesYoungPrimeFactors h,
        ((p : ℕ) ^ (h.factorization p)) = h := by
  unfold hughesYoungPrimeFactors
  rw [prod_map]
  change (∏ x ∈ h.primeFactors.attach, x.1 ^ h.factorization x.1) = h
  simpa [← Nat.prod_factorization_eq_prod_primeFactors] using
    Nat.prod_factorization_pow_eq_self hh

example (s : Finset ℕ) (f : ℕ → ℕ) (z : ℂ) :
    (∏ p ∈ s, ((f p : ℕ) : ℂ) ^ z) =
      (((∏ p ∈ s, f p) : ℕ) : ℂ) ^ z := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.cast_mul]
      rw [Complex.natCast_mul_natCast_cpow]
      rw [ih]

example {h : ℕ} (hh : h ≠ 0) (z : ℂ) :
    ∏ p ∈ hughesYoungPrimeFactors h,
        ((p : ℂ) ^ z) ^ (h.factorization p) = (h : ℂ) ^ z := by
  calc
    _ = ∏ p ∈ hughesYoungPrimeFactors h,
        (((p : ℕ) ^ (h.factorization p) : ℕ) : ℂ) ^ z := by
      apply Finset.prod_congr rfl
      intro p _hp
      rw [Nat.cast_pow]
      rw [← Complex.natCast_cpow_natCast_mul]
      exact (Complex.cpow_nat_mul (p : ℂ) (h.factorization p) z).symm
    _ = (((∏ p ∈ hughesYoungPrimeFactors h,
        (p : ℕ) ^ (h.factorization p)) : ℕ) : ℂ) ^ z := by
      induction hughesYoungPrimeFactors h using Finset.induction_on with
      | empty => simp
      | @insert p s hp ih =>
          rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.cast_mul]
          rw [Complex.natCast_mul_natCast_cpow]
          rw [ih]
    _ = _ := by
      rw [show ∏ p ∈ hughesYoungPrimeFactors h,
          (p : ℕ) ^ (h.factorization p) = h by
        unfold hughesYoungPrimeFactors
        rw [prod_map]
        change (∏ x ∈ h.primeFactors.attach, x.1 ^ h.factorization x.1) = h
        simpa [← Nat.prod_factorization_eq_prod_primeFactors] using
          Nat.prod_factorization_pow_eq_self hh]

example {e : ℕ} {x u v a b r : ℂ}
    (hx : x ≠ 0) (hx1 : 1-x ≠ 0) (hr : r ≠ 0) :
    ((1-x^(1+e))-a*((u+v*x)*(1-x^e))+b*(x-x^e))/(r*(1-x)) =
      x^e * (((1-(x⁻¹)^(1+e))-a*((v+u*x⁻¹)*(1-(x⁻¹)^e))+
        b*(x⁻¹-(x⁻¹)^e))/(r*(1-x⁻¹))) := by
  have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hx1))
  rw [Nat.one_add]
  simp only [pow_succ, inv_pow]
  field_simp [hx, hx1, hxm, hr, pow_ne_zero]
  ring

example (e p : ℕ) (hp : 0 < p) (alpha delta : ℂ) :
    (p : ℂ) ^ (alpha * (e : ℕ)) *
        hughesYoungC0 e ((p : ℂ) ^ (-alpha - delta)) =
      (p : ℂ) ^ (-alpha) * hughesYoungB0 e p (-alpha) delta := by
  let A : ℂ := (p : ℂ) ^ alpha
  let D : ℂ := (p : ℂ) ^ (-delta)
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hA : A ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  have hAi : (p : ℂ) ^ (-alpha) = A⁻¹ := by
    exact Complex.cpow_neg (p : ℂ) alpha
  have hD : (p : ℂ) ^ (-delta) = D := rfl
  have hAD : (p : ℂ) ^ (-alpha - delta) = A⁻¹ * D := by
    rw [show -alpha - delta = -alpha + -delta by ring]
    rw [Complex.cpow_add _ _ hpC, hAi, hD]
  have hAe : (p : ℂ) ^ (alpha * (e : ℕ)) = A ^ e := by
    exact Complex.cpow_mul_nat _ _ _
  have hA1 : (p : ℂ) ^ (alpha * (1 + e : ℕ)) = A ^ (1 + e) := by
    exact Complex.cpow_mul_nat _ _ _
  have hD1 : (p : ℂ) ^ (-delta * (1 + e : ℕ)) = D ^ (1 + e) := by
    exact Complex.cpow_mul_nat _ _ _
  rw [hAe, hAD, hughesYoungB0]
  rw [show - -alpha = alpha by ring, hA1, hD1, hAi]
  exact hughesYoungEquation161_algebra hA

example (e p : ℕ) (hp : 0 < p) (alpha beta gamma delta : ℂ) :
    (p : ℂ) ^ (alpha * (e : ℕ)) *
        hughesYoungC1 e ((p : ℂ) ^ (gamma - delta))
          ((p : ℂ) ^ (alpha - beta))
          ((p : ℂ) ^ (-alpha - delta)) =
      (p : ℂ) ^ (-alpha) *
        hughesYoungB1 e p (-gamma) beta (-alpha) delta 0 := by
  let A : ℂ := (p : ℂ) ^ alpha
  let B : ℂ := (p : ℂ) ^ (-beta)
  let G : ℂ := (p : ℂ) ^ gamma
  let D : ℂ := (p : ℂ) ^ (-delta)
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hA : A ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  have hAi : (p : ℂ) ^ (-alpha) = A⁻¹ := Complex.cpow_neg _ _
  have hAe : (p : ℂ) ^ (alpha * (e : ℕ)) = A ^ e :=
    Complex.cpow_mul_nat _ _ _
  have hGD : (p : ℂ) ^ (gamma - delta) = G * D := by
    rw [show gamma-delta=gamma+(-delta) by ring]
    exact Complex.cpow_add _ _ hpC
  have hAB : (p : ℂ) ^ (alpha - beta) = A * B := by
    rw [show alpha-beta=alpha+(-beta) by ring]
    exact Complex.cpow_add _ _ hpC
  have hAD : (p : ℂ) ^ (-alpha - delta) = A⁻¹ * D := by
    rw [show -alpha-delta=(-alpha)+(-delta) by ring]
    rw [Complex.cpow_add _ _ hpC, hAi]
  have hApD : (p : ℂ) ^ (alpha - delta) = A * D := by
    rw [show alpha-delta=alpha+(-delta) by ring]
    exact Complex.cpow_add _ _ hpC
  have hDe : (p : ℂ) ^ (-delta * (e : ℕ)) = D ^ e :=
    Complex.cpow_mul_nat _ _ _
  rw [hAe, hGD, hAB, hAD, hughesYoungB1]
  rw [show - -gamma = gamma by ring]
  rw [show - -alpha - delta = alpha - delta by ring, hApD]
  rw [show - -alpha * (e : ℕ) = alpha * (e : ℕ) by ring, hAe, hDe]
  rw [neg_zero, Complex.cpow_zero, mul_one, hAi]
  change A ^ e * hughesYoungC1 e (G * D) (A * B) (A⁻¹ * D) =
    A⁻¹ * ((G + B) * (A * D) * (A ^ e - D ^ e))
  unfold hughesYoungC1
  simpa only [mul_assoc] using
    (hughesYoungEquation162_algebra (e := e) (B := B) (G := G) (D := D) hA)

example (e p : ℕ) (hp : 0 < p) (alpha beta gamma delta : ℂ) :
    (p : ℂ) ^ (alpha * (e : ℕ)) *
        ((p : ℂ) ^ (alpha - beta + gamma - delta) *
          hughesYoungC2 e ((p : ℂ) ^ (-alpha - delta))) =
      (p : ℂ) ^ (-alpha) *
        hughesYoungB2 e p (-gamma) beta (-alpha) delta 0 := by
  let A : ℂ := (p : ℂ) ^ alpha
  let B : ℂ := (p : ℂ) ^ (-beta)
  let G : ℂ := (p : ℂ) ^ gamma
  let D : ℂ := (p : ℂ) ^ (-delta)
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hA : A ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  have hAi : (p : ℂ) ^ (-alpha) = A⁻¹ := Complex.cpow_neg _ _
  have hAe : (p : ℂ) ^ (alpha * (e : ℕ)) = A ^ e :=
    Complex.cpow_mul_nat _ _ _
  have hDe : (p : ℂ) ^ (-delta * (e : ℕ)) = D ^ e :=
    Complex.cpow_mul_nat _ _ _
  have hAD : (p : ℂ) ^ (-alpha - delta) = A⁻¹ * D := by
    rw [show -alpha - delta = (-alpha) + (-delta) by ring]
    rw [Complex.cpow_add _ _ hpC, hAi]
  have hABGD : (p : ℂ) ^ (alpha - beta + gamma - delta) = A*B*G*D := by
    rw [show alpha-beta+gamma-delta=alpha+(-beta)+gamma+(-delta) by ring]
    rw [Complex.cpow_add _ _ hpC, Complex.cpow_add _ _ hpC,
      Complex.cpow_add _ _ hpC]
  have hGBAD : (p : ℂ) ^ (gamma - beta + alpha - delta) = G*B*A*D := by
    rw [show gamma-beta+alpha-delta=gamma+(-beta)+alpha+(-delta) by ring]
    rw [Complex.cpow_add _ _ hpC, Complex.cpow_add _ _ hpC,
      Complex.cpow_add _ _ hpC]
  have hDAe : (p : ℂ) ^ (-delta + alpha * (e : ℕ)) = D*A^e := by
    rw [Complex.cpow_add _ _ hpC, hAe]
  have hADe : (p : ℂ) ^ (alpha - delta * (e : ℕ)) = A*D^e := by
    rw [show alpha-delta*(e:ℕ)=alpha+(-delta*(e:ℕ)) by ring]
    rw [Complex.cpow_add _ _ hpC, hDe]
  rw [hAe, hABGD, hAD, hughesYoungB2]
  rw [show - -gamma - beta - -alpha - delta = gamma-beta+alpha-delta by ring,
    hGBAD]
  rw [show -delta - -alpha * (e : ℕ) = -delta+alpha*(e:ℕ) by ring, hDAe]
  rw [show - -alpha - delta * (e : ℕ) = alpha-delta*(e:ℕ) by ring, hADe]
  rw [mul_zero, Complex.cpow_zero, mul_one, hAi]
  unfold hughesYoungC2
  simpa only [mul_assoc] using
    (hughesYoungEquation163_algebra (e := e) (B := B) (G := G) (D := D) hA)

example (e p : ℕ) (hp : 0 < p) (alpha beta gamma delta : ℂ)
    (hc : 1 - (p : ℂ)^(-alpha-delta) ≠ 0)
    (hr : 1 - (p : ℂ)^(-2+alpha-beta+gamma-delta) ≠ 0) :
    (p : ℂ)^(alpha*(e:ℕ)) *
      hughesYoungCPrimeFactor e p alpha beta gamma delta 0 =
      hughesYoungBPrimeFactor e p (-gamma) beta (-alpha) delta 0 := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpAlpha : (p : ℂ)^alpha ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  have hnum :
      (p : ℂ)^(alpha*(e:ℕ)) *
        (hughesYoungC0 e ((p:ℂ)^(-alpha-delta)) -
          (p:ℂ)^(-1:ℂ) * hughesYoungC1 e ((p:ℂ)^(gamma-delta))
            ((p:ℂ)^(alpha-beta)) ((p:ℂ)^(-alpha-delta)) +
          (p:ℂ)^(-2:ℂ) * ((p:ℂ)^(alpha-beta+gamma-delta) *
            hughesYoungC2 e ((p:ℂ)^(-alpha-delta)))) =
      (p:ℂ)^(-alpha) *
        (hughesYoungB0 e p (-alpha) delta -
          (p:ℂ)^(-1:ℂ) * hughesYoungB1 e p (-gamma) beta (-alpha) delta 0 +
          (p:ℂ)^(-2:ℂ) * hughesYoungB2 e p (-gamma) beta (-alpha) delta 0) := by
    linear_combination
      hughesYoungEquation161 e p hp alpha delta -
      (p:ℂ)^(-1:ℂ) * hughesYoungEquation162 e p hp alpha beta gamma delta +
      (p:ℂ)^(-2:ℂ) * hughesYoungEquation163 e p hp alpha beta gamma delta
  have hfirst :
      (p:ℂ)^alpha * (1-(p:ℂ)^(-alpha-delta)) =
        (p:ℂ)^alpha-(p:ℂ)^(-delta) := by
    rw [mul_sub, mul_one]
    rw [show -alpha-delta=(-alpha)+(-delta) by ring]
    rw [Complex.cpow_add _ _ hpC, Complex.cpow_neg]
    field_simp [hpAlpha]
  unfold hughesYoungCPrimeFactor hughesYoungCPrimeNumerator
    hughesYoungBPrimeFactor
  dsimp only
  simp only [mul_zero, sub_zero, neg_neg]
  rw [show -2 - -gamma - beta - -alpha - delta =
    -2+alpha-beta+gamma-delta by ring]
  have hbfirst : (p:ℂ)^alpha-(p:ℂ)^(-delta) ≠ 0 := by
    rw [← hfirst]
    exact mul_ne_zero hpAlpha hc
  rw [← mul_div_assoc, hnum]
  rw [← hfirst]
  rw [Complex.cpow_neg]
  field_simp [hpAlpha, hc, hr, hbfirst]

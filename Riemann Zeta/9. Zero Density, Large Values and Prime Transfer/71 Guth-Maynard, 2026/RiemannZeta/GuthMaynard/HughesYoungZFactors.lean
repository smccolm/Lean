import RiemannZeta.GuthMaynard.HughesYoungCFunctionalEquation

open Complex Finset
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Hughes--Young equations (140)--(178): finite Euler factors

The `B` factors below are the literal rational Euler factors in equations
(142)--(156).  The algebraic identities at the end are the local content of
equations (161)--(163) and (170)--(172).  They are kept separate from residue
calculus so the arithmetic cancellation can be audited independently.
-/

/-- Equation (143). -/
def hughesYoungB0 (e p : ℕ) (gamma delta : ℂ) : ℂ :=
  (p : ℂ) ^ (-gamma * (1 + e : ℕ)) -
    (p : ℂ) ^ (-delta * (1 + e : ℕ))

/-- Equation (144). -/
def hughesYoungB1
    (e p : ℕ) (alpha beta gamma delta s : ℂ) : ℂ :=
  ((p : ℂ) ^ (-alpha) + (p : ℂ) ^ (-beta)) *
    (p : ℂ) ^ (-gamma - delta) *
    ((p : ℂ) ^ (-gamma * (e : ℕ)) -
      (p : ℂ) ^ (-delta * (e : ℕ))) *
    (p : ℂ) ^ (-s)

/-- Equation (145). -/
def hughesYoungB2
    (e p : ℕ) (alpha beta gamma delta s : ℂ) : ℂ :=
  (p : ℂ) ^ (-alpha - beta - gamma - delta) *
    ((p : ℂ) ^ (-delta - gamma * (e : ℕ)) -
      (p : ℂ) ^ (-gamma - delta * (e : ℕ))) *
    (p : ℂ) ^ (-2 * s)

/-- Equation (142), the local factor at `p^e || h`. -/
def hughesYoungBPrimeFactor
    (e p : ℕ) (alpha beta gamma delta s : ℂ) : ℂ :=
  (hughesYoungB0 e p gamma delta -
      (p : ℂ) ^ (-1 : ℂ) *
        hughesYoungB1 e p alpha beta gamma delta s +
      (p : ℂ) ^ (-2 : ℂ) *
        hughesYoungB2 e p alpha beta gamma delta s) /
    (((p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta)) *
      (1 - (p : ℂ) ^
        (-2 - alpha - beta - gamma - delta - 2 * s)))

/-- Equation (140), in its finite rational Euler-product form. -/
def hughesYoungB
    (h : ℕ) (alpha beta gamma delta s : ℂ) : ℂ :=
  ∏ p ∈ hughesYoungPrimeFactors h,
    hughesYoungBPrimeFactor (h.factorization p) p
      alpha beta gamma delta s

/-- Equation (141). -/
def hughesYoungBPair
    (h k : ℕ) (alpha beta gamma delta s : ℂ) : ℂ :=
  hughesYoungB h alpha beta gamma delta s *
    hughesYoungB k gamma delta alpha beta s

/-- Algebraic core of equation (161).  The source substitution is
`A = p^alpha` and `D = p^(-delta)`. -/
theorem hughesYoungEquation161_algebra
    {e : ℕ} {A D : ℂ} (hA : A ≠ 0) :
    A ^ e * (1 - (A⁻¹ * D) ^ (1 + e)) =
      A⁻¹ * (A ^ (1 + e) - D ^ (1 + e)) := by
  rw [Nat.one_add]
  simp only [pow_succ, mul_pow, inv_pow]
  field_simp [hA, pow_ne_zero]

/-- Algebraic core of equation (162), with
`A=p^alpha`, `B=p^(-beta)`, `G=p^gamma`, `D=p^(-delta)`. -/
theorem hughesYoungEquation162_algebra
    {e : ℕ} {A B G D : ℂ} (hA : A ≠ 0) :
    A ^ e * (G * D + (A * B) * (A⁻¹ * D)) *
        (1 - (A⁻¹ * D) ^ e) =
      A⁻¹ * (G + B) * (A * D) * (A ^ e - D ^ e) := by
  simp only [mul_pow, inv_pow]
  field_simp [hA, pow_ne_zero]

/-- Algebraic core of equation (163). -/
theorem hughesYoungEquation163_algebra
    {e : ℕ} {A B G D : ℂ} (hA : A ≠ 0) :
    A ^ e * (A * B * G * D) *
        (A⁻¹ * D - (A⁻¹ * D) ^ e) =
      A⁻¹ * (G * B * A * D) *
        (D * A ^ e - A * D ^ e) := by
  simp only [mul_pow, inv_pow]
  field_simp [hA, pow_ne_zero]

/-- Algebraic core of equation (170), with
`G=p^gamma` and `D=p^(-delta)`. -/
theorem hughesYoungEquation170_algebra
    {e : ℕ} {G D : ℂ} (hG : G ≠ 0) :
    (G⁻¹) ^ e * (1 - (G * D) ^ (1 + e)) =
      G * ((G⁻¹) ^ (1 + e) - D ^ (1 + e)) := by
  rw [Nat.one_add]
  simp only [pow_succ, mul_pow, inv_pow]
  field_simp [hG, pow_ne_zero]

/-- Algebraic core of equation (171). -/
theorem hughesYoungEquation171_algebra
    {e : ℕ} {A B G D : ℂ} (hA : A ≠ 0) (hG : G ≠ 0) :
    (G⁻¹) ^ e * (G * D + (A * B) * (G * D)) *
        (1 - (G * D) ^ e) =
      G * (A⁻¹ + B) * (G⁻¹ * D) *
        ((G⁻¹) ^ e - D ^ e) * (A * G) := by
  simp only [mul_pow, inv_pow]
  field_simp [hA, hG, pow_ne_zero]

/-- Algebraic core of equation (172). -/
theorem hughesYoungEquation172_algebra
    {e : ℕ} {A B G D : ℂ} (hA : A ≠ 0) (hG : G ≠ 0) :
    (G⁻¹) ^ e * (A * B * G * D) *
        (G * D - (G * D) ^ e) =
      G * (A⁻¹ * B * G⁻¹ * D) *
        (D * (G⁻¹) ^ e - G⁻¹ * D ^ e) *
        (A * G) ^ 2 := by
  simp only [mul_pow, inv_pow]
  field_simp [hA, hG, pow_ne_zero]

/-- Hughes--Young equation (161), with the source prime-power
substitutions restored. -/
theorem hughesYoungEquation161
    (e p : ℕ) (hp : 0 < p) (alpha delta : ℂ) :
    (p : ℂ) ^ (alpha * (e : ℕ)) *
        hughesYoungC0 e ((p : ℂ) ^ (-alpha - delta)) =
      (p : ℂ) ^ (-alpha) * hughesYoungB0 e p (-alpha) delta := by
  let A : ℂ := (p : ℂ) ^ alpha
  let D : ℂ := (p : ℂ) ^ (-delta)
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hA : A ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  have hAi : (p : ℂ) ^ (-alpha) = A⁻¹ :=
    Complex.cpow_neg (p : ℂ) alpha
  have hAD : (p : ℂ) ^ (-alpha - delta) = A⁻¹ * D := by
    rw [show -alpha - delta = -alpha + -delta by ring]
    rw [Complex.cpow_add _ _ hpC, hAi]
  have hAe : (p : ℂ) ^ (alpha * (e : ℕ)) = A ^ e :=
    Complex.cpow_mul_nat _ _ _
  have hA1 : (p : ℂ) ^ (alpha * (1 + e : ℕ)) = A ^ (1 + e) :=
    Complex.cpow_mul_nat _ _ _
  have hD1 : (p : ℂ) ^ (-delta * (1 + e : ℕ)) = D ^ (1 + e) :=
    Complex.cpow_mul_nat _ _ _
  rw [hAe, hAD, hughesYoungB0]
  rw [show - -alpha = alpha by ring, hA1, hD1, hAi]
  exact hughesYoungEquation161_algebra hA

/-- Hughes--Young equation (162), with the source prime-power
substitutions restored. -/
theorem hughesYoungEquation162
    (e p : ℕ) (hp : 0 < p) (alpha beta gamma delta : ℂ) :
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
    rw [show gamma - delta = gamma + (-delta) by ring]
    exact Complex.cpow_add _ _ hpC
  have hAB : (p : ℂ) ^ (alpha - beta) = A * B := by
    rw [show alpha - beta = alpha + (-beta) by ring]
    exact Complex.cpow_add _ _ hpC
  have hAD : (p : ℂ) ^ (-alpha - delta) = A⁻¹ * D := by
    rw [show -alpha - delta = (-alpha) + (-delta) by ring]
    rw [Complex.cpow_add _ _ hpC, hAi]
  have hApD : (p : ℂ) ^ (alpha - delta) = A * D := by
    rw [show alpha - delta = alpha + (-delta) by ring]
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

/-- Hughes--Young equation (163), with the source prime-power
substitutions restored. -/
theorem hughesYoungEquation163
    (e p : ℕ) (hp : 0 < p) (alpha beta gamma delta : ℂ) :
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
  have hABGD : (p : ℂ) ^ (alpha - beta + gamma - delta) = A * B * G * D := by
    rw [show alpha - beta + gamma - delta =
      alpha + (-beta) + gamma + (-delta) by ring]
    rw [Complex.cpow_add _ _ hpC, Complex.cpow_add _ _ hpC,
      Complex.cpow_add _ _ hpC]
  have hGBAD : (p : ℂ) ^ (gamma - beta + alpha - delta) = G * B * A * D := by
    rw [show gamma - beta + alpha - delta =
      gamma + (-beta) + alpha + (-delta) by ring]
    rw [Complex.cpow_add _ _ hpC, Complex.cpow_add _ _ hpC,
      Complex.cpow_add _ _ hpC]
  have hDAe : (p : ℂ) ^ (-delta + alpha * (e : ℕ)) = D * A ^ e := by
    rw [Complex.cpow_add _ _ hpC, hAe]
  have hADe : (p : ℂ) ^ (alpha - delta * (e : ℕ)) = A * D ^ e := by
    rw [show alpha - delta * (e : ℕ) =
      alpha + (-delta * (e : ℕ)) by ring]
    rw [Complex.cpow_add _ _ hpC, hDe]
  rw [hAe, hABGD, hAD, hughesYoungB2]
  rw [show - -gamma - beta - -alpha - delta =
    gamma - beta + alpha - delta by ring, hGBAD]
  rw [show -delta - -alpha * (e : ℕ) =
    -delta + alpha * (e : ℕ) by ring, hDAe]
  rw [show - -alpha - delta * (e : ℕ) =
    alpha - delta * (e : ℕ) by ring, hADe]
  rw [mul_zero, Complex.cpow_zero, mul_one, hAi]
  unfold hughesYoungC2
  simpa only [mul_assoc] using
    (hughesYoungEquation163_algebra (e := e) (B := B) (G := G) (D := D) hA)

/-- Primewise combination of equations (161)--(163), including the two
denominators in equations (142) and (100). -/
theorem hughesYoungEquation160_local
    (e p : ℕ) (hp : 0 < p) (alpha beta gamma delta : ℂ)
    (hc : 1 - (p : ℂ) ^ (-alpha - delta) ≠ 0)
    (hr : 1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0) :
    (p : ℂ) ^ (alpha * (e : ℕ)) *
        hughesYoungCPrimeFactor e p alpha beta gamma delta 0 =
      hughesYoungBPrimeFactor e p (-gamma) beta (-alpha) delta 0 := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpAlpha : (p : ℂ) ^ alpha ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  have hnum :
      (p : ℂ) ^ (alpha * (e : ℕ)) *
        (hughesYoungC0 e ((p : ℂ) ^ (-alpha - delta)) -
          (p : ℂ) ^ (-1 : ℂ) *
            hughesYoungC1 e ((p : ℂ) ^ (gamma - delta))
              ((p : ℂ) ^ (alpha - beta))
              ((p : ℂ) ^ (-alpha - delta)) +
          (p : ℂ) ^ (-2 : ℂ) *
            ((p : ℂ) ^ (alpha - beta + gamma - delta) *
              hughesYoungC2 e ((p : ℂ) ^ (-alpha - delta)))) =
      (p : ℂ) ^ (-alpha) *
        (hughesYoungB0 e p (-alpha) delta -
          (p : ℂ) ^ (-1 : ℂ) *
            hughesYoungB1 e p (-gamma) beta (-alpha) delta 0 +
          (p : ℂ) ^ (-2 : ℂ) *
            hughesYoungB2 e p (-gamma) beta (-alpha) delta 0) := by
    linear_combination
      hughesYoungEquation161 e p hp alpha delta -
      (p : ℂ) ^ (-1 : ℂ) *
        hughesYoungEquation162 e p hp alpha beta gamma delta +
      (p : ℂ) ^ (-2 : ℂ) *
        hughesYoungEquation163 e p hp alpha beta gamma delta
  have hfirst :
      (p : ℂ) ^ alpha * (1 - (p : ℂ) ^ (-alpha - delta)) =
        (p : ℂ) ^ alpha - (p : ℂ) ^ (-delta) := by
    rw [mul_sub, mul_one]
    rw [show -alpha - delta = (-alpha) + (-delta) by ring]
    rw [Complex.cpow_add _ _ hpC, Complex.cpow_neg]
    field_simp [hpAlpha]
  unfold hughesYoungCPrimeFactor hughesYoungCPrimeNumerator
    hughesYoungBPrimeFactor
  dsimp only
  simp only [mul_zero, sub_zero, neg_neg]
  rw [show -2 - -gamma - beta - -alpha - delta =
    -2 + alpha - beta + gamma - delta by ring]
  have hbfirst : (p : ℂ) ^ alpha - (p : ℂ) ^ (-delta) ≠ 0 := by
    rw [← hfirst]
    exact mul_ne_zero hpAlpha hc
  rw [← mul_div_assoc, hnum]
  rw [← hfirst]
  rw [Complex.cpow_neg]
  field_simp [hpAlpha, hc, hr, hbfirst]

/-- Hughes--Young equation (158), obtained by multiplying the three local
identities (161)--(163) over the prime factors of `h`. -/
theorem hughesYoungEquation158
    {h : ℕ} (hh : 0 < h) {alpha beta gamma delta : ℂ}
    (hc : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-alpha - delta) ≠ 0)
    (hr : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0) :
    (h : ℂ) ^ alpha * hughesYoungC h alpha beta gamma delta 0 =
      hughesYoungB h (-gamma) beta (-alpha) delta 0 := by
  rw [hughesYoungC, hughesYoungB]
  calc
    (h : ℂ) ^ alpha *
        ∏ p ∈ hughesYoungPrimeFactors h,
          hughesYoungCPrimeFactor (h.factorization p) p
            alpha beta gamma delta 0 =
      (∏ p ∈ hughesYoungPrimeFactors h,
          ((p : ℂ) ^ alpha) ^ (h.factorization p)) *
        ∏ p ∈ hughesYoungPrimeFactors h,
          hughesYoungCPrimeFactor (h.factorization p) p
            alpha beta gamma delta 0 := by
        rw [prod_hughesYoungPrimeFactors_cpow hh.ne']
    _ = ∏ p ∈ hughesYoungPrimeFactors h,
        (((p : ℂ) ^ alpha) ^ (h.factorization p) *
          hughesYoungCPrimeFactor (h.factorization p) p
            alpha beta gamma delta 0) := by
        rw [Finset.prod_mul_distrib]
    _ = ∏ p ∈ hughesYoungPrimeFactors h,
        hughesYoungBPrimeFactor (h.factorization p) p
          (-gamma) beta (-alpha) delta 0 := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [← Complex.cpow_mul_nat]
        exact hughesYoungEquation160_local (h.factorization p) p p.2.pos
          alpha beta gamma delta (hc p hp) (hr p hp)

/-- Hughes--Young equation (157), the two-variable form of (158). -/
theorem hughesYoungEquation157
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {alpha beta gamma delta : ℂ}
    (hhc : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-alpha - delta) ≠ 0)
    (hhr : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0)
    (hkc : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-gamma - beta) ≠ 0)
    (hkr : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-2 + gamma - delta + alpha - beta) ≠ 0) :
    (h : ℂ) ^ alpha * (k : ℂ) ^ gamma *
        (hughesYoungC h alpha beta gamma delta 0 *
          hughesYoungC k gamma delta alpha beta 0) =
      hughesYoungBPair h k (-gamma) beta (-alpha) delta 0 := by
  have hH := hughesYoungEquation158 hh hhc hhr
  have hK := hughesYoungEquation158 (h := k) hk hkc hkr
  unfold hughesYoungBPair
  calc
    (h : ℂ) ^ alpha * (k : ℂ) ^ gamma *
        (hughesYoungC h alpha beta gamma delta 0 *
          hughesYoungC k gamma delta alpha beta 0) =
      ((h : ℂ) ^ alpha * hughesYoungC h alpha beta gamma delta 0) *
        ((k : ℂ) ^ gamma * hughesYoungC k gamma delta alpha beta 0) := by
        ring
    _ = _ := by rw [hH, hK]

/-- Hughes--Young equation (170), with the source prime-power
substitutions restored. -/
theorem hughesYoungEquation170
    (e p : ℕ) (hp : 0 < p) (gamma delta : ℂ) :
    (p : ℂ) ^ (-gamma * (e : ℕ)) *
        hughesYoungC0 e ((p : ℂ) ^ (gamma - delta)) =
      (p : ℂ) ^ gamma * hughesYoungB0 e p gamma delta := by
  let G : ℂ := (p : ℂ) ^ gamma
  let D : ℂ := (p : ℂ) ^ (-delta)
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hG : G ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  have hGi : (p : ℂ) ^ (-gamma) = G⁻¹ := Complex.cpow_neg _ _
  have hGie : (p : ℂ) ^ (-gamma * (e : ℕ)) = (G⁻¹) ^ e := by
    rw [Complex.cpow_mul_nat, hGi]
  have hGD : (p : ℂ) ^ (gamma - delta) = G * D := by
    rw [show gamma - delta = gamma + (-delta) by ring]
    exact Complex.cpow_add _ _ hpC
  have hGi1 : (p : ℂ) ^ (-gamma * (1 + e : ℕ)) =
      (G⁻¹) ^ (1 + e) := by
    rw [Complex.cpow_mul_nat, hGi]
  have hD1 : (p : ℂ) ^ (-delta * (1 + e : ℕ)) = D ^ (1 + e) :=
    Complex.cpow_mul_nat _ _ _
  rw [hGie, hGD, hughesYoungB0, hGi1, hD1]
  exact hughesYoungEquation170_algebra hG

/-- Hughes--Young equation (171), with the source prime-power
substitutions restored. -/
theorem hughesYoungEquation171
    (e p : ℕ) (hp : 0 < p) (alpha beta gamma delta : ℂ) :
    (p : ℂ) ^ (-gamma * (e : ℕ)) *
        hughesYoungC1 e ((p : ℂ) ^ (gamma - delta))
          ((p : ℂ) ^ (alpha - beta))
          ((p : ℂ) ^ (gamma - delta)) =
      (p : ℂ) ^ gamma *
        hughesYoungB1 e p alpha beta gamma delta (-alpha - gamma) := by
  let A : ℂ := (p : ℂ) ^ alpha
  let B : ℂ := (p : ℂ) ^ (-beta)
  let G : ℂ := (p : ℂ) ^ gamma
  let D : ℂ := (p : ℂ) ^ (-delta)
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hA : A ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  have hG : G ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  have hAi : (p : ℂ) ^ (-alpha) = A⁻¹ := Complex.cpow_neg _ _
  have hGi : (p : ℂ) ^ (-gamma) = G⁻¹ := Complex.cpow_neg _ _
  have hGie : (p : ℂ) ^ (-gamma * (e : ℕ)) = (G⁻¹) ^ e := by
    rw [Complex.cpow_mul_nat, hGi]
  have hDe : (p : ℂ) ^ (-delta * (e : ℕ)) = D ^ e :=
    Complex.cpow_mul_nat _ _ _
  have hGD : (p : ℂ) ^ (gamma - delta) = G * D := by
    rw [show gamma - delta = gamma + (-delta) by ring]
    exact Complex.cpow_add _ _ hpC
  have hAB : (p : ℂ) ^ (alpha - beta) = A * B := by
    rw [show alpha - beta = alpha + (-beta) by ring]
    exact Complex.cpow_add _ _ hpC
  have hGiD : (p : ℂ) ^ (-gamma - delta) = G⁻¹ * D := by
    rw [show -gamma - delta = (-gamma) + (-delta) by ring]
    rw [Complex.cpow_add _ _ hpC, hGi]
  have hAG : (p : ℂ) ^ (alpha + gamma) = A * G :=
    Complex.cpow_add _ _ hpC
  rw [hGie, hGD, hAB, hughesYoungB1, hAi, hGiD, hGie, hDe]
  rw [show -(-alpha - gamma) = alpha + gamma by ring, hAG]
  change (G⁻¹) ^ e * hughesYoungC1 e (G * D) (A * B) (G * D) =
    G * ((A⁻¹ + B) * (G⁻¹ * D) * ((G⁻¹) ^ e - D ^ e) * (A * G))
  unfold hughesYoungC1
  simpa only [mul_assoc] using
    (hughesYoungEquation171_algebra (e := e) (A := A) (B := B)
      (G := G) (D := D) hA hG)

/-- Hughes--Young equation (172), with the source prime-power
substitutions restored. -/
theorem hughesYoungEquation172
    (e p : ℕ) (hp : 0 < p) (alpha beta gamma delta : ℂ) :
    (p : ℂ) ^ (-gamma * (e : ℕ)) *
        ((p : ℂ) ^ (alpha - beta + gamma - delta) *
          hughesYoungC2 e ((p : ℂ) ^ (gamma - delta))) =
      (p : ℂ) ^ gamma *
        hughesYoungB2 e p alpha beta gamma delta (-alpha - gamma) := by
  let A : ℂ := (p : ℂ) ^ alpha
  let B : ℂ := (p : ℂ) ^ (-beta)
  let G : ℂ := (p : ℂ) ^ gamma
  let D : ℂ := (p : ℂ) ^ (-delta)
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hA : A ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  have hG : G ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  have hAi : (p : ℂ) ^ (-alpha) = A⁻¹ := Complex.cpow_neg _ _
  have hGi : (p : ℂ) ^ (-gamma) = G⁻¹ := Complex.cpow_neg _ _
  have hGie : (p : ℂ) ^ (-gamma * (e : ℕ)) = (G⁻¹) ^ e := by
    rw [Complex.cpow_mul_nat, hGi]
  have hDe : (p : ℂ) ^ (-delta * (e : ℕ)) = D ^ e :=
    Complex.cpow_mul_nat _ _ _
  have hGD : (p : ℂ) ^ (gamma - delta) = G * D := by
    rw [show gamma - delta = gamma + (-delta) by ring]
    exact Complex.cpow_add _ _ hpC
  have hABGD : (p : ℂ) ^ (alpha - beta + gamma - delta) = A * B * G * D := by
    rw [show alpha - beta + gamma - delta =
      alpha + (-beta) + gamma + (-delta) by ring]
    rw [Complex.cpow_add _ _ hpC, Complex.cpow_add _ _ hpC,
      Complex.cpow_add _ _ hpC]
  have hABGiD : (p : ℂ) ^ (-alpha - beta - gamma - delta) =
      A⁻¹ * B * G⁻¹ * D := by
    rw [show -alpha - beta - gamma - delta =
      (-alpha) + (-beta) + (-gamma) + (-delta) by ring]
    rw [Complex.cpow_add _ _ hpC, Complex.cpow_add _ _ hpC,
      Complex.cpow_add _ _ hpC, hAi, hGi]
  have hDGie : (p : ℂ) ^ (-delta - gamma * (e : ℕ)) =
      D * (G⁻¹) ^ e := by
    rw [show -delta - gamma * (e : ℕ) =
      (-delta) + (-gamma * (e : ℕ)) by ring]
    rw [Complex.cpow_add _ _ hpC, hGie]
  have hGiDe : (p : ℂ) ^ (-gamma - delta * (e : ℕ)) =
      G⁻¹ * D ^ e := by
    rw [show -gamma - delta * (e : ℕ) =
      (-gamma) + (-delta * (e : ℕ)) by ring]
    rw [Complex.cpow_add _ _ hpC, hGi, hDe]
  have hAG2 : (p : ℂ) ^ (-2 * (-alpha - gamma)) = (A * G) ^ 2 := by
    rw [show -2 * (-alpha - gamma) = alpha + gamma + (alpha + gamma) by ring]
    rw [Complex.cpow_add _ _ hpC, Complex.cpow_add _ _ hpC]
    ring
  rw [hGie, hABGD, hGD, hughesYoungB2, hABGiD, hDGie, hGiDe, hAG2]
  unfold hughesYoungC2
  simpa only [mul_assoc] using
    (hughesYoungEquation172_algebra (e := e) (A := A) (B := B)
      (G := G) (D := D) hA hG)

/-- Primewise equation (169), including the rational denominators from
equations (100) and (142). -/
theorem hughesYoungEquation169_local
    (e p : ℕ) (hp : 0 < p) (alpha beta gamma delta : ℂ)
    (hc : 1 - (p : ℂ) ^ (gamma - delta) ≠ 0)
    (hr : 1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0) :
    (p : ℂ) ^ (-gamma * (e : ℕ)) *
        hughesYoungCPrimeFactor e p alpha beta gamma delta
          ((-alpha - gamma) / 2) =
      hughesYoungBPrimeFactor e p alpha beta gamma delta
        (-alpha - gamma) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpGamma : (p : ℂ) ^ gamma ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hpC)
  have hnum :
      (p : ℂ) ^ (-gamma * (e : ℕ)) *
        (hughesYoungC0 e ((p : ℂ) ^ (gamma - delta)) -
          (p : ℂ) ^ (-1 : ℂ) *
            hughesYoungC1 e ((p : ℂ) ^ (gamma - delta))
              ((p : ℂ) ^ (alpha - beta))
              ((p : ℂ) ^ (gamma - delta)) +
          (p : ℂ) ^ (-2 : ℂ) *
            ((p : ℂ) ^ (alpha - beta + gamma - delta) *
              hughesYoungC2 e ((p : ℂ) ^ (gamma - delta)))) =
      (p : ℂ) ^ gamma *
        (hughesYoungB0 e p gamma delta -
          (p : ℂ) ^ (-1 : ℂ) *
            hughesYoungB1 e p alpha beta gamma delta (-alpha - gamma) +
          (p : ℂ) ^ (-2 : ℂ) *
            hughesYoungB2 e p alpha beta gamma delta (-alpha - gamma)) := by
    linear_combination
      hughesYoungEquation170 e p hp gamma delta -
      (p : ℂ) ^ (-1 : ℂ) *
        hughesYoungEquation171 e p hp alpha beta gamma delta +
      (p : ℂ) ^ (-2 : ℂ) *
        hughesYoungEquation172 e p hp alpha beta gamma delta
  have hfirst :
      (p : ℂ) ^ gamma * ((p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta)) =
        1 - (p : ℂ) ^ (gamma - delta) := by
    rw [mul_sub]
    rw [Complex.cpow_neg]
    field_simp [hpGamma]
    rw [show gamma - delta = gamma + (-delta) by ring]
    rw [Complex.cpow_add _ _ hpC]
  have hbfirst : (p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta) ≠ 0 := by
    intro hzero
    apply hc
    rw [← hfirst, hzero, mul_zero]
  unfold hughesYoungCPrimeFactor hughesYoungCPrimeNumerator
    hughesYoungBPrimeFactor
  dsimp only
  simp only [div_eq_mul_inv]
  have hs : -alpha - delta - 2 * ((-alpha - gamma) * (2 : ℂ)⁻¹) =
      gamma - delta := by ring
  rw [hs]
  rw [show -2 - alpha - beta - gamma - delta -
      2 * (-alpha - gamma) =
    -2 + alpha - beta + gamma - delta by ring]
  rw [← mul_assoc, hnum, ← hfirst]
  field_simp [hr, hc, hbfirst, hpGamma]

/-- Hughes--Young equation (167), obtained from equation (169) at every
prime power dividing `h`. -/
theorem hughesYoungEquation167
    {h : ℕ} (hh : 0 < h) {alpha beta gamma delta : ℂ}
    (hc : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (gamma - delta) ≠ 0)
    (hr : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0) :
    (h : ℂ) ^ (-gamma) *
        hughesYoungC h alpha beta gamma delta ((-alpha - gamma) / 2) =
      hughesYoungB h alpha beta gamma delta (-alpha - gamma) := by
  rw [hughesYoungC, hughesYoungB]
  calc
    (h : ℂ) ^ (-gamma) *
        ∏ p ∈ hughesYoungPrimeFactors h,
          hughesYoungCPrimeFactor (h.factorization p) p
            alpha beta gamma delta ((-alpha - gamma) / 2) =
      (∏ p ∈ hughesYoungPrimeFactors h,
          (((p : ℂ) ^ (-gamma)) ^ (h.factorization p))) *
        ∏ p ∈ hughesYoungPrimeFactors h,
          hughesYoungCPrimeFactor (h.factorization p) p
            alpha beta gamma delta ((-alpha - gamma) / 2) := by
        rw [prod_hughesYoungPrimeFactors_cpow hh.ne']
    _ = ∏ p ∈ hughesYoungPrimeFactors h,
        (((p : ℂ) ^ (-gamma)) ^ (h.factorization p) *
          hughesYoungCPrimeFactor (h.factorization p) p
            alpha beta gamma delta ((-alpha - gamma) / 2)) := by
        rw [Finset.prod_mul_distrib]
    _ = ∏ p ∈ hughesYoungPrimeFactors h,
        hughesYoungBPrimeFactor (h.factorization p) p
          alpha beta gamma delta (-alpha - gamma) := by
        apply Finset.prod_congr rfl
        intro p hp'
        rw [← Complex.cpow_mul_nat]
        exact hughesYoungEquation169_local (h.factorization p) p p.2.pos
          alpha beta gamma delta (hc p hp') (hr p hp')

/-- The two-variable form used in equation (164). -/
theorem hughesYoungEquation167_pair
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {alpha beta gamma delta : ℂ}
    (hhc : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (gamma - delta) ≠ 0)
    (hhr : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0)
    (hkc : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (alpha - beta) ≠ 0)
    (hkr : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-2 + gamma - delta + alpha - beta) ≠ 0) :
    (h : ℂ) ^ (-gamma) * (k : ℂ) ^ (-alpha) *
        (hughesYoungC h alpha beta gamma delta ((-alpha - gamma) / 2) *
          hughesYoungC k gamma delta alpha beta ((-alpha - gamma) / 2)) =
      hughesYoungBPair h k alpha beta gamma delta (-alpha - gamma) := by
  have hH := hughesYoungEquation167 hh hhc hhr
  have hK := hughesYoungEquation167 (h := k) hk hkc hkr
  have hK' :
      (k : ℂ) ^ (-alpha) *
          hughesYoungC k gamma delta alpha beta ((-alpha - gamma) / 2) =
        hughesYoungB k gamma delta alpha beta (-alpha - gamma) := by
    have hs : (-gamma - alpha) / 2 = (-alpha - gamma) / 2 := by ring
    have ht : -gamma - alpha = -alpha - gamma := by ring
    rw [hs, ht] at hK
    exact hK
  unfold hughesYoungBPair
  calc
    (h : ℂ) ^ (-gamma) * (k : ℂ) ^ (-alpha) *
        (hughesYoungC h alpha beta gamma delta ((-alpha - gamma) / 2) *
          hughesYoungC k gamma delta alpha beta ((-alpha - gamma) / 2)) =
      ((h : ℂ) ^ (-gamma) *
          hughesYoungC h alpha beta gamma delta ((-alpha - gamma) / 2)) *
        ((k : ℂ) ^ (-alpha) *
          hughesYoungC k gamma delta alpha beta ((-alpha - gamma) / 2)) := by
        ring
    _ = _ := by rw [hH, hK']

/-- The finite rational Euler factor is invariant under simultaneously
interchanging the two shifts on each side.  This is the inspection step at
the end of equation (178). -/
theorem hughesYoungBPrimeFactor_swap
    (e p : ℕ) (alpha beta gamma delta s : ℂ) :
    hughesYoungBPrimeFactor e p alpha beta gamma delta s =
      hughesYoungBPrimeFactor e p beta alpha delta gamma s := by
  have h0 : hughesYoungB0 e p delta gamma =
      -hughesYoungB0 e p gamma delta := by
    unfold hughesYoungB0
    ring
  have h1 : hughesYoungB1 e p beta alpha delta gamma s =
      -hughesYoungB1 e p alpha beta gamma delta s := by
    unfold hughesYoungB1
    ring_nf
  have h2 : hughesYoungB2 e p beta alpha delta gamma s =
      -hughesYoungB2 e p alpha beta gamma delta s := by
    unfold hughesYoungB2
    ring_nf
  have hd0 : (p : ℂ) ^ (-delta) - (p : ℂ) ^ (-gamma) =
      -((p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta)) := by ring
  have hd1 :
      (p : ℂ) ^ (-2 - beta - alpha - delta - gamma - 2 * s) =
        (p : ℂ) ^ (-2 - alpha - beta - gamma - delta - 2 * s) := by
    congr 1
    ring
  unfold hughesYoungBPrimeFactor
  rw [h0, h1, h2, hd0, hd1]
  have hn :
      -hughesYoungB0 e p gamma delta -
          (p : ℂ) ^ (-1 : ℂ) * (-hughesYoungB1 e p alpha beta gamma delta s) +
          (p : ℂ) ^ (-2 : ℂ) * (-hughesYoungB2 e p alpha beta gamma delta s) =
        -(hughesYoungB0 e p gamma delta -
          (p : ℂ) ^ (-1 : ℂ) * hughesYoungB1 e p alpha beta gamma delta s +
          (p : ℂ) ^ (-2 : ℂ) * hughesYoungB2 e p alpha beta gamma delta s) := by
    ring
  have hd :
      (-( (p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta))) *
          (1 - (p : ℂ) ^ (-2 - alpha - beta - gamma - delta - 2 * s)) =
        -(((p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta)) *
          (1 - (p : ℂ) ^ (-2 - alpha - beta - gamma - delta - 2 * s))) := by
    ring
  rw [hn, hd, neg_div_neg_eq]

/-- Whole-product version of the inspection identity following equation
(178). -/
theorem hughesYoungB_swap
    (h : ℕ) (alpha beta gamma delta s : ℂ) :
    hughesYoungB h alpha beta gamma delta s =
      hughesYoungB h beta alpha delta gamma s := by
  unfold hughesYoungB
  apply Finset.prod_congr rfl
  intro p _hp
  exact hughesYoungBPrimeFactor_swap (h.factorization p) p
    alpha beta gamma delta s

/-- Continuity in the spectral variable of one regular equation-(142)
Euler factor. -/
theorem continuousAt_hughesYoungBPrimeFactor
    (e p : ℕ) (hp : 0 < p) (alpha beta gamma delta s0 : ℂ)
    (hden :
      ((p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta)) *
        (1 - (p : ℂ) ^
          (-2 - alpha - beta - gamma - delta - 2 * s0)) ≠ 0) :
    ContinuousAt (fun s : ℂ =>
      hughesYoungBPrimeFactor e p alpha beta gamma delta s) s0 := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpow1 : ContinuousAt (fun s : ℂ => (p : ℂ) ^ (-s)) s0 :=
    (continuousAt_const_cpow hpC).comp (by fun_prop)
  have hpow2 : ContinuousAt (fun s : ℂ => (p : ℂ) ^ (-2 * s)) s0 :=
    (continuousAt_const_cpow hpC).comp (by fun_prop)
  have hpowDen : ContinuousAt
      (fun s : ℂ =>
        (p : ℂ) ^ (-2 - alpha - beta - gamma - delta - 2 * s)) s0 :=
    (continuousAt_const_cpow hpC).comp (by fun_prop)
  unfold hughesYoungBPrimeFactor hughesYoungB0 hughesYoungB1 hughesYoungB2
  apply ContinuousAt.div
  · fun_prop (disch := assumption)
  · fun_prop (disch := assumption)
  · exact hden

/-- Continuity of the finite Euler product (140) on its regular locus. -/
theorem continuousAt_hughesYoungB
    (h : ℕ) (alpha beta gamma delta s0 : ℂ)
    (hden : ∀ p ∈ hughesYoungPrimeFactors h,
      ((p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta)) *
        (1 - (p : ℂ) ^
          (-2 - alpha - beta - gamma - delta - 2 * s0)) ≠ 0) :
    ContinuousAt (fun s : ℂ =>
      hughesYoungB h alpha beta gamma delta s) s0 := by
  unfold hughesYoungB
  have hprod : ∀ S : Finset Nat.Primes,
      (∀ p ∈ S,
        ((p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta)) *
          (1 - (p : ℂ) ^
            (-2 - alpha - beta - gamma - delta - 2 * s0)) ≠ 0) →
      ContinuousAt (fun s : ℂ =>
        ∏ p ∈ S, hughesYoungBPrimeFactor (h.factorization p) p
          alpha beta gamma delta s) s0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro _hden
        simpa using (continuousAt_const : ContinuousAt (fun _s : ℂ => (1 : ℂ)) s0)
    | @insert p S hpS ih =>
        intro hdenS
        simp only [Finset.prod_insert hpS]
        exact (continuousAt_hughesYoungBPrimeFactor
          (h.factorization p) p p.2.pos alpha beta gamma delta s0
          (hdenS p (Finset.mem_insert_self p S))).mul
          (ih (fun q hq => hdenS q (Finset.mem_insert_of_mem hq)))
  exact hprod (hughesYoungPrimeFactors h) hden

/-- Continuity of the paired finite Euler product (141). -/
theorem continuousAt_hughesYoungBPair
    (h k : ℕ) (alpha beta gamma delta s0 : ℂ)
    (hhden : ∀ p ∈ hughesYoungPrimeFactors h,
      ((p : ℂ) ^ (-gamma) - (p : ℂ) ^ (-delta)) *
        (1 - (p : ℂ) ^
          (-2 - alpha - beta - gamma - delta - 2 * s0)) ≠ 0)
    (hkden : ∀ p ∈ hughesYoungPrimeFactors k,
      ((p : ℂ) ^ (-alpha) - (p : ℂ) ^ (-beta)) *
        (1 - (p : ℂ) ^
          (-2 - gamma - delta - alpha - beta - 2 * s0)) ≠ 0) :
    ContinuousAt (fun s : ℂ =>
      hughesYoungBPair h k alpha beta gamma delta s) s0 := by
  unfold hughesYoungBPair
  exact (continuousAt_hughesYoungB h alpha beta gamma delta s0 hhden).mul
    (continuousAt_hughesYoungB k gamma delta alpha beta s0 hkden)

/-- Hughes--Young equations (177)--(178), before the final swap symmetry of
the finite Euler product. -/
theorem hughesYoungEquations177_178
    {h : ℕ} (hh : 0 < h) {alpha beta gamma delta : ℂ}
    (hx : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-alpha + beta) ≠ 0)
    (hc : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (alpha - beta) ≠ 0)
    (hr : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0) :
    (h : ℂ) ^ alpha *
        hughesYoungC h alpha beta gamma delta ((-beta - delta) / 2) =
      hughesYoungB h (-gamma) (-delta) (-alpha) (-beta) (beta + delta) := by
  have hFE := hughesYoungEquation125 (h := h) hh
    (alpha := alpha) (beta := beta) (gamma := gamma) (delta := delta)
    (s := (beta + delta) / 2) (by
      intro p hp
      rw [show -alpha - delta + 2 * ((beta + delta) / 2) =
        -alpha + beta by ring]
      exact hx p hp) hr
  have h167 := hughesYoungEquation167 (h := h) hh
    (alpha := -delta) (beta := -gamma) (gamma := -beta) (delta := -alpha)
    (by
      intro p hp
      rw [show -beta - -alpha = alpha - beta by ring]
      exact hc p hp)
    (by
      intro p hp
      rw [show -2 + -delta - -gamma + -beta - -alpha =
        -2 + alpha - beta + gamma - delta by ring]
      exact hr p hp)
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hFE' :
      (h : ℂ) ^ alpha *
          hughesYoungC h alpha beta gamma delta ((-beta - delta) / 2) =
        (h : ℂ) ^ beta *
          hughesYoungC h (-delta) (-gamma) (-beta) (-alpha)
            ((beta + delta) / 2) := by
    let s : ℂ := (beta + delta) / 2
    calc
      (h : ℂ) ^ alpha *
          hughesYoungC h alpha beta gamma delta ((-beta - delta) / 2) =
        (h : ℂ) ^ s *
          ((h : ℂ) ^ (-s + alpha) *
            hughesYoungC h alpha beta gamma delta (-s)) := by
          rw [← mul_assoc, ← Complex.cpow_add _ _ hhC]
          have he : s + (-s + alpha) = alpha := by ring
          have hs : -s = (-beta - delta) / 2 := by
            simp only [s]
            ring
          rw [he, hs]
      _ = (h : ℂ) ^ s *
          ((h : ℂ) ^ (s - delta) *
            hughesYoungC h (-delta) (-gamma) (-beta) (-alpha) s) := by
          rw [hFE]
      _ = (h : ℂ) ^ beta *
          hughesYoungC h (-delta) (-gamma) (-beta) (-alpha)
            ((beta + delta) / 2) := by
          rw [← mul_assoc, ← Complex.cpow_add _ _ hhC]
          have he : s + (s - delta) = beta := by
            simp only [s]
            ring
          rw [he]
  have h167' :
      (h : ℂ) ^ beta *
          hughesYoungC h (-delta) (-gamma) (-beta) (-alpha)
            ((beta + delta) / 2) =
          hughesYoungB h (-delta) (-gamma) (-beta) (-alpha)
          (beta + delta) := by
    have hs : (- -delta - -beta) / 2 = (beta + delta) / 2 := by ring
    have ht : - -delta - -beta = beta + delta := by ring
    rw [hs, ht] at h167
    simpa only [neg_neg] using h167
  rw [hFE', h167', hughesYoungB_swap]

/-- Hughes--Young equation (175), obtained by applying equations
(177)--(178) to both twist variables. -/
theorem hughesYoungEquation175
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {alpha beta gamma delta : ℂ}
    (hhx : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-alpha + beta) ≠ 0)
    (hhc : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (alpha - beta) ≠ 0)
    (hhr : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-2 + alpha - beta + gamma - delta) ≠ 0)
    (hkx : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-gamma + delta) ≠ 0)
    (hkc : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (gamma - delta) ≠ 0)
    (hkr : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-2 + gamma - delta + alpha - beta) ≠ 0) :
    (h : ℂ) ^ alpha * (k : ℂ) ^ gamma *
        (hughesYoungC h alpha beta gamma delta ((-beta - delta) / 2) *
          hughesYoungC k gamma delta alpha beta ((-beta - delta) / 2)) =
      hughesYoungBPair h k (-gamma) (-delta) (-alpha) (-beta)
        (beta + delta) := by
  have hH := hughesYoungEquations177_178 hh hhx hhc hhr
  have hK := hughesYoungEquations177_178 (h := k) hk hkx hkc hkr
  have hK' :
      (k : ℂ) ^ gamma *
          hughesYoungC k gamma delta alpha beta ((-beta - delta) / 2) =
        hughesYoungB k (-alpha) (-beta) (-gamma) (-delta)
          (beta + delta) := by
    have hs : (-delta - beta) / 2 = (-beta - delta) / 2 := by ring
    have ht : delta + beta = beta + delta := by ring
    rw [hs, ht] at hK
    exact hK
  unfold hughesYoungBPair
  calc
    (h : ℂ) ^ alpha * (k : ℂ) ^ gamma *
        (hughesYoungC h alpha beta gamma delta ((-beta - delta) / 2) *
          hughesYoungC k gamma delta alpha beta ((-beta - delta) / 2)) =
      ((h : ℂ) ^ alpha *
          hughesYoungC h alpha beta gamma delta ((-beta - delta) / 2)) *
        ((k : ℂ) ^ gamma *
          hughesYoungC k gamma delta alpha beta ((-beta - delta) / 2)) := by
        ring
    _ = _ := by rw [hH, hK']

end RiemannZeta.GuthMaynard

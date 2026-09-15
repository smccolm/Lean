import Tao2026.BurgessWeilCRT

/-!
# Cube-free iteration for the Burgess complete Weil bound

This file performs the exact arithmetic iteration of the CRT result.  Every
nontrivial cube-free modulus splits off one full prime-power component with
exponent one or two.  Strong induction then reduces the remaining composite
complete-correlation predicate to local estimates at prime and prime-square
levels, while preserving one common nonzero coefficient witness.
-/

namespace Tao2026

open Finset Complex
open scoped BigOperators ComplexConjugate

noncomputable section

/-- A nontrivial cube-free modulus splits as `p^k * n`, where `k` is one or
two, the factors are coprime, and the residual factor is strictly smaller. -/
theorem exists_primePower_coprime_decomposition_of_cubefree
    {q : ℕ} (hq : TaoCubefree q) (hq1 : q ≠ 1) :
    ∃ p k n : ℕ, p.Prime ∧ (k = 1 ∨ k = 2) ∧
      (p ^ k).Coprime n ∧ p ^ k * n = q ∧ n < q := by
  let p := q.minFac
  let k := q.factorization p
  let n := q / p ^ k
  have hq0 : q ≠ 0 := hq.ne_zero
  have hp : p.Prime := Nat.minFac_prime hq1
  have hpd : p ∣ q := Nat.minFac_dvd q
  have hk1 : 1 ≤ k := (hp.dvd_iff_one_le_factorization hq0).mp hpd
  have hk2 : k ≤ 2 := by
    by_contra hk
    have hk3 : 3 ≤ k := by omega
    exact hq p hp ((hp.pow_dvd_iff_le_factorization hq0).mpr hk3)
  have hk : k = 1 ∨ k = 2 := by omega
  have hn0 : n ≠ 0 := (Nat.ordCompl_pos p hq0).ne'
  have hcop : (p ^ k).Coprime n := (Nat.coprime_ordCompl hp hq0).pow_left k
  have hmul : p ^ k * n = q := by
    exact Nat.ordProj_mul_ordCompl_eq_self q p
  refine ⟨p, k, n, hp, hk, hcop, hmul, ?_⟩
  rw [← hmul]
  have hpk : 1 < p ^ k := by
    rcases hk with hk | hk
    · simpa [hk] using hp.one_lt
    · rw [hk, pow_two]
      nlinarith [hp.one_lt]
  have hlt := (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hn0)).2 hpk
  simpa using hlt

/-- At a prime modulus, the required local estimate is already trivial when
the prime divides the selected source coefficient. -/
theorem norm_burgessCompleteCorrelation_le_prime_of_coefficient_dvd
    (p B r : ℕ) [NeZero (p ^ 1)] (hp : p.Prime)
    (χ : DirichletCharacter ℂ (p ^ 1))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r)
    (hAj : burgessTupleDifferenceProduct uv j ≠ 0)
    (hdiv : p ∣ (burgessTupleDifferenceProduct uv j).natAbs)
    (hr : 2 ≤ r) :
    ‖burgessCompleteCorrelation χ uv‖ ≤
      burgessCompositeWeilFactor (p ^ 1) r *
        burgessCoefficientGcdContribution (p ^ 1) uv j := by
  have htriv := norm_burgessCompleteCorrelation_le_modulus χ uv
  have hgcdeq : Nat.gcd (burgessTupleDifferenceProduct uv j).natAbs p = p :=
    Nat.gcd_eq_right_iff_dvd.mpr hdiv
  unfold burgessCompositeWeilFactor burgessCoefficientGcdContribution
  rw [if_pos hAj]
  simp only [hp.primeFactors, Finset.card_singleton, pow_one]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hp.one_le
  have hfour : (1 : ℝ) ≤ 4 * r := by
    exact_mod_cast (show 1 ≤ 4 * r by omega)
  have hfactor : (1 : ℝ) ≤ (4 * r) * Real.sqrt p := by
    simpa using mul_le_mul hfour hsqrt (by norm_num) (by positivity)
  calc
    ‖burgessCompleteCorrelation χ uv‖ ≤ (p : ℝ) := by simpa using htriv
    _ ≤ ((4 * r : ℕ) : ℝ) * Real.sqrt p *
        Nat.gcd (burgessTupleDifferenceProduct uv j).natAbs p := by
      push_cast
      have hg : (p : ℝ) ≤ Nat.gcd
          (burgessTupleDifferenceProduct uv j).natAbs p := by
        rw [hgcdeq]
      calc
        (p : ℝ) ≤ Nat.gcd (burgessTupleDifferenceProduct uv j).natAbs p := hg
        _ ≤ (4 * (r : ℝ)) * Real.sqrt p *
            Nat.gcd (burgessTupleDifferenceProduct uv j).natAbs p := by
          simpa using mul_le_mul_of_nonneg_right hfactor
            (Nat.cast_nonneg (Nat.gcd
              (burgessTupleDifferenceProduct uv j).natAbs p))

/-- At a prime-square modulus, divisibility of the selected coefficient by
the underlying prime likewise makes the target weaker than the trivial
modulus bound. -/
theorem norm_burgessCompleteCorrelation_le_primeSquare_of_coefficient_dvd
    (p B r : ℕ) [NeZero (p ^ 2)] (hp : p.Prime)
    (χ : DirichletCharacter ℂ (p ^ 2))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r)
    (hAj : burgessTupleDifferenceProduct uv j ≠ 0)
    (hdiv : p ∣ (burgessTupleDifferenceProduct uv j).natAbs)
    (hr : 2 ≤ r) :
    ‖burgessCompleteCorrelation χ uv‖ ≤
      burgessCompositeWeilFactor (p ^ 2) r *
        burgessCoefficientGcdContribution (p ^ 2) uv j := by
  have htriv := norm_burgessCompleteCorrelation_le_modulus χ uv
  have hpdvd : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
  have hpgcd : p ≤ Nat.gcd
      (burgessTupleDifferenceProduct uv j).natAbs (p ^ 2) := by
    have hd := Nat.dvd_gcd hdiv hpdvd
    exact Nat.le_of_dvd
      (Nat.gcd_pos_of_pos_right _ (pow_pos hp.pos 2)) hd
  unfold burgessCompositeWeilFactor burgessCoefficientGcdContribution
  rw [if_pos hAj]
  rw [Nat.primeFactors_prime_pow (by norm_num : (2 : ℕ) ≠ 0) hp]
  simp only [Finset.card_singleton, pow_one]
  push_cast
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ p)]
  have hpReal : (0 : ℝ) ≤ p := by positivity
  have hgReal : (p : ℝ) ≤ Nat.gcd
      (burgessTupleDifferenceProduct uv j).natAbs (p ^ 2) := by
    exact_mod_cast hpgcd
  have hfour : (1 : ℝ) ≤ 4 * r := by
    exact_mod_cast (show 1 ≤ 4 * r by omega)
  have hfac : (p : ℝ) ≤ 4 * (r : ℝ) * p := by
    simpa using mul_le_mul_of_nonneg_right hfour hpReal
  calc
    ‖burgessCompleteCorrelation χ uv‖ ≤ ((p ^ 2 : ℕ) : ℝ) := htriv
    _ = (p : ℝ) * p := by push_cast; ring
    _ ≤ (4 * (r : ℝ) * p) *
        Nat.gcd (burgessTupleDifferenceProduct uv j).natAbs (p ^ 2) := by
      exact mul_le_mul hfac hgReal hpReal (by positivity)
    _ = 4 * (r : ℝ) * p *
        Nat.gcd (burgessTupleDifferenceProduct uv j).natAbs (p ^ 2) := rfl

/-- The only local analytic input needed for the composite complete Weil
bound: the fixed-coefficient estimate for primitive characters modulo `p` or
`p^2`. -/
def TaoPrimitivePrimePowerBurgessCompleteWeilBound : Prop :=
  ∀ (p k B r : ℕ) [NeZero (p ^ k)]
    (χ : DirichletCharacter ℂ (p ^ k))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r),
    p.Prime → (k = 1 ∨ k = 2) → 2 ≤ r →
    DirichletCharacter.IsPrimitive χ →
    burgessTupleDifferenceProduct uv j ≠ 0 →
    ‖burgessCompleteCorrelation χ uv‖ ≤
      burgessCompositeWeilFactor (p ^ k) r *
        burgessCoefficientGcdContribution (p ^ k) uv j

/-- The genuinely nontrivial local boundary may be restricted to coefficients
coprime to the underlying prime. -/
def TaoPrimitivePrimePowerCoprimeCoefficientWeilBound : Prop :=
  ∀ (p k B r : ℕ) [NeZero (p ^ k)]
    (χ : DirichletCharacter ℂ (p ^ k))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r),
    p.Prime → (k = 1 ∨ k = 2) → 2 ≤ r →
    DirichletCharacter.IsPrimitive χ →
    burgessTupleDifferenceProduct uv j ≠ 0 →
    (burgessTupleDifferenceProduct uv j).natAbs.Coprime p →
    ‖burgessCompleteCorrelation χ uv‖ ≤
      burgessCompositeWeilFactor (p ^ k) r *
        burgessCoefficientGcdContribution (p ^ k) uv j

/-- The local prime/prime-square estimate specialized to the sole moment
order used in Tao's argument. -/
def TaoPrimitivePrimePowerBurgessCompleteWeilBoundRSeven : Prop :=
  ∀ (p k B : ℕ) [NeZero (p ^ k)]
    (χ : DirichletCharacter ℂ (p ^ k))
    (uv : (Fin 7 → Fin B) × (Fin 7 → Fin B))
    (j : Fin 7 ⊕ Fin 7),
    p.Prime → (k = 1 ∨ k = 2) →
    DirichletCharacter.IsPrimitive χ →
    burgessTupleDifferenceProduct uv j ≠ 0 →
    ‖burgessCompleteCorrelation χ uv‖ ≤
      burgessCompositeWeilFactor (p ^ k) 7 *
        burgessCoefficientGcdContribution (p ^ k) uv j

/-- The coprime-coefficient form of the fixed `r = 7` local estimate. -/
def TaoPrimitivePrimePowerCoprimeCoefficientWeilBoundRSeven : Prop :=
  ∀ (p k B : ℕ) [NeZero (p ^ k)]
    (χ : DirichletCharacter ℂ (p ^ k))
    (uv : (Fin 7 → Fin B) × (Fin 7 → Fin B))
    (j : Fin 7 ⊕ Fin 7),
    p.Prime → (k = 1 ∨ k = 2) →
    DirichletCharacter.IsPrimitive χ →
    burgessTupleDifferenceProduct uv j ≠ 0 →
    (burgessTupleDifferenceProduct uv j).natAbs.Coprime p →
    ‖burgessCompleteCorrelation χ uv‖ ≤
      burgessCompositeWeilFactor (p ^ k) 7 *
        burgessCoefficientGcdContribution (p ^ k) uv j

/-- The composite Weil factor at a prime is the literal square-root factor
appearing in the local estimate. -/
theorem burgessCompositeWeilFactor_prime (p r : ℕ) (hp : p.Prime) :
    burgessCompositeWeilFactor p r =
      ((4 * r : ℕ) : ℝ) * Real.sqrt p := by
  simp [burgessCompositeWeilFactor, hp.primeFactors]

/-- The composite Weil factor at a prime square is the literal linear factor
in the underlying prime. -/
theorem burgessCompositeWeilFactor_primeSquare (p r : ℕ) (hp : p.Prime) :
    burgessCompositeWeilFactor (p ^ 2) r =
      ((4 * r : ℕ) : ℝ) * p := by
  unfold burgessCompositeWeilFactor
  rw [Nat.primeFactors_prime_pow (by norm_num : (2 : ℕ) ≠ 0) hp]
  simp only [Finset.card_singleton, pow_one]
  push_cast
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ p)]

/-- A coefficient coprime to `p` contributes gcd weight one at prime
level. -/
theorem burgessCoefficientGcdContribution_prime_eq_one_of_coprime
    (p B r : ℕ) (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r)
    (hAj : burgessTupleDifferenceProduct uv j ≠ 0)
    (hcop : (burgessTupleDifferenceProduct uv j).natAbs.Coprime p) :
    burgessCoefficientGcdContribution p uv j = 1 := by
  unfold burgessCoefficientGcdContribution
  rw [if_pos hAj, hcop.gcd_eq_one]

/-- A coefficient coprime to `p` also contributes gcd weight one at
prime-square level. -/
theorem burgessCoefficientGcdContribution_primeSquare_eq_one_of_coprime
    (p B r : ℕ) (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r)
    (hAj : burgessTupleDifferenceProduct uv j ≠ 0)
    (hcop : (burgessTupleDifferenceProduct uv j).natAbs.Coprime p) :
    burgessCoefficientGcdContribution (p ^ 2) uv j = 1 := by
  unfold burgessCoefficientGcdContribution
  rw [if_pos hAj, (hcop.pow_right 2).gcd_eq_one]

/-- The residual prime-level analytic input, with the selected coefficient
coprime to the prime. -/
def TaoPrimitivePrimeCoprimeCoefficientWeilBound : Prop :=
  ∀ (p B r : ℕ) [NeZero (p ^ 1)]
    (χ : DirichletCharacter ℂ (p ^ 1))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r),
    p.Prime → 2 ≤ r → DirichletCharacter.IsPrimitive χ →
    burgessTupleDifferenceProduct uv j ≠ 0 →
    (burgessTupleDifferenceProduct uv j).natAbs.Coprime p →
    ‖burgessCompleteCorrelation χ uv‖ ≤
      ((4 * r : ℕ) : ℝ) * Real.sqrt p

/-- The residual prime-level input at the fixed fourteenth moment. -/
def TaoPrimitivePrimeCoprimeCoefficientWeilBoundRSeven : Prop :=
  ∀ (p B : ℕ) [NeZero (p ^ 1)]
    (χ : DirichletCharacter ℂ (p ^ 1))
    (uv : (Fin 7 → Fin B) × (Fin 7 → Fin B))
    (j : Fin 7 ⊕ Fin 7),
    p.Prime → DirichletCharacter.IsPrimitive χ →
    burgessTupleDifferenceProduct uv j ≠ 0 →
    (burgessTupleDifferenceProduct uv j).natAbs.Coprime p →
    ‖burgessCompleteCorrelation χ uv‖ ≤
      ((4 * 7 : ℕ) : ℝ) * Real.sqrt p

/-- The residual prime-square analytic input, with the selected coefficient
coprime to the underlying prime. -/
def TaoPrimitivePrimeSquareCoprimeCoefficientWeilBound : Prop :=
  ∀ (p B r : ℕ) [NeZero (p ^ 2)]
    (χ : DirichletCharacter ℂ (p ^ 2))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r),
    p.Prime → 2 ≤ r → DirichletCharacter.IsPrimitive χ →
    burgessTupleDifferenceProduct uv j ≠ 0 →
    (burgessTupleDifferenceProduct uv j).natAbs.Coprime p →
    ‖burgessCompleteCorrelation χ uv‖ ≤
      ((4 * r : ℕ) : ℝ) * p

/-- Separate coprime-coefficient estimates at prime and prime-square levels
are exactly the local input needed by the cube-free iteration. -/
theorem TaoPrimitivePrimePowerCoprimeCoefficientWeilBound.ofPrimeAndPrimeSquare
    (hprime : TaoPrimitivePrimeCoprimeCoefficientWeilBound)
    (hprimeSquare : TaoPrimitivePrimeSquareCoprimeCoefficientWeilBound) :
    TaoPrimitivePrimePowerCoprimeCoefficientWeilBound := by
  intro p k B r _ χ uv j hp hk hr hχ hAj hcop
  rcases hk with rfl | rfl
  · simpa [burgessCompositeWeilFactor_prime p r hp,
      burgessCoefficientGcdContribution_prime_eq_one_of_coprime
        p B r uv j hAj hcop] using
      hprime p B r χ uv j hp hr hχ hAj hcop
  · simpa [burgessCompositeWeilFactor_primeSquare p r hp,
      burgessCoefficientGcdContribution_primeSquare_eq_one_of_coprime
        p B r uv j hAj hcop] using
      hprimeSquare p B r χ uv j hp hr hχ hAj hcop

/-- The coprime-coefficient local estimate implies the unrestricted local
prime/prime-square predicate; the complementary branch is elementary. -/
theorem TaoPrimitivePrimePowerCoprimeCoefficientWeilBound.toPrimePower
    (hlocal : TaoPrimitivePrimePowerCoprimeCoefficientWeilBound) :
    TaoPrimitivePrimePowerBurgessCompleteWeilBound := by
  intro p k B r _ χ uv j hp hk hr hχ hAj
  by_cases hcop : (burgessTupleDifferenceProduct uv j).natAbs.Coprime p
  · exact hlocal p k B r χ uv j hp hk hr hχ hAj hcop
  · have hdiv : p ∣ (burgessTupleDifferenceProduct uv j).natAbs := by
      simpa [Nat.coprime_comm, hp.coprime_iff_not_dvd] using hcop
    rcases hk with hk | hk
    · subst k
      exact norm_burgessCompleteCorrelation_le_prime_of_coefficient_dvd
        p B r hp χ uv j hAj hdiv hr
    · subst k
      exact norm_burgessCompleteCorrelation_le_primeSquare_of_coefficient_dvd
        p B r hp χ uv j hAj hdiv hr

/-- Strong induction over the cube-free modulus preserves a fixed nonzero
coefficient witness and proves the corresponding fixed-gcd bound. -/
theorem norm_burgessCompleteCorrelation_le_coefficient_of_primePowerWeil
    (hlocal : TaoPrimitivePrimePowerBurgessCompleteWeilBound) :
    ∀ {q B r : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      (uv : (Fin r → Fin B) × (Fin r → Fin B))
      (j : Fin r ⊕ Fin r),
      2 ≤ r → TaoCubefree q → DirichletCharacter.IsPrimitive χ →
      burgessTupleDifferenceProduct uv j ≠ 0 →
      ‖burgessCompleteCorrelation χ uv‖ ≤
        burgessCompositeWeilFactor q r *
          burgessCoefficientGcdContribution q uv j := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro B r _ χ uv j hr hq hχ hAj
      by_cases hq1 : q = 1
      · subst q
        have hχone : χ = 1 := DirichletCharacter.level_one χ
        subst χ
        calc
          ‖burgessCompleteCorrelation (1 : DirichletCharacter ℂ 1) uv‖ ≤
              (1 : ℝ) := by
            simpa using norm_burgessCompleteCorrelation_le_modulus
              (1 : DirichletCharacter ℂ 1) uv
          _ = burgessCompositeWeilFactor 1 r *
              burgessCoefficientGcdContribution 1 uv j := by
            simp [burgessCompositeWeilFactor,
              burgessCoefficientGcdContribution, hAj]
      · obtain ⟨p, k, n, hp, hk, hcop, hmul, hnlt⟩ :=
          exists_primePower_coprime_decomposition_of_cubefree hq hq1
        have hpk0 : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
        subst q
        have hn0 : n ≠ 0 := right_ne_zero_of_mul (NeZero.ne (p ^ k * n))
        haveI : NeZero (p ^ k) := ⟨hpk0⟩
        haveI : NeZero n := ⟨hn0⟩
        have hleft := hlocal p k B r
          (burgessCRTLeftCharacter (p ^ k) n hcop χ) uv j hp hk hr
          (burgessCRTLeftCharacter_isPrimitive (p ^ k) n hcop χ hχ) hAj
        have hnCube : TaoCubefree n :=
          hq.of_dvd (n.dvd_mul_left (p ^ k))
        have hright := ih n hnlt
          (burgessCRTRightCharacter (p ^ k) n hcop χ) uv j hr hnCube
          (burgessCRTRightCharacter_isPrimitive (p ^ k) n hcop χ hχ) hAj
        exact norm_burgessCompleteCorrelation_le_coefficient_of_coprime
          (p ^ k) n B r hcop χ uv j hleft hright

/-- Prime and prime-square fixed-coefficient estimates imply the full relaxed
composite cube-free Weil predicate used by the Burgess moment. -/
theorem TaoPrimitivePrimePowerBurgessCompleteWeilBound.toComposite
    (hlocal : TaoPrimitivePrimePowerBurgessCompleteWeilBound) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound := by
  intro q B r _ χ uv hr hq hχ huv
  obtain ⟨j, hAj⟩ :=
    exists_burgessTupleDifferenceProduct_ne_zero_of_mem_nondegenerate uv huv
  have hfixed :=
    norm_burgessCompleteCorrelation_le_coefficient_of_primePowerWeil
      hlocal χ uv j hr hq hχ hAj
  have hcoefficient :
      (burgessCoefficientGcdContribution q uv j : ℝ) ≤
        burgessTupleGcdWeight q uv := by
    exact_mod_cast burgessCoefficientGcdContribution_le_tupleGcdWeight q B r uv j
  exact hfixed.trans (mul_le_mul_of_nonneg_left hcoefficient (by
    unfold burgessCompositeWeilFactor
    positivity))

/-- The genuinely nontrivial coprime-coefficient local predicate directly
implies the full relaxed composite cube-free Weil predicate. -/
theorem TaoPrimitivePrimePowerCoprimeCoefficientWeilBound.toComposite
    (hlocal : TaoPrimitivePrimePowerCoprimeCoefficientWeilBound) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  hlocal.toPrimePower.toComposite

/-- A fixed-`r = 7` prime estimate and the proved all-order prime-square
estimate supply the fixed local prime-power input. -/
theorem TaoPrimitivePrimePowerCoprimeCoefficientWeilBoundRSeven.ofPrimeAndPrimeSquare
    (hprime : TaoPrimitivePrimeCoprimeCoefficientWeilBoundRSeven)
    (hprimeSquare : TaoPrimitivePrimeSquareCoprimeCoefficientWeilBound) :
    TaoPrimitivePrimePowerCoprimeCoefficientWeilBoundRSeven := by
  intro p k B _ χ uv j hp hk hχ hAj hcop
  rcases hk with rfl | rfl
  · simpa [burgessCompositeWeilFactor_prime p 7 hp,
      burgessCoefficientGcdContribution_prime_eq_one_of_coprime
        p B 7 uv j hAj hcop] using
      hprime p B χ uv j hp hχ hAj hcop
  · simpa [burgessCompositeWeilFactor_primeSquare p 7 hp,
      burgessCoefficientGcdContribution_primeSquare_eq_one_of_coprime
        p B 7 uv j hAj hcop] using
      hprimeSquare p B 7 χ uv j hp (by omega) hχ hAj hcop

/-- At `r = 7`, the coprime local estimate implies the unrestricted local
estimate; the coefficient-divisible branch remains elementary. -/
theorem TaoPrimitivePrimePowerCoprimeCoefficientWeilBoundRSeven.toPrimePower
    (hlocal : TaoPrimitivePrimePowerCoprimeCoefficientWeilBoundRSeven) :
    TaoPrimitivePrimePowerBurgessCompleteWeilBoundRSeven := by
  intro p k B _ χ uv j hp hk hχ hAj
  by_cases hcop : (burgessTupleDifferenceProduct uv j).natAbs.Coprime p
  · exact hlocal p k B χ uv j hp hk hχ hAj hcop
  · have hdiv : p ∣ (burgessTupleDifferenceProduct uv j).natAbs := by
      simpa [Nat.coprime_comm, hp.coprime_iff_not_dvd] using hcop
    rcases hk with hk | hk
    · subst k
      exact norm_burgessCompleteCorrelation_le_prime_of_coefficient_dvd
        p B 7 hp χ uv j hAj hdiv (by omega)
    · subst k
      exact norm_burgessCompleteCorrelation_le_primeSquare_of_coefficient_dvd
        p B 7 hp χ uv j hAj hdiv (by omega)

/-- Strong induction over a cube-free modulus at the fixed moment order. -/
theorem norm_burgessCompleteCorrelation_le_coefficient_of_primePowerWeilRSeven
    (hlocal : TaoPrimitivePrimePowerBurgessCompleteWeilBoundRSeven) :
    ∀ {q B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
      (uv : (Fin 7 → Fin B) × (Fin 7 → Fin B))
      (j : Fin 7 ⊕ Fin 7),
      TaoCubefree q → DirichletCharacter.IsPrimitive χ →
      burgessTupleDifferenceProduct uv j ≠ 0 →
      ‖burgessCompleteCorrelation χ uv‖ ≤
        burgessCompositeWeilFactor q 7 *
          burgessCoefficientGcdContribution q uv j := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro B _ χ uv j hq hχ hAj
      by_cases hq1 : q = 1
      · subst q
        have hχone : χ = 1 := DirichletCharacter.level_one χ
        subst χ
        calc
          ‖burgessCompleteCorrelation (1 : DirichletCharacter ℂ 1) uv‖ ≤
              (1 : ℝ) := by
            simpa using norm_burgessCompleteCorrelation_le_modulus
              (1 : DirichletCharacter ℂ 1) uv
          _ = burgessCompositeWeilFactor 1 7 *
              burgessCoefficientGcdContribution 1 uv j := by
            simp [burgessCompositeWeilFactor,
              burgessCoefficientGcdContribution, hAj]
      · obtain ⟨p, k, n, hp, hk, hcop, hmul, hnlt⟩ :=
          exists_primePower_coprime_decomposition_of_cubefree hq hq1
        have hpk0 : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
        subst q
        have hn0 : n ≠ 0 := right_ne_zero_of_mul (NeZero.ne (p ^ k * n))
        haveI : NeZero (p ^ k) := ⟨hpk0⟩
        haveI : NeZero n := ⟨hn0⟩
        have hleft := hlocal p k B
          (burgessCRTLeftCharacter (p ^ k) n hcop χ) uv j hp hk
          (burgessCRTLeftCharacter_isPrimitive (p ^ k) n hcop χ hχ) hAj
        have hnCube : TaoCubefree n :=
          hq.of_dvd (n.dvd_mul_left (p ^ k))
        have hright := ih n hnlt
          (burgessCRTRightCharacter (p ^ k) n hcop χ) uv j hnCube
          (burgessCRTRightCharacter_isPrimitive (p ^ k) n hcop χ hχ) hAj
        exact norm_burgessCompleteCorrelation_le_coefficient_of_coprime
          (p ^ k) n B 7 hcop χ uv j hleft hright

/-- The fixed local prime-power estimate implies precisely the complete Weil
predicate required by the fourteenth moment. -/
theorem TaoPrimitivePrimePowerBurgessCompleteWeilBoundRSeven.toComposite
    (hlocal : TaoPrimitivePrimePowerBurgessCompleteWeilBoundRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven := by
  intro q B _ χ uv hq hχ huv
  obtain ⟨j, hAj⟩ :=
    exists_burgessTupleDifferenceProduct_ne_zero_of_mem_nondegenerate uv huv
  have hfixed :=
    norm_burgessCompleteCorrelation_le_coefficient_of_primePowerWeilRSeven
      hlocal χ uv j hq hχ hAj
  have hcoefficient :
      (burgessCoefficientGcdContribution q uv j : ℝ) ≤
        burgessTupleGcdWeight q uv := by
    exact_mod_cast burgessCoefficientGcdContribution_le_tupleGcdWeight q B 7 uv j
  exact hfixed.trans (mul_le_mul_of_nonneg_left hcoefficient (by
    unfold burgessCompositeWeilFactor
    positivity))

/-- The fixed coprime local predicate directly supplies the fourteenth-moment
composite estimate. -/
theorem TaoPrimitivePrimePowerCoprimeCoefficientWeilBoundRSeven.toComposite
    (hlocal : TaoPrimitivePrimePowerCoprimeCoefficientWeilBoundRSeven) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  hlocal.toPrimePower.toComposite

end

end Tao2026

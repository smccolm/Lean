import RiemannZeta.GuthMaynard.ArithmeticCoefficients
import RiemannZeta.GuthMaynard.PolynomialPowers
import RiemannZeta.GuthMaynard.TypeIIZeros

open Complex Finset
open Filter Topology
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-- Exact Dirichlet-convolution coefficient of the square of the short
Möbius polynomial. -/
noncomputable def shortMobiusSquareCoeff (T : ℝ) (n : ℕ) : ℂ :=
  ∑ p ∈ (Fintype.piFinset (fun (_ : Fin 2) => Finset.Ico 1 (detectorCutoff T))).filter
      (fun p => (∏ j : Fin 2, p j) = n),
    ∏ j : Fin 2, (ArithmeticFunction.moebius (p j) : ℂ)

lemma shortMobiusSquare_tuple_mem_support (T : ℝ) (p : Fin 2 → ℕ)
    (hp : p ∈ Fintype.piFinset
      (fun (_ : Fin 2) => Finset.Ico 1 (detectorCutoff T))) :
    (∏ j : Fin 2, p j) ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2) := by
  rw [Fintype.mem_piFinset] at hp
  rw [Finset.mem_Icc]
  constructor
  · calc
      1 = ∏ _j : Fin 2, 1 := by simp
      _ ≤ ∏ j : Fin 2, p j := by
        apply Finset.prod_le_prod
        · intro _ _
          omega
        · intro j _
          exact (Finset.mem_Ico.mp (hp j)).1
  · calc
      ∏ j : Fin 2, p j ≤ ∏ _j : Fin 2, detectorCutoff T := by
        apply Finset.prod_le_prod
        · intro _ _
          omega
        · intro j _
          exact (Finset.mem_Ico.mp (hp j)).2.le
      _ = (detectorCutoff T) ^ 2 := by simp

/-- Exact finite convolution expansion of `M(s)^2`; the support endpoint is
the square of the source cutoff. -/
theorem shortMobiusPolynomial_sq_eq (T : ℝ) (s : ℂ) :
    shortMobiusPolynomial T s ^ 2 =
      ∑ n ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        shortMobiusSquareCoeff T n * (n : ℂ) ^ (-s) := by
  let tuples := Fintype.piFinset
    (fun (_ : Fin 2) => Finset.Ico 1 (detectorCutoff T))
  have hSupport : ∀ p ∈ tuples,
      (∏ j : Fin 2, p j) ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2) := by
    intro p hp
    exact shortMobiusSquare_tuple_mem_support T p hp
  rw [shortMobiusPolynomial, Finset.sum_pow']
  change (∑ p ∈ tuples,
      ∏ j : Fin 2, ((ArithmeticFunction.moebius (p j) : ℂ) *
        (p j : ℂ) ^ (-s))) = _
  calc
    (∑ p ∈ tuples,
        ∏ j : Fin 2, ((ArithmeticFunction.moebius (p j) : ℂ) *
          (p j : ℂ) ^ (-s))) =
        ∑ p ∈ tuples,
          (∏ j : Fin 2, (ArithmeticFunction.moebius (p j) : ℂ)) *
            ((∏ j : Fin 2, p j : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.prod_mul_distrib, prod_natCast_cpow_eq]
    _ = ∑ n ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ p ∈ tuples with (∏ j : Fin 2, p j) = n,
          (∏ j : Fin 2, (ArithmeticFunction.moebius (p j) : ℂ)) *
            ((∏ j : Fin 2, p j : ℕ) : ℂ) ^ (-s) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hSupport _
    _ = ∑ n ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        shortMobiusSquareCoeff T n * (n : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [shortMobiusSquareCoeff, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

/-- The squared short Möbius polynomial is supported in the exact range needed
for the generic twisted-moment theorem. -/
theorem shortMobiusSquareCoeff_eq_zero_of_not_mem {T : ℝ} {n : ℕ}
    (hn : n ∉ Finset.Icc 1 ((detectorCutoff T) ^ 2)) :
    shortMobiusSquareCoeff T n = 0 := by
  rw [shortMobiusSquareCoeff]
  apply Finset.sum_eq_zero
  intro p hp
  have hpSupport := shortMobiusSquare_tuple_mem_support T p
    (Finset.mem_filter.mp hp).1
  exact (hn ((Finset.mem_filter.mp hp).2 ▸ hpSupport)).elim

/-- The squared detector cutoff lies in the Hughes--Young short-polynomial
range for all sufficiently large heights. -/
theorem eventually_detectorCutoff_sq_le_rpow :
    ∀ᶠ T : ℝ in atTop,
      ((detectorCutoff T) ^ 2 : ℝ) ≤ T ^ (1 / 22 : ℝ) := by
  have hExponent : 0 < (7 / 275 : ℝ) := by norm_num
  have hGrow : Tendsto (fun T : ℝ => T ^ (7 / 275 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop hExponent
  filter_upwards [eventually_ge_atTop (1 : ℝ), hGrow.eventually (eventually_ge_atTop 9)]
    with T hT hNine
  have hTPos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hSmallPow : 1 ≤ T ^ (1 / 100 : ℝ) :=
    Real.one_le_rpow hT (by norm_num)
  have hFloor :
      (⌊2 * T ^ (1 / 100 : ℝ)⌋₊ : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ) := by
    exact_mod_cast Nat.floor_le (by positivity : 0 ≤ 2 * T ^ (1 / 100 : ℝ))
  have hCutoff : (detectorCutoff T : ℝ) ≤ 3 * T ^ (1 / 100 : ℝ) := by
    rw [detectorCutoff, Nat.cast_add, Nat.cast_one]
    linarith
  have hSquare : ((detectorCutoff T) ^ 2 : ℝ) ≤
      9 * T ^ (1 / 50 : ℝ) := by
    have hCutNonneg : (0 : ℝ) ≤ detectorCutoff T := by positivity
    calc
      ((detectorCutoff T) ^ 2 : ℝ) ≤ (3 * T ^ (1 / 100 : ℝ)) ^ 2 := by
        gcongr
      _ = 9 * (T ^ (1 / 100 : ℝ) * T ^ (1 / 100 : ℝ)) := by ring
      _ = 9 * T ^ (1 / 50 : ℝ) := by
        rw [← Real.rpow_add hTPos]
        norm_num
  calc
    ((detectorCutoff T) ^ 2 : ℝ) ≤ 9 * T ^ (1 / 50 : ℝ) := hSquare
    _ ≤ T ^ (7 / 275 : ℝ) * T ^ (1 / 50 : ℝ) := by gcongr
    _ = T ^ (1 / 22 : ℝ) := by
      rw [← Real.rpow_add hTPos]
      norm_num

/-- Product-tuples contributing to one coefficient inject into the positive
divisors of that coefficient. -/
theorem shortMobiusSquare_fiber_card_le_divisors (T : ℝ) {n : ℕ} (hn : 0 < n) :
    ((Fintype.piFinset (fun (_ : Fin 2) => Finset.Ico 1 (detectorCutoff T))).filter
      (fun p => (∏ j : Fin 2, p j) = n)).card ≤ n.divisors.card := by
  let tuples := Fintype.piFinset
    (fun (_ : Fin 2) => Finset.Ico 1 (detectorCutoff T))
  let fiber := tuples.filter (fun p => (∏ j : Fin 2, p j) = n)
  change fiber.card ≤ n.divisors.card
  apply Finset.card_le_card_of_injOn (fun p : Fin 2 → ℕ => p 0)
  · intro p hp
    change p ∈ fiber at hp
    have hpProd := (Finset.mem_filter.mp hp).2
    rw [Fin.prod_univ_two] at hpProd
    change p 0 ∈ n.divisors
    rw [Nat.mem_divisors]
    exact ⟨⟨p 1, hpProd.symm⟩, hn.ne'⟩
  · intro p hp q hq hpq
    change p ∈ fiber at hp
    change q ∈ fiber at hq
    have hpProd := (Finset.mem_filter.mp hp).2
    have hqProd := (Finset.mem_filter.mp hq).2
    have hpTuple := (Finset.mem_filter.mp hp).1
    change p ∈ tuples at hpTuple
    rw [Fintype.mem_piFinset] at hpTuple
    have hp0 : 0 < p 0 := by
      have := (Finset.mem_Ico.mp (hpTuple 0)).1
      omega
    change p 0 = q 0 at hpq
    rw [Fin.prod_univ_two] at hpProd hqProd
    funext j
    fin_cases j
    · exact hpq
    · apply Nat.mul_left_cancel hp0
      calc
        p 0 * p 1 = n := hpProd
        _ = q 0 * q 1 := hqProd.symm
        _ = p 0 * q 1 := by rw [hpq]

/-- Each squared Möbius coefficient is bounded by the ordinary divisor count,
uniformly in the detector height. -/
theorem norm_shortMobiusSquareCoeff_le_divisors (T : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖shortMobiusSquareCoeff T n‖ ≤ (n.divisors.card : ℝ) := by
  let fiber :=
    (Fintype.piFinset (fun (_ : Fin 2) => Finset.Ico 1 (detectorCutoff T))).filter
      (fun p => (∏ j : Fin 2, p j) = n)
  rw [shortMobiusSquareCoeff]
  calc
    ‖∑ p ∈ fiber, ∏ j : Fin 2, (ArithmeticFunction.moebius (p j) : ℂ)‖
        ≤ ∑ _p ∈ fiber, (1 : ℝ) := by
          apply norm_sum_le_of_le
          intro p _hp
          rw [norm_prod]
          calc
            ∏ j : Fin 2, ‖(ArithmeticFunction.moebius (p j) : ℂ)‖
                ≤ ∏ _j : Fin 2, (1 : ℝ) := by
                  apply Finset.prod_le_prod
                  · intro _ _
                    positivity
                  · intro j _
                    exact norm_moebius_cast_le_one (p j)
            _ = 1 := by simp
    _ = (fiber.card : ℝ) := by simp
    _ ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast shortMobiusSquare_fiber_card_le_divisors T hn

/-- Source-uniform epsilon-power bound for the exact `M²` coefficients. -/
theorem shortMobiusSquareCoeff_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (n : ℕ), 0 < n →
      ‖shortMobiusSquareCoeff T n‖ ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hDivisor⟩ := divisorCountBound_native ε hε
  refine ⟨C, hC, ?_⟩
  intro T n hn
  exact (norm_shortMobiusSquareCoeff_le_divisors T hn).trans (hDivisor n hn)

/-- Exact algebraic reduction of the Type-II moment to a zeta fourth moment
twisted by the squared Möbius polynomial. -/
theorem twistedZetaMomentIntegrand_eq_zeta_four_mul_mobius_sq
    (T t : ℝ) :
    twistedZetaMomentIntegrand T t =
      ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 4 *
        ‖shortMobiusPolynomial T ((1 / 2 : ℂ) + (t : ℂ) * I) ^ 2‖ ^ 2 := by
  rw [twistedZetaMomentIntegrand, norm_mul, norm_pow]
  ring

/-- Integral form of the exact `|Mζ|⁴ = |ζ|⁴ |M²|²` reduction. -/
theorem twistedZetaFourthMoment_eq :
    twistedZetaFourthMoment = fun T =>
      ∫ t in T / 2..3 * T,
        ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 4 *
          ‖shortMobiusPolynomial T ((1 / 2 : ℂ) + (t : ℂ) * I) ^ 2‖ ^ 2 := by
  funext T
  rw [twistedZetaFourthMoment]
  apply intervalIntegral.integral_congr
  intro t _ht
  exact twistedZetaMomentIntegrand_eq_zeta_four_mul_mobius_sq T t

end RiemannZeta.GuthMaynard

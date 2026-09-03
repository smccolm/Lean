import GafniTao.Pintz2023Arithmetic
import RiemannZeta.GuthMaynard.ClassicalDensity
import RiemannZeta.GuthMaynard.PolynomialPowers
import RiemannZeta.GuthMaynard.ArithmeticCoefficients

/-!
# The source polynomial in Pintz (2023), equations (4.1), (4.12), and (4.15)

Pintz does not power the bare Möbius mollifier.  The coefficient in his
equation (4.1) is

`a n = ∑ d ∣ n, d ≤ X, μ(d)`,

the Dirichlet coefficient of `ζ M_X`.  This file exposes that coefficient,
its exact dyadic polynomial, and the literal finite convolution obtained by
raising a dyadic block to a natural power.  These are algebraic identities;
the analytic estimates used in (4.19)--(4.24) are deliberately kept for the
subsequent module.
-/

open Complex Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Pintz's coefficient `a_n` from equation (4.1). -/
noncomputable def pintz2023Coeff (X n : ℕ) : ℂ :=
  mollifiedZetaCoeff X n

theorem pintz2023Coeff_eq_divisor_sum (X n : ℕ) :
    pintz2023Coeff X n =
      ∑ d ∈ n.divisors.filter (fun d => d ≤ X),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
  rfl

/-- Möbius inversion removes all nonconstant coefficients below the
mollifier length. -/
theorem pintz2023Coeff_eq_zero
    {X n : ℕ} (hn : 1 < n) (hnX : n ≤ X) :
    pintz2023Coeff X n = 0 := by
  exact mollifiedZetaCoeff_eq_zero X n hn hnX

/-- The elementary source bound `|a_n| ≤ τ(n)`.  The right side is the
literal number of positive divisors, so no unproved divisor-function
asymptotic is hidden here. -/
theorem norm_pintz2023Coeff_le_divisors_card (X n : ℕ) :
    ‖pintz2023Coeff X n‖ ≤ n.divisors.card := by
  unfold pintz2023Coeff mollifiedZetaCoeff
  calc
    ‖∑ d ∈ n.divisors.filter (fun d => d ≤ X),
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ ≤
        ∑ d ∈ n.divisors.filter (fun d => d ≤ X),
          ‖((ArithmeticFunction.moebius d : ℤ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors.filter (fun d => d ≤ X), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      simpa using moebius_coeff_norm_le_one d
    _ = ((n.divisors.filter (fun d => d ≤ X)).card : ℝ) := by simp
    _ ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- A literal dyadic block `(U,2U]` of the coefficient sequence from (4.1). -/
noncomputable def pintz2023Block
    (X U : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc U (2 * U), pintz2023Coeff X n * (n : ℂ) ^ (-s)

/-- The coefficient obtained by taking the `h`-th power of a fixed Pintz
dyadic block and collecting tuples with the same product. -/
noncomputable def pintz2023PowerCoeff
    (X U h m : ℕ) : ℂ :=
  ∑ p ∈
      (Fintype.piFinset
        (fun (_ : Fin h) => Finset.Ioc U (2 * U))).filter
          (fun p => (∏ j : Fin h, p j) = m),
    ∏ j : Fin h, pintz2023Coeff X (p j)

theorem pintz2023PowerCoeff_product_mem_support
    (U h : ℕ) (p : Fin h → ℕ)
    (hp : p ∈ Fintype.piFinset
      (fun (_ : Fin h) => Finset.Ioc U (2 * U))) :
    (∏ j : Fin h, p j) ∈ Finset.Icc (U ^ h) ((2 * U) ^ h) := by
  exact powCoeff_product_mem_support U h p hp

/-- Exact finite form of the powering step preceding Pintz (4.15). -/
theorem pintz2023_block_power_identity
    (X U h : ℕ) (s : ℂ) :
    (pintz2023Block X U s) ^ h =
      ∑ m ∈ Finset.Icc (U ^ h) ((2 * U) ^ h),
        pintz2023PowerCoeff X U h m * (m : ℂ) ^ (-s) := by
  classical
  let tuples := Fintype.piFinset
    (fun (_ : Fin h) => Finset.Ioc U (2 * U))
  have hsupport : ∀ p ∈ tuples,
      (∏ j : Fin h, p j) ∈ Finset.Icc (U ^ h) ((2 * U) ^ h) := by
    intro p hp
    exact pintz2023PowerCoeff_product_mem_support U h p hp
  rw [pintz2023Block, Finset.sum_pow']
  change (∑ p ∈ tuples,
      ∏ j : Fin h,
        (pintz2023Coeff X (p j) * (p j : ℂ) ^ (-s))) = _
  calc
    (∑ p ∈ tuples,
        ∏ j : Fin h,
          (pintz2023Coeff X (p j) * (p j : ℂ) ^ (-s))) =
        ∑ p ∈ tuples,
          (∏ j : Fin h, pintz2023Coeff X (p j)) *
            ((∏ j : Fin h, p j : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.prod_mul_distrib, prod_natCast_cpow_eq]
    _ = ∑ m ∈ Finset.Icc (U ^ h) ((2 * U) ^ h),
        ∑ p ∈ tuples with (∏ j : Fin h, p j) = m,
          (∏ j : Fin h, pintz2023Coeff X (p j)) *
            ((∏ j : Fin h, p j : ℕ) : ℂ) ^ (-s) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hsupport _
    _ = ∑ m ∈ Finset.Icc (U ^ h) ((2 * U) ^ h),
        pintz2023PowerCoeff X U h m * (m : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [pintz2023PowerCoeff, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

/-- A nonempty powered block has no coefficient at the artificial lower
endpoint `U^h`; every source coordinate is strictly larger than `U`. -/
theorem pintz2023PowerCoeff_lower_endpoint_eq_zero
    (X U h : ℕ) (hU : 0 < U) (hh : 0 < h) :
    pintz2023PowerCoeff X U h (U ^ h) = 0 := by
  classical
  rw [pintz2023PowerCoeff]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨hpSupport, hpProduct⟩
  rw [Fintype.mem_piFinset] at hpSupport
  have hCoordinate : ∀ j : Fin h, U + 1 ≤ p j := by
    intro j
    have hj := hpSupport j
    rw [Finset.mem_Ioc] at hj
    omega
  have hProductLower : (U + 1) ^ h ≤ ∏ j : Fin h, p j := by
    calc
      (U + 1) ^ h = ∏ _j : Fin h, (U + 1) := by simp
      _ ≤ ∏ j : Fin h, p j := by
        apply Finset.prod_le_prod
        · intro j hj
          omega
        · intro j hj
          exact hCoordinate j
  have hStrict : U ^ h < (U + 1) ^ h :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self U) hh.ne'
  omega

/-- Source-faithful half-open support after removing the zero lower
endpoint. -/
theorem pintz2023_block_power_identity_Ioc
    (X U h : ℕ) (s : ℂ) (hU : 0 < U) (hh : 0 < h) :
    (pintz2023Block X U s) ^ h =
      ∑ m ∈ Finset.Ioc (U ^ h) ((2 * U) ^ h),
        pintz2023PowerCoeff X U h m * (m : ℂ) ^ (-s) := by
  rw [pintz2023_block_power_identity]
  rw [Finset.Icc_eq_cons_Ioc]
  · simp [pintz2023PowerCoeff_lower_endpoint_eq_zero X U h hU hh]
  · exact Nat.pow_le_pow_left (by omega) h

/-- Uniform epsilon-power growth of the exact coefficients in (4.15).
The proof uses only the classical divisor bound for each `a_n` and the
ordered-factorization bound for collecting tuples with a common product. -/
theorem pintz2023PowerCoeff_bound_native
    (h : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ X U m : ℕ, 0 < m →
      ‖pintz2023PowerCoeff X U h m‖ ≤ C * (m : ℝ) ^ epsilon := by
  let delta : ℝ := epsilon / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  obtain ⟨A, hA, hDivisor⟩ := divisorCountBound_native delta hdelta
  obtain ⟨B, hB, hFactorization⟩ :=
    factorizationCountBound_native h delta hdelta
  refine ⟨B * A ^ h, mul_pos hB (pow_pos hA h), ?_⟩
  intro X U m hm
  let source :=
    (Fintype.piFinset
      (fun (_ : Fin h) => Finset.Ioc U (2 * U))).filter
        (fun p => (∏ j : Fin h, p j) = m)
  let target :=
    (Fintype.piFinset
      (fun (_ : Fin h) => Finset.Ioc 1 m)).filter
        (fun p => (∏ j : Fin h, p j) = m)
  have hsource : source ⊆ target := by
    simpa only [source, target] using pow_coeff_subset U h m hm
  have hterm (p : Fin h → ℕ) (hp : p ∈ source) :
      ‖∏ j : Fin h, pintz2023Coeff X (p j)‖ ≤
        A ^ h * (m : ℝ) ^ delta := by
    have hpSource := hp
    change p ∈
      (Fintype.piFinset
        (fun (_ : Fin h) => Finset.Ioc U (2 * U))).filter
          (fun p => (∏ j : Fin h, p j) = m) at hpSource
    rw [Finset.mem_filter] at hpSource
    rcases hpSource with ⟨hpSupport, hpProduct⟩
    rw [Fintype.mem_piFinset] at hpSupport
    rw [norm_prod]
    calc
      ∏ j : Fin h, ‖pintz2023Coeff X (p j)‖ ≤
          ∏ j : Fin h, A * (p j : ℝ) ^ delta := by
        apply Finset.prod_le_prod
        · intro j hj
          exact norm_nonneg _
        · intro j hj
          have hpj : 0 < p j := by
            have := (Finset.mem_Ioc.mp (hpSupport j)).1
            omega
          exact (norm_pintz2023Coeff_le_divisors_card X (p j)).trans
            (hDivisor (p j) hpj)
      _ = (∏ _j : Fin h, A) *
          (∏ j : Fin h, (p j : ℝ) ^ delta) := by
        rw [Finset.prod_mul_distrib]
      _ = A ^ h * (m : ℝ) ^ delta := by
        rw [Real.finsetProd_rpow Finset.univ (fun j => (p j : ℝ))]
        · have hpProductReal :
              ∏ j : Fin h, (p j : ℝ) = (m : ℝ) := by
            exact_mod_cast hpProduct
          rw [hpProductReal]
          simp
        · intro j hj
          positivity
  rw [pintz2023PowerCoeff]
  calc
    ‖∑ p ∈ source, ∏ j : Fin h, pintz2023Coeff X (p j)‖ ≤
        ∑ p ∈ source, ‖∏ j : Fin h, pintz2023Coeff X (p j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ source, A ^ h * (m : ℝ) ^ delta := by
      exact Finset.sum_le_sum fun p hp => hterm p hp
    _ = (source.card : ℝ) * (A ^ h * (m : ℝ) ^ delta) := by simp
    _ ≤ (target.card : ℝ) * (A ^ h * (m : ℝ) ^ delta) := by
      gcongr
    _ ≤ (B * (m : ℝ) ^ delta) *
        (A ^ h * (m : ℝ) ^ delta) := by
      gcongr
      simpa only [target] using hFactorization m hm
    _ = (B * A ^ h) * (m : ℝ) ^ epsilon := by
      have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
      calc
        B * (m : ℝ) ^ delta * (A ^ h * (m : ℝ) ^ delta) =
            (B * A ^ h) * ((m : ℝ) ^ delta * (m : ℝ) ^ delta) := by ring
        _ = (B * A ^ h) * (m : ℝ) ^ (delta + delta) := by
          rw [Real.rpow_add hmReal]
        _ = (B * A ^ h) * (m : ℝ) ^ epsilon := by
          congr 2
          dsimp only [delta]
          ring

#print axioms pintz2023Coeff_eq_zero
#print axioms norm_pintz2023Coeff_le_divisors_card
#print axioms pintz2023_block_power_identity
#print axioms pintz2023_block_power_identity_Ioc
#print axioms pintz2023PowerCoeff_bound_native

end

end GafniTao

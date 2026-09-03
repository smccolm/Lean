import GafniTao.Pintz2023Localization

/-!
# Pintz (2023), equation (4.15): powering a truncated dyadic interval

The last interval selected in Pintz's dyadic decomposition need only be a
subset of `(U,2U]`.  Consequently the full-block convolution is not by itself
an exact source model.  This file collects products over an arbitrary finite
interval and proves the exact powered Dirichlet-polynomial identity, together
with the genuine dyadic support inherited from the subset hypothesis.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The Pintz polynomial on an arbitrary finite index set. -/
noncomputable def pintz2023IntervalBlock
    (X : ℕ) (Iset : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Iset, pintz2023Coeff X n * (n : ℂ) ^ (-s)

/-- Coefficients obtained after taking the `h`-th power of an arbitrary
finite Pintz block and collecting tuples with equal product. -/
noncomputable def pintz2023IntervalPowerCoeff
    (X : ℕ) (Iset : Finset ℕ) (h m : ℕ) : ℂ :=
  ∑ p ∈
      (Fintype.piFinset (fun (_ : Fin h) => Iset)).filter
        (fun p => (∏ j : Fin h, p j) = m),
    ∏ j : Fin h, pintz2023Coeff X (p j)

theorem pintz2023IntervalPowerCoeff_product_mem_support
    {Iset : Finset ℕ} {U h : ℕ}
    (hI : Iset ⊆ Finset.Ioc U (2 * U))
    (p : Fin h → ℕ)
    (hp : p ∈ Fintype.piFinset (fun (_ : Fin h) => Iset)) :
    (∏ j : Fin h, p j) ∈ Finset.Icc (U ^ h) ((2 * U) ^ h) := by
  apply powCoeff_product_mem_support U h p
  rw [Fintype.mem_piFinset] at hp ⊢
  intro j
  exact hI (hp j)

/-- Exact finite identity for the source's possibly truncated selected
interval. -/
theorem pintz2023_interval_power_identity
    (X : ℕ) {Iset : Finset ℕ} (U h : ℕ) (s : ℂ)
    (hI : Iset ⊆ Finset.Ioc U (2 * U)) :
    (pintz2023IntervalBlock X Iset s) ^ h =
      ∑ m ∈ Finset.Icc (U ^ h) ((2 * U) ^ h),
        pintz2023IntervalPowerCoeff X Iset h m * (m : ℂ) ^ (-s) := by
  classical
  let tuples := Fintype.piFinset (fun (_ : Fin h) => Iset)
  have hsupport : ∀ p ∈ tuples,
      (∏ j : Fin h, p j) ∈ Finset.Icc (U ^ h) ((2 * U) ^ h) := by
    intro p hp
    exact pintz2023IntervalPowerCoeff_product_mem_support hI p hp
  rw [pintz2023IntervalBlock, Finset.sum_pow']
  change (∑ p ∈ tuples,
      ∏ j : Fin h,
        (pintz2023Coeff X (p j) * (p j : ℂ) ^ (-s))) = _
  calc
    (∑ p ∈ tuples,
        ∏ j : Fin h,
          (pintz2023Coeff X (p j) * (p j : ℂ) ^ (-s))) =
        ∑ p ∈ tuples,
          (∏ j : Fin h, pintz2023Coeff X (p j)) *
            (((∏ j : Fin h, p j) : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.prod_mul_distrib, prod_natCast_cpow_eq]
    _ = ∑ m ∈ Finset.Icc (U ^ h) ((2 * U) ^ h),
        ∑ p ∈ tuples with (∏ j : Fin h, p j) = m,
          (∏ j : Fin h, pintz2023Coeff X (p j)) *
            (((∏ j : Fin h, p j) : ℕ) : ℂ) ^ (-s) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hsupport _
    _ = ∑ m ∈ Finset.Icc (U ^ h) ((2 * U) ^ h),
        pintz2023IntervalPowerCoeff X Iset h m * (m : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [pintz2023IntervalPowerCoeff, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

theorem pintz2023IntervalPowerCoeff_lower_endpoint_eq_zero
    (X : ℕ) {Iset : Finset ℕ} (U h : ℕ)
    (hI : Iset ⊆ Finset.Ioc U (2 * U))
    (hU : 0 < U) (hh : 0 < h) :
    pintz2023IntervalPowerCoeff X Iset h (U ^ h) = 0 := by
  classical
  rw [pintz2023IntervalPowerCoeff]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨hpSupport, hpProduct⟩
  rw [Fintype.mem_piFinset] at hpSupport
  have hCoordinate : ∀ j : Fin h, U + 1 ≤ p j := by
    intro j
    have hj := hI (hpSupport j)
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

/-- Half-open support form of equation (4.15), valid for a truncated final
dyadic block as well as for a complete block. -/
theorem pintz2023_interval_power_identity_Ioc
    (X : ℕ) {Iset : Finset ℕ} (U h : ℕ) (s : ℂ)
    (hI : Iset ⊆ Finset.Ioc U (2 * U))
    (hU : 0 < U) (hh : 0 < h) :
    (pintz2023IntervalBlock X Iset s) ^ h =
      ∑ m ∈ Finset.Ioc (U ^ h) ((2 * U) ^ h),
        pintz2023IntervalPowerCoeff X Iset h m * (m : ℂ) ^ (-s) := by
  rw [pintz2023_interval_power_identity X U h s hI]
  rw [Finset.Icc_eq_cons_Ioc]
  · simp [pintz2023IntervalPowerCoeff_lower_endpoint_eq_zero
      X U h hI hU hh]
  · exact Nat.pow_le_pow_left (by omega) h

/-- The full-block coefficient is recovered definitionally from the general
truncated-interval coefficient. -/
theorem pintz2023IntervalPowerCoeff_full_block
    (X U h m : ℕ) :
    pintz2023IntervalPowerCoeff X (Finset.Ioc U (2 * U)) h m =
      pintz2023PowerCoeff X U h m := by
  rfl

/-- Uniform epsilon-power growth for the exact coefficients of a truncated
selected interval.  This is the coefficient estimate used after (4.15); its
constant may depend on the fixed powering exponent and epsilon, but not on
the mollifier length, selected block, truncation, or product. -/
theorem pintz2023IntervalPowerCoeff_bound_native
    (h : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X U m : ℕ) (Iset : Finset ℕ),
        Iset ⊆ Finset.Ioc U (2 * U) → 0 < U → 0 < m →
        ‖pintz2023IntervalPowerCoeff X Iset h m‖ ≤
          C * (m : ℝ) ^ epsilon := by
  let delta : ℝ := epsilon / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  obtain ⟨A, hA, hDivisor⟩ := divisorCountBound_native delta hdelta
  obtain ⟨B, hB, hFactorization⟩ :=
    factorizationCountBound_native h delta hdelta
  refine ⟨B * A ^ h, mul_pos hB (pow_pos hA h), ?_⟩
  intro X U m Iset hI hU hm
  let source :=
    (Fintype.piFinset (fun (_ : Fin h) => Iset)).filter
      (fun p => (∏ j : Fin h, p j) = m)
  let target :=
    (Fintype.piFinset (fun (_ : Fin h) => Finset.Ioc 1 m)).filter
      (fun p => (∏ j : Fin h, p j) = m)
  have hsource : source ⊆ target := by
    intro p hp
    dsimp only [source, target] at hp ⊢
    rw [Finset.mem_filter] at hp ⊢
    rcases hp with ⟨hpSupport, hpProduct⟩
    refine ⟨?_, hpProduct⟩
    rw [Fintype.mem_piFinset] at hpSupport ⊢
    intro j
    have hpjI := hI (hpSupport j)
    have hpjPos : 1 < p j := by
      have := (Finset.mem_Ioc.mp hpjI).1
      omega
    have hpjLe : p j ≤ m := by
      have hfactor : p j ≤ ∏ i : Fin h, p i := by
        apply Finset.single_le_prod'
        · intro i hi
          exact Nat.zero_lt_of_lt
            (Finset.mem_Ioc.mp (hI (hpSupport i))).1
        · exact Finset.mem_univ j
      simpa only [hpProduct] using hfactor
    exact Finset.mem_Ioc.mpr ⟨hpjPos, hpjLe⟩
  have hterm (p : Fin h → ℕ) (hp : p ∈ source) :
      ‖∏ j : Fin h, pintz2023Coeff X (p j)‖ ≤
        A ^ h * (m : ℝ) ^ delta := by
    have hpSource := hp
    change p ∈
      (Fintype.piFinset (fun (_ : Fin h) => Iset)).filter
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
            exact Nat.zero_lt_of_lt
              (Finset.mem_Ioc.mp (hI (hpSupport j))).1
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
  rw [pintz2023IntervalPowerCoeff]
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

#print axioms pintz2023_interval_power_identity
#print axioms pintz2023_interval_power_identity_Ioc
#print axioms pintz2023IntervalPowerCoeff_full_block
#print axioms pintz2023IntervalPowerCoeff_bound_native

end

end GafniTao

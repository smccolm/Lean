import GafniTao.Pintz2023CoefficientSplit
import GafniTao.Pintz2023IntervalPower
import GafniTao.Pintz2023HalaszEnergy

/-!
# Pintz (2023), equations (4.15)--(4.16): the surviving small-m power

The coefficient powered after (4.14) is the small-`m` coefficient `a''_n`,
not the original coefficient `a_n`.  This module records that distinction in
the type of the convolution and proves the exact finite Dirichlet-polynomial
identity on a possibly truncated dyadic interval.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The collected coefficient after taking the `h`-th power of the literal
small-`m` block in (4.15). -/
noncomputable def pintz2023SmallMIntervalPowerCoeff
    (X : ℕ) (R : ℝ) (Iset : Finset ℕ) (h m : ℕ) : ℂ :=
  ∑ p ∈
      (Fintype.piFinset (fun (_ : Fin h) => Iset)).filter
        (fun p => (∏ j : Fin h, p j) = m),
    ∏ j : Fin h, pintz2023SmallMCoeff X (p j) R

/-- Exact power identity for the surviving part of equation (4.15). -/
theorem pintz2023_smallM_interval_power_identity
    (X : ℕ) (R : ℝ) {Iset : Finset ℕ} (U h : ℕ) (s : ℂ)
    (hI : Iset ⊆ Finset.Ioc U (2 * U)) :
    (pintz2023SplitIntervalBlock
      (fun n => pintz2023SmallMCoeff X n R) Iset s) ^ h =
      ∑ m ∈ Finset.Icc (U ^ h) ((2 * U) ^ h),
        pintz2023SmallMIntervalPowerCoeff X R Iset h m *
          (m : ℂ) ^ (-s) := by
  classical
  let tuples := Fintype.piFinset (fun (_ : Fin h) => Iset)
  have hsupport : ∀ p ∈ tuples,
      (∏ j : Fin h, p j) ∈ Finset.Icc (U ^ h) ((2 * U) ^ h) := by
    intro p hp
    apply powCoeff_product_mem_support U h p
    rw [Fintype.mem_piFinset] at hp ⊢
    intro j
    exact hI (hp j)
  rw [pintz2023SplitIntervalBlock, Finset.sum_pow']
  change (∑ p ∈ tuples,
      ∏ j : Fin h,
        (pintz2023SmallMCoeff X (p j) R * (p j : ℂ) ^ (-s))) = _
  calc
    (∑ p ∈ tuples,
        ∏ j : Fin h,
          (pintz2023SmallMCoeff X (p j) R * (p j : ℂ) ^ (-s))) =
        ∑ p ∈ tuples,
          (∏ j : Fin h, pintz2023SmallMCoeff X (p j) R) *
            (((∏ j : Fin h, p j) : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.prod_mul_distrib, prod_natCast_cpow_eq]
    _ = ∑ m ∈ Finset.Icc (U ^ h) ((2 * U) ^ h),
        ∑ p ∈ tuples with (∏ j : Fin h, p j) = m,
          (∏ j : Fin h, pintz2023SmallMCoeff X (p j) R) *
            (((∏ j : Fin h, p j) : ℕ) : ℂ) ^ (-s) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hsupport _
    _ = ∑ m ∈ Finset.Icc (U ^ h) ((2 * U) ^ h),
        pintz2023SmallMIntervalPowerCoeff X R Iset h m *
          (m : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [pintz2023SmallMIntervalPowerCoeff, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

theorem pintz2023SmallMIntervalPowerCoeff_lower_endpoint_eq_zero
    (X : ℕ) (R : ℝ) {Iset : Finset ℕ} (U h : ℕ)
    (hI : Iset ⊆ Finset.Ioc U (2 * U))
    (hU : 0 < U) (hh : 0 < h) :
    pintz2023SmallMIntervalPowerCoeff X R Iset h (U ^ h) = 0 := by
  classical
  rw [pintz2023SmallMIntervalPowerCoeff]
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

/-- Half-open version used by Pintz after the second dyadic subdivision. -/
theorem pintz2023_smallM_interval_power_identity_Ioc
    (X : ℕ) (R : ℝ) {Iset : Finset ℕ} (U h : ℕ) (s : ℂ)
    (hI : Iset ⊆ Finset.Ioc U (2 * U))
    (hU : 0 < U) (hh : 0 < h) :
    (pintz2023SplitIntervalBlock
      (fun n => pintz2023SmallMCoeff X n R) Iset s) ^ h =
      ∑ m ∈ Finset.Ioc (U ^ h) ((2 * U) ^ h),
        pintz2023SmallMIntervalPowerCoeff X R Iset h m *
          (m : ℂ) ^ (-s) := by
  rw [pintz2023_smallM_interval_power_identity X R U h s hI]
  rw [Finset.Icc_eq_cons_Ioc]
  · simp [pintz2023SmallMIntervalPowerCoeff_lower_endpoint_eq_zero
      X R U h hI hU hh]
  · exact Nat.pow_le_pow_left (by omega) h

/-- Uniform epsilon-power bound for the exact small-`m` powered
coefficients. -/
theorem pintz2023SmallMIntervalPowerCoeff_bound_native
    (h : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X U m : ℕ) (R : ℝ) (Iset : Finset ℕ),
        Iset ⊆ Finset.Ioc U (2 * U) → 0 < U → 0 < m →
        ‖pintz2023SmallMIntervalPowerCoeff X R Iset h m‖ ≤
          C * (m : ℝ) ^ epsilon := by
  let delta : ℝ := epsilon / 2
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  obtain ⟨A, hA, hDivisor⟩ := divisorCountBound_native delta hdelta
  obtain ⟨B, hB, hFactorization⟩ :=
    factorizationCountBound_native h delta hdelta
  refine ⟨B * A ^ h, mul_pos hB (pow_pos hA h), ?_⟩
  intro X U m R Iset hI hU hm
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
      rw [Finset.mem_Ioc] at hpjI
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
      ‖∏ j : Fin h, pintz2023SmallMCoeff X (p j) R‖ ≤
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
      ∏ j : Fin h, ‖pintz2023SmallMCoeff X (p j) R‖ ≤
          ∏ j : Fin h, A * (p j : ℝ) ^ delta := by
        apply Finset.prod_le_prod
        · intro j hj
          exact norm_nonneg _
        · intro j hj
          have hpj : 0 < p j :=
            Nat.zero_lt_of_lt (Finset.mem_Ioc.mp (hI (hpSupport j))).1
          exact (norm_pintz2023SmallMCoeff_le_divisors_card X (p j) R).trans
            (hDivisor (p j) hpj)
      _ = (∏ _j : Fin h, A) *
          (∏ j : Fin h, (p j : ℝ) ^ delta) := by
        rw [Finset.prod_mul_distrib]
      _ = A ^ h * (m : ℝ) ^ delta := by
        rw [Real.finsetProd_rpow Finset.univ (fun j => (p j : ℝ))]
        · have hpProductReal : ∏ j : Fin h, (p j : ℝ) = (m : ℝ) := by
            exact_mod_cast hpProduct
          rw [hpProductReal]
          simp
        · intro j hj
          positivity
  rw [pintz2023SmallMIntervalPowerCoeff]
  calc
    ‖∑ p ∈ source, ∏ j : Fin h,
        pintz2023SmallMCoeff X (p j) R‖ ≤
        ∑ p ∈ source, ‖∏ j : Fin h,
          pintz2023SmallMCoeff X (p j) R‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ source, A ^ h * (m : ℝ) ^ delta := by
      exact Finset.sum_le_sum fun p hp => hterm p hp
    _ = (source.card : ℝ) * (A ^ h * (m : ℝ) ^ delta) := by simp
    _ ≤ (target.card : ℝ) * (A ^ h * (m : ℝ) ^ delta) := by gcongr
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

/-- Exact `d_n`-energy estimate for the small-`m` coefficient that actually
survives equation (4.14). -/
theorem exists_sum_norm_pintz2023SmallMIntervalPowerHalaszD_sq_le
    (h : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X U N : ℕ) (R : ℝ) (baseI ambient Iset : Finset ℕ)
        (eta lambda : ℝ),
        baseI ⊆ Finset.Ioc U (2 * U) → 0 < U → 0 < N →
        Iset ⊆ ambient → (∀ n ∈ ambient, 0 < n) →
        Iset ⊆ Finset.Ioc N (2 * N) →
        -1 - 4 * eta - 2 / lambda + 2 * epsilon ≤ 0 →
        (∑ n ∈ ambient,
          ‖pintz2023HalaszDSupported Iset
            (pintz2023SmallMIntervalPowerCoeff X R baseI h)
              N eta lambda n‖ ^ 2) ≤
          C ^ 2 *
            (Real.exp (-1) * (1 - Real.exp (-(1 / 2 : ℝ))))⁻¹ *
            (N : ℝ) ^ (-4 * eta - 2 / lambda + 2 * epsilon) := by
  obtain ⟨C, hC, hCoeff⟩ :=
    pintz2023SmallMIntervalPowerCoeff_bound_native h epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro X U N R baseI ambient Iset eta lambda hbaseI hU hN
    hIambient hpositive hIdyadic hExponent
  apply sum_norm_pintz2023HalaszDSupported_sq_le ambient Iset
    (pintz2023SmallMIntervalPowerCoeff X R baseI h)
      eta lambda epsilon C hN hIambient hpositive hIdyadic hC.le hExponent
  intro n hn
  exact hCoeff X U n R baseI hbaseI hU
    (hpositive n (hIambient hn))

#print axioms pintz2023_smallM_interval_power_identity
#print axioms pintz2023_smallM_interval_power_identity_Ioc
#print axioms pintz2023SmallMIntervalPowerCoeff_bound_native
#print axioms exists_sum_norm_pintz2023SmallMIntervalPowerHalaszD_sq_le

end

end GafniTao

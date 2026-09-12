import Tao2026.SmoothNumberCEPBootstrap

/-!
# Coarse PNT blocks for the critical smooth-number lower bound

For the `u log u + O(u log log u)` estimate needed by Tao, one may group the
very thin CEP bands into dyadic prime blocks.  A fixed two-sided PNT threshold
then gives a reciprocal-prime contribution of order `1 / log n` from each
block, avoiding any appeal to a quantitative PNT error on shrinking
intervals.
-/

open scoped BigOperators Chebyshev

namespace Tao2026

noncomputable section

open Filter Topology Finset

/-- A fixed threshold beyond which `theta(n)` lies between its `3/4` and
`5/4` linear envelopes. -/
theorem exists_chebyshevTheta_quarter_threshold :
    ∃ B : ℕ, 4 ≤ B ∧ ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta n ∧
        Chebyshev.theta n ≤ (5 / 4 : ℝ) * n := by
  have herrReal : ∀ᶠ t : ℝ in Filter.atTop,
      |Chebyshev.theta t - t| ≤ (1 / 4 : ℝ) * t := by
    have h := Asymptotics.IsEquivalent.isLittleO chebyshev_asymptotic
    rw [Asymptotics.isLittleO_iff] at h
    have hquarter := h (by norm_num : (0 : ℝ) < 1 / 4)
    filter_upwards [hquarter, eventually_gt_atTop (0 : ℝ)] with t ht htPos
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at ht
    change |Chebyshev.theta t - t| ≤ (1 / 4 : ℝ) * |t| at ht
    rw [abs_of_pos htPos] at ht
    exact ht
  have herrNat : ∀ᶠ n : ℕ in Filter.atTop,
      |Chebyshev.theta (n : ℝ) - n| ≤ (1 / 4 : ℝ) * n :=
    tendsto_natCast_atTop_atTop.eventually herrReal
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 herrNat
  refine ⟨max 4 B, le_max_left _ _, ?_⟩
  intro n hn
  have hnerr := hB n ((le_max_right 4 B).trans hn)
  rw [abs_le] at hnerr
  constructor <;> linarith

/-- Natural-prime block `(n/2,n]`. -/
def cepDyadicPrimeBlock (n : ℕ) : Finset ℕ :=
  n.primesLE \ (n / 2).primesLE

theorem mem_cepDyadicPrimeBlock_iff {n p : ℕ} :
    p ∈ cepDyadicPrimeBlock n ↔
      p.Prime ∧ n / 2 < p ∧ p ≤ n := by
  rw [cepDyadicPrimeBlock, Finset.mem_sdiff]
  simp only [Nat.mem_primesLE]
  aesop

theorem sum_log_cepDyadicPrimeBlock (n : ℕ) :
    ∑ p ∈ cepDyadicPrimeBlock n, Real.log (p : ℝ) =
      Chebyshev.theta (n : ℝ) -
        Chebyshev.theta ((n / 2 : ℕ) : ℝ) := by
  have hsubset : (n / 2).primesLE ⊆ n.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.mem_primesLE.mp hp).1.trans (Nat.div_le_self n 2),
        (Nat.mem_primesLE.mp hp).2⟩
  rw [cepDyadicPrimeBlock, eq_sub_iff_add_eq]
  simpa only [Chebyshev.theta_eq_sum_primesLE_log] using
    (Finset.sum_sdiff hsubset
      (f := fun p : ℕ => Real.log (p : ℝ)))

theorem log_le_nat_mul_log_mul_inv_of_mem_cepDyadicPrimeBlock
    {n p : ℕ} (hn : 2 ≤ n) (hp : p ∈ cepDyadicPrimeBlock n) :
    Real.log (p : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) * (p : ℝ)⁻¹ := by
  have hpData := Finset.mem_sdiff.mp hp
  have hpPrime := Nat.prime_of_mem_primesLE hpData.1
  have hpn := Nat.le_of_mem_primesLE hpData.1
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hnPos : (0 : ℝ) < n := by positivity
  have hlogp0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
  have hlogpn : Real.log (p : ℝ) ≤ Real.log (n : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hpPos hnPos (by exact_mod_cast hpn)
  have hprod : (p : ℝ) * Real.log (p : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) :=
    mul_le_mul (by exact_mod_cast hpn) hlogpn hlogp0 (by positivity)
  calc
    Real.log (p : ℝ) =
        ((p : ℝ) * Real.log (p : ℝ)) * (p : ℝ)⁻¹ := by
      field_simp
    _ ≤ ((n : ℝ) * Real.log (n : ℝ)) * (p : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hprod (by positivity)

/-- A dyadic block with the two PNT envelope bounds has reciprocal-prime
mass at least `1/(8 log n)`. -/
theorem one_div_eight_log_le_sum_inv_cepDyadicPrimeBlock
    {n : ℕ} (hn : 4 ≤ n)
    (hlower : (3 / 4 : ℝ) * n ≤ Chebyshev.theta (n : ℝ))
    (hupper : Chebyshev.theta ((n / 2 : ℕ) : ℝ) ≤
      (5 / 4 : ℝ) * (n / 2 : ℕ)) :
    1 / (8 * Real.log (n : ℝ)) ≤
      ∑ p ∈ cepDyadicPrimeBlock n, ((p : ℝ)⁻¹) := by
  let S := ∑ p ∈ cepDyadicPrimeBlock n, ((p : ℝ)⁻¹)
  have hsum : Chebyshev.theta (n : ℝ) -
      Chebyshev.theta ((n / 2 : ℕ) : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) * S := by
    rw [← sum_log_cepDyadicPrimeBlock]
    calc
      ∑ p ∈ cepDyadicPrimeBlock n, Real.log (p : ℝ) ≤
          ∑ p ∈ cepDyadicPrimeBlock n,
            (n : ℝ) * Real.log (n : ℝ) * (p : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        exact log_le_nat_mul_log_mul_inv_of_mem_cepDyadicPrimeBlock
          (by omega) hp
      _ = (n : ℝ) * Real.log (n : ℝ) * S := by
        simp only [S, Finset.mul_sum]
  have hnHalf : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := Nat.cast_div_le
  have htheta : (n : ℝ) / 8 ≤
      Chebyshev.theta (n : ℝ) -
        Chebyshev.theta ((n / 2 : ℕ) : ℝ) := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hupper' : Chebyshev.theta ((n / 2 : ℕ) : ℝ) ≤
        (5 / 8 : ℝ) * n := by
      calc
        Chebyshev.theta ((n / 2 : ℕ) : ℝ) ≤
            (5 / 4 : ℝ) * ((n / 2 : ℕ) : ℝ) := hupper
        _ ≤ (5 / 4 : ℝ) * ((n : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hnHalf (by norm_num)
        _ = (5 / 8 : ℝ) * n := by ring
    linarith
  have hmain : (n : ℝ) / 8 ≤
      (n : ℝ) * Real.log (n : ℝ) * S := htheta.trans hsum
  have hnPos : (0 : ℝ) < n := by positivity
  have hlogPos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  apply (div_le_iff₀ (mul_pos (by norm_num) hlogPos)).2
  have hmain' : 1 ≤ 8 * Real.log (n : ℝ) * S := by
    calc
      1 = ((n : ℝ) / 8) * (8 / (n : ℝ)) := by field_simp
      _ ≤ ((n : ℝ) * Real.log (n : ℝ) * S) * (8 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
      _ = 8 * Real.log (n : ℝ) * S := by field_simp
  simpa only [S, mul_comm, mul_left_comm, mul_assoc] using hmain'

/-- The dyadic blocks descending from a common endpoint are pairwise
disjoint. -/
theorem disjoint_cepDyadicPrimeBlock_div_pow_two
    {y i j : ℕ} (hij : i ≠ j) :
    Disjoint (cepDyadicPrimeBlock (y / 2 ^ i))
      (cepDyadicPrimeBlock (y / 2 ^ j)) := by
  rw [Finset.disjoint_left]
  intro p hpi hpj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hpow : 2 ^ (i + 1) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hdiv : y / 2 ^ j ≤ y / 2 ^ (i + 1) :=
      Nat.div_le_div_left hpow (pow_pos (by norm_num) _)
    have hstep : y / 2 ^ (i + 1) = (y / 2 ^ i) / 2 := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    have hi := (mem_cepDyadicPrimeBlock_iff.mp hpi).2.1
    have hj := (mem_cepDyadicPrimeBlock_iff.mp hpj).2.2
    rw [hstep] at hdiv
    omega
  · have hpow : 2 ^ (j + 1) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hdiv : y / 2 ^ i ≤ y / 2 ^ (j + 1) :=
      Nat.div_le_div_left hpow (pow_pos (by norm_num) _)
    have hstep : y / 2 ^ (j + 1) = (y / 2 ^ j) / 2 := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
    have hi := (mem_cepDyadicPrimeBlock_iff.mp hpi).2.2
    have hj := (mem_cepDyadicPrimeBlock_iff.mp hpj).2.1
    rw [hstep] at hdiv
    omega

/-- Union of the first `J` dyadic prime blocks below `y`. -/
def cepDyadicPrimeBlockUnion (y J : ℕ) : Finset ℕ :=
  (Finset.range J).biUnion fun j => cepDyadicPrimeBlock (y / 2 ^ j)

theorem sum_cepDyadicPrimeBlockUnion
    (y J : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ cepDyadicPrimeBlockUnion y J, f p =
      ∑ j ∈ Finset.range J,
        ∑ p ∈ cepDyadicPrimeBlock (y / 2 ^ j), f p := by
  apply Finset.sum_biUnion
  intro i hi j hj hij
  exact disjoint_cepDyadicPrimeBlock_div_pow_two hij

theorem mem_cepDyadicPrimeBlockUnion_prime_le
    {y J p : ℕ} (hp : p ∈ cepDyadicPrimeBlockUnion y J) :
    p.Prime ∧ p ≤ y := by
  rw [cepDyadicPrimeBlockUnion, Finset.mem_biUnion] at hp
  obtain ⟨j, hj, hpj⟩ := hp
  have hpData := mem_cepDyadicPrimeBlock_iff.mp hpj
  exact ⟨hpData.1, hpData.2.2.trans (Nat.div_le_self y (2 ^ j))⟩

/-- The same dyadic union as an alphabet of bounded primes, ready for the
one-band CEP packet. -/
noncomputable def cepDyadicPrimeAlphabet (y J : ℕ) :
    Finset (TaoBoundedPrime y) :=
  Finset.univ.filter fun p => (p : ℕ) ∈ cepDyadicPrimeBlockUnion y J

theorem mem_cepDyadicPrimeAlphabet_iff
    {y J : ℕ} {p : TaoBoundedPrime y} :
    p ∈ cepDyadicPrimeAlphabet y J ↔
      (p : ℕ) ∈ cepDyadicPrimeBlockUnion y J := by
  simp [cepDyadicPrimeAlphabet]

theorem image_cepDyadicPrimeAlphabet
    (y J : ℕ) :
    (cepDyadicPrimeAlphabet y J).image
        (fun p : TaoBoundedPrime y => (p : ℕ)) =
      cepDyadicPrimeBlockUnion y J := by
  ext p
  constructor
  · intro hp
    rw [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact mem_cepDyadicPrimeAlphabet_iff.mp hq
  · intro hp
    have hpData := mem_cepDyadicPrimeBlockUnion_prime_le hp
    let q : TaoBoundedPrime y :=
      ⟨p, Nat.mem_primesLE.mpr ⟨hpData.2, hpData.1⟩⟩
    rw [Finset.mem_image]
    exact ⟨q, mem_cepDyadicPrimeAlphabet_iff.mpr hp, rfl⟩

theorem sum_inv_cepDyadicPrimeAlphabet (y J : ℕ) :
    ∑ p ∈ cepDyadicPrimeAlphabet y J, (((p : ℕ) : ℝ)⁻¹) =
      ∑ p ∈ cepDyadicPrimeBlockUnion y J, ((p : ℝ)⁻¹) := by
  rw [← image_cepDyadicPrimeAlphabet y J, Finset.sum_image]
  intro p hp q hq hpq
  exact Subtype.ext hpq

/-- Summing the dyadic block bounds gives a reciprocal mass proportional to
the number of retained blocks. -/
theorem card_div_eight_log_le_sum_inv_cepDyadicPrimeAlphabet
    {B y J : ℕ} (hB : 4 ≤ B)
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta n ∧
        Chebyshev.theta n ≤ (5 / 4 : ℝ) * n)
    (hbottom : ∀ j ∈ Finset.range J, B ≤ y / 2 ^ (j + 1)) :
    (J : ℝ) / (8 * Real.log (y : ℝ)) ≤
      ∑ p ∈ cepDyadicPrimeAlphabet y J, (((p : ℕ) : ℝ)⁻¹) := by
  by_cases hJ : J = 0
  · subst J
    simp
    positivity
  have hyB : B ≤ y := by
    have hzero : 0 ∈ Finset.range J := Finset.mem_range.mpr (Nat.pos_of_ne_zero hJ)
    exact (hbottom 0 hzero).trans (Nat.div_le_self y (2 ^ (0 + 1)))
  have hyTwo : 2 ≤ y := (by omega : 2 ≤ B).trans hyB
  rw [sum_inv_cepDyadicPrimeAlphabet, sum_cepDyadicPrimeBlockUnion]
  calc
    (J : ℝ) / (8 * Real.log (y : ℝ)) =
        ∑ _j ∈ Finset.range J, 1 / (8 * Real.log (y : ℝ)) := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ j ∈ Finset.range J,
        ∑ p ∈ cepDyadicPrimeBlock (y / 2 ^ j), ((p : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      let n := y / 2 ^ j
      have hstep : y / 2 ^ (j + 1) = n / 2 := by
        dsimp only [n]
        rw [Nat.div_div_eq_div_mul, pow_succ]
      have hnHalfB : B ≤ n / 2 := by
        rw [← hstep]
        exact hbottom j hj
      have hnB : B ≤ n := hnHalfB.trans (Nat.div_le_self n 2)
      have hnFour : 4 ≤ n := hB.trans hnB
      have hpntN := hpnt n hnB
      have hpntHalf := hpnt (n / 2) hnHalfB
      have hblock := one_div_eight_log_le_sum_inv_cepDyadicPrimeBlock
        hnFour hpntN.1 hpntHalf.2
      have hnY : n ≤ y := Nat.div_le_self y (2 ^ j)
      have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hyPos : (0 : ℝ) < y := by positivity
      have hlogNY : Real.log (n : ℝ) ≤ Real.log (y : ℝ) :=
        Real.strictMonoOn_log.monotoneOn hnPos hyPos (by exact_mod_cast hnY)
      have hlogNPos : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hlogYPos : 0 < Real.log (y : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < y by omega))
      exact (one_div_le_one_div_of_le
        (mul_pos (by norm_num) hlogNPos)
        (mul_le_mul_of_nonneg_left hlogNY (by norm_num))).trans hblock

/-- Number of dyadic blocks spanning the logarithmic width `1/log u`. -/
def cepDyadicBlockCount (y : ℕ) (u : ℝ) : ℕ :=
  ⌊Real.log (y : ℝ) / (Real.log 2 * Real.log u)⌋₊

/-- A single power budget places every retained dyadic bottom above `B`. -/
theorem cepDyadicBlockBottom_of_pow_mul_le
    {B y J : ℕ} (hbudget : 2 ^ J * B ≤ y)
    {j : ℕ} (hj : j < J) :
    B ≤ y / 2 ^ (j + 1) := by
  apply (Nat.le_div_iff_mul_le (pow_pos (by norm_num) (j + 1))).2
  calc
    B * 2 ^ (j + 1) ≤ B * 2 ^ J := by
      exact Nat.mul_le_mul_left B
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = 2 ^ J * B := by ac_rfl
    _ ≤ y := hbudget

/-- Flooring the logarithmic block count does not make the union descend
past `y^(1/log u)`. -/
theorem cast_two_pow_cepDyadicBlockCount_le_rpow
    {y : ℕ} {u : ℝ} (hy : 1 ≤ y) (hu : 1 < u) :
    ((2 ^ cepDyadicBlockCount y u : ℕ) : ℝ) ≤
      (y : ℝ) ^ (1 / Real.log u : ℝ) := by
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogUPos : 0 < Real.log u := Real.log_pos hu
  have hyPos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hfloor : (cepDyadicBlockCount y u : ℝ) ≤
      Real.log (y : ℝ) / (Real.log 2 * Real.log u) := by
    exact_mod_cast Nat.floor_le (by positivity :
      0 ≤ Real.log (y : ℝ) / (Real.log 2 * Real.log u))
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  calc
    (2 : ℝ) ^ (cepDyadicBlockCount y u : ℝ) ≤
        (2 : ℝ) ^
          (Real.log (y : ℝ) / (Real.log 2 * Real.log u)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
    _ = (y : ℝ) ^ (1 / Real.log u : ℝ) := by
      rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hyPos]
      congr 1
      field_simp [hlogTwoPos.ne', hlogUPos.ne']

/-- In the critical range, the dyadic descent together with a fixed endpoint
`B ≤ u` consumes at most the available smoothness scale `y`. -/
theorem two_pow_cepDyadicBlockCount_mul_le
    {B y : ℕ} {u : ℝ} (hy : 1 ≤ y)
    (hlogU : 2 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huY : u ≤ Real.sqrt y) :
    2 ^ cepDyadicBlockCount y u * B ≤ y := by
  have hu : 1 < u := by
    have : 0 < Real.log u := by linarith
    exact (Real.log_pos_iff ((Nat.cast_nonneg B).trans hBu)).mp this
  have hpow := cast_two_pow_cepDyadicBlockCount_le_rpow hy hu
  have hyOne : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hexponent : 1 / Real.log u ≤ (1 / 2 : ℝ) := by
    rw [div_le_div_iff₀ (by linarith : 0 < Real.log u) (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hrpowRoot : (y : ℝ) ^ (1 / Real.log u : ℝ) ≤ Real.sqrt y := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hyOne hexponent
  have hreal : (((2 ^ cepDyadicBlockCount y u * B : ℕ) : ℝ)) ≤ (y : ℝ) := by
    rw [Nat.cast_mul]
    calc
      ((2 ^ cepDyadicBlockCount y u : ℕ) : ℝ) * (B : ℝ) ≤
          Real.sqrt y * Real.sqrt y :=
        mul_le_mul (hpow.trans hrpowRoot) (hBu.trans huY)
          (by positivity) (Real.sqrt_nonneg _)
      _ = (y : ℝ) := Real.mul_self_sqrt (by positivity)
  exact_mod_cast hreal

/-- The concrete critical hypotheses place every dyadic bottom above the
fixed PNT threshold. -/
theorem cepDyadicBlockBottom_of_criticalRange
    {B y : ℕ} {u : ℝ} (hy : 1 ≤ y)
    (hlogU : 2 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huY : u ≤ Real.sqrt y) :
    ∀ j ∈ Finset.range (cepDyadicBlockCount y u),
      B ≤ y / 2 ^ (j + 1) := by
  intro j hj
  exact cepDyadicBlockBottom_of_pow_mul_le
    (two_pow_cepDyadicBlockCount_mul_le hy hlogU hBu huY)
    (Finset.mem_range.mp hj)

/-- The critical constraint `u ≤ sqrt y` leaves room for at least two of the
chosen dyadic blocks. -/
theorem two_le_log_ratio_of_le_sqrt
    {y : ℕ} {u : ℝ} (hy : 1 ≤ y) (hu : 1 < u)
    (huY : u ≤ Real.sqrt y) :
    2 ≤ Real.log (y : ℝ) / (Real.log 2 * Real.log u) := by
  have huPos : 0 < u := zero_lt_one.trans hu
  have hyNonneg : (0 : ℝ) ≤ y := by positivity
  have hyPos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hsqrtPos : 0 < Real.sqrt y := Real.sqrt_pos.2 hyPos
  have hlogs : Real.log u ≤ Real.log (Real.sqrt y) :=
    Real.strictMonoOn_log.monotoneOn huPos hsqrtPos huY
  rw [Real.log_sqrt hyNonneg] at hlogs
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoUpper : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlogUPos : 0 < Real.log u := Real.log_pos hu
  apply (le_div_iff₀ (mul_pos hlogTwoPos hlogUPos)).2
  calc
    2 * (Real.log 2 * Real.log u) ≤ 2 * Real.log u := by
      nlinarith
    _ ≤ Real.log (y : ℝ) := by linarith

theorem half_log_ratio_le_cepDyadicBlockCount
    {y : ℕ} {u : ℝ}
    (hratio : 2 ≤ Real.log (y : ℝ) / (Real.log 2 * Real.log u)) :
    Real.log (y : ℝ) / (2 * Real.log 2 * Real.log u) ≤
      (cepDyadicBlockCount y u : ℝ) := by
  let R := Real.log (y : ℝ) / (Real.log 2 * Real.log u)
  have hfloor := Nat.lt_floor_add_one R
  have hcast : R - 1 < (cepDyadicBlockCount y u : ℝ) := by
    push_cast at hfloor
    simpa only [cepDyadicBlockCount, R] using (sub_lt_iff_lt_add).2 hfloor
  have hhalf : R / 2 ≤ R - 1 := by linarith
  have hrewrite :
      Real.log (y : ℝ) / (2 * Real.log 2 * Real.log u) = R / 2 := by
    dsimp only [R]
    ring
  rw [hrewrite]
  exact hhalf.trans hcast.le

/-- The dyadic alphabet has reciprocal mass `≫ 1/log u` whenever its last
bottom endpoint remains above the fixed PNT threshold. -/
theorem one_div_log_le_sum_inv_cepDyadicPrimeAlphabet
    {B y : ℕ} {u : ℝ} (hB : 4 ≤ B) (hy : 2 ≤ y) (hu : 1 < u)
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta n ∧
        Chebyshev.theta n ≤ (5 / 4 : ℝ) * n)
    (hratio : 2 ≤ Real.log (y : ℝ) / (Real.log 2 * Real.log u))
    (hbottom : ∀ j ∈ Finset.range (cepDyadicBlockCount y u),
      B ≤ y / 2 ^ (j + 1)) :
    1 / (16 * Real.log 2 * Real.log u) ≤
      ∑ p ∈ cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u),
        (((p : ℕ) : ℝ)⁻¹) := by
  have hmass := card_div_eight_log_le_sum_inv_cepDyadicPrimeAlphabet
    hB hpnt hbottom
  have hcount := half_log_ratio_le_cepDyadicBlockCount hratio
  have hlogYPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogUPos : 0 < Real.log u := Real.log_pos hu
  apply le_trans ?_ hmass
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * Real.log 2 * Real.log u)
    (mul_pos (by norm_num) hlogYPos)]
  field_simp [hlogTwoPos.ne', hlogUPos.ne', hlogYPos.ne'] at hcount ⊢
  nlinarith

/-- Reciprocal mass for the dyadic alphabet under the concrete critical
range hypotheses, with no shrinking-interval PNT input. -/
theorem one_div_log_le_sum_inv_cepDyadicPrimeAlphabet_of_criticalRange
    {B y : ℕ} {u : ℝ} (hB : 4 ≤ B) (hy : 2 ≤ y)
    (hlogU : 2 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huY : u ≤ Real.sqrt y)
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta n ∧
        Chebyshev.theta n ≤ (5 / 4 : ℝ) * n) :
    1 / (16 * Real.log 2 * Real.log u) ≤
      ∑ p ∈ cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u),
        (((p : ℕ) : ℝ)⁻¹) := by
  have hu : 1 < u := by
    have hlogPos : 0 < Real.log u := by linarith
    exact (Real.log_pos_iff ((Nat.cast_nonneg B).trans hBu)).mp hlogPos
  apply one_div_log_le_sum_inv_cepDyadicPrimeAlphabet hB hy hu hpnt
  · exact two_le_log_ratio_of_le_sqrt (by omega) hu huY
  · exact cepDyadicBlockBottom_of_criticalRange (by omega) hlogU hBu huY

/-- Bottom endpoint below all retained dyadic prime blocks. -/
def cepDyadicCofactorCutoff (y : ℕ) (u : ℝ) : ℕ :=
  y / 2 ^ cepDyadicBlockCount y u

/-- We retain almost `u` prime factors, leaving a cofactor budget of order
`u / log u`. -/
def cepDyadicMultiplicity (u : ℝ) : ℕ :=
  ⌊u - 2 * u / Real.log u⌋₊

theorem cast_cepDyadicMultiplicity_le
    {u : ℝ} (hu : 1 < u) (hlogU : 2 ≤ Real.log u) :
    (cepDyadicMultiplicity u : ℝ) ≤ u - 2 * u / Real.log u := by
  apply Nat.floor_le
  have hu0 : 0 ≤ u := (zero_lt_one.trans hu).le
  have hlogPos : 0 < Real.log u := Real.log_pos hu
  rw [sub_nonneg, div_le_iff₀ hlogPos]
  nlinarith

theorem cast_cepDyadicMultiplicity_le_self
    {u : ℝ} (hu : 1 < u) (hlogU : 2 ≤ Real.log u) :
    (cepDyadicMultiplicity u : ℝ) ≤ u := by
  exact (cast_cepDyadicMultiplicity_le hu hlogU).trans (by
    have : 0 ≤ 2 * u / Real.log u := by positivity
    linarith)

theorem sub_one_lt_cast_cepDyadicMultiplicity (u : ℝ) :
    u - 2 * u / Real.log u - 1 < (cepDyadicMultiplicity u : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (u - 2 * u / Real.log u)
  push_cast at hfloor
  simpa only [cepDyadicMultiplicity] using
    (sub_lt_iff_lt_add).2 hfloor

theorem cepDyadicCofactorCutoff_le (y : ℕ) (u : ℝ) :
    cepDyadicCofactorCutoff y u ≤ y := by
  exact Nat.div_le_self _ _

theorem nat_le_cepDyadicCofactorCutoff_of_criticalRange
    {B y : ℕ} {u : ℝ} (hy : 1 ≤ y)
    (hlogU : 2 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huY : u ≤ Real.sqrt y) :
    B ≤ cepDyadicCofactorCutoff y u := by
  rw [cepDyadicCofactorCutoff]
  apply (Nat.le_div_iff_mul_le
    (pow_pos (by norm_num) (cepDyadicBlockCount y u))).2
  have hbudget := two_pow_cepDyadicBlockCount_mul_le hy hlogU hBu huY
  simpa only [mul_comm] using hbudget

/-- Up to the unavoidable factor two from natural division, the common
cofactor cutoff retains the full logarithmic exponent `1 - 1/log u`. -/
theorem rpow_one_sub_one_div_log_le_two_mul_cepDyadicCofactorCutoff
    {B y : ℕ} {u : ℝ} (hB : 1 ≤ B) (hy : 2 ≤ y)
    (hlogU : 2 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huY : u ≤ Real.sqrt y) :
    (y : ℝ) ^ (1 - 1 / Real.log u : ℝ) ≤
      2 * (cepDyadicCofactorCutoff y u : ℕ) := by
  let d := 2 ^ cepDyadicBlockCount y u
  have hu : 1 < u := by
    have hlogPos : 0 < Real.log u := by linarith
    exact (Real.log_pos_iff ((Nat.cast_nonneg B).trans hBu)).mp hlogPos
  have hdPos : 0 < d := by dsimp only [d]; positivity
  have hbudget := two_pow_cepDyadicBlockCount_mul_le
    (show 1 ≤ y by omega) hlogU hBu huY
  have hdY : d ≤ y := by
    calc
      d = d * 1 := by simp
      _ ≤ d * B := Nat.mul_le_mul_left d hB
      _ ≤ y := hbudget
  have hpow : (d : ℝ) ≤ (y : ℝ) ^ (1 / Real.log u : ℝ) := by
    simpa only [d] using cast_two_pow_cepDyadicBlockCount_le_rpow
      (show 1 ≤ y by omega) hu
  have hdiv := cast_div_le_two_mul_natDiv hdPos hdY
  have hyNonneg : (0 : ℝ) ≤ y := by positivity
  have hyPos : (0 : ℝ) < y := by positivity
  have hdRealPos : (0 : ℝ) < d := by exact_mod_cast hdPos
  have hrpowPos : 0 < (y : ℝ) ^ (1 / Real.log u : ℝ) := by positivity
  calc
    (y : ℝ) ^ (1 - 1 / Real.log u : ℝ) =
        (y : ℝ) / (y : ℝ) ^ (1 / Real.log u : ℝ) := by
      rw [Real.rpow_sub hyPos, Real.rpow_one]
    _ ≤ (y : ℝ) / (d : ℝ) :=
      div_le_div_of_nonneg_left hyNonneg hdRealPos hpow
    _ ≤ 2 * (y / d : ℕ) := hdiv
    _ = 2 * (cepDyadicCofactorCutoff y u : ℕ) := by
      simp only [cepDyadicCofactorCutoff, d]

/-- Sharp logarithmic lower bound for the common cofactor cutoff.  The second
`1/log u` absorbs the factor-two loss from natural division. -/
theorem one_sub_two_div_log_mul_log_le_log_cepDyadicCofactorCutoff
    {B y : ℕ} {u : ℝ} (hB : 4 ≤ B) (hy : 2 ≤ y)
    (hlogU : 2 ≤ Real.log u) (hBu : (B : ℝ) ≤ u)
    (huY : u ≤ Real.sqrt y) :
    (1 - 2 / Real.log u) * Real.log (y : ℝ) ≤
      Real.log (cepDyadicCofactorCutoff y u : ℕ) := by
  let w := cepDyadicCofactorCutoff y u
  have hu : 1 < u := by
    have hlogPos : 0 < Real.log u := by linarith
    exact (Real.log_pos_iff ((Nat.cast_nonneg B).trans hBu)).mp hlogPos
  have hwy := nat_le_cepDyadicCofactorCutoff_of_criticalRange
    (show 1 ≤ y by omega) hlogU hBu huY
  have hwPos : (0 : ℝ) < w := by
    exact_mod_cast (show 0 < w by simpa only [w] using (lt_of_lt_of_le (by omega : 0 < B) hwy))
  have hyPos : (0 : ℝ) < y := by positivity
  have hlower :=
    rpow_one_sub_one_div_log_le_two_mul_cepDyadicCofactorCutoff
      (show 1 ≤ B by omega) hy hlogU hBu huY
  have hrpowPos : 0 < (y : ℝ) ^ (1 - 1 / Real.log u : ℝ) := by positivity
  have htwoWPos : 0 < (2 : ℝ) * (w : ℝ) := mul_pos (by norm_num) hwPos
  have hlower' : (y : ℝ) ^ (1 - 1 / Real.log u : ℝ) ≤
      (2 : ℝ) * (w : ℝ) := by simpa only [w] using hlower
  have hlogs := Real.strictMonoOn_log.monotoneOn hrpowPos
    htwoWPos hlower'
  rw [Real.log_rpow hyPos,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hwPos.ne'] at hlogs
  have huPos : 0 < u := zero_lt_one.trans hu
  have hsqrtPos : 0 < Real.sqrt y := Real.sqrt_pos.2 hyPos
  have hlogSqrt : Real.log u ≤ Real.log (Real.sqrt y) :=
    Real.strictMonoOn_log.monotoneOn huPos hsqrtPos huY
  rw [Real.log_sqrt (by positivity : (0 : ℝ) ≤ y)] at hlogSqrt
  have hlogUPos : 0 < Real.log u := Real.log_pos hu
  have hratioTwo : 2 ≤ Real.log (y : ℝ) / Real.log u := by
    apply (le_div_iff₀ hlogUPos).2
    linarith
  have hlogTwoUpper : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlogTwoBudget : Real.log 2 ≤ Real.log (y : ℝ) / Real.log u :=
    hlogTwoUpper.trans (by linarith)
  dsimp only [w] at hlogs ⊢
  have hrearrange :
      (1 - 2 / Real.log u) * Real.log (y : ℝ) =
        (1 - 1 / Real.log u) * Real.log (y : ℝ) -
          Real.log (y : ℝ) / Real.log u := by ring
  rw [hrearrange]
  linarith

/-- Every prime in the coarse alphabet lies strictly above its common
cofactor cutoff. -/
theorem cepDyadicCofactorCutoff_lt_of_mem
    {y : ℕ} {u : ℝ} {p : TaoBoundedPrime y}
    (hp : p ∈ cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u)) :
    cepDyadicCofactorCutoff y u < (p : ℕ) := by
  have hpUnion := mem_cepDyadicPrimeAlphabet_iff.mp hp
  rw [cepDyadicPrimeBlockUnion, Finset.mem_biUnion] at hpUnion
  obtain ⟨j, hj, hpj⟩ := hpUnion
  have hjlt : j < cepDyadicBlockCount y u := Finset.mem_range.mp hj
  have hpow : 2 ^ (j + 1) ≤ 2 ^ cepDyadicBlockCount y u :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdiv : y / 2 ^ cepDyadicBlockCount y u ≤ y / 2 ^ (j + 1) :=
    Nat.div_le_div_left hpow (pow_pos (by norm_num) _)
  have hstep : y / 2 ^ (j + 1) = (y / 2 ^ j) / 2 := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  have hpLower := (mem_cepDyadicPrimeBlock_iff.mp hpj).2.1
  rw [← hstep] at hpLower
  rw [cepDyadicCofactorCutoff]
  exact hdiv.trans_lt hpLower

/-- Every multiplier in the coarse packet is positive. -/
theorem cepDyadicPacketProduct_pos
    {y r : ℕ} {u : ℝ} {m : ℕ}
    (hm : m ∈ cepPrimePacketProducts
      (cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u)) r) :
    0 < m := by
  exact Nat.pos_of_ne_zero
    (isSmooth_iff.mp (mem_cepPrimePacketProducts_isSmooth hm)).1

/-- The common cutoff supplies a sharp lower size for every coarse packet
multiplier. -/
theorem pow_cepDyadicCofactorCutoff_le_packetProduct
    {y r : ℕ} {u : ℝ} {m : ℕ}
    (hm : m ∈ cepPrimePacketProducts
      (cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u)) r) :
    (cepDyadicCofactorCutoff y u : ℝ) ^ r ≤ (m : ℝ) := by
  apply pow_le_cast_cepPrimePacketProduct (by positivity)
  · intro p hp
    exact_mod_cast (cepDyadicCofactorCutoff_lt_of_mem hp).le
  · exact hm

/-- With the near-`u` multiplicity, every coarse packet multiplier stays
below the ambient Rankin saddle `X`. -/
theorem cepDyadicPacketProduct_le_X
    {X y m : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y)
    (hlogU : 2 ≤ Real.log (smoothRankinRatio X y))
    (hm : m ∈ cepPrimePacketProducts
      (cepDyadicPrimeAlphabet y
        (cepDyadicBlockCount y (smoothRankinRatio X y)))
      (cepDyadicMultiplicity (smoothRankinRatio X y))) :
    m ≤ X := by
  let u := smoothRankinRatio X y
  let r := cepDyadicMultiplicity u
  let P := cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u)
  have hmUpper : (m : ℝ) ≤ (y : ℝ) ^ r := by
    apply cast_cepPrimePacketProduct_le_pow
    · intro p hp
      exact_mod_cast (Nat.le_of_mem_primesLE p.2)
    · simpa only [P, r, u] using hm
  have hrU : (r : ℝ) ≤ u := by
    simpa only [r, u] using cast_cepDyadicMultiplicity_le_self hu hlogU
  have hyOne : (1 : ℝ) ≤ y := by exact_mod_cast (show 1 ≤ y by omega)
  have hpow : (y : ℝ) ^ r ≤ (y : ℝ) ^ u := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hyOne hrU
  have hreal : (m : ℝ) ≤ (X : ℝ) := by
    calc
      (m : ℝ) ≤ (y : ℝ) ^ r := hmUpper
      _ ≤ (y : ℝ) ^ u := hpow
      _ = (X : ℝ) := by simpa only [u] using rpow_smoothRankinRatio hX hy
  exact_mod_cast hreal

/-- Uniform real depth budget for all cofactors left by the coarse packet. -/
def cepDyadicCofactorDepthBudget (u : ℝ) : ℝ :=
  10 * u / Real.log u

/-- Common endpoint-Hildebrand denominator for every coarse packet
cofactor. -/
def cepDyadicCofactorDenominatorBudget (B X : ℕ) (u : ℝ) : ℝ :=
  (B : ℝ) * 2 ^ ⌈cepDyadicCofactorDepthBudget u⌉₊ *
    Real.log X ^ (⌈cepDyadicCofactorDepthBudget u⌉₊ + 1)

theorem smoothLowerDepth_cepDyadicCofactor_le_budget
    {B X y m : ℕ} (hB : 4 ≤ B) (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y)
    (hlogU : 4 ≤ Real.log (smoothRankinRatio X y))
    (hBu : (B : ℝ) ≤ smoothRankinRatio X y)
    (huY : smoothRankinRatio X y ≤ Real.sqrt y)
    (hm : m ∈ cepPrimePacketProducts
      (cepDyadicPrimeAlphabet y
        (cepDyadicBlockCount y (smoothRankinRatio X y)))
      (cepDyadicMultiplicity (smoothRankinRatio X y))) :
    (smoothLowerDepth (X / m)
        (cepDyadicCofactorCutoff y (smoothRankinRatio X y)) : ℝ) ≤
      cepDyadicCofactorDepthBudget (smoothRankinRatio X y) := by
  let u := smoothRankinRatio X y
  let r := cepDyadicMultiplicity u
  let w := cepDyadicCofactorCutoff y u
  let q := X / m
  have hmPos : 0 < m := cepDyadicPacketProduct_pos
    (by simpa only [u, r] using hm)
  have hmX : m ≤ X := cepDyadicPacketProduct_le_X hX hy hu (by linarith)
    (by simpa only [u, r] using hm)
  have hqOne : 1 ≤ q := by
    dsimp only [q]
    exact (Nat.le_div_iff_mul_le hmPos).2 (by simpa using hmX)
  have hBw : B ≤ w := by
    simpa only [w, u] using nat_le_cepDyadicCofactorCutoff_of_criticalRange
      (show 1 ≤ y by omega) (by linarith) hBu huY
  have hwTwo : 2 ≤ w := (by omega : 2 ≤ B).trans hBw
  have hlogwPos : 0 < Real.log (w : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  have hlogyPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hloguPos : 0 < Real.log u := by simpa only [u] using (show
    0 < Real.log (smoothRankinRatio X y) by linarith)
  have hlogwSharp :
      (1 - 2 / Real.log u) * Real.log (y : ℝ) ≤ Real.log (w : ℝ) := by
    simpa only [w, u] using
      one_sub_two_div_log_mul_log_le_log_cepDyadicCofactorCutoff
        hB hy (by simpa only [u] using (show
          2 ≤ Real.log (smoothRankinRatio X y) by linarith)) hBu huY
  have hcoeffHalf : (1 / 2 : ℝ) ≤ 1 - 2 / Real.log u := by
    have hLu : 4 ≤ Real.log u := by simpa only [u] using hlogU
    have htwoDiv : 2 / Real.log u ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ hloguPos]
      nlinarith
    nlinarith
  have hhalfLogw : (1 / 2 : ℝ) * Real.log (y : ℝ) ≤ Real.log (w : ℝ) :=
    (mul_le_mul_of_nonneg_right hcoeffHalf hlogyPos.le).trans hlogwSharp
  have hmLower : (w : ℝ) ^ r ≤ (m : ℝ) := by
    simpa only [w, r, u] using pow_cepDyadicCofactorCutoff_le_packetProduct hm
  have hmRealPos : (0 : ℝ) < m := by exact_mod_cast hmPos
  have hlogm : (r : ℝ) * Real.log (w : ℝ) ≤ Real.log (m : ℝ) := by
    have h := Real.log_le_log (pow_pos (by exact_mod_cast (show 0 < w by omega)) r) hmLower
    rw [Real.log_pow] at h
    exact h
  have hqPos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hquotPos : (0 : ℝ) < (X : ℝ) / (m : ℝ) := by positivity
  have hqCast : (q : ℝ) ≤ (X : ℝ) / (m : ℝ) := by
    apply (le_div_iff₀ hmRealPos).2
    exact_mod_cast Nat.div_mul_le_self X m
  have hlogq : Real.log (q : ℝ) ≤
      Real.log (X : ℝ) - Real.log (m : ℝ) := by
    calc
      Real.log (q : ℝ) ≤ Real.log ((X : ℝ) / (m : ℝ)) :=
        Real.strictMonoOn_log.monotoneOn hqPos hquotPos hqCast
      _ = Real.log (X : ℝ) - Real.log (m : ℝ) :=
        Real.log_div (by positivity) (by positivity)
  have hlogX : Real.log (X : ℝ) = u * Real.log (y : ℝ) := by
    simpa only [u] using (smoothRankinRatio_mul_log hy).symm
  have hrLower := sub_one_lt_cast_cepDyadicMultiplicity u
  have hrLower' : u - 2 * u / Real.log u - 1 < (r : ℝ) := by
    simpa only [r] using hrLower
  have hrUpper : (r : ℝ) ≤ u := by
    simpa only [r] using cast_cepDyadicMultiplicity_le_self hu
      (by simpa only [u] using (show 2 ≤ Real.log (smoothRankinRatio X y) by linarith))
  have hlogLeU : Real.log u ≤ u := by
    have h := Real.log_le_sub_one_of_pos (zero_lt_one.trans hu)
    linarith
  have honeLe : 1 ≤ u / Real.log u := by
    apply (le_div_iff₀ hloguPos).2
    simpa using hlogLeU
  have htwoR : 2 * (r : ℝ) / Real.log u ≤ 2 * u / Real.log u := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrUpper (by norm_num)) hloguPos.le
  have hcoefficient :
      u - (r : ℝ) + 2 * (r : ℝ) / Real.log u ≤
        5 * u / Real.log u := by
    have hgap : u - (r : ℝ) ≤ 3 * u / Real.log u := by
      calc
        u - (r : ℝ) ≤ 2 * u / Real.log u + 1 := by linarith
        _ ≤ 2 * u / Real.log u + u / Real.log u :=
          add_le_add_right honeLe _
        _ = 3 * u / Real.log u := by ring
    calc
      u - (r : ℝ) + 2 * (r : ℝ) / Real.log u ≤
          3 * u / Real.log u + 2 * u / Real.log u :=
        add_le_add hgap htwoR
      _ = 5 * u / Real.log u := by ring
  have hlogqLoss : Real.log (q : ℝ) ≤
      (5 * u / Real.log u) * Real.log (y : ℝ) := by
    calc
      Real.log (q : ℝ) ≤ Real.log (X : ℝ) - Real.log (m : ℝ) := hlogq
      _ ≤ u * Real.log (y : ℝ) -
          (r : ℝ) * Real.log (w : ℝ) := by rw [hlogX]; linarith
      _ ≤ u * Real.log (y : ℝ) -
          (r : ℝ) * ((1 - 2 / Real.log u) * Real.log (y : ℝ)) := by
        gcongr
      _ = (u - (r : ℝ) + 2 * (r : ℝ) / Real.log u) *
          Real.log (y : ℝ) := by ring
      _ ≤ (5 * u / Real.log u) * Real.log (y : ℝ) :=
        mul_le_mul_of_nonneg_right hcoefficient hlogyPos.le
  have hcoef0 : 0 ≤ 5 * u / Real.log u := by positivity
  have hlogyTwo : Real.log (y : ℝ) ≤ 2 * Real.log (w : ℝ) := by linarith
  have hratio : smoothRankinRatio q w ≤ 10 * u / Real.log u := by
    rw [smoothRankinRatio, div_le_iff₀ hlogwPos]
    calc
      Real.log (q : ℝ) ≤ (5 * u / Real.log u) * Real.log (y : ℝ) := hlogqLoss
      _ ≤ (5 * u / Real.log u) * (2 * Real.log (w : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogyTwo hcoef0
      _ = (10 * u / Real.log u) * Real.log (w : ℝ) := by ring
  exact (smoothLowerDepth_cast_le_rankinRatio (by omega) hwTwo).trans
    (by simpa only [cepDyadicCofactorDepthBudget, q, w, u] using hratio)

theorem cepCofactorHildebrandDenominator_le_dyadicBudget
    {B X y m : ℕ} (hB : 4 ≤ B) (hX : 3 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y)
    (hlogU : 4 ≤ Real.log (smoothRankinRatio X y))
    (hBu : (B : ℝ) ≤ smoothRankinRatio X y)
    (huY : smoothRankinRatio X y ≤ Real.sqrt y)
    (hm : m ∈ cepPrimePacketProducts
      (cepDyadicPrimeAlphabet y
        (cepDyadicBlockCount y (smoothRankinRatio X y)))
      (cepDyadicMultiplicity (smoothRankinRatio X y))) :
    cepCofactorHildebrandDenominator B (X / m)
        (cepDyadicCofactorCutoff y (smoothRankinRatio X y)) ≤
      cepDyadicCofactorDenominatorBudget B X (smoothRankinRatio X y) := by
  let u := smoothRankinRatio X y
  let w := cepDyadicCofactorCutoff y u
  let q := X / m
  let d := smoothLowerDepth q w
  let K := ⌈cepDyadicCofactorDepthBudget u⌉₊
  have hmPos : 0 < m := cepDyadicPacketProduct_pos
    (by simpa only [u] using hm)
  have hmX : m ≤ X := cepDyadicPacketProduct_le_X (by omega) hy hu (by linarith)
    (by simpa only [u] using hm)
  have hqOne : 1 ≤ q := by
    dsimp only [q]
    exact (Nat.le_div_iff_mul_le hmPos).2 (by simpa using hmX)
  have hdepth : (d : ℝ) ≤ cepDyadicCofactorDepthBudget u := by
    simpa only [d, q, w, u] using
      smoothLowerDepth_cepDyadicCofactor_le_budget
        hB (by omega) hy hu hlogU hBu huY hm
  have hdepthCeil : (d : ℝ) ≤ (K : ℝ) :=
    hdepth.trans (by simpa only [K] using
      (Nat.le_ceil (cepDyadicCofactorDepthBudget u)))
  have hdK : d ≤ K := by exact_mod_cast hdepthCeil
  have hqX : q ≤ X := by
    dsimp only [q]
    exact Nat.div_le_self X m
  have hlogq0 : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hqOne)
  have hlogqX : Real.log (q : ℝ) ≤ Real.log (X : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · show (0 : ℝ) < q
      exact_mod_cast (show 0 < q by omega)
    · show (0 : ℝ) < X
      positivity
    · exact_mod_cast hqX
  have hlogXOne : 1 ≤ Real.log (X : ℝ) := by
    have hthree : (1 : ℝ) ≤ Real.log 3 := by
      linarith [Real.log_three_gt_d9]
    exact hthree.trans (Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 3) (by positivity : (0 : ℝ) < X)
      (by exact_mod_cast hX))
  have htwoPow : (2 : ℝ) ^ d ≤ (2 : ℝ) ^ K :=
    pow_le_pow_right₀ (by norm_num) hdK
  have hlogPow : Real.log (q : ℝ) ^ (d + 1) ≤
      Real.log (X : ℝ) ^ (K + 1) :=
    (pow_le_pow_left₀ hlogq0 hlogqX (d + 1)).trans
      (pow_le_pow_right₀ hlogXOne (Nat.add_le_add_right hdK 1))
  unfold cepCofactorHildebrandDenominator
  unfold cepDyadicCofactorDenominatorBudget
  have hfinal : (B : ℝ) * (2 : ℝ) ^ d * Real.log (q : ℝ) ^ (d + 1) ≤
      (B : ℝ) * (2 : ℝ) ^ K * Real.log (X : ℝ) ^ (K + 1) := by
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left
        (mul_le_mul htwoPow hlogPow (pow_nonneg hlogq0 _) (by positivity))
        (Nat.cast_nonneg B))
  simpa only [u, w, q, d, K] using hfinal

/-- One-band recurrence bridge for the coarse dyadic packet. -/
theorem density_mul_X_mul_cepDyadicPacketMass_le_psiNat
    {X y r : ℕ} {u D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ m ∈ cepPrimePacketProducts
        (cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u)) r,
      D * (X : ℝ) / (m : ℝ) ≤
        (psiNat (X / m) (cepDyadicCofactorCutoff y u) : ℝ)) :
    D * (X : ℝ) *
        ((∑ p ∈ cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u),
          (((p : ℕ) : ℝ)⁻¹)) ^ r / (Nat.factorial r : ℝ)) ≤
      (psiNat X y : ℝ) := by
  let P := cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u)
  let w := cepDyadicCofactorCutoff y u
  have hpacket := reciprocalPrimeSum_pow_div_factorial_le_productReciprocalSum P r
  calc
    D * (X : ℝ) *
        ((∑ p ∈ P, (((p : ℕ) : ℝ)⁻¹)) ^ r /
          (Nat.factorial r : ℝ)) ≤
        D * (X : ℝ) *
          ∑ m ∈ cepPrimePacketProducts P r, ((m : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left hpacket
        (mul_nonneg hD0 (Nat.cast_nonneg X))
    _ ≤ (psiNat X y : ℝ) := by
      apply density_mul_X_mul_sum_inv_le_psiNat
        (cepDyadicCofactorCutoff_le y u)
      · intro m hm
        exact (isSmooth_iff.mp (mem_cepPrimePacketProducts_isSmooth hm)).1
      · intro m hm
        exact mem_cepPrimePacketProducts_isSmooth hm
      · intro m hm q hq hqm
        obtain ⟨p, hp, rfl⟩ :=
          exists_mem_of_prime_dvd_cepPrimePacketProduct hm hq hqm
        exact cepDyadicCofactorCutoff_lt_of_mem hp
      · simpa only [P, w] using hD

/-- End-to-end finite coarse CEP/Hildebrand packet.  It uses only fixed-scale
PNT envelopes and one displayed pointwise cofactor-denominator bound. -/
theorem cepDyadicPacketMass_le_psiNat_of_hildebrandDenominatorBound
    {B X y : ℕ} {D : ℝ}
    (hB : 4 ≤ B)
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta n ∧
        Chebyshev.theta n ≤ (5 / 4 : ℝ) * n)
    (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y)
    (hlogU : 2 ≤ Real.log (smoothRankinRatio X y))
    (hBu : (B : ℝ) ≤ smoothRankinRatio X y)
    (huY : smoothRankinRatio X y ≤ Real.sqrt y)
    (hD : 0 < D) (hDsmall : 4 * D ≤ 1)
    (hden : ∀ m ∈ cepPrimePacketProducts
        (cepDyadicPrimeAlphabet y
          (cepDyadicBlockCount y (smoothRankinRatio X y)))
        (cepDyadicMultiplicity (smoothRankinRatio X y)),
      cepCofactorHildebrandDenominator B (X / m)
          (cepDyadicCofactorCutoff y (smoothRankinRatio X y)) ≤
        1 / (2 * D)) :
    D * (X : ℝ) *
        ((1 / (16 * Real.log 2 *
          Real.log (smoothRankinRatio X y))) ^
            cepDyadicMultiplicity (smoothRankinRatio X y) /
          (Nat.factorial
            (cepDyadicMultiplicity (smoothRankinRatio X y)) : ℝ)) ≤
      (psiNat X y : ℝ) := by
  let u := smoothRankinRatio X y
  let P := cepDyadicPrimeAlphabet y (cepDyadicBlockCount y u)
  let r := cepDyadicMultiplicity u
  let w := cepDyadicCofactorCutoff y u
  have hmass : 1 / (16 * Real.log 2 * Real.log u) ≤
      ∑ p ∈ P, (((p : ℕ) : ℝ)⁻¹) := by
    simpa only [u, P] using
      one_div_log_le_sum_inv_cepDyadicPrimeAlphabet_of_criticalRange
        hB hy hlogU hBu huY hpnt
  have hmass0 : 0 ≤ 1 / (16 * Real.log 2 * Real.log u) := by
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogUPos : 0 < Real.log u := Real.log_pos hu
    positivity
  have hpacket := density_mul_X_mul_cepDyadicPacketMass_le_psiNat
    (X := X) (y := y) (r := r) (u := u) hD.le (by
      intro m hm
      apply cofactorDensity_of_hildebrandDenominatorBound hB
        (fun n hn => (hpnt n hn).1.trans' (by
          have hn0 : (0 : ℝ) ≤ n := by positivity
          nlinarith))
      · exact cepDyadicPacketProduct_pos (by simpa only [P, r, u] using hm)
      · exact cepDyadicPacketProduct_le_X hX hy hu hlogU
          (by simpa only [P, r, u] using hm)
      · simpa only [w, u] using
          nat_le_cepDyadicCofactorCutoff_of_criticalRange
            (show 1 ≤ y by omega) hlogU hBu huY
      · exact hD
      · exact hDsmall
      · simpa only [P, r, w, u] using hden m (by simpa only [P, r, u] using hm))
  apply le_trans ?_ hpacket
  apply mul_le_mul_of_nonneg_left
  · exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hmass0 hmass r) (by positivity)
  · exact mul_nonneg hD.le (Nat.cast_nonneg X)

/-- Common-budget version of the finite coarse packet theorem. -/
theorem cepDyadicPacketMass_le_psiNat_of_denominatorBudget
    {B X y : ℕ} {D : ℝ}
    (hB : 4 ≤ B)
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta n ∧
        Chebyshev.theta n ≤ (5 / 4 : ℝ) * n)
    (hX : 3 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y)
    (hlogU : 4 ≤ Real.log (smoothRankinRatio X y))
    (hBu : (B : ℝ) ≤ smoothRankinRatio X y)
    (huY : smoothRankinRatio X y ≤ Real.sqrt y)
    (hD : 0 < D) (hDsmall : 4 * D ≤ 1)
    (hbudget : cepDyadicCofactorDenominatorBudget B X
        (smoothRankinRatio X y) ≤ 1 / (2 * D)) :
    D * (X : ℝ) *
        ((1 / (16 * Real.log 2 *
          Real.log (smoothRankinRatio X y))) ^
            cepDyadicMultiplicity (smoothRankinRatio X y) /
          (Nat.factorial
            (cepDyadicMultiplicity (smoothRankinRatio X y)) : ℝ)) ≤
      (psiNat X y : ℝ) := by
  apply cepDyadicPacketMass_le_psiNat_of_hildebrandDenominatorBound
    hB hpnt (by omega) hy hu (by linarith) hBu huY hD hDsmall
  intro m hm
  exact (cepCofactorHildebrandDenominator_le_dyadicBudget
    hB hX hy hu hlogU hBu huY hm).trans hbudget

/-- Canonical positive density chosen from the common coarse denominator. -/
def cepDyadicCofactorDensity (B X : ℕ) (u : ℝ) : ℝ :=
  1 / (4 * max 1 (cepDyadicCofactorDenominatorBudget B X u))

theorem cepDyadicCofactorDensity_pos (B X : ℕ) (u : ℝ) :
    0 < cepDyadicCofactorDensity B X u := by
  unfold cepDyadicCofactorDensity
  have hmax : (0 : ℝ) < max 1 (cepDyadicCofactorDenominatorBudget B X u) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

theorem four_mul_cepDyadicCofactorDensity_le_one (B X : ℕ) (u : ℝ) :
    4 * cepDyadicCofactorDensity B X u ≤ 1 := by
  unfold cepDyadicCofactorDensity
  have hmax : (1 : ℝ) ≤ max 1 (cepDyadicCofactorDenominatorBudget B X u) :=
    le_max_left _ _
  have hmaxPos : (0 : ℝ) < max 1 (cepDyadicCofactorDenominatorBudget B X u) :=
    zero_lt_one.trans_le hmax
  rw [div_eq_mul_inv]
  field_simp [hmaxPos.ne']
  exact hmax

theorem cepDyadicDenominatorBudget_le_densityReciprocal
    (B X : ℕ) (u : ℝ) :
    cepDyadicCofactorDenominatorBudget B X u ≤
      1 / (2 * cepDyadicCofactorDensity B X u) := by
  let H := max 1 (cepDyadicCofactorDenominatorBudget B X u)
  have hHPos : (0 : ℝ) < H :=
    lt_of_lt_of_le zero_lt_one (by simpa only [H] using
      (le_max_left (1 : ℝ) (cepDyadicCofactorDenominatorBudget B X u)))
  have hdenH : cepDyadicCofactorDenominatorBudget B X u ≤ H := by
    exact le_max_right _ _
  unfold cepDyadicCofactorDensity
  change cepDyadicCofactorDenominatorBudget B X u ≤
    1 / (2 * (1 / (4 * H)))
  have heq : 1 / (2 * (1 / (4 * H))) = 2 * H := by
    field_simp [hHPos.ne']
    norm_num
  rw [heq]
  linarith

/-- Fully explicit finite coarse CEP lower bound, conditional only on the
fixed PNT envelopes and the displayed critical-range inequalities. -/
theorem cepDyadicCriticalFiniteLower
    {B X y : ℕ}
    (hB : 4 ≤ B)
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta n ∧
        Chebyshev.theta n ≤ (5 / 4 : ℝ) * n)
    (hX : 3 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y)
    (hlogU : 4 ≤ Real.log (smoothRankinRatio X y))
    (hBu : (B : ℝ) ≤ smoothRankinRatio X y)
    (huY : smoothRankinRatio X y ≤ Real.sqrt y) :
    cepDyadicCofactorDensity B X (smoothRankinRatio X y) * (X : ℝ) *
        ((1 / (16 * Real.log 2 *
          Real.log (smoothRankinRatio X y))) ^
            cepDyadicMultiplicity (smoothRankinRatio X y) /
          (Nat.factorial
            (cepDyadicMultiplicity (smoothRankinRatio X y)) : ℝ)) ≤
      (psiNat X y : ℝ) := by
  apply cepDyadicPacketMass_le_psiNat_of_denominatorBudget
    hB hpnt hX hy hu hlogU hBu huY
  · exact cepDyadicCofactorDensity_pos _ _ _
  · exact four_mul_cepDyadicCofactorDensity_le_one _ _ _
  · exact cepDyadicDenominatorBudget_le_densityReciprocal _ _ _

/-- Secondary loss exposed by the coarse packet after reserving the main
`u log u` saddle term. -/
def cepDyadicSaddleError (B X y : ℕ) : ℝ :=
  let u := smoothRankinRatio X y
  let r := cepDyadicMultiplicity u
  let c := 16 * Real.log 2 * Real.log u
  let H := max 1 (cepDyadicCofactorDenominatorBudget B X u)
  ((r : ℝ) - u) * Real.log u + (r : ℝ) * Real.log c + Real.log (4 * H)

theorem exp_neg_packetLoss
    {u c H : ℝ} (hu : 0 < u) (hc : 0 < c) (hH : 0 < H) (r : ℕ) :
    Real.exp (-((r : ℝ) * Real.log u + (r : ℝ) * Real.log c +
      Real.log (4 * H))) =
      1 / (4 * H) * ((1 / c) ^ r / u ^ r) := by
  rw [show -((r : ℝ) * Real.log u + (r : ℝ) * Real.log c +
      Real.log (4 * H)) =
      (r : ℝ) * (-Real.log u) + (r : ℝ) * (-Real.log c) +
        (-Real.log (4 * H)) by ring]
  rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_neg, Real.exp_neg, Real.exp_neg,
    Real.exp_log hu, Real.exp_log hc, Real.exp_log (mul_pos (by norm_num) hH)]
  field_simp [hu.ne', hc.ne', hH.ne']
  simp [hu.ne']

/-- The explicit finite theorem in sharp-saddle form. -/
theorem cepDyadicCriticalFiniteSaddle
    {B X y : ℕ}
    (hB : 4 ≤ B)
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta n ∧
        Chebyshev.theta n ≤ (5 / 4 : ℝ) * n)
    (hX : 3 ≤ X) (hy : 2 ≤ y)
    (hu : 1 < smoothRankinRatio X y)
    (hlogU : 4 ≤ Real.log (smoothRankinRatio X y))
    (hBu : (B : ℝ) ≤ smoothRankinRatio X y)
    (huY : smoothRankinRatio X y ≤ Real.sqrt y) :
    (X : ℝ) * Real.exp
        (-(smoothRankinRatio X y * Real.log (smoothRankinRatio X y) +
          cepDyadicSaddleError B X y)) ≤
      (psiNat X y : ℝ) := by
  let u := smoothRankinRatio X y
  let r := cepDyadicMultiplicity u
  let c := 16 * Real.log 2 * Real.log u
  let H := max 1 (cepDyadicCofactorDenominatorBudget B X u)
  have huPos : 0 < u := zero_lt_one.trans (by simpa only [u] using hu)
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloguPos : 0 < Real.log u := Real.log_pos (by simpa only [u] using hu)
  have hcPos : 0 < c := by dsimp only [c]; positivity
  have hHOne : (1 : ℝ) ≤ H := by
    exact le_max_left _ _
  have hHPos : 0 < H := zero_lt_one.trans_le hHOne
  have hrU : (r : ℝ) ≤ u := by
    simpa only [r, u] using cast_cepDyadicMultiplicity_le_self hu (by linarith)
  have hfact : (Nat.factorial r : ℝ) ≤ u ^ r := by
    calc
      (Nat.factorial r : ℝ) ≤ ((r ^ r : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_le_pow r
      _ = (r : ℝ) ^ r := by norm_cast
      _ ≤ u ^ r := pow_le_pow_left₀ (by positivity) hrU r
  have hbase0 : 0 ≤ (1 / c : ℝ) ^ r := by positivity
  have hscalar :
      Real.exp (-(u * Real.log u + cepDyadicSaddleError B X y)) ≤
        cepDyadicCofactorDensity B X u *
          ((1 / c) ^ r / (Nat.factorial r : ℝ)) := by
    have herrRewrite :
        u * Real.log u + cepDyadicSaddleError B X y =
          (r : ℝ) * Real.log u + (r : ℝ) * Real.log c +
            Real.log (4 * H) := by
      simp only [cepDyadicSaddleError, u, r, c, H]
      ring
    rw [herrRewrite, exp_neg_packetLoss huPos hcPos hHPos r]
    unfold cepDyadicCofactorDensity
    change 1 / (4 * H) * ((1 / c) ^ r / u ^ r) ≤
      1 / (4 * H) * ((1 / c) ^ r / (Nat.factorial r : ℝ))
    apply mul_le_mul_of_nonneg_left
    · exact div_le_div_of_nonneg_left hbase0 (by positivity) hfact
    · positivity
  have hfinite := cepDyadicCriticalFiniteLower hB hpnt hX hy hu hlogU hBu huY
  calc
    (X : ℝ) * Real.exp
        (-(smoothRankinRatio X y * Real.log (smoothRankinRatio X y) +
          cepDyadicSaddleError B X y)) ≤
        (X : ℝ) * (cepDyadicCofactorDensity B X u *
          ((1 / c) ^ r / (Nat.factorial r : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [u] using hscalar
      · positivity
    _ = cepDyadicCofactorDensity B X u * (X : ℝ) *
          ((1 / c) ^ r / (Nat.factorial r : ℝ)) := by ring
    _ ≤ (psiNat X y : ℝ) := by
      simpa only [u, r, c] using hfinite

/-! ## Critical-sequence error audit -/

theorem IsTaoCriticalSmoothRegime.tendsto_log_rankinRatio_div_iteratedLog
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => Real.log (smoothRankinRatio (X x) (y x)) /
      iteratedLog x) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hnormalized := hregime.tendsto_rankinRatio_div_taoUZero hα
  have hlogNormalized : Tendsto (fun x =>
      Real.log (smoothRankinRatio (X x) (y x) / taoUZero x))
      atTop (𝓝 (Real.log (1 / α))) :=
    (Real.continuousAt_log (one_div_ne_zero hα.ne')).tendsto.comp hnormalized
  have hcorrection := hlogNormalized.div_atTop tendsto_iteratedLog_atTop
  have hsum := hcorrection.add tendsto_log_taoUZero_div_iteratedLog
  have hsumHalf : Tendsto (fun x =>
      Real.log (smoothRankinRatio (X x) (y x) / taoUZero x) /
          iteratedLog x +
        Real.log (taoUZero x) / iteratedLog x) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using hsum
  apply hsumHalf.congr'
  filter_upwards [hnormalized.eventually (Ioi_mem_nhds (one_div_pos.mpr hα)),
    tendsto_taoUZero_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hnormPos huPos
  have hproduct :
      (smoothRankinRatio (X x) (y x) / taoUZero x) * taoUZero x =
        smoothRankinRatio (X x) (y x) := by
    field_simp [huPos.ne']
  have hlogProduct :
      Real.log (smoothRankinRatio (X x) (y x)) =
        Real.log (smoothRankinRatio (X x) (y x) / taoUZero x) +
          Real.log (taoUZero x) := by
    conv_lhs => rw [← hproduct]
    rw [Real.log_mul hnormPos.ne' huPos.ne']
  rw [hlogProduct]
  ring

theorem IsTaoCriticalSmoothRegime.tendsto_log_log_X_div_log_rankinRatio
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => Real.log (Real.log (X x)) /
      Real.log (smoothRankinRatio (X x) (y x))) atTop (𝓝 2) := by
  have hquot := hregime.tendsto_log_log_X_div_iteratedLog.div
    (hregime.tendsto_log_rankinRatio_div_iteratedLog hα)
    (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hquotTwo : Tendsto (fun x =>
      (Real.log (Real.log (X x)) / iteratedLog x) /
        (Real.log (smoothRankinRatio (X x) (y x)) / iteratedLog x))
      atTop (𝓝 2) := by simpa using hquot
  apply hquotTwo.congr'
  filter_upwards [tendsto_iteratedLog_atTop.eventually
      (eventually_gt_atTop (0 : ℝ)),
    (hregime.tendsto_rankinRatio_atTop hα).eventually
      (eventually_gt_atTop (1 : ℝ))] with x hiterPos huOne
  field_simp [hiterPos.ne', (Real.log_pos huOne).ne']

/-- A generous pointwise `O(u log log u)` audit of the explicit coarse
secondary error. -/
theorem cepDyadicSaddleError_le
    {B X y : ℕ} (hB : 4 ≤ B) (hX : 3 ≤ X)
    (hu : 1 < smoothRankinRatio X y)
    (hlogU : 4 ≤ Real.log (smoothRankinRatio X y))
    (hloglogU : 1 ≤ Real.log (Real.log (smoothRankinRatio X y)))
    (hloglogX : Real.log (Real.log (X : ℝ)) ≤
      3 * Real.log (smoothRankinRatio X y))
    (hlogB : Real.log (B : ℝ) ≤ smoothRankinRatio X y) :
    cepDyadicSaddleError B X y ≤
      60 * smoothRankinRatio X y *
        Real.log (Real.log (smoothRankinRatio X y)) := by
  let u := smoothRankinRatio X y
  let r := cepDyadicMultiplicity u
  let L := Real.log u
  let LL := Real.log L
  let c := 16 * Real.log 2 * L
  let K := ⌈cepDyadicCofactorDepthBudget u⌉₊
  let A := cepDyadicCofactorDenominatorBudget B X u
  let H := max 1 A
  have hu' : 1 < u := by simpa only [u] using hu
  have huPos : 0 < u := zero_lt_one.trans hu'
  have hLFour : 4 ≤ L := by simpa only [L, u] using hlogU
  have hLPos : 0 < L := by linarith
  have hLLeU : L ≤ u := by
    have h := Real.log_le_sub_one_of_pos huPos
    simpa only [L] using h.trans (by linarith : u - 1 ≤ u)
  have hLLOne : 1 ≤ LL := by simpa only [LL, L, u] using hloglogU
  have hrU : (r : ℝ) ≤ u := by
    simpa only [r] using cast_cepDyadicMultiplicity_le_self hu' (by
      simpa only [L] using hLFour.trans' (by norm_num : (2 : ℝ) ≤ 4))
  have hfirst : ((r : ℝ) - u) * L ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrU) hLPos.le
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogTwoUpper : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hcPos : 0 < c := by dsimp only [c]; positivity
  have hcUpper : c ≤ 16 * L := by
    dsimp only [c]
    nlinarith
  have hlogcRaw : Real.log c ≤ Real.log (16 * L) :=
    Real.strictMonoOn_log.monotoneOn hcPos (mul_pos (by norm_num) hLPos) hcUpper
  have hlogSixteen : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogc : Real.log c ≤ 5 * LL := by
    rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hLPos.ne', hlogSixteen]
      at hlogcRaw
    have hfour : 4 * Real.log 2 ≤ 4 := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hlogTwoUpper (by norm_num : (0 : ℝ) ≤ 4))
    have : 4 + LL ≤ 5 * LL := by linarith
    linarith
  have hrlogc : (r : ℝ) * Real.log c ≤ 5 * u * LL := by
    calc
      (r : ℝ) * Real.log c ≤ (r : ℝ) * (5 * LL) :=
        mul_le_mul_of_nonneg_left hlogc (Nat.cast_nonneg r)
      _ ≤ u * (5 * LL) :=
        mul_le_mul_of_nonneg_right hrU (by positivity)
      _ = 5 * u * LL := by ring
  have hdepth0 : 0 ≤ cepDyadicCofactorDepthBudget u := by
    unfold cepDyadicCofactorDepthBudget
    positivity
  have hK : (K : ℝ) ≤ 10 * u / L + 1 := by
    exact (Nat.ceil_lt_add_one hdepth0).le
  have hKLe : (K : ℝ) ≤ 11 * u := by
    have honeU : 1 ≤ u := hu'.le
    have hdivLe : u / L ≤ u := by
      apply (div_le_iff₀ hLPos).2
      nlinarith
    calc
      (K : ℝ) ≤ 10 * u / L + 1 := hK
      _ ≤ 10 * u + u := by
        have hten : 10 * (u / L) ≤ 10 * u :=
          mul_le_mul_of_nonneg_left hdivLe (by norm_num : (0 : ℝ) ≤ 10)
        convert add_le_add hten honeU using 1
        all_goals ring
      _ = 11 * u := by ring
  have hlogXOne : 1 ≤ Real.log (X : ℝ) := by
    have hthree : (1 : ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
    exact hthree.trans (Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 3) (by positivity : (0 : ℝ) < X)
      (by exact_mod_cast hX))
  have hAOne : (1 : ℝ) ≤ A := by
    dsimp only [A, cepDyadicCofactorDenominatorBudget, K]
    have hBOne : (1 : ℝ) ≤ B := by exact_mod_cast (show 1 ≤ B by omega)
    have htwoOne : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
    have hlogPowOne : (1 : ℝ) ≤ Real.log (X : ℝ) ^ (K + 1) :=
      one_le_pow₀ hlogXOne
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hBOne htwoOne) hlogPowOne
  have hH : H = A := max_eq_right hAOne
  have hBPos : (0 : ℝ) < B := by positivity
  have hlogXPos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlogXOne
  have hlogA : Real.log A = Real.log (B : ℝ) + (K : ℝ) * Real.log 2 +
      ((K : ℝ) + 1) * Real.log (Real.log (X : ℝ)) := by
    dsimp only [A, cepDyadicCofactorDenominatorBudget]
    rw [Real.log_mul (mul_ne_zero hBPos.ne' (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)))
        (pow_ne_zero _ hlogXPos.ne'),
      Real.log_mul hBPos.ne' (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlogXSecondary : Real.log (Real.log (X : ℝ)) ≤ 3 * L := by
    simpa only [L, u] using hloglogX
  have hlogXSecondary0 : 0 ≤ Real.log (Real.log (X : ℝ)) :=
    Real.log_nonneg hlogXOne
  have hlogAUpper : Real.log A ≤ 48 * u := by
    rw [hlogA]
    have hKlogTwo : (K : ℝ) * Real.log 2 ≤ 11 * u :=
      (mul_le_mul_of_nonneg_left hlogTwoUpper (Nat.cast_nonneg K)).trans (by
        simpa using hKLe)
    have hKPower : ((K : ℝ) + 1) * Real.log (Real.log (X : ℝ)) ≤ 36 * u := by
      calc
        ((K : ℝ) + 1) * Real.log (Real.log (X : ℝ)) ≤
            (10 * u / L + 2) * (3 * L) := by
          exact mul_le_mul (by linarith) hlogXSecondary
            hlogXSecondary0 (by positivity)
        _ = 30 * u + 6 * L := by field_simp [hLPos.ne']; ring
        _ ≤ 36 * u := by linarith
    have hlogB' : Real.log (B : ℝ) ≤ u := by simpa only [u] using hlogB
    linarith
  have hlogFourH : Real.log (4 * H) ≤ 50 * u := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (by rw [hH]; exact (lt_of_lt_of_le zero_lt_one hAOne).ne')]
    rw [hH]
    have hlogFour : Real.log (4 : ℝ) ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hlogTwoUpper (by norm_num : (0 : ℝ) ≤ 2))
    have huOne : 1 ≤ u := hu'.le
    linarith
  have hlogFourHFinal : Real.log (4 * H) ≤ 50 * u * LL := by
    exact hlogFourH.trans (by nlinarith)
  dsimp only [cepDyadicSaddleError, u, r, c, H, L, LL] at hfirst
  dsimp only [cepDyadicSaddleError, u, r, c, H, L, LL] at hrlogc
  dsimp only [cepDyadicSaddleError, u, r, c, H, L, LL] at hlogFourHFinal
  dsimp only [A] at hlogFourHFinal
  dsimp only [u] at hlogFourHFinal
  dsimp only [cepDyadicSaddleError, u, r, c, H, L, LL]
  have hproductNonneg : 0 ≤ smoothRankinRatio X y *
      Real.log (Real.log (smoothRankinRatio X y)) := by
    have hu0 : 0 ≤ smoothRankinRatio X y := by simpa only [u] using huPos.le
    have hll0 : 0 ≤ Real.log (Real.log (smoothRankinRatio X y)) :=
      zero_le_one.trans hloglogU
    positivity
  linarith

/-- The coarse dyadic construction supplies the previously missing sharp
critical smooth-number saddle packet. -/
theorem IsTaoCriticalSmoothRegime.hasCriticalSmoothLowerSaddle_coarseCEP
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    HasCriticalSmoothLowerSaddle X y
      (criticalSmoothLowerCEPError 60 X y) := by
  obtain ⟨B, hB, hpnt⟩ := exists_chebyshevTheta_quarter_threshold
  have huTop := hregime.tendsto_rankinRatio_atTop hα
  have hloguTop := Real.tendsto_log_atTop.comp huTop
  have hlogloguTop := Real.tendsto_log_atTop.comp hloguTop
  have hratio :=
    (hregime.tendsto_log_log_X_div_log_rankinRatio hα).eventually
      (Iio_mem_nhds (show (2 : ℝ) < 3 by norm_num))
  filter_upwards [hregime.eventually_three_le_X,
    hregime.eventually_two_le_y hα,
    huTop.eventually (eventually_gt_atTop (1 : ℝ)),
    hloguTop.eventually (eventually_ge_atTop (4 : ℝ)),
    hlogloguTop.eventually (eventually_ge_atTop (1 : ℝ)),
    huTop.eventually (eventually_ge_atTop (B : ℝ)),
    huTop.eventually (eventually_ge_atTop (Real.log (B : ℝ))),
    hregime.eventually_rankinRatio_le_y_rpow_half hα,
    hratio] with x hX hy hu hlogU hloglogU hBu hlogB huY hratio'
  have hloguPos : 0 < Real.log (smoothRankinRatio (X x) (y x)) :=
    Real.log_pos hu
  have hloglogX : Real.log (Real.log (X x : ℝ)) ≤
      3 * Real.log (smoothRankinRatio (X x) (y x)) :=
    ((div_lt_iff₀ hloguPos).mp hratio').le
  have huSqrt : smoothRankinRatio (X x) (y x) ≤ Real.sqrt (y x) := by
    simpa only [Real.sqrt_eq_rpow] using huY
  have herr := cepDyadicSaddleError_le hB hX hu hlogU hloglogU
    hloglogX hlogB
  have hfinite := cepDyadicCriticalFiniteSaddle hB hpnt hX hy hu hlogU
    hBu huSqrt
  calc
    (X x : ℝ) * Real.exp
        (-(smoothRankinRatio (X x) (y x) *
            Real.log (smoothRankinRatio (X x) (y x)) +
          criticalSmoothLowerCEPError 60 X y x)) ≤
      (X x : ℝ) * Real.exp
        (-(smoothRankinRatio (X x) (y x) *
            Real.log (smoothRankinRatio (X x) (y x)) +
          cepDyadicSaddleError B (X x) (y x))) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        dsimp only [criticalSmoothLowerCEPError]
        linarith
      · positivity
    _ ≤ (psiNat (X x) (y x) : ℝ) := hfinite

/-- Unconditional sharp critical lower half of Proposition 2.1(i), obtained
from the coarse CEP packet. -/
theorem IsTaoCriticalSmoothRegime.eventually_self_div_taoZ_rpow_le_psiNat
    {X y : ℕ → ℕ} {α ε : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      (X x : ℝ) / (taoZ x) ^ (1 / α + ε) ≤
        (psiNat (X x) (y x) : ℝ) := by
  exact hregime.eventually_self_div_taoZ_rpow_le_psiNat_of_cep hα hε
    (hregime.hasCriticalSmoothLowerSaddle_coarseCEP hα)

end

end Tao2026

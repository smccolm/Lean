import GafniTao.ExceptionalSet
import PrimeNumberTheoremAnd.BrunTitchmarsh
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The multiplicative local scale in Gafni--Tao Section 2

This module records the exact physical scale `tau = X^(1-theta)` and proves
the deterministic part of the replacement of `x^theta` by `x/tau` on one
short multiplicative interval.  The arithmetic Brun--Titchmarsh comparison is
kept separate from these identities.
-/

namespace GafniTao

open Asymptotics Filter
open scoped ArithmeticFunction.vonMangoldt BigOperators

/-- The frozen local scale used throughout Section 2. -/
noncomputable def localTau (X theta : ℝ) : ℝ :=
  X ^ (1 - theta)

theorem localTau_pos {X theta : ℝ} (hX : 0 < X) :
    0 < localTau X theta := by
  exact Real.rpow_pos_of_pos hX _

/-- Exact factorization of `x/tau` into the original length and the local
multiplicative displacement. -/
theorem div_localTau_eq_rpow_mul_ratio
    {X x theta : ℝ} (hX : 0 < X) (hx : 0 < x) :
    x / localTau X theta =
      x ^ theta * (x / X) ^ (1 - theta) := by
  rw [localTau, Real.div_rpow hx.le hX.le]
  have hpow : x ^ theta * x ^ (1 - theta) = x := by
    rw [← Real.rpow_add hx]
    rw [show theta + (1 - theta) = 1 by ring, Real.rpow_one]
  calc
    x / X ^ (1 - theta) =
        (x ^ theta * x ^ (1 - theta)) / X ^ (1 - theta) := by
      rw [hpow]
    _ = x ^ theta * (x ^ (1 - theta) / X ^ (1 - theta)) := by ring

/-- On `X <= x <= (1+u)X`, the physical length `x/tau` differs from
`x^theta` by at most the literal relative displacement `u`. -/
theorem localScale_comparison
    {X x theta u : ℝ} (hX : 0 < X) (hthetaLower : 0 ≤ theta)
    (hthetaUpper : theta ≤ 1)
    (hxLower : X ≤ x) (hxUpper : x ≤ (1 + u) * X) :
    x ^ theta ≤ x / localTau X theta ∧
      x / localTau X theta ≤ (1 + u) * x ^ theta := by
  have hx : 0 < x := hX.trans_le hxLower
  have hratioLower : 1 ≤ x / X := by
    exact (le_div_iff₀ hX).2 (by simpa using hxLower)
  have hratioUpper : x / X ≤ 1 + u := by
    exact (div_le_iff₀ hX).2 (by simpa [mul_comm] using hxUpper)
  have hexponentLower : 0 ≤ 1 - theta := by linarith
  have hpowLower : 1 ≤ (x / X) ^ (1 - theta) :=
    Real.one_le_rpow hratioLower hexponentLower
  have hpowUpper : (x / X) ^ (1 - theta) ≤ 1 + u :=
    (Real.rpow_le_self_of_one_le hratioLower (by linarith)).trans hratioUpper
  have hxpow : 0 ≤ x ^ theta := Real.rpow_nonneg hx.le theta
  rw [div_localTau_eq_rpow_mul_ratio hX hx]
  constructor
  · simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpowLower hxpow
  · simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hpowUpper hxpow

theorem localScale_sub_nonneg
    {X x theta u : ℝ} (hX : 0 < X) (hthetaLower : 0 ≤ theta)
    (hthetaUpper : theta ≤ 1)
    (hxLower : X ≤ x) (hxUpper : x ≤ (1 + u) * X) :
    0 ≤ x / localTau X theta - x ^ theta := by
  linarith [
    (localScale_comparison hX hthetaLower hthetaUpper hxLower hxUpper).1]

theorem localScale_sub_le
    {X x theta u : ℝ} (hX : 0 < X) (hthetaLower : 0 ≤ theta)
    (hthetaUpper : theta ≤ 1)
    (hxLower : X ≤ x) (hxUpper : x ≤ (1 + u) * X) :
    x / localTau X theta - x ^ theta ≤ u * x ^ theta := by
  have h :=
    (localScale_comparison hX hthetaLower hthetaUpper hxLower hxUpper).2
  linarith

/-- Left endpoint of the additive grid used to produce a finite family of
paper-admissible multiplicative intervals. -/
def localCoverLeft (X u : ℝ) (k : ℕ) : ℝ :=
  X + k * u * X

theorem localCoverLeft_ge
    {X u : ℝ} (hX : 0 ≤ X) (hu : 0 ≤ u) (k : ℕ) :
    X ≤ localCoverLeft X u k := by
  unfold localCoverLeft
  have hterm : 0 ≤ (k : ℝ) * u * X := by positivity
  linarith

/-- Every point of `[X,2X]` lies in one member of a finite family of
intervals `[Y,(1+u)Y]`.  The displayed bound on `k` makes the cover finite
without hiding its dependence on `u`. -/
theorem exists_local_multiplicative_cover
    {X x u : ℝ} (hX : 0 < X) (hu : 0 < u)
    (hx : x ∈ Set.Icc X (2 * X)) :
    ∃ k : ℕ, k ≤ ⌈1 / u⌉₊ ∧
      localCoverLeft X u k ≤ x ∧
      x ≤ (1 + u) * localCoverLeft X u k := by
  let a : ℝ := (x - X) / (u * X)
  have hden : 0 < u * X := mul_pos hu hX
  have haNonneg : 0 ≤ a := by
    exact div_nonneg (sub_nonneg.mpr hx.1) hden.le
  let k : ℕ := ⌊a⌋₊
  have hkLower : (k : ℝ) ≤ a := by
    exact Nat.floor_le haNonneg
  have hkUpper : a < (k : ℝ) + 1 := by
    exact Nat.lt_floor_add_one a
  have haBound : a ≤ 1 / u := by
    rw [div_le_iff₀ hden]
    have hxBound : x - X ≤ X := by linarith [hx.2]
    calc
      x - X ≤ X := hxBound
      _ = (1 / u) * (u * X) := by field_simp
  have hkCeil : k ≤ ⌈1 / u⌉₊ := by
    have hceil : 1 / u ≤ (⌈1 / u⌉₊ : ℝ) :=
      Nat.le_ceil (1 / u)
    have hkReal : (k : ℝ) ≤ (⌈1 / u⌉₊ : ℝ) :=
      (hkLower.trans haBound).trans hceil
    exact_mod_cast hkReal
  refine ⟨k, hkCeil, ?_, ?_⟩
  · unfold localCoverLeft
    have hkScaled : (k : ℝ) * (u * X) ≤ x - X := by
      exact (le_div_iff₀ hden).mp (by simpa [a] using hkLower)
    nlinarith
  · have hstep : x < X + ((k : ℝ) + 1) * (u * X) := by
      have hkScaled : x - X < ((k : ℝ) + 1) * (u * X) :=
        (div_lt_iff₀ hden).mp (by simpa [a] using hkUpper)
      linarith
    have hleft : X ≤ localCoverLeft X u k :=
      localCoverLeft_ge hX.le hu.le k
    unfold localCoverLeft at hleft ⊢
    nlinarith

/-- Half-open strengthening of the finite multiplicative cover.  The strict
right endpoint is what permits an exact set inclusion into the source's
half-open local events without adding a finite endpoint exceptional set. -/
theorem exists_local_multiplicative_cover_Ico
    {X x u : ℝ} (hX : 0 < X) (hu : 0 < u)
    (hx : x ∈ Set.Icc X (2 * X)) :
    ∃ k : ℕ, k ≤ ⌈1 / u⌉₊ ∧
      localCoverLeft X u k ≤ x ∧
      x < (1 + u) * localCoverLeft X u k := by
  let a : ℝ := (x - X) / (u * X)
  have hden : 0 < u * X := mul_pos hu hX
  have haNonneg : 0 ≤ a :=
    div_nonneg (sub_nonneg.mpr hx.1) hden.le
  let k : ℕ := ⌊a⌋₊
  have hkLower : (k : ℝ) ≤ a := Nat.floor_le haNonneg
  have hkUpper : a < (k : ℝ) + 1 := Nat.lt_floor_add_one a
  have haBound : a ≤ 1 / u := by
    rw [div_le_iff₀ hden]
    have hxBound : x - X ≤ X := by linarith [hx.2]
    calc
      x - X ≤ X := hxBound
      _ = (1 / u) * (u * X) := by field_simp
  have hkCeil : k ≤ ⌈1 / u⌉₊ := by
    have hceil : 1 / u ≤ (⌈1 / u⌉₊ : ℝ) := Nat.le_ceil (1 / u)
    exact_mod_cast (hkLower.trans haBound).trans hceil
  refine ⟨k, hkCeil, ?_, ?_⟩
  · unfold localCoverLeft
    have hkScaled : (k : ℝ) * (u * X) ≤ x - X :=
      (le_div_iff₀ hden).mp (by simpa [a] using hkLower)
    nlinarith
  · have hstep : x < X + ((k : ℝ) + 1) * (u * X) := by
      have hkScaled : x - X < ((k : ℝ) + 1) * (u * X) :=
        (div_lt_iff₀ hden).mp (by simpa [a] using hkUpper)
      linarith
    have hleft : X ≤ localCoverLeft X u k :=
      localCoverLeft_ge hX.le hu.le k
    unfold localCoverLeft at hleft ⊢
    nlinarith

/-- The Mangoldt interval sum is nonnegative term by term. -/
theorem mangoldtIntervalSum_nonneg (x y : ℝ) :
    0 ≤ mangoldtIntervalSum x y := by
  exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- Splitting two nested real-endpoint intervals leaves exactly the adjacent
half-open interval; floors and equality endpoints are inherited from the
proved Chebyshev bridge. -/
theorem mangoldtIntervalSum_sub_eq
    (x : ℝ) {y₁ y₂ : ℝ} (hy₁ : 0 ≤ y₁) (hy₂ : y₁ ≤ y₂) :
    mangoldtIntervalSum x y₂ - mangoldtIntervalSum x y₁ =
      mangoldtIntervalSum (x + y₁) (y₂ - y₁) := by
  rw [mangoldtIntervalSum_eq_psi_sub x (hy₁.trans hy₂),
    mangoldtIntervalSum_eq_psi_sub x hy₁,
    mangoldtIntervalSum_eq_psi_sub (x + y₁) (sub_nonneg.mpr hy₂)]
  rw [show x + y₁ + (y₂ - y₁) = x + y₂ by ring]
  ring

/-- Uniform displacement of a `k`-th root across a positive interval.  The
factor `a^(-1/2)` is deliberately independent of `k`; this is the saving that
makes the local prime-power contribution negligible even when `theta < 1/2`.
-/
theorem rpow_inv_nat_sub_le
    {a b : ℝ} {k : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hk : 2 ≤ k) :
    b ^ ((k : ℝ)⁻¹) - a ^ ((k : ℝ)⁻¹) ≤
      a ^ (-(1 / 2 : ℝ)) * (b - a) := by
  let r : ℝ := (k : ℝ)⁻¹
  have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : (0 : ℝ) < k := lt_of_lt_of_le (by norm_num) hkReal
  have hrNonneg : 0 ≤ r := by positivity
  have hrHalf : r ≤ 1 / 2 := by
    simpa [r, one_div] using
      (inv_le_inv₀ hkPos (by norm_num : (0 : ℝ) < 2)).2 hkReal
  have hrOne : r ≤ 1 := hrHalf.trans (by norm_num)
  have hcont : ContinuousOn (fun z : ℝ ↦ z ^ r) (Set.Ici a) := by
    intro z hz
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) (ha.trans hz))))).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun z : ℝ ↦ z ^ r) (interior (Set.Ici a)) := by
    intro z hz
    have hz' : a < z := by simpa using hz
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) (ha.trans hz'.le))))).differentiableAt.differentiableWithinAt
  have hderiv : ∀ z ∈ interior (Set.Ici a),
      deriv (fun w : ℝ ↦ w ^ r) z ≤ a ^ (-(1 / 2 : ℝ)) := by
    intro z hz
    have hz' : a < z := by simpa using hz
    have hzOne : 1 ≤ z := ha.trans hz'.le
    have hexpNonpos : r - 1 ≤ 0 := by linarith
    have hbase : z ^ (r - 1) ≤ a ^ (r - 1) :=
      Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le (by norm_num) ha) hz'.le hexpNonpos
    have hexp : r - 1 ≤ -(1 / 2 : ℝ) := by linarith
    have haexp : a ^ (r - 1) ≤ a ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le ha hexp
    rw [Real.deriv_rpow_const]
    calc
      r * z ^ (r - 1) ≤ 1 * z ^ (r - 1) := by
        exact mul_le_mul_of_nonneg_right hrOne (Real.rpow_nonneg (by positivity) _)
      _ ≤ a ^ (r - 1) := by simpa using hbase
      _ ≤ a ^ (-(1 / 2 : ℝ)) := haexp
  simpa [r] using
    (convex_Ici a).image_sub_le_mul_sub_of_deriv_le hcont hdiff hderiv
      a (Set.mem_Ici.mpr le_rfl) b (Set.mem_Ici.mpr hab) hab

/-- The number of integer bases whose `k`-th powers can enter `(a,b]` has
the expected local root-length bound, including the one unavoidable endpoint
unit. -/
theorem nat_root_interval_card_le
    {a b : ℝ} {k : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hk : 2 ≤ k) :
    ((Finset.Ioc ⌊a ^ ((k : ℝ)⁻¹)⌋₊ ⌊b ^ ((k : ℝ)⁻¹)⌋₊).card : ℝ) ≤
      a ^ (-(1 / 2 : ℝ)) * (b - a) + 1 := by
  have haRootNonneg : 0 ≤ a ^ ((k : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  have hbRootNonneg : 0 ≤ b ^ ((k : ℝ)⁻¹) :=
    Real.rpow_nonneg (zero_le_one.trans (ha.trans hab)) _
  have hrootMono : a ^ ((k : ℝ)⁻¹) ≤ b ^ ((k : ℝ)⁻¹) := by
    exact Real.rpow_le_rpow (by positivity) hab (by positivity)
  have hfloorMono : ⌊a ^ ((k : ℝ)⁻¹)⌋₊ ≤ ⌊b ^ ((k : ℝ)⁻¹)⌋₊ :=
    Nat.floor_mono hrootMono
  rw [Nat.card_Ioc]
  rw [Nat.cast_sub hfloorMono]
  have hfloorUpper : (⌊b ^ ((k : ℝ)⁻¹)⌋₊ : ℝ) ≤
      b ^ ((k : ℝ)⁻¹) := Nat.floor_le hbRootNonneg
  have hfloorLower : a ^ ((k : ℝ)⁻¹) <
      (⌊a ^ ((k : ℝ)⁻¹)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hrounding :
      (⌊b ^ ((k : ℝ)⁻¹)⌋₊ : ℝ) -
          (⌊a ^ ((k : ℝ)⁻¹)⌋₊ : ℝ) ≤
        b ^ ((k : ℝ)⁻¹) - a ^ ((k : ℝ)⁻¹) + 1 := by
    linarith
  exact hrounding.trans (by
    simpa [add_comm] using add_le_add_right (rpow_inv_nat_sub_le ha hab hk) 1)

/-- The part of a Mangoldt interval sum supported on non-primes.  Since
`Lambda` itself is supported on prime powers, this is exactly the higher
prime-power contribution rather than a proxy for it. -/
noncomputable def primePowerTailIntervalSum (a y : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊a⌋₊ ⌊a + y⌋₊).filter (fun n ↦ ¬n.Prime), Λ n

/-- One exponent slice of the exact higher-prime-power contribution. -/
noncomputable def primePowerExponentSlice (a b : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc 0 ⌊b ^ ((1 : ℝ) / k)⌋₊).filter
      (fun p ↦ p.Prime ∧ a < (p ^ k : ℕ) ∧ ¬(p ^ k).Prime),
    Λ (p ^ k)

/-- Exact exponent-indexed expansion of the local non-prime Mangoldt sum.
The source and target retain all endpoint inequalities literally. -/
theorem primePowerTailIntervalSum_eq_exponent_sum
    {a y : ℝ} (ha : 0 ≤ a) (hy : 0 ≤ y) :
    primePowerTailIntervalSum a y =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log (a + y) / Real.log 2⌋₊,
        primePowerExponentSlice a (a + y) k := by
  classical
  let f : ℕ → ℝ := fun n ↦ if a < n ∧ ¬n.Prime then Λ n else 0
  have hdecomp := Chebyshev.sum_PrimePow_eq_sum_sum f (add_nonneg ha hy)
  have hdecomp' :
      (∑ n ∈ Finset.Ioc 0 ⌊a + y⌋₊ with IsPrimePow n, f n) =
        ∑ k ∈ Finset.Icc 1 ⌊Real.log (a + y) / Real.log 2⌋₊,
          primePowerExponentSlice a (a + y) k := by
    simpa only [f, primePowerExponentSlice, Finset.sum_filter, ← ite_and,
      and_assoc] using hdecomp
  rw [← hdecomp']
  unfold primePowerTailIntervalSum f
  have hIoc : Finset.Ioc ⌊a⌋₊ ⌊a + y⌋₊ =
      (Finset.Ioc 0 ⌊a + y⌋₊).filter (fun n ↦ ⌊a⌋₊ < n) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_filter]
    omega
  rw [hIoc]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Ioc] at hn
  by_cases hprime : n.Prime
  · simp [hprime]
  by_cases hpp : IsPrimePow n
  · have haCast : a < (n : ℝ) ↔ ⌊a⌋₊ < n := (Nat.floor_lt ha).symm
    simp [hprime, hpp, haCast]
  · have hLambda : Λ n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
    simp [hprime, hpp, hLambda]

@[simp] theorem primePowerExponentSlice_one (a b : ℝ) :
    primePowerExponentSlice a b 1 = 0 := by
  classical
  unfold primePowerExponentSlice
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_filter] at hp
  exact (hp.2.2.2 (by simpa using hp.2.1)).elim

/-- Each higher-power exponent slice is bounded by its local root-interval
cardinality times `log b`. -/
theorem primePowerExponentSlice_le
    {a b : ℝ} {k : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hk : 2 ≤ k) :
    primePowerExponentSlice a b k ≤
      (a ^ (-(1 / 2 : ℝ)) * (b - a) + 1) * Real.log b := by
  classical
  let s : Finset ℕ :=
    (Finset.Ioc 0 ⌊b ^ ((1 : ℝ) / k)⌋₊).filter
      (fun p ↦ p.Prime ∧ a < (p ^ k : ℕ) ∧ ¬(p ^ k).Prime)
  let roots : Finset ℕ :=
    Finset.Ioc ⌊a ^ ((k : ℝ)⁻¹)⌋₊ ⌊b ^ ((k : ℝ)⁻¹)⌋₊
  have hb : 1 ≤ b := ha.trans hab
  have hlog : 0 ≤ Real.log b := Real.log_nonneg hb
  have hkPosNat : k ≠ 0 := by omega
  have hkPosReal : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk)
  have hkOne : (1 : ℝ) / k ≤ 1 := by
    rw [div_le_one hkPosReal]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hkPosNat)
  have hsRoots : s ⊆ roots := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_Ioc] at hp
    rw [Finset.mem_Ioc]
    have hpRootNonneg : 0 ≤ a ^ ((k : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
    have hapow : a < (p : ℝ) ^ (k : ℝ) := by
      simpa [Real.rpow_natCast] using hp.2.2.1
    have hpRoot : a ^ ((k : ℝ)⁻¹) < (p : ℝ) :=
      (Real.rpow_inv_lt_iff_of_pos (by positivity) (by positivity) hkPosReal).2 hapow
    exact ⟨(Nat.floor_lt hpRootNonneg).2 hpRoot, by simpa [one_div] using hp.1.2⟩
  have hcard : (s.card : ℝ) ≤
      a ^ (-(1 / 2 : ℝ)) * (b - a) + 1 := by
    have hcardNat : s.card ≤ roots.card := Finset.card_le_card hsRoots
    have hcardReal : (s.card : ℝ) ≤ (roots.card : ℝ) := by exact_mod_cast hcardNat
    exact hcardReal.trans (by
      simpa [roots] using nat_root_interval_card_le ha hab hk)
  unfold primePowerExponentSlice
  change (∑ p ∈ s, Λ (p ^ k)) ≤ _
  calc
    (∑ p ∈ s, Λ (p ^ k)) ≤ ∑ _p ∈ s, Real.log b := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := (Finset.mem_filter.mp hp).2
      have hpPrime : p.Prime := hpData.1
      have hpDomain := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
      have hpLeRoot : (p : ℝ) ≤ b ^ ((1 : ℝ) / k) := by
        exact (Nat.le_floor_iff (Real.rpow_nonneg (by positivity) _)).mp hpDomain
      have hrootLe : b ^ ((1 : ℝ) / k) ≤ b :=
        Real.rpow_le_self_of_one_le hb hkOne
      rw [ArithmeticFunction.vonMangoldt_apply_pow hkPosNat,
        ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
      exact Real.log_le_log (by exact_mod_cast hpPrime.pos) (hpLeRoot.trans hrootLe)
    _ = s.card * Real.log b := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (a ^ (-(1 / 2 : ℝ)) * (b - a) + 1) * Real.log b :=
      mul_le_mul_of_nonneg_right hcard hlog

/-- Complete local prime-power bound.  Unlike the global
`psi-theta = O(sqrt x log x)` estimate, this retains the interval length and
therefore remains negligible in every fixed positive `theta` range after the
usual logarithmic absorption. -/
theorem primePowerTailIntervalSum_le
    {a y : ℝ} (ha : 1 ≤ a) (hy : 0 ≤ y) :
    primePowerTailIntervalSum a y ≤
      (⌊Real.log (a + y) / Real.log 2⌋₊ : ℝ) *
        ((a ^ (-(1 / 2 : ℝ)) * y + 1) * Real.log (a + y)) := by
  classical
  let K : ℕ := ⌊Real.log (a + y) / Real.log 2⌋₊
  let C : ℝ := (a ^ (-(1 / 2 : ℝ)) * y + 1) * Real.log (a + y)
  have hb : 1 ≤ a + y := by linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (add_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans ha) _) hy) zero_le_one)
      (Real.log_nonneg hb)
  rw [primePowerTailIntervalSum_eq_exponent_sum (zero_le_one.trans ha) hy]
  change (∑ k ∈ Finset.Icc 1 K, primePowerExponentSlice a (a + y) k) ≤
    (K : ℝ) * C
  calc
    (∑ k ∈ Finset.Icc 1 K, primePowerExponentSlice a (a + y) k) ≤
        ∑ _k ∈ Finset.Icc 1 K, C := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Finset.mem_Icc] at hk
      rcases eq_or_lt_of_le hk.1 with rfl | hkTwo
      · simpa using hC
      · have hs := primePowerExponentSlice_le ha (le_add_of_nonneg_right hy)
          (by omega : 2 ≤ k)
        simpa [C] using hs
    _ = ((Finset.Icc 1 K).card : ℝ) * C := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (K : ℝ) * C := by simp

/-- Prime-supported part of the same real-endpoint interval. -/
noncomputable def primeMangoldtIntervalSum (a y : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊a⌋₊ ⌊a + y⌋₊).filter Nat.Prime, Λ n

theorem mangoldtIntervalSum_eq_prime_add_tail (a y : ℝ) :
    mangoldtIntervalSum a y =
      primeMangoldtIntervalSum a y + primePowerTailIntervalSum a y := by
  classical
  rw [mangoldtIntervalSum, primeMangoldtIntervalSum, primePowerTailIntervalSum]
  exact (Finset.sum_filter_add_sum_filter_not
    (Finset.Ioc ⌊a⌋₊ ⌊a + y⌋₊) Nat.Prime Λ).symm

theorem prime_part_subset_primesBetween
    (a y : ℝ) :
    (Finset.Ioc ⌊a⌋₊ ⌊a + y⌋₊).filter Nat.Prime ⊆
      (Finset.Icc ⌈a⌉₊ ⌊a + y⌋₊).filter Nat.Prime := by
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  refine ⟨?_, hn.2⟩
  rw [Finset.mem_Ioc] at hn
  rw [Finset.mem_Icc]
  constructor
  · exact (Nat.ceil_le_floor_add_one a).trans (by omega)
  · exact hn.1.2

/-- Brun--Titchmarsh applied only to the prime-supported part, with its
logarithmic weight retained explicitly. -/
theorem primeMangoldtIntervalSum_le_brunTitchmarsh
    {a y z : ℝ} (ha : 1 ≤ a) (hy : 0 < y) (hz : 1 < z) :
    primeMangoldtIntervalSum a y ≤
      Real.log (a + y) *
        (2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3) := by
  classical
  let sp : Finset ℕ :=
    (Finset.Ioc ⌊a⌋₊ ⌊a + y⌋₊).filter Nat.Prime
  have hb : 1 ≤ a + y := by linarith
  have hlog : 0 ≤ Real.log (a + y) := Real.log_nonneg hb
  have hprimeCard : sp.card ≤ BrunTitchmarsh.primesBetween a (a + y) := by
    exact Finset.card_le_card (prime_part_subset_primesBetween a y)
  have hweighted : (∑ n ∈ sp, Λ n) ≤
      BrunTitchmarsh.primesBetween a (a + y) * Real.log (a + y) := by
    calc
      (∑ n ∈ sp, Λ n) = ∑ n ∈ sp, Real.log n := by
        apply Finset.sum_congr rfl
        intro n hn
        exact ArithmeticFunction.vonMangoldt_apply_prime
          (Finset.mem_filter.mp hn).2
      _ ≤ ∑ _n ∈ sp, Real.log (a + y) := by
        apply Finset.sum_le_sum
        intro n hn
        apply Real.log_le_log
        · exact_mod_cast (Finset.mem_filter.mp hn).2.pos
        · exact (Nat.le_floor_iff (by linarith : 0 ≤ a + y)).mp
            (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
      _ = sp.card * Real.log (a + y) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ BrunTitchmarsh.primesBetween a (a + y) * Real.log (a + y) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hprimeCard) hlog
  have hprimeCount := BrunTitchmarsh.primesBetween_le a y z
    (by linarith) hy hz
  unfold primeMangoldtIntervalSum
  change (∑ n ∈ sp, Λ n) ≤ _
  calc
    (∑ n ∈ sp, Λ n) ≤
        BrunTitchmarsh.primesBetween a (a + y) * Real.log (a + y) := hweighted
    _ ≤ (2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3) *
        Real.log (a + y) := mul_le_mul_of_nonneg_right hprimeCount hlog
    _ = _ := by ring

/-- Source-relevant Brun--Titchmarsh bound for the complete von Mangoldt
interval.  Its prime-power error is local in `y`, so this theorem applies in
the small-exponent range where the older global remainder does not. -/
theorem mangoldtIntervalSum_le_brunTitchmarsh_local
    {a y z : ℝ} (ha : 1 ≤ a) (hy : 0 < y) (hz : 1 < z) :
    mangoldtIntervalSum a y ≤
      Real.log (a + y) *
          (2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3) +
        (⌊Real.log (a + y) / Real.log 2⌋₊ : ℝ) *
          ((a ^ (-(1 / 2 : ℝ)) * y + 1) * Real.log (a + y)) := by
  rw [mangoldtIntervalSum_eq_prime_add_tail]
  exact add_le_add
    (primeMangoldtIntervalSum_le_brunTitchmarsh ha hy hz)
    (primePowerTailIntervalSum_le ha hy.le)

/-- Explicit error majorant used when replacing `x^theta` by `x/tau`.
Every term comes from either Brun--Titchmarsh or the exact local prime-power
decomposition above. -/
noncomputable def localMangoldtReplacementError (a d z : ℝ) : ℝ :=
  Real.log (a + d) *
      (2 * d / Real.log z + 6 * z * (1 + Real.log z) ^ 3) +
    (⌊Real.log (a + d) / Real.log 2⌋₊ : ℝ) *
      ((a ^ (-(1 / 2 : ℝ)) * d + 1) * Real.log (a + d))

/-- Power choice in Brun--Titchmarsh.  It makes the leading logarithmic
quotient a literal constant while leaving a strictly smaller power in the
sieve remainder. -/
noncomputable def localReplacementZ (a d theta : ℝ) : ℝ :=
  (a + d) ^ (theta / 4)

theorem one_lt_localReplacementZ
    {a d theta : ℝ} (ha : 1 < a) (hd : 0 ≤ d) (htheta : 0 < theta) :
    1 < localReplacementZ a d theta := by
  unfold localReplacementZ
  exact Real.one_lt_rpow (by linarith) (by linarith)

/-- Exact ledger after the source-compatible power choice for the
Brun--Titchmarsh parameter. -/
theorem localMangoldtReplacementError_at_power
    {a d theta : ℝ} (ha : 1 < a) (hd : 0 ≤ d) (htheta : 0 < theta) :
    localMangoldtReplacementError a d (localReplacementZ a d theta) =
      8 * d / theta +
        6 * (a + d) ^ (theta / 4) * Real.log (a + d) *
          (1 + (theta / 4) * Real.log (a + d)) ^ 3 +
        (⌊Real.log (a + d) / Real.log 2⌋₊ : ℝ) *
          ((a ^ (-(1 / 2 : ℝ)) * d + 1) * Real.log (a + d)) := by
  have hab : 0 < a + d := by linarith
  have hlog : Real.log (a + d) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have hthetaNe : theta ≠ 0 := ne_of_gt htheta
  unfold localMangoldtReplacementError localReplacementZ
  rw [Real.log_rpow hab]
  field_simp
  ring

theorem localMangoldtReplacementError_nonneg
    {a d z : ℝ} (ha : 1 ≤ a) (hd : 0 ≤ d) (hz : 1 < z) :
    0 ≤ localMangoldtReplacementError a d z := by
  have hab : 1 ≤ a + d := by linarith
  have hlogb : 0 ≤ Real.log (a + d) := Real.log_nonneg hab
  have hlogz : 0 < Real.log z := Real.log_pos hz
  unfold localMangoldtReplacementError
  apply add_nonneg
  · exact mul_nonneg hlogb (add_nonneg (div_nonneg (by positivity) hlogz.le) (by positivity))
  · exact mul_nonneg (by positivity)
      (mul_nonneg (add_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans ha) _) hd)
        zero_le_one) hlogb)

/-- The local-model Mangoldt sum with the paper's exact physical length. -/
noncomputable def localMangoldtSum (X theta x : ℝ) : ℝ :=
  mangoldtIntervalSum x (x / localTau X theta)

/-- Exact arithmetic difference between the local model and the original
`x^theta` interval.  This is the entry point for the local prime and
prime-power estimates; no asymptotic error has yet been substituted. -/
theorem localMangoldtSum_sub_short_eq
    {X x theta u : ℝ} (hX : 0 < X) (hthetaLower : 0 ≤ theta)
    (hthetaUpper : theta ≤ 1)
    (hxLower : X ≤ x) (hxUpper : x ≤ (1 + u) * X) :
    localMangoldtSum X theta x - mangoldtShortSum x theta =
      mangoldtIntervalSum (x + x ^ theta)
        (x / localTau X theta - x ^ theta) := by
  have hx : 0 < x := hX.trans_le hxLower
  have hscale :=
    (localScale_comparison hX hthetaLower hthetaUpper hxLower hxUpper).1
  exact mangoldtIntervalSum_sub_eq x (Real.rpow_nonneg hx.le theta) hscale

/-- Exact, complete quantitative form of the local replacement in Gafni--Tao
line (2.2): the absolute discrepancy is controlled by the explicit
Brun--Titchmarsh plus local-prime-power error. -/
theorem abs_localMangoldtSum_sub_short_le
    {X x theta u z : ℝ} (hX : 1 ≤ X) (hthetaLower : 0 ≤ theta)
    (hthetaUpper : theta ≤ 1)
    (hxLower : X ≤ x) (hxUpper : x ≤ (1 + u) * X) (hz : 1 < z) :
    |localMangoldtSum X theta x - mangoldtShortSum x theta| ≤
      localMangoldtReplacementError (x + x ^ theta)
        (x / localTau X theta - x ^ theta) z := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hx : 1 ≤ x := hX.trans hxLower
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hd := localScale_sub_nonneg hXpos hthetaLower hthetaUpper hxLower hxUpper
  have ha : 1 ≤ x + x ^ theta := by
    exact hx.trans (le_add_of_nonneg_right (Real.rpow_nonneg hxpos.le theta))
  rw [localMangoldtSum_sub_short_eq hXpos hthetaLower hthetaUpper hxLower hxUpper]
  rw [abs_of_nonneg (mangoldtIntervalSum_nonneg _ _)]
  by_cases hdZero : x / localTau X theta - x ^ theta = 0
  · rw [hdZero]
    have hzero : mangoldtIntervalSum (x + x ^ theta) 0 = 0 := by
      rw [mangoldtIntervalSum_eq_psi_sub _ le_rfl]
      simp
    rw [hzero]
    exact localMangoldtReplacementError_nonneg ha le_rfl hz
  · exact mangoldtIntervalSum_le_brunTitchmarsh_local ha
      (lt_of_le_of_ne hd (Ne.symm hdZero)) hz

/-- The complete local replacement with the Brun--Titchmarsh parameter
eliminated.  This is the form used by the later epsilon/logarithm absorption
ledger. -/
theorem abs_localMangoldtSum_sub_short_le_power_ledger
    {X x theta u : ℝ} (hX : 1 < X) (hthetaLower : 0 < theta)
    (hthetaUpper : theta ≤ 1)
    (hxLower : X ≤ x) (hxUpper : x ≤ (1 + u) * X) :
    |localMangoldtSum X theta x - mangoldtShortSum x theta| ≤
      8 * (x / localTau X theta - x ^ theta) / theta +
        6 * (x + x / localTau X theta) ^ (theta / 4) *
          Real.log (x + x / localTau X theta) *
          (1 + (theta / 4) * Real.log (x + x / localTau X theta)) ^ 3 +
        (⌊Real.log (x + x / localTau X theta) / Real.log 2⌋₊ : ℝ) *
          (((x + x ^ theta) ^ (-(1 / 2 : ℝ)) *
              (x / localTau X theta - x ^ theta) + 1) *
            Real.log (x + x / localTau X theta)) := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hx : 1 < x := hX.trans_le hxLower
  have hd := localScale_sub_nonneg hXpos hthetaLower.le hthetaUpper hxLower hxUpper
  have ha : 1 < x + x ^ theta :=
    hx.trans_le (le_add_of_nonneg_right (Real.rpow_nonneg (zero_le_one.trans hx.le) theta))
  have hmain := abs_localMangoldtSum_sub_short_le hX.le hthetaLower.le hthetaUpper
    hxLower hxUpper (one_lt_localReplacementZ ha hd hthetaLower)
  rw [localMangoldtReplacementError_at_power ha hd hthetaLower] at hmain
  simpa [add_assoc, add_left_comm, add_comm] using hmain

/-- A one-variable envelope for all non-leading terms in the exact local
replacement ledger.  It is deliberately explicit so the later epsilon
absorption does not conceal any logarithmic or prime-power loss. -/
noncomputable def localReplacementRemainderEnvelope
    (theta u x : ℝ) : ℝ :=
  324 * 3 ^ (theta / 4) * x ^ (theta / 4) * Real.log x ^ 4 +
    (4 / Real.log 2) * (u * x ^ (theta - 1 / 2) + 1) * Real.log x ^ 2

/-- Every term in the explicit local-replacement remainder is of lower order
than the physical interval length `x^theta`, for every fixed positive
`theta`.  This includes the prime-power term when `theta < 1/2`. -/
theorem localReplacementRemainderEnvelope_isLittleO
    {theta u : ℝ} (htheta : 0 < theta) :
    (fun x : ℝ => localReplacementRemainderEnvelope theta u x) =o[atTop]
      (fun x : ℝ => x ^ theta) := by
  have hlog4r : (fun x : ℝ => Real.log x ^ (4 : ℝ)) =o[atTop]
      (fun x : ℝ => x ^ (3 * theta / 4)) :=
    isLittleO_log_rpow_rpow_atTop 4 (by linarith)
  have hlog4 : (fun x : ℝ => Real.log x ^ (4 : ℕ)) =o[atTop]
      (fun x : ℝ => x ^ (3 * theta / 4)) := by
    apply hlog4r.congr' _ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x _hx
    exact Real.rpow_natCast (Real.log x) 4
  have hfirst0 :=
    (isBigO_refl (fun x : ℝ => x ^ (theta / 4)) atTop).mul_isLittleO hlog4
  have hfirst :
      (fun x : ℝ => 324 * 3 ^ (theta / 4) * x ^ (theta / 4) * Real.log x ^ 4)
        =o[atTop] (fun x : ℝ => x ^ theta) := by
    have hfirst1 :
        (fun x : ℝ => x ^ (theta / 4) * Real.log x ^ 4) =o[atTop]
          (fun x : ℝ => x ^ theta) := by
      apply hfirst0.congr' EventuallyEq.rfl
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx]
      congr 1
      ring
    simpa only [mul_assoc] using
      hfirst1.const_mul_left (324 * 3 ^ (theta / 4))
  have hlog2r : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[atTop]
      (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop 2 (by norm_num)
  have hlog2 : (fun x : ℝ => Real.log x ^ (2 : ℕ)) =o[atTop]
      (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
    apply hlog2r.congr' _ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x _hx
    exact Real.rpow_natCast (Real.log x) 2
  have hscaled0 :=
    (isBigO_refl (fun x : ℝ => x ^ (theta - 1 / 2)) atTop).mul_isLittleO hlog2
  have hscaled :
      (fun x : ℝ => u * x ^ (theta - 1 / 2) * Real.log x ^ 2) =o[atTop]
        (fun x : ℝ => x ^ theta) := by
    have hbase :
        (fun x : ℝ => x ^ (theta - 1 / 2) * Real.log x ^ 2) =o[atTop]
          (fun x : ℝ => x ^ theta) := by
      apply hscaled0.congr' EventuallyEq.rfl
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx]
      congr 1
      ring
    simpa only [mul_assoc] using hbase.const_mul_left u
  have hpure : (fun x : ℝ => Real.log x ^ (2 : ℕ)) =o[atTop]
      (fun x : ℝ => x ^ theta) := by
    have hpureR := isLittleO_log_rpow_rpow_atTop 2 htheta
    apply hpureR.congr' _ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x _hx
    exact Real.rpow_natCast (Real.log x) 2
  have hsecond0 := hscaled.add hpure
  have hsecond :
      (fun x : ℝ => (4 / Real.log 2) * (u * x ^ (theta - 1 / 2) + 1) *
          Real.log x ^ 2) =o[atTop] (fun x : ℝ => x ^ theta) := by
    apply (hsecond0.const_mul_left (4 / Real.log 2)).congr' _ EventuallyEq.rfl
    exact Filter.Eventually.of_forall fun x => by ring
  exact hfirst.add hsecond

/-- Pointwise domination of the two non-leading terms in the exact ledger by
the one-variable envelope.  The hypotheses are uniform over a whole local
multiplicative interval. -/
theorem localReplacementRemainder_le_envelope
    {X x theta u : ℝ}
    (hX : 0 < X) (hxLarge : (3 : ℝ) ≤ x)
    (htheta : 0 < theta) (hthetaUpper : theta ≤ 1)
    (huLower : 0 ≤ u) (huUpper : u ≤ 1)
    (hxLower : X ≤ x) (hxUpper : x ≤ (1 + u) * X) :
    6 * (x + x / localTau X theta) ^ (theta / 4) *
          Real.log (x + x / localTau X theta) *
          (1 + (theta / 4) * Real.log (x + x / localTau X theta)) ^ 3 +
        (Nat.floor (Real.log (x + x / localTau X theta) / Real.log 2) : ℝ) *
          (((x + x ^ theta) ^ (-(1 / 2 : ℝ)) *
              (x / localTau X theta - x ^ theta) + 1) *
            Real.log (x + x / localTau X theta)) ≤
      localReplacementRemainderEnvelope theta u x := by
  have hx : 1 < x := by linarith
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogx : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hxpos
      ((Real.exp_one_lt_d9.trans_le (by norm_num)).le.trans hxLarge)
  have hxpow_le : x ^ theta ≤ x := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx.le hthetaUpper
  have hscale := localScale_comparison hX htheta.le hthetaUpper hxLower hxUpper
  have hscaleUpper : x / localTau X theta ≤ 2 * x ^ theta := by
    calc
      x / localTau X theta ≤ (1 + u) * x ^ theta := hscale.2
      _ ≤ 2 * x ^ theta := by gcongr; linarith
  have hbLower : 1 < x + x / localTau X theta := by
    have htau : 0 < localTau X theta := localTau_pos hX
    have hquot : 0 < x / localTau X theta := div_pos hxpos htau
    linarith
  have hbUpper : x + x / localTau X theta ≤ 3 * x := by
    calc
      x + x / localTau X theta ≤ x + 2 * x ^ theta := by linarith
      _ ≤ 3 * x := by linarith
  have hlogbNonneg : 0 ≤ Real.log (x + x / localTau X theta) :=
    Real.log_nonneg hbLower.le
  have hlogb : Real.log (x + x / localTau X theta) ≤ 2 * Real.log x := by
    calc
      Real.log (x + x / localTau X theta) ≤ Real.log (3 * x) :=
        Real.log_le_log (by positivity) hbUpper
      _ = Real.log 3 + Real.log x := by rw [Real.log_mul (by norm_num) hxpos.ne']
      _ ≤ 2 * Real.log x := by
        have hlog3 :=
          Real.strictMonoOn_log.monotoneOn (by norm_num) hxpos hxLarge
        linarith
  have hbpow : (x + x / localTau X theta) ^ (theta / 4) ≤
      3 ^ (theta / 4) * x ^ (theta / 4) := by
    calc
      (x + x / localTau X theta) ^ (theta / 4) ≤
          (3 * x) ^ (theta / 4) := by gcongr
      _ = 3 ^ (theta / 4) * x ^ (theta / 4) := by
        rw [Real.mul_rpow (by norm_num : 0 ≤ (3 : ℝ)) hxpos.le]
  have hinner : 1 + (theta / 4) * Real.log (x + x / localTau X theta) ≤
      3 * Real.log x := by
    have hquarter : theta / 4 ≤ 1 := by linarith
    have hprod : (theta / 4) * Real.log (x + x / localTau X theta) ≤
        2 * Real.log x := by
      calc
        _ ≤ 1 * Real.log (x + x / localTau X theta) := by gcongr
        _ ≤ 2 * Real.log x := by simpa using hlogb
    linarith
  have hinnerNonneg :
      0 ≤ 1 + (theta / 4) * Real.log (x + x / localTau X theta) := by
    positivity
  have hterm2 :
      6 * (x + x / localTau X theta) ^ (theta / 4) *
          Real.log (x + x / localTau X theta) *
          (1 + (theta / 4) * Real.log (x + x / localTau X theta)) ^ 3 ≤
        324 * 3 ^ (theta / 4) * x ^ (theta / 4) * Real.log x ^ 4 := by
    calc
      _ ≤ 6 * (3 ^ (theta / 4) * x ^ (theta / 4)) *
          (2 * Real.log x) * (3 * Real.log x) ^ 3 := by gcongr
      _ = _ := by ring
  have hdNonneg := localScale_sub_nonneg hX htheta.le hthetaUpper hxLower hxUpper
  have hdUpper := localScale_sub_le hX htheta.le hthetaUpper hxLower hxUpper
  have haPow : (x + x ^ theta) ^ (-(1 / 2 : ℝ)) ≤
      x ^ (-(1 / 2 : ℝ)) := by
    apply Real.rpow_le_rpow_of_nonpos hxpos
    · exact le_add_of_nonneg_right (Real.rpow_nonneg hxpos.le theta)
    · norm_num
  have hweighted :
      (x + x ^ theta) ^ (-(1 / 2 : ℝ)) *
          (x / localTau X theta - x ^ theta) ≤
        u * x ^ (theta - 1 / 2) := by
    calc
      _ ≤ x ^ (-(1 / 2 : ℝ)) *
          (x / localTau X theta - x ^ theta) := by gcongr
      _ ≤ x ^ (-(1 / 2 : ℝ)) * (u * x ^ theta) := by gcongr
      _ = u * x ^ (theta - 1 / 2) := by
        calc
          x ^ (-(1 / 2 : ℝ)) * (u * x ^ theta) =
              u * (x ^ (-(1 / 2 : ℝ)) * x ^ theta) := by ring
          _ = u * x ^ (theta - 1 / 2) := by
            rw [← Real.rpow_add hxpos]
            congr 2
            ring
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfloor :
      (Nat.floor (Real.log (x + x / localTau X theta) / Real.log 2) : ℝ) ≤
        2 * Real.log x / Real.log 2 := by
    calc
      _ ≤ Real.log (x + x / localTau X theta) / Real.log 2 :=
        Nat.floor_le (div_nonneg hlogbNonneg hlogTwo.le)
      _ ≤ 2 * Real.log x / Real.log 2 := by gcongr
  have hterm3 :
      (Nat.floor (Real.log (x + x / localTau X theta) / Real.log 2) : ℝ) *
          (((x + x ^ theta) ^ (-(1 / 2 : ℝ)) *
              (x / localTau X theta - x ^ theta) + 1) *
            Real.log (x + x / localTau X theta)) ≤
        (4 / Real.log 2) * (u * x ^ (theta - 1 / 2) + 1) * Real.log x ^ 2 := by
    calc
      _ ≤ (2 * Real.log x / Real.log 2) *
          ((u * x ^ (theta - 1 / 2) + 1) * (2 * Real.log x)) := by gcongr
      _ = _ := by ring
  exact add_le_add hterm2 hterm3

/-- Uniform source-level local replacement: for fixed positive `theta` and
local relative width `u`, every point of a sufficiently high multiplicative
interval has replacement loss at most
`(8*u/theta + eta) * x^theta`.  The `eta` term contains all logarithmic,
prime-power, floor, and Brun--Titchmarsh sieve remainders. -/
theorem eventually_abs_localMangoldtSum_sub_short_le
    {theta u eta : ℝ} (htheta : 0 < theta) (hthetaUpper : theta ≤ 1)
    (huLower : 0 ≤ u) (huUpper : u ≤ 1) (heta : 0 < eta) :
    ∀ᶠ X in atTop, ∀ x : ℝ,
      X ≤ x → x ≤ (1 + u) * X →
      |localMangoldtSum X theta x - mangoldtShortSum x theta| ≤
        (8 * u / theta + eta) * x ^ theta := by
  have hsmall := (localReplacementRemainderEnvelope_isLittleO
    (u := u) htheta).bound heta
  obtain ⟨M, hM⟩ := eventually_atTop.1 hsmall
  filter_upwards [eventually_ge_atTop (max (max M 3) 2)] with X hX
  intro x hxLower hxUpper
  have hXone : 1 < X := lt_of_lt_of_le (by norm_num) ((le_max_right (max M 3) 2).trans hX)
  have hxThree : (3 : ℝ) ≤ x :=
    (le_max_right M 3).trans ((le_max_left (max M 3) 2).trans hX) |>.trans hxLower
  have hxM : M ≤ x :=
    (le_max_left M 3).trans ((le_max_left (max M 3) 2).trans hX) |>.trans hxLower
  have hxpos : 0 < x := by linarith
  have henvelopeNorm := hM x hxM
  have henvelopeNonneg : 0 ≤ localReplacementRemainderEnvelope theta u x := by
    unfold localReplacementRemainderEnvelope
    positivity
  have henvelope : localReplacementRemainderEnvelope theta u x ≤ eta * x ^ theta := by
    simpa [Real.norm_of_nonneg henvelopeNonneg,
      Real.norm_of_nonneg (Real.rpow_nonneg hxpos.le theta)] using henvelopeNorm
  have hledger := abs_localMangoldtSum_sub_short_le_power_ledger
    hXone htheta hthetaUpper hxLower hxUpper
  have hrem := localReplacementRemainder_le_envelope
    (zero_lt_one.trans hXone) hxThree htheta hthetaUpper huLower huUpper hxLower hxUpper
  have hd := localScale_sub_le (zero_lt_one.trans hXone) htheta.le hthetaUpper
    hxLower hxUpper
  have hrem' :
      8 * (x / localTau X theta - x ^ theta) / theta +
          6 * (x + x / localTau X theta) ^ (theta / 4) *
            Real.log (x + x / localTau X theta) *
            (1 + (theta / 4) * Real.log (x + x / localTau X theta)) ^ 3 +
          (Nat.floor (Real.log (x + x / localTau X theta) / Real.log 2) : ℝ) *
            (((x + x ^ theta) ^ (-(1 / 2 : ℝ)) *
                (x / localTau X theta - x ^ theta) + 1) *
              Real.log (x + x / localTau X theta)) ≤
        8 * (x / localTau X theta - x ^ theta) / theta +
          localReplacementRemainderEnvelope theta u x := by
    linarith
  calc
    |localMangoldtSum X theta x - mangoldtShortSum x theta| ≤
        8 * (x / localTau X theta - x ^ theta) / theta +
          localReplacementRemainderEnvelope theta u x := hledger.trans hrem'
    _ ≤ 8 * (u * x ^ theta) / theta + eta * x ^ theta := by
      exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num))
        htheta.le) henvelope
    _ = (8 * u / theta + eta) * x ^ theta := by ring

/-- The literal `O(u*x^theta)` form used with `u = delta/J` in the paper.
The constant is explicit and depends only on `theta`; all other losses have
already been absorbed after a threshold that may depend on `theta` and `u`. -/
theorem eventually_abs_localMangoldtSum_sub_short_le_relative
    {theta u : ℝ} (htheta : 0 < theta) (hthetaUpper : theta ≤ 1)
    (hu : 0 < u) (huUpper : u ≤ 1) :
    ∀ᶠ X in atTop, ∀ x : ℝ,
      X ≤ x → x ≤ (1 + u) * X →
      |localMangoldtSum X theta x - mangoldtShortSum x theta| ≤
        (8 / theta + 1) * u * x ^ theta := by
  filter_upwards [eventually_abs_localMangoldtSum_sub_short_le
    htheta hthetaUpper hu.le huUpper hu] with X hX
  intro x hxLower hxUpper
  calc
    |localMangoldtSum X theta x - mangoldtShortSum x theta| ≤
        (8 * u / theta + u) * x ^ theta := hX x hxLower hxUpper
    _ = (8 / theta + 1) * u * x ^ theta := by ring

/-- A fully explicit von-Mangoldt version of the available Brun--Titchmarsh
input.  Prime powers are not discarded: their entire contribution is bounded
by Mathlib's explicit `psi-theta` estimate. -/
theorem mangoldtIntervalSum_le_brunTitchmarsh
    {a y z : ℝ} (ha : 1 ≤ a) (hy : 0 < y) (hz : 1 < z) :
    mangoldtIntervalSum a y ≤
      Real.log (a + y) *
          (2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3) +
        2 * Real.sqrt (a + y) * Real.log (a + y) := by
  classical
  let s : Finset ℕ := Finset.Ioc ⌊a⌋₊ ⌊a + y⌋₊
  let sp : Finset ℕ := s.filter Nat.Prime
  let sn : Finset ℕ := s.filter (fun n => ¬n.Prime)
  have hb : 1 ≤ a + y := by linarith
  have hlog : 0 ≤ Real.log (a + y) := Real.log_nonneg hb
  have hsplit : mangoldtIntervalSum a y =
      (∑ n ∈ sp, Λ n) + ∑ n ∈ sn, Λ n := by
    rw [mangoldtIntervalSum]
    exact (Finset.sum_filter_add_sum_filter_not s Nat.Prime Λ).symm
  have hprimeCard : sp.card ≤ BrunTitchmarsh.primesBetween a (a + y) := by
    exact Finset.card_le_card (prime_part_subset_primesBetween a y)
  have hprime : (∑ n ∈ sp, Λ n) ≤
      BrunTitchmarsh.primesBetween a (a + y) * Real.log (a + y) := by
    calc
      (∑ n ∈ sp, Λ n) = ∑ n ∈ sp, Real.log n := by
        apply Finset.sum_congr rfl
        intro n hn
        exact ArithmeticFunction.vonMangoldt_apply_prime
          (Finset.mem_filter.mp hn).2
      _ ≤ ∑ _n ∈ sp, Real.log (a + y) := by
        apply Finset.sum_le_sum
        intro n hn
        apply Real.log_le_log
        · exact_mod_cast (Finset.mem_filter.mp hn).2.pos
        · exact (Nat.le_floor_iff (by linarith : 0 ≤ a + y)).mp
            (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
      _ = sp.card * Real.log (a + y) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ BrunTitchmarsh.primesBetween a (a + y) *
          Real.log (a + y) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hprimeCard) hlog
  have hnonprimeSubset : sn ⊆
      (Finset.Ioc 0 ⌊a + y⌋₊).filter (fun n => ¬n.Prime) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨?_, hn.2⟩
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨by omega, hn.1.2⟩
  have hnonprime : (∑ n ∈ sn, Λ n) ≤
      Chebyshev.psi (a + y) - Chebyshev.theta (a + y) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    exact Finset.sum_le_sum_of_subset_of_nonneg hnonprimeSubset
      (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hprimeCount := BrunTitchmarsh.primesBetween_le a y z
    (by linarith) hy hz
  rw [hsplit]
  calc
    (∑ n ∈ sp, Λ n) + ∑ n ∈ sn, Λ n ≤
        BrunTitchmarsh.primesBetween a (a + y) * Real.log (a + y) +
          (Chebyshev.psi (a + y) - Chebyshev.theta (a + y)) :=
      add_le_add hprime hnonprime
    _ ≤ (2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3) *
          Real.log (a + y) +
        2 * Real.sqrt (a + y) * Real.log (a + y) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hprimeCount hlog
      · exact Chebyshev.psi_sub_theta_le hb
    _ = _ := by ring

end GafniTao

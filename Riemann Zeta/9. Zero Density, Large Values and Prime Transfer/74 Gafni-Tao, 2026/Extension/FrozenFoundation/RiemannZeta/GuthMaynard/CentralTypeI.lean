import RiemannZeta.GuthMaynard.ExtractSeparated
import RiemannZeta.GuthMaynard.ExponentArithmetic
import RiemannZeta.GuthMaynard.HalaszMontgomery
import RiemannZeta.GuthMaynard.PolynomialPowers
import RiemannZeta.GuthMaynard.Statements

open Complex Filter Asymptotics
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

set_option maxHeartbeats 800000

/-- A single powered-coefficient constant works for every exponent selected
by equation (13.1). This is the finite-uniformity step behind the bound
`2 ≤ k ≤ 101`. -/
theorem uniform_powCoeff_bound_up_to_101
    (hPow : PowCoeffBoundProp) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (k N m : ℕ) (T : ℝ), k ≤ 101 → 0 < m → 1 ≤ T →
        ‖powCoeff N k m T‖ ≤ A * (m : ℝ) ^ δ := by
  classical
  let coefficientConstant (k : ℕ) : ℝ := Classical.choose (hPow k δ hδ)
  have hConstantSpec (k : ℕ) := Classical.choose_spec (hPow k δ hδ)
  let A := 1 + ∑ k ∈ Finset.range 102, coefficientConstant k
  have hA : 1 ≤ A := by
    dsimp [A]
    have hSum : 0 ≤ ∑ k ∈ Finset.range 102, coefficientConstant k := by
      apply Finset.sum_nonneg
      intro k hk
      exact (hConstantSpec k).1.le
    linarith
  refine ⟨A, hA, ?_⟩
  intro k N m T hk hm hT
  have hkMem : k ∈ Finset.range 102 := Finset.mem_range.mpr (by omega)
  have hCkLe : coefficientConstant k ≤ A := by
    dsimp [A]
    have hLe := Finset.single_le_sum (fun i _ => (hConstantSpec i).1.le) hkMem
    linarith
  exact (hConstantSpec k).2 N m T hm hT |>.trans
    (mul_le_mul_of_nonneg_right hCkLe (Real.rpow_nonneg (Nat.cast_nonneg m) _))

/-- Restrict a coefficient sequence to one dyadic block. This is necessary
because the source large-values input bounds all coefficients, whereas a
Dirichlet polynomial only observes coefficients on its own block. -/
noncomputable def restrictToDyadicBlock (M : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc M (2 * M) then a n else 0

@[simp]
theorem dirichletPoly_restrictToDyadicBlock (M : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    dirichletPoly M (restrictToDyadicBlock M a) t = dirichletPoly M a t := by
  unfold dirichletPoly restrictToDyadicBlock dyadicInterval
  apply Finset.sum_congr rfl
  intro n hn
  rw [if_pos hn]

theorem norm_restrictToDyadicBlock_le_one
    (M : ℕ) (a : ℕ → ℂ)
    (hBlock : ∀ n ∈ Finset.Ioc M (2 * M), ‖a n‖ ≤ 1) :
    ∀ n, ‖restrictToDyadicBlock M a n‖ ≤ 1 := by
  intro n
  by_cases hn : n ∈ Finset.Ioc M (2 * M)
  · simpa [restrictToDyadicBlock, hn] using hBlock n hn
  · simp [restrictToDyadicBlock, hn]

theorem dyadic_block_subset_powered_support
    (N k r n : ℕ) (hr : r < k)
    (hn : n ∈ Finset.Ioc (2 ^ r * N ^ k) (2 * (2 ^ r * N ^ k))) :
    n ∈ Finset.Ioc (N ^ k) (2 ^ k * N ^ k) := by
  rw [Finset.mem_Ioc] at hn ⊢
  constructor
  · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (pow_pos (by omega) r)) hn.1
  · have hrSucc : r + 1 ≤ k := by omega
    have hPow : 2 ^ (r + 1) ≤ (2 : ℕ) ^ k :=
      pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 2) hrSucc
    calc
      n ≤ 2 * (2 ^ r * N ^ k) := hn.2
      _ = 2 ^ (r + 1) * N ^ k := by rw [pow_succ]; ring
      _ ≤ 2 ^ k * N ^ k := Nat.mul_le_mul_right _ hPow

/-- The selected powered block has globally unit-bounded restricted
coefficients and exactly the same polynomial values as the unrestricted
normalized powered coefficients. -/
theorem selected_block_coefficients
    (N k r : ℕ) (σ T c A δ : ℝ)
    (hN : 0 < N) (hσ : 0 ≤ σ) (hA : 0 < A) (hδ : 0 < δ)
    (hr : r < k)
    (hCoeff : ∀ m : ℕ, 0 < m →
      ‖powCoeff N k m T‖ ≤ A * (m : ℝ) ^ δ) :
    let M := 2 ^ r * N ^ k
    let a := phaseShiftCoeffs c (normalizedPoweredCoeffs N k σ T A δ)
    (∀ n, ‖restrictToDyadicBlock M a n‖ ≤ 1) ∧
      ∀ u, dirichletPoly M (restrictToDyadicBlock M a) u = dirichletPoly M a u := by
  dsimp only
  constructor
  · apply norm_restrictToDyadicBlock_le_one
    intro n hn
    have hnWide := dyadic_block_subset_powered_support N k r n hr hn
    exact norm_phaseShift_normalizedPoweredCoeffs_le_one N k n σ T c A δ
      hN hσ hA hδ hnWide (hCoeff n (by
        exact lt_trans (pow_pos hN k) (Finset.mem_Ioc.mp hnWide).1))
  · intro u
    exact dirichletPoly_restrictToDyadicBlock _ _ _

/-- Inverting a positive detector threshold converts its normalization loss
and `Q^σ` factor into the exponents used in Section 13.1. -/
theorem inverse_normalized_threshold_sq
    (Q P V σ : ℝ) (hQ : 0 < Q) (hP : 0 < P)
    (hV : Q ^ σ / P ≤ V) :
    V ^ (-2 : ℝ) ≤ P ^ (2 : ℕ) * Q ^ (-2 * σ) := by
  have hLowerPos : 0 < Q ^ σ / P := div_pos (Real.rpow_pos_of_pos hQ _) hP
  calc
    V ^ (-2 : ℝ) ≤ (Q ^ σ / P) ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hLowerPos hV (by norm_num)
    _ = P ^ (2 : ℕ) * Q ^ (-2 * σ) := by
      rw [Real.div_rpow (Real.rpow_nonneg hQ.le _) hP.le,
        Real.rpow_neg (Real.rpow_nonneg hQ.le _) 2,
        Real.rpow_neg hP.le 2]
      have hQexp : Q ^ (-2 * σ) = ((Q ^ σ) ^ (2 : ℕ))⁻¹ := by
        rw [show -2 * σ = -(σ * 2) by ring, Real.rpow_neg hQ.le,
          Real.rpow_mul hQ.le]
        simp only [Real.rpow_two]
      rw [hQexp]
      field_simp [ne_of_gt hP, ne_of_gt (Real.rpow_pos_of_pos hQ σ)]
      simp only [Real.rpow_two]

theorem inverse_normalized_threshold_fourth
    (Q P V σ : ℝ) (hQ : 0 < Q) (hP : 0 < P)
    (hV : Q ^ σ / P ≤ V) :
    V ^ (-4 : ℝ) ≤ P ^ (4 : ℕ) * Q ^ (-4 * σ) := by
  have hVpos : 0 < V :=
    lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos hQ _) hP) hV
  have hSq := inverse_normalized_threshold_sq Q P V σ hQ hP hV
  have hLeftNonneg : 0 ≤ V ^ (-2 : ℝ) := Real.rpow_nonneg hVpos.le _
  have hRightNonneg : 0 ≤ P ^ (2 : ℕ) * Q ^ (-2 * σ) := by positivity
  have hPow := pow_le_pow_left₀ hLeftNonneg hSq 2
  have hVexp : V ^ (-4 : ℝ) = (V ^ (-2 : ℝ)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hVpos.le]
    congr 1
    ring
  have hQexp : Q ^ (-4 * σ) = (Q ^ (-2 * σ)) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    congr 1
    ring
  rw [← hVexp, mul_pow, ← hQexp] at hPow
  norm_num at hPow ⊢
  have hPpow : (P ^ (2 : ℕ)) ^ (2 : ℕ) = P ^ (4 : ℕ) := by ring
  rw [hPpow] at hPow
  exact hPow

/-- The complete normalization loss attached to a fixed powered block. -/
noncomputable def section13Loss (A δ : ℝ) (k : ℕ) (Q T : ℝ) : ℝ :=
  A * (((2 : ℝ) ^ k) * Q) ^ δ * (k : ℝ) * (4 * Real.log T) ^ k

theorem section13_threshold_identity
    (A δ Q T σ : ℝ) (k : ℕ) (hA : 0 < A) (hQ : 0 < Q)
    (hk : 0 < k) (hT : 1 < T) :
    (Q ^ σ * (1 / (4 * Real.log T)) ^ k /
        (A * (((2 : ℝ) ^ k) * Q) ^ δ)) / (k : ℝ) =
      Q ^ σ / section13Loss A δ k Q T := by
  have hLog : 0 < Real.log T := Real.log_pos hT
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hScale : 0 < ((2 : ℝ) ^ k) * Q := by positivity
  unfold section13Loss
  rw [one_div, inv_pow]
  field_simp [ne_of_gt hA, ne_of_gt hQ, ne_of_gt hLog, ne_of_gt hkReal,
    ne_of_gt hScale, ne_of_gt (Real.rpow_pos_of_pos hScale δ)]

lemma eventually_log_pow_le_rpow (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, (Real.log T) ^ n ≤ T ^ η := by
  have hLittle := isLittleO_log_rpow_rpow_atTop (n : ℝ) hη
  filter_upwards [hLittle.eventuallyLE, eventually_ge_atTop (1 : ℝ)] with T hLog hT
  have hLogNonneg : 0 ≤ Real.log T := Real.log_nonneg hT
  have hTNonneg : 0 ≤ T := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLogNonneg _),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hTNonneg _)] at hLog
  rw [← Real.rpow_natCast]
  exact hLog

/-- All coefficient-normalization, block-pigeonhole, and logarithmic losses
are uniform over `2 ≤ k ≤ 101` and cost only an arbitrarily small power of
the height. -/
theorem eventually_section13Loss_fourth_bound
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (k : ℕ) (Q : ℝ),
      2 ≤ k → k ≤ 101 → 1 ≤ Q → Q ≤ T ^ (2 : ℕ) →
      section13Loss A (ε / 100) k Q T ^ (4 : ℕ) ≤
        (A ^ (4 : ℕ) * ((2 : ℝ) ^ 101) ^ (4 * (ε / 100)) *
          (101 : ℝ) ^ (4 : ℕ) * (((4 : ℝ) ^ (202 : ℕ)) ^ (2 : ℕ))) *
          T ^ (ε / 10) := by
  filter_upwards [eventually_log_pow_le_rpow 404 (ε / 100) (by linarith),
    eventually_ge_atTop (Real.exp 1)] with T hLog hT k Q hkLower hkUpper hQOne hQT
  have hTOne : 1 ≤ T := by
    have : (1 : ℝ) < Real.exp 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact (this.trans_le hT).le
  have hLogOne : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) hT
  have hkPow : ((2 : ℝ) ^ k) ≤ (2 : ℝ) ^ 101 := by
    exact pow_le_pow_right₀ (by norm_num) hkUpper
  have hBase : ((2 : ℝ) ^ k) * Q ≤ ((2 : ℝ) ^ 101) * T ^ (2 : ℕ) := by
    gcongr
  have hδ : 0 ≤ ε / 100 := by linarith
  have hRpow := Real.rpow_le_rpow (by positivity) hBase hδ
  have hLogBase : 1 ≤ 4 * Real.log T := by nlinarith
  have hkFour : 4 * k ≤ 404 := by omega
  have hLogNat : (4 * Real.log T) ^ (4 * k) ≤
      (4 * Real.log T) ^ (404 : ℕ) := pow_le_pow_right₀ hLogBase hkFour
  have hLogLoss : ((4 * Real.log T) ^ k) ^ (4 : ℕ) ≤
      (((4 : ℝ) ^ (202 : ℕ)) ^ (2 : ℕ)) * T ^ (ε / 100) := by
    calc
      ((4 * Real.log T) ^ k) ^ (4 : ℕ) =
          (4 * Real.log T) ^ (4 * k) := by rw [← pow_mul]; congr 1; omega
      _ ≤ (4 * Real.log T) ^ (404 : ℕ) := hLogNat
      _ = (((4 : ℝ) ^ (202 : ℕ)) ^ (2 : ℕ)) *
          (Real.log T) ^ (404 : ℕ) := by
        rw [mul_pow]
        congr 1
        rw [← pow_mul]
      _ ≤ (((4 : ℝ) ^ (202 : ℕ)) ^ (2 : ℕ)) * T ^ (ε / 100) := by gcongr
  have hkReal : (k : ℝ) ≤ 101 := by exact_mod_cast hkUpper
  have hkLoss : (k : ℝ) ^ (4 : ℕ) ≤ (101 : ℝ) ^ (4 : ℕ) := by gcongr
  have hRpowFourth : ((((2 : ℝ) ^ k) * Q) ^ (ε / 100)) ^ (4 : ℕ) ≤
      (((2 : ℝ) ^ 101) ^ (4 * (ε / 100))) * T ^ (8 * (ε / 100)) := by
    have hKPower : ((((2 : ℝ) ^ 101) ^ (ε / 100)) ^ (4 : ℕ)) =
        ((2 : ℝ) ^ 101) ^ (4 * (ε / 100)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ) ^ 101)]
      congr 1
      ring
    have hTPower : (((T ^ (2 : ℕ)) ^ (ε / 100)) ^ (4 : ℕ)) =
        T ^ (8 * (ε / 100)) := by
      rw [← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity : 0 ≤ T ^ (2 : ℕ))]
      rw [← Real.rpow_two T,
        ← Real.rpow_mul (le_trans (by norm_num : (0 : ℝ) ≤ 1) hTOne)]
      congr 1
      ring
    calc
      ((((2 : ℝ) ^ k) * Q) ^ (ε / 100)) ^ (4 : ℕ)
          ≤ ((((2 : ℝ) ^ 101) * T ^ (2 : ℕ)) ^ (ε / 100)) ^ (4 : ℕ) := by
            gcongr
      _ = (((2 : ℝ) ^ 101) ^ (4 * (ε / 100))) *
          T ^ (8 * (ε / 100)) := by
        rw [Real.mul_rpow (by positivity) (by positivity), mul_pow]
        rw [hKPower, hTPower]
  have hHeight : T ^ (8 * (ε / 100)) * T ^ (ε / 100) ≤ T ^ (ε / 10) := by
    rw [← Real.rpow_add (by positivity : 0 < T)]
    exact Real.rpow_le_rpow_of_exponent_le hTOne (by linarith)
  unfold section13Loss
  rw [mul_pow, mul_pow, mul_pow]
  calc
    A ^ (4 : ℕ) * ((((2 : ℝ) ^ k * Q) ^ (ε / 100)) ^ (4 : ℕ)) *
          (k : ℝ) ^ (4 : ℕ) * ((4 * Real.log T) ^ k) ^ (4 : ℕ)
        ≤ A ^ (4 : ℕ) *
          (((2 : ℝ) ^ 101) ^ (4 * (ε / 100)) * T ^ (8 * (ε / 100))) *
          (101 : ℝ) ^ (4 : ℕ) *
          ((((4 : ℝ) ^ (202 : ℕ)) ^ (2 : ℕ)) * T ^ (ε / 100)) := by
            gcongr
    _ = (A ^ (4 : ℕ) * ((2 : ℝ) ^ 101) ^ (4 * (ε / 100)) *
          (101 : ℝ) ^ (4 : ℕ) * (((4 : ℝ) ^ (202 : ℕ)) ^ (2 : ℕ))) *
          (T ^ (8 * (ε / 100)) * T ^ (ε / 100)) := by ring
    _ ≤ (A ^ (4 : ℕ) * ((2 : ℝ) ^ 101) ^ (4 * (ε / 100)) *
          (101 : ℝ) ^ (4 : ℕ) * (((4 : ℝ) ^ (202 : ℕ)) ^ (2 : ℕ))) *
          T ^ (ε / 10) := by
            gcongr

/-- Replacing a selected block length `M ≤ 2^101 Q` costs only an absolute
factor in each of the three Guth--Maynard terms. -/
theorem selected_block_large_value_terms_le
    (σ T Q M : ℝ) (hQ : 0 < Q) (hT : 0 ≤ T)
    (hM : 0 ≤ M) (hMUpper : M ≤ (2 : ℝ) ^ 101 * Q) :
    M ^ (2 : ℕ) * Q ^ (-2 * σ) +
        M ^ (18 / 5 : ℝ) * Q ^ (-4 * σ) +
        T * M ^ (12 / 5 : ℝ) * Q ^ (-4 * σ) ≤
      ((2 : ℝ) ^ 101) ^ (4 : ℕ) *
        (Q ^ (2 - 2 * σ) + Q ^ (18 / 5 - 4 * σ) +
          T * Q ^ (12 / 5 - 4 * σ)) := by
  let K : ℝ := (2 : ℝ) ^ 101
  have hKOne : 1 ≤ K := by dsimp [K]; norm_num
  have hKPos : 0 < K := lt_of_lt_of_le zero_lt_one hKOne
  have hTwo : (0 : ℝ) ≤ 2 := by norm_num
  have hEighteen : (0 : ℝ) ≤ 18 / 5 := by norm_num
  have hTwelve : (0 : ℝ) ≤ 12 / 5 := by norm_num
  have hM2 : M ^ (2 : ℕ) ≤ K ^ (4 : ℕ) * Q ^ (2 : ℝ) := by
    calc
      M ^ (2 : ℕ) = M ^ (2 : ℝ) := by rw [Real.rpow_two]
      _ ≤ (K * Q) ^ (2 : ℝ) := Real.rpow_le_rpow hM hMUpper hTwo
      _ = K ^ (2 : ℝ) * Q ^ (2 : ℝ) := Real.mul_rpow hKPos.le hQ.le
      _ ≤ K ^ (4 : ℕ) * Q ^ (2 : ℝ) := by
        gcongr
        rw [Real.rpow_two]
        exact pow_le_pow_right₀ hKOne (by norm_num)
  have hM18 : M ^ (18 / 5 : ℝ) ≤ K ^ (4 : ℕ) * Q ^ (18 / 5 : ℝ) := by
    calc
      M ^ (18 / 5 : ℝ) ≤ (K * Q) ^ (18 / 5 : ℝ) :=
        Real.rpow_le_rpow hM hMUpper hEighteen
      _ = K ^ (18 / 5 : ℝ) * Q ^ (18 / 5 : ℝ) := Real.mul_rpow hKPos.le hQ.le
      _ ≤ K ^ (4 : ℕ) * Q ^ (18 / 5 : ℝ) := by
        gcongr
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hKOne (by norm_num)
  have hM12 : M ^ (12 / 5 : ℝ) ≤ K ^ (4 : ℕ) * Q ^ (12 / 5 : ℝ) := by
    calc
      M ^ (12 / 5 : ℝ) ≤ (K * Q) ^ (12 / 5 : ℝ) :=
        Real.rpow_le_rpow hM hMUpper hTwelve
      _ = K ^ (12 / 5 : ℝ) * Q ^ (12 / 5 : ℝ) := Real.mul_rpow hKPos.le hQ.le
      _ ≤ K ^ (4 : ℕ) * Q ^ (12 / 5 : ℝ) := by
        gcongr
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hKOne (by norm_num)
  dsimp [K] at hM2 hM18 hM12 hKOne hKPos ⊢
  have hCombineTwo : Q ^ (2 : ℝ) * Q ^ (-2 * σ) = Q ^ (2 - 2 * σ) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  have hCombineEighteen : Q ^ (18 / 5 : ℝ) * Q ^ (-4 * σ) =
      Q ^ (18 / 5 - 4 * σ) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  have hCombineTwelve : Q ^ (12 / 5 : ℝ) * Q ^ (-4 * σ) =
      Q ^ (12 / 5 - 4 * σ) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  calc
    M ^ (2 : ℕ) * Q ^ (-2 * σ) +
          M ^ (18 / 5 : ℝ) * Q ^ (-4 * σ) +
          T * M ^ (12 / 5 : ℝ) * Q ^ (-4 * σ)
        ≤ ((2 : ℝ) ^ 101) ^ (4 : ℕ) * Q ^ (2 : ℝ) * Q ^ (-2 * σ) +
          ((2 : ℝ) ^ 101) ^ (4 : ℕ) * Q ^ (18 / 5 : ℝ) * Q ^ (-4 * σ) +
          T * (((2 : ℝ) ^ 101) ^ (4 : ℕ) * Q ^ (12 / 5 : ℝ)) *
            Q ^ (-4 * σ) := by gcongr
    _ = ((2 : ℝ) ^ 101) ^ (4 : ℕ) * (Q ^ (2 : ℝ) * Q ^ (-2 * σ)) +
        ((2 : ℝ) ^ 101) ^ (4 : ℕ) * (Q ^ (18 / 5 : ℝ) * Q ^ (-4 * σ)) +
        T * ((2 : ℝ) ^ 101) ^ (4 : ℕ) *
          (Q ^ (12 / 5 : ℝ) * Q ^ (-4 * σ)) := by ring
    _ = ((2 : ℝ) ^ 101) ^ (4 : ℕ) *
        (Q ^ (2 - 2 * σ) + Q ^ (18 / 5 - 4 * σ) +
          T * Q ^ (12 / 5 - 4 * σ)) := by
      rw [hCombineTwo, hCombineEighteen, hCombineTwelve]
      ring

theorem selected_block_mean_value_terms_le
    (σ T Q M : ℝ) (hQ : 0 < Q) (hT : 0 ≤ T)
    (hM : 0 ≤ M) (hMUpper : M ≤ (2 : ℝ) ^ 101 * Q) :
    (3 * T + M) * M * Q ^ (-2 * σ) ≤
      3 * ((2 : ℝ) ^ 101) ^ (2 : ℕ) *
        (Q ^ (2 - 2 * σ) + T * Q ^ (1 - 2 * σ)) := by
  let K : ℝ := (2 : ℝ) ^ 101
  have hKOne : 1 ≤ K := by dsimp [K]; norm_num
  have hKPos : 0 < K := lt_of_lt_of_le zero_lt_one hKOne
  have hMOne : M ≤ K * Q := hMUpper
  have hM2 : M ^ (2 : ℕ) ≤ K ^ (2 : ℕ) * Q ^ (2 : ℝ) := by
    calc
      M ^ (2 : ℕ) = M ^ (2 : ℝ) := by rw [Real.rpow_two]
      _ ≤ (K * Q) ^ (2 : ℝ) := Real.rpow_le_rpow hM hMOne (by norm_num)
      _ = K ^ (2 : ℝ) * Q ^ (2 : ℝ) := Real.mul_rpow hKPos.le hQ.le
      _ = K ^ (2 : ℕ) * Q ^ (2 : ℝ) := by rw [Real.rpow_two]
  have hKLeK2 : K ≤ K ^ (2 : ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hKOne (by norm_num : 1 ≤ 2)
  have hMLinear : M ≤ K ^ (2 : ℕ) * Q := hMOne.trans (by gcongr)
  have hCombineTwo : Q ^ (2 : ℝ) * Q ^ (-2 * σ) = Q ^ (2 - 2 * σ) := by
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  have hCombineOne : Q * Q ^ (-2 * σ) = Q ^ (1 - 2 * σ) := by
    nth_rewrite 1 [← Real.rpow_one Q]
    rw [← Real.rpow_add hQ]
    congr 1
    ring
  dsimp [K] at hM2 hMLinear hKOne hKPos ⊢
  calc
    (3 * T + M) * M * Q ^ (-2 * σ) =
        (3 * T * M + M ^ (2 : ℕ)) * Q ^ (-2 * σ) := by ring
    _ ≤ (3 * T * (((2 : ℝ) ^ 101) ^ (2 : ℕ) * Q) +
        ((2 : ℝ) ^ 101) ^ (2 : ℕ) * Q ^ (2 : ℝ)) * Q ^ (-2 * σ) := by
      gcongr
    _ = ((2 : ℝ) ^ 101) ^ (2 : ℕ) * (Q ^ (2 : ℝ) * Q ^ (-2 * σ)) +
        3 * T * ((2 : ℝ) ^ 101) ^ (2 : ℕ) *
          (Q * Q ^ (-2 * σ)) := by ring
    _ = ((2 : ℝ) ^ 101) ^ (2 : ℕ) * Q ^ (2 - 2 * σ) +
        3 * T * ((2 : ℝ) ^ 101) ^ (2 : ℕ) * Q ^ (1 - 2 * σ) := by
      rw [hCombineTwo, hCombineOne]
    _ ≤ 3 * ((2 : ℝ) ^ 101) ^ (2 : ℕ) *
        (Q ^ (2 - 2 * σ) + T * Q ^ (1 - 2 * σ)) := by
      have hFirst : 0 ≤ ((2 : ℝ) ^ 101) ^ (2 : ℕ) * Q ^ (2 - 2 * σ) := by
        positivity
      nlinarith

/-- The central Type-I positive-slab estimate required by the zero-density
transfer. -/
def TypeIPositiveSlabBoundProp : Prop :=
  ∀ σ : ℝ, 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    EpsilonPowerBound
      (fun T => (typeIZeroCount σ T (2 * T) T : ℝ))
      (fun T => T ^ final_exponent σ)

/-- Section 13.1: extraction, bounded powering, fixed-block pigeonholing,
the Guth--Maynard/mean-value dichotomy, and exponent arithmetic prove the
central Type-I slab estimate from the individually named source inputs. -/
theorem typeIPositiveSlabBound_of_section13_inputs
    (hLargeValues : GuthMaynardLargeValues)
    (hMeanValue : MontgomeryMeanValue)
    (hExtract : ExtractSeparatedTarget)
    (hPow : PowCoeffBoundProp) :
    TypeIPositiveSlabBoundProp := by
  intro σ hσLower hσUpper ε hε
  let η := ε / 100
  let δ := ε / 100
  have hη : 0 < η := by dsimp [η]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨A, hAOne, hCoeff⟩ := uniform_powCoeff_bound_up_to_101 hPow δ hδ
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one hAOne
  obtain ⟨CE, TE, hCE, hTE, hExtractAll⟩ := hExtract η hη
  obtain ⟨CG, TG, hCG, hTG, hLarge⟩ :=
    guthMaynardLargeValues_neg hLargeValues η hη
  obtain ⟨CM, hCM, hMean⟩ := halasz_montgomery_lemma_of_mean_value hMeanValue
  have hScaleEvent := eventually_detectorScaleUpper_sq_le σ hσLower hσUpper
  have hLossEvent := eventually_section13Loss_fourth_bound A ε hA hε
  let lossConstant := A ^ (4 : ℕ) * ((2 : ℝ) ^ 101) ^ (4 * (ε / 100)) *
    (101 : ℝ) ^ (4 : ℕ) * (((4 : ℝ) ^ (202 : ℕ)) ^ (2 : ℕ))
  let totalConstant := CE * 101 * lossConstant *
    (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
      CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ))
  have hLossConstant : 0 ≤ lossConstant := by
    dsimp [lossConstant]
    positivity
  apply IsBigO.of_bound totalConstant
  filter_upwards [hScaleEvent, hLossEvent,
    eventually_ge_atTop (max TE (max TG (Real.exp 2)))] with
      T hScale hLoss hT
  have hTE' : TE ≤ T := le_trans (le_max_left _ _) hT
  have hTG' : TG ≤ 3 * T := by
    have : TG ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_right TE _) hT)
    linarith
  have hTExp : Real.exp 2 ≤ T :=
    le_trans (le_max_right TG _) (le_trans (le_max_right TE _) hT)
  have hTOne : 1 ≤ T := by
    have : (1 : ℝ) < Real.exp 2 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact (this.trans_le hTExp).le
  have hTStrict : 1 < T := by
    have : (1 : ℝ) < Real.exp 2 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact this.trans_le hTExp
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTOne
  have hThreeT : 1 ≤ 3 * T := by nlinarith
  have hLogPos : 0 < Real.log T := Real.log_pos hTStrict
  have hFinalNonneg := final_exponent_nonneg σ hσLower hσUpper
  have hTargetNonneg : 0 ≤ T ^ ε * |T ^ final_exponent σ| := by positivity
  rcases hExtractAll σ T hσLower hσUpper hTE' with hZero | hData
  · simp only [hZero, Nat.cast_zero, abs_zero, norm_zero]
    positivity
  · rcases hData with ⟨W, j, H, c, hj, hHNonneg, hHEps, hHT, hc,
      hWSeparated, hWInterval, hDetector, hCoeffNorm, hTypeCount⟩
    have hjScale := (mem_admissibleDyadicIndices T j).mp hj
    let N₀ : ℕ := 2 ^ j
    have hN₀Pos : 0 < N₀ := pow_pos (by omega) j
    have hN₀Real : (N₀ : ℝ) = (2 : ℝ) ^ j := by simp [N₀]
    have hN₀One : 1 < (N₀ : ℝ) := by
      rw [hN₀Real]
      exact lt_of_lt_of_le (Real.one_lt_rpow hTStrict (by norm_num)) hjScale.1
    have hN₀UpperSq : (N₀ : ℝ) ^ (2 : ℝ) ≤
        T ^ (15 / (6 + 10 * σ)) := by
      rw [hN₀Real, Real.rpow_two]
      exact (pow_le_pow_left₀ (by positivity) hjScale.2 2).trans hScale
    obtain ⟨k, hkLower, hkUpper, hEquationLower, hEquationUpper⟩ :=
      k_selection (N₀ : ℝ) T σ hN₀One hTStrict hσLower
        (by simpa [hN₀Real] using hjScale.1) hN₀UpperSq
    have hkPos : 0 < k := by omega
    let Qn : ℕ := N₀ ^ k
    let Q : ℝ := Qn
    have hQnPos : 0 < Qn := pow_pos hN₀Pos k
    have hQ : 0 < Q := by
      change (0 : ℝ) < (Qn : ℝ)
      exact_mod_cast hQnPos
    have hQOne : 1 ≤ Q := by
      change (1 : ℝ) ≤ (Qn : ℝ)
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hQnPos.ne')
    have hQFormula : Q = (N₀ : ℝ) ^ (k : ℝ) := by
      dsimp [Q, Qn]
      rw [Nat.cast_pow, Real.rpow_natCast]
    have hEquationLowerQ : T ^ (10 / (6 + 10 * σ)) ≤ Q := by
      simpa [hQFormula] using hEquationLower
    have hEquationUpperQ : Q ≤ T ^ (15 / (6 + 10 * σ)) := by
      simpa [hQFormula] using hEquationUpper
    have hUpperExponent : 15 / (6 + 10 * σ) ≤ 2 := by
      have hd := denom_pos σ hσLower
      rw [div_le_iff₀ hd]
      linarith
    have hQTSq : Q ≤ T ^ (2 : ℕ) := by
      calc
        Q ≤ T ^ (15 / (6 + 10 * σ)) := hEquationUpperQ
        _ ≤ T ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hTOne hUpperExponent
        _ = T ^ (2 : ℕ) := by rw [Real.rpow_two]
    let L : ℝ := 1 / (4 * Real.log T)
    have hL : 0 < L := by dsimp [L]; positivity
    let a := phaseShiftCoeffs c (normalizedPoweredCoeffs N₀ k σ T A δ)
    have hDenom : 0 < A * ((2 ^ k * N₀ ^ k : ℕ) : ℝ) ^ δ := by positivity
    have hWide : ∀ u ∈ W,
        Q ^ σ * L ^ k / (A * ((2 ^ k * N₀ ^ k : ℕ) : ℝ) ^ δ) ≤
          ‖wideDirichletPoly Qn k a u‖ := by
      intro u hu
      have hDetect : L ≤ ‖detectPoly N₀ (σ + I * (u + c)) T‖ := by
        have hArg : (σ : ℂ) + I * ((u : ℂ) + (c : ℂ)) =
            (σ : ℂ) + I * (((u + c : ℝ) : ℂ)) := by push_cast; ring
        rw [hArg, detectPoly_translate]
        simpa [L, N₀] using hDetector u hu
      have hRaw := normalized_powered_wide_lower N₀ k σ T c u A δ L
        hN₀Pos hkPos hL.le hDenom hDetect
      simpa [Q, Qn, a] using hRaw
    obtain ⟨r, hr, W', hW'Subset, hWCard, hBlockValues⟩ :=
      exists_dyadic_block_and_subset Qn k a W
        (Q ^ σ * L ^ k / (A * ((2 ^ k * N₀ ^ k : ℕ) : ℝ) ^ δ))
        hkPos hWide
    have hrLt : r < k := Finset.mem_range.mp hr
    let M : ℕ := 2 ^ r * Qn
    let b := restrictToDyadicBlock M a
    have hCoeffK : ∀ m : ℕ, 0 < m →
        ‖powCoeff N₀ k m T‖ ≤ A * (m : ℝ) ^ δ :=
      fun m hm => hCoeff k N₀ m T hkUpper hm hTOne
    have hSelected := selected_block_coefficients N₀ k r σ T c A δ hN₀Pos
      (by linarith) hA hδ hrLt hCoeffK
    have hb : ∀ n, ‖b n‖ ≤ 1 := by simpa [M, b, a] using hSelected.1
    have hBlockValuesB : ∀ u ∈ W',
        (Q ^ σ * L ^ k /
          (A * ((2 ^ k * N₀ ^ k : ℕ) : ℝ) ^ δ)) / (k : ℝ) ≤
          ‖dirichletPoly M b u‖ := by
      intro u hu
      rw [hSelected.2 u]
      simpa [M, a] using hBlockValues u hu
    have hCastScale : ((2 ^ k * N₀ ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k * Q := by
      simp [Q, Qn, Nat.cast_mul, Nat.cast_pow]
    have hThreshold : ∀ u ∈ W', Q ^ σ / section13Loss A δ k Q T ≤
        ‖dirichletPoly M b u‖ := by
      intro u hu
      rw [← section13_threshold_identity A δ Q T σ k hA hQ hkPos
        hTStrict]
      rw [hCastScale] at hBlockValuesB
      simpa [L] using hBlockValuesB u hu
    have hPPos : 0 < section13Loss A δ k Q T := by
      unfold section13Loss
      positivity
    have hPOne : 1 ≤ section13Loss A δ k Q T := by
      have hLogOne : 1 ≤ 4 * Real.log T := by
        have hExpOne : Real.exp 1 ≤ T :=
          le_trans (by norm_num : Real.exp 1 ≤ Real.exp 2) hTExp
        have hLogRaw := Real.log_le_log (Real.exp_pos 1) hExpOne
        have hLog : 1 ≤ Real.log T := by simpa using hLogRaw
        nlinarith
      have hScaleOne : 1 ≤ ((2 : ℝ) ^ k) * Q := by
        have hTwoPow : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
          simpa only [pow_zero] using
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le k))
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (2 : ℝ) ^ k * Q :=
            mul_le_mul hTwoPow hQOne (by norm_num) (by positivity)
      have hScaleRpow : 1 ≤ (((2 : ℝ) ^ k) * Q) ^ δ :=
        Real.one_le_rpow hScaleOne hδ.le
      have hkReal : (1 : ℝ) ≤ k := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hkLower)
      have hLogPow : 1 ≤ (4 * Real.log T) ^ k :=
        pow_le_pow_right₀ hLogOne (Nat.zero_le k)
      unfold section13Loss
      calc
        (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
        _ ≤ A * (((2 : ℝ) ^ k * Q) ^ δ) * (k : ℝ) *
            (4 * Real.log T) ^ k := by gcongr
    have hInv2 := inverse_normalized_threshold_sq Q (section13Loss A δ k Q T)
      (Q ^ σ / section13Loss A δ k Q T) σ hQ hPPos le_rfl
    have hInv4 := inverse_normalized_threshold_fourth Q (section13Loss A δ k Q T)
      (Q ^ σ / section13Loss A δ k Q T) σ hQ hPPos le_rfl
    have hMPos : 0 < M := by dsimp [M]; positivity
    have hMNonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hMUpper : (M : ℝ) ≤ (2 : ℝ) ^ 101 * Q := by
      have hrLe : r ≤ 101 := le_trans hrLt.le hkUpper
      have hp : (2 : ℕ) ^ r ≤ (2 : ℕ) ^ 101 :=
        pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 2) hrLe
      have hpReal : ((2 : ℕ) ^ r : ℝ) ≤ ((2 : ℕ) ^ 101 : ℝ) := by
        exact_mod_cast hp
      dsimp [M]
      push_cast
      change (2 : ℝ) ^ r * Q ≤ (2 : ℝ) ^ 101 * Q
      exact mul_le_mul_of_nonneg_right hpReal hQ.le
    have hLossNow := hLoss k Q hkLower hkUpper hQOne hQTSq
    have hW'Separated : IsSeparated 1 W' :=
      fun x hx y hy hxy => hWSeparated x (hW'Subset hx) y (hW'Subset hy) hxy
    have hW'Interval : InBaseInterval (3 * T) W' :=
      fun u hu => hWInterval u (hW'Subset hu)
    have hTypeToSubset : (typeIZeroCount σ T (2 * T) T : ℝ) ≤
        CE * T ^ η * (k : ℝ) * (W'.card : ℝ) := by
      calc
        _ ≤ CE * T ^ η * (W.card : ℝ) := hTypeCount
        _ ≤ CE * T ^ η * ((k : ℝ) * (W'.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hWCard (by positivity)
        _ = CE * T ^ η * (k : ℝ) * (W'.card : ℝ) := by ring
    have hBranch : (W'.card : ℝ) ≤
        lossConstant *
          (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
            CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) *
          T ^ (ε / 10 + η) * T ^ final_exponent σ := by
      by_cases hSmall : Q ≤ T ^ alpha σ
      · have hVPos : 0 < Q ^ σ / section13Loss A δ k Q T := by positivity
        have hRaw := hLarge M (Q ^ σ / section13Loss A δ k Q T) (3 * T) b W'
          hMPos hTG' hVPos hb hW'Separated hW'Interval hThreshold
        have hInv2Le4 : (section13Loss A δ k Q T) ^ (2 : ℕ) * Q ^ (-2 * σ) ≤
            (section13Loss A δ k Q T) ^ (4 : ℕ) * Q ^ (-2 * σ) := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ hPOne (by norm_num)) (Real.rpow_nonneg hQ.le _)
        have hRawTerms :
            (M : ℝ) ^ (2 : ℕ) *
                (Q ^ σ / section13Loss A δ k Q T) ^ (-2 : ℝ) +
              (M : ℝ) ^ (18 / 5 : ℝ) *
                (Q ^ σ / section13Loss A δ k Q T) ^ (-4 : ℝ) +
              3 * T * (M : ℝ) ^ (12 / 5 : ℝ) *
                (Q ^ σ / section13Loss A δ k Q T) ^ (-4 : ℝ) ≤
            (section13Loss A δ k Q T) ^ (4 : ℕ) *
              ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 * T ^ final_exponent σ := by
          calc
            _ ≤ (M : ℝ) ^ (2 : ℕ) *
                  ((section13Loss A δ k Q T) ^ (2 : ℕ) * Q ^ (-2 * σ)) +
                (M : ℝ) ^ (18 / 5 : ℝ) *
                  ((section13Loss A δ k Q T) ^ (4 : ℕ) * Q ^ (-4 * σ)) +
                3 * T * (M : ℝ) ^ (12 / 5 : ℝ) *
                  ((section13Loss A δ k Q T) ^ (4 : ℕ) * Q ^ (-4 * σ)) := by
              gcongr
            _ ≤ (M : ℝ) ^ (2 : ℕ) *
                  ((section13Loss A δ k Q T) ^ (4 : ℕ) * Q ^ (-2 * σ)) +
                (M : ℝ) ^ (18 / 5 : ℝ) *
                  ((section13Loss A δ k Q T) ^ (4 : ℕ) * Q ^ (-4 * σ)) +
                3 * T * (M : ℝ) ^ (12 / 5 : ℝ) *
                  ((section13Loss A δ k Q T) ^ (4 : ℕ) * Q ^ (-4 * σ)) := by
              gcongr
            _ = (section13Loss A δ k Q T) ^ (4 : ℕ) *
                ((M : ℝ) ^ (2 : ℕ) * Q ^ (-2 * σ) +
                  (M : ℝ) ^ (18 / 5 : ℝ) * Q ^ (-4 * σ) +
                  3 * T * (M : ℝ) ^ (12 / 5 : ℝ) * Q ^ (-4 * σ)) := by ring
            _ ≤ (section13Loss A δ k Q T) ^ (4 : ℕ) *
                (((2 : ℝ) ^ 101) ^ (4 : ℕ) *
                  (Q ^ (2 - 2 * σ) + Q ^ (18 / 5 - 4 * σ) +
                    3 * T * Q ^ (12 / 5 - 4 * σ))) := by
              gcongr
              exact selected_block_large_value_terms_le σ (3 * T) Q M hQ
                (by positivity) hMNonneg hMUpper
            _ ≤ (section13Loss A δ k Q T) ^ (4 : ℕ) *
                ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 * T ^ final_exponent σ := by
              have hFirst := large_values_first_term_le σ T Q hσLower hσUpper hTOne hQ.le
                hEquationUpperQ
              have hSecond := large_values_second_term_le σ T Q hσLower hσUpper
                hTOne hQ.le hSmall
              have hThird := large_values_third_term_le σ T Q hσLower hTOne hEquationLowerQ
              have hTerms5 : Q ^ (2 - 2 * σ) + Q ^ (18 / 5 - 4 * σ) +
                  3 * T * Q ^ (12 / 5 - 4 * σ) ≤ 5 * T ^ final_exponent σ := by
                linarith
              calc
                (section13Loss A δ k Q T) ^ (4 : ℕ) *
                    (((2 : ℝ) ^ 101) ^ (4 : ℕ) *
                      (Q ^ (2 - 2 * σ) + Q ^ (18 / 5 - 4 * σ) +
                        3 * T * Q ^ (12 / 5 - 4 * σ))) =
                    ((section13Loss A δ k Q T) ^ (4 : ℕ) *
                      ((2 : ℝ) ^ 101) ^ (4 : ℕ)) *
                      (Q ^ (2 - 2 * σ) + Q ^ (18 / 5 - 4 * σ) +
                        3 * T * Q ^ (12 / 5 - 4 * σ)) := by ring
                _ ≤ ((section13Loss A δ k Q T) ^ (4 : ℕ) *
                      ((2 : ℝ) ^ 101) ^ (4 : ℕ)) *
                      (5 * T ^ final_exponent σ) :=
                    mul_le_mul_of_nonneg_left hTerms5 (by positivity)
                _ = (section13Loss A δ k Q T) ^ (4 : ℕ) *
                    ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 *
                      T ^ final_exponent σ := by ring
        calc
          (W'.card : ℝ) ≤ CG * (3 * T) ^ η *
              ((M : ℝ) ^ (2 : ℕ) *
                  (Q ^ σ / section13Loss A δ k Q T) ^ (-2 : ℝ) +
                (M : ℝ) ^ (18 / 5 : ℝ) *
                  (Q ^ σ / section13Loss A δ k Q T) ^ (-4 : ℝ) +
                3 * T * (M : ℝ) ^ (12 / 5 : ℝ) *
                  (Q ^ σ / section13Loss A δ k Q T) ^ (-4 : ℝ)) := hRaw
          _ ≤ CG * (3 * T) ^ η *
              ((section13Loss A δ k Q T) ^ (4 : ℕ) *
                ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 * T ^ final_exponent σ) := by
            gcongr
          _ ≤ lossConstant *
              (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) *
              T ^ (ε / 10 + η) * T ^ final_exponent σ := by
            have hCore : CG * 3 ^ η *
                (section13Loss A δ k Q T ^ (4 : ℕ)) *
                ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 ≤
              lossConstant *
                (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                  CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) * T ^ (ε / 10) := by
              calc
                _ ≤ CG * 3 ^ η * (lossConstant * T ^ (ε / 10)) *
                    ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 := by gcongr
                _ ≤ lossConstant *
                    (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                      CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) * T ^ (ε / 10) := by
                  have hExtra : 0 ≤ CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ) := by positivity
                  calc
                    CG * 3 ^ η * (lossConstant * T ^ (ε / 10)) *
                        ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 =
                      (lossConstant * T ^ (ε / 10)) *
                        (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5) := by ring
                    _ ≤ (lossConstant * T ^ (ε / 10)) *
                        (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                          CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) :=
                      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hExtra) (by positivity)
                    _ = lossConstant *
                        (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                          CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) * T ^ (ε / 10) := by ring
            rw [Real.mul_rpow (by norm_num) hTpos.le, Real.rpow_add hTpos]
            calc
              CG * (3 ^ η * T ^ η) *
                  (section13Loss A δ k Q T ^ (4 : ℕ) *
                    ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 * T ^ final_exponent σ) =
                (CG * 3 ^ η * section13Loss A δ k Q T ^ (4 : ℕ) *
                  ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5) * T ^ η *
                  T ^ final_exponent σ := by ring
              _ ≤ (lossConstant *
                  (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                    CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) * T ^ (ε / 10)) *
                  T ^ η * T ^ final_exponent σ := by gcongr
              _ = lossConstant *
                  (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                    CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) *
                  (T ^ (ε / 10) * T ^ η) * T ^ final_exponent σ := by ring
      · have hLargeQ : T ^ alpha σ ≤ Q := (not_le.mp hSmall).le
        have hVPos : 0 < Q ^ σ / section13Loss A δ k Q T := by positivity
        have hRaw := hMean M (3 * T) (Q ^ σ / section13Loss A δ k Q T)
          W' b hMPos hThreeT hVPos hW'Separated hW'Interval hThreshold
        have hCoeffSum : ∑ n ∈ Finset.Ioc M (2 * M), ‖b n‖ ^ 2 ≤ (M : ℝ) := by
          calc
            _ ≤ ∑ _n ∈ Finset.Ioc M (2 * M), (1 : ℝ) := by
              gcongr with n hn
              nlinarith [hb n, norm_nonneg (b n)]
            _ = (M : ℝ) := by
              simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
              norm_cast
              omega
        have hMeanTerms := mean_value_terms_le σ T Q hσLower hσUpper hTOne hQ.le
          hEquationUpperQ hLargeQ
        calc
          (W'.card : ℝ) ≤ CM * (3 * T + (M : ℝ)) *
              (Q ^ σ / section13Loss A δ k Q T) ^ (-2 : ℝ) *
              ∑ n ∈ Finset.Ioc M (2 * M), ‖b n‖ ^ 2 := hRaw
          _ ≤ CM * (3 * T + (M : ℝ)) *
              ((section13Loss A δ k Q T) ^ (2 : ℕ) * Q ^ (-2 * σ)) *
              (M : ℝ) := by
            gcongr
          _ = CM * ((section13Loss A δ k Q T) ^ (2 : ℕ) *
              ((3 * T + (M : ℝ)) * (M : ℝ) * Q ^ (-2 * σ))) := by ring
          _ ≤ CM * ((section13Loss A δ k Q T) ^ (4 : ℕ) *
              (3 * ((2 : ℝ) ^ 101) ^ (2 : ℕ) *
                (Q ^ (2 - 2 * σ) + T * Q ^ (1 - 2 * σ)))) := by
            have hP24 : section13Loss A δ k Q T ^ (2 : ℕ) ≤
                section13Loss A δ k Q T ^ (4 : ℕ) :=
              pow_le_pow_right₀ hPOne (by norm_num)
            have hBlockMean := selected_block_mean_value_terms_le σ T Q M hQ
              hTpos.le hMNonneg hMUpper
            calc
              CM * (section13Loss A δ k Q T ^ (2 : ℕ) *
                  ((3 * T + (M : ℝ)) * (M : ℝ) * Q ^ (-2 * σ))) ≤
                  CM * (section13Loss A δ k Q T ^ (4 : ℕ) *
                    ((3 * T + (M : ℝ)) * (M : ℝ) * Q ^ (-2 * σ))) := by
                    gcongr
              _ ≤ CM * (section13Loss A δ k Q T ^ (4 : ℕ) *
                  (3 * ((2 : ℝ) ^ 101) ^ (2 : ℕ) *
                    (Q ^ (2 - 2 * σ) + T * Q ^ (1 - 2 * σ)))) := by
                    gcongr
          _ ≤ CM * ((section13Loss A δ k Q T) ^ (4 : ℕ) *
              (6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ) * T ^ final_exponent σ)) := by
            have hFactor : 0 ≤ CM * section13Loss A δ k Q T ^ (4 : ℕ) *
                (3 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) := by positivity
            calc
              CM * (section13Loss A δ k Q T ^ (4 : ℕ) *
                  (3 * ((2 : ℝ) ^ 101) ^ (2 : ℕ) *
                    (Q ^ (2 - 2 * σ) + T * Q ^ (1 - 2 * σ)))) =
                  (CM * section13Loss A δ k Q T ^ (4 : ℕ) *
                    (3 * ((2 : ℝ) ^ 101) ^ (2 : ℕ))) *
                    (Q ^ (2 - 2 * σ) + T * Q ^ (1 - 2 * σ)) := by ring
              _ ≤ (CM * section13Loss A δ k Q T ^ (4 : ℕ) *
                    (3 * ((2 : ℝ) ^ 101) ^ (2 : ℕ))) *
                    (2 * T ^ final_exponent σ) :=
                  mul_le_mul_of_nonneg_left hMeanTerms hFactor
              _ = CM * (section13Loss A δ k Q T ^ (4 : ℕ) *
                  (6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ) * T ^ final_exponent σ)) := by ring
          _ ≤ lossConstant *
              (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) *
              T ^ (ε / 10 + η) * T ^ final_exponent σ := by
            have hEtaOne : 1 ≤ T ^ η := Real.one_le_rpow hTOne hη.le
            rw [Real.rpow_add hTpos]
            have hCore : CM * section13Loss A δ k Q T ^ (4 : ℕ) *
                (6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) ≤
              lossConstant *
                (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                  CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) *
                (T ^ (ε / 10) * T ^ η) := by
              calc
                _ ≤ CM * (lossConstant * T ^ (ε / 10)) *
                    (6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) := by gcongr
                _ ≤ lossConstant *
                    (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                      CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) *
                    (T ^ (ε / 10) * T ^ η) := by
                  have hExtra : 0 ≤ CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 := by
                    positivity
                  calc
                    CM * (lossConstant * T ^ (ε / 10)) *
                        (6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) =
                      (lossConstant * T ^ (ε / 10)) *
                        (CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) := by ring
                    _ ≤ (lossConstant * T ^ (ε / 10)) *
                        (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                          CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) :=
                      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hExtra)
                        (mul_nonneg hLossConstant (Real.rpow_nonneg hTpos.le _))
                    _ ≤ (lossConstant * T ^ (ε / 10)) *
                        (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                          CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) * T ^ η := by
                      let Z := (lossConstant * T ^ (ε / 10)) *
                        (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                          CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ))
                      have hZ : 0 ≤ Z := by dsimp [Z]; positivity
                      change Z ≤ Z * T ^ η
                      calc
                        Z = Z * 1 := by ring
                        _ ≤ Z * T ^ η := mul_le_mul_of_nonneg_left hEtaOne hZ
                    _ = lossConstant *
                        (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                          CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) *
                        (T ^ (ε / 10) * T ^ η) := by ring
            calc
              CM * (section13Loss A δ k Q T ^ (4 : ℕ) *
                  (6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ) * T ^ final_exponent σ)) =
                (CM * section13Loss A δ k Q T ^ (4 : ℕ) *
                  (6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ))) * T ^ final_exponent σ := by ring
              _ ≤ (lossConstant *
                  (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                    CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) *
                  (T ^ (ε / 10) * T ^ η)) * T ^ final_exponent σ := by gcongr
              _ = lossConstant *
                  (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                    CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) *
                  (T ^ (ε / 10) * T ^ η) * T ^ final_exponent σ := by ring
    have hFinalPoint : (typeIZeroCount σ T (2 * T) T : ℝ) ≤
        totalConstant * (T ^ ε * |T ^ final_exponent σ|) := by
      have hkReal : (k : ℝ) ≤ 101 := by exact_mod_cast hkUpper
      have hPre := hTypeToSubset.trans (mul_le_mul_of_nonneg_left hBranch (by positivity))
      rw [abs_of_nonneg (Real.rpow_nonneg hTpos.le _)]
      have hExponent : η + (ε / 10 + η) ≤ ε := by dsimp [η]; linarith
      have hPowers : T ^ η * T ^ (ε / 10 + η) ≤ T ^ ε := by
        rw [← Real.rpow_add hTpos]
        exact Real.rpow_le_rpow_of_exponent_le hTOne hExponent
      let D := CE * 101 * lossConstant *
        (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
          CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ))
      have hD : 0 ≤ D := by dsimp [D]; positivity
      calc
        (typeIZeroCount σ T (2 * T) T : ℝ) ≤
            CE * T ^ η * (k : ℝ) *
              (lossConstant *
                (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                  CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) *
                T ^ (ε / 10 + η) * T ^ final_exponent σ) := hPre
        _ ≤ CE * T ^ η * 101 *
              (lossConstant *
                (CG * 3 ^ η * ((2 : ℝ) ^ 101) ^ (4 : ℕ) * 5 +
                  CM * 6 * ((2 : ℝ) ^ 101) ^ (2 : ℕ)) *
                T ^ (ε / 10 + η) * T ^ final_exponent σ) := by gcongr
        _ = D * (T ^ η * T ^ (ε / 10 + η)) * T ^ final_exponent σ := by
          dsimp [D]
          ring
        _ ≤ D * T ^ ε * T ^ final_exponent σ := by
          gcongr
        _ = totalConstant * (T ^ ε * T ^ final_exponent σ) := by
          dsimp [D, totalConstant]
          ring
    simp only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hTargetNonneg]
    rw [abs_of_nonneg (show 0 ≤ (typeIZeroCount σ T (2 * T) T : ℝ) from
      Nat.cast_nonneg _)]
    exact hFinalPoint

end RiemannZeta.GuthMaynard

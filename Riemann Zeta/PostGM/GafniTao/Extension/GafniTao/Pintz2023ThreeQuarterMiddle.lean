import GafniTao.Pintz2023CorollaryOne
import GafniTao.PintzNearOneZetaMiddle

/-!
# Pintz's coefficient-one-half bound on conductor-scale blocks

The off-diagonal Gram calculation reaches real part `3/4`.  On
`1 <= log t / log N <= 3/2` the elementary B-process is already strong
enough after the Dirichlet weight is restored.  On
`3/2 <= log t / log N <= 2` we use the literal order-three
Heath--Brown derivative estimate and compare each of its three monomials
with the coefficient-one-half zeta target.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Pintz's equation-(3.1) block with `xi = 1 - sigma` is exactly the
ordinary zero-shift Dirichlet block used by the zeta decomposition. -/
theorem pintz2023WeightedBlock_one_sub_eq_ford
    (sigma : ℝ) (N R : ℕ) (t : ℝ) :
    pintz2023WeightedBlock (1 - sigma) N R t =
      fordShiftedWeightedBlock sigma N R 0 t := by
  unfold pintz2023WeightedBlock fordShiftedWeightedBlock
  simp only [sub_sub_cancel, add_zero]
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hphase :
      fordShiftedLogPhase n 0 t =
        unitaryPhase (logarithmicPhase t n) := by
    unfold fordShiftedLogPhase unitaryPhase logarithmicPhase
    simp only [add_zero, ofReal_neg, ofReal_mul]
    apply congrArg Complex.exp
    ring
  rw [hphase, unitaryPhase_logarithmicPhase_eq_cpow t n hnPos]

/-- The only nonlinear inequality needed in the order-three conductor
range.  Writing `r = sqrt u`, it is the nonnegativity of
`9 r^3 - 12 r^2 + 2` on `[0,1/2]`. -/
theorem pintz_threeQuarter_orderThree_core
    {u : ℝ} (hu : 0 ≤ u) (huUpper : u ≤ 1 / 4) :
    u - 1 / 6 ≤ (3 / 4 : ℝ) * u ^ (3 / 2 : ℝ) := by
  let r : ℝ := Real.sqrt u
  have hr : 0 ≤ r := Real.sqrt_nonneg u
  have hrUpper : r ≤ 1 / 2 := by
    have hsqrt := Real.sqrt_le_sqrt huUpper
    norm_num at hsqrt ⊢
    simpa [r] using hsqrt
  have hrsq : r ^ 2 = u := by
    dsimp only [r]
    exact Real.sq_sqrt hu
  have hrcube : r ^ 3 = u ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * (3 : ℕ) by norm_num,
      Real.rpow_mul_natCast]
    rw [show u ^ (1 / 2 : ℝ) = Real.sqrt u by
      exact (Real.sqrt_eq_rpow u).symm]
    exact hu
  have hrsqLe : r ^ 2 ≤ r / 2 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrUpper)]
  have hbracket :
      9 * (r ^ 2 + r / 2 + 1 / 4) - 12 * (r + 1 / 2) ≤ 0 := by
    nlinarith
  have hfactor :
      9 * r ^ 3 - 12 * r ^ 2 + 2 - 1 / 8 =
        (r - 1 / 2) *
          (9 * (r ^ 2 + r / 2 + 1 / 4) - 12 * (r + 1 / 2)) := by
    ring
  have hprod : 0 ≤
      (r - 1 / 2) *
        (9 * (r ^ 2 + r / 2 + 1 / 4) - 12 * (r + 1 / 2)) :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hrUpper) hbracket
  rw [← hrcube, ← hrsq]
  nlinarith [hfactor]

/-- All three order-three derivative-test exponents are dominated by the
target on `3/2 <= tau <= 2`. -/
theorem pintz_threeQuarter_orderThree_exponents
    {sigma epsilon tau : ℝ}
    (hsigmaUpper : sigma ≤ 1) (hsigmaLower : 3 / 4 ≤ sigma)
    (hepsilon : 0 ≤ epsilon)
    (htauLower : 3 / 2 ≤ tau) (htauUpper : tau ≤ 2) :
    (1 - sigma) - 1 / 2 + tau / 6 + epsilon ≤
        tau * ((1 / 2 : ℝ) * (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) ∧
    (1 - sigma) - 1 / 6 + epsilon ≤
        tau * ((1 / 2 : ℝ) * (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) ∧
    (1 - sigma) - tau / 9 + epsilon ≤
        tau * ((1 / 2 : ℝ) * (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  let u : ℝ := 1 - sigma
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have huUpper : u ≤ 1 / 4 := by dsimp only [u]; linarith
  have hcore := pintz_threeQuarter_orderThree_core hu huUpper
  have htarget :
      u - 1 / 6 ≤ tau * ((1 / 2 : ℝ) * u ^ (3 / 2 : ℝ)) := by
    have hthree :
        (3 / 4 : ℝ) * u ^ (3 / 2 : ℝ) ≤
          tau * ((1 / 2 : ℝ) * u ^ (3 / 2 : ℝ)) := by
      have hpow : 0 ≤ u ^ (3 / 2 : ℝ) := Real.rpow_nonneg hu _
      nlinarith
    exact hcore.trans hthree
  have heps : epsilon ≤ tau * epsilon := by nlinarith
  dsimp only [u] at htarget ⊢
  constructor
  · have hfirst :
        (1 - sigma) - 1 / 2 + tau / 6 ≤
          (1 - sigma) - 1 / 6 := by linarith
    nlinarith
  · constructor
    · nlinarith
    · have hthird :
          (1 - sigma) - tau / 9 ≤ (1 - sigma) - 1 / 6 := by
        nlinarith
      nlinarith

/-- The order-three derivative estimate, with the physical height written as
`N^tau`, supplies the complete weighted block throughout the upper half of
the conductor range. -/
theorem norm_fordShiftedWeightedBlock_zero_le_threeQuarter_orderThree
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma tau : ℝ) (N R : ℕ),
      sigma ≤ 1 → 3 / 4 ≤ sigma →
      1024 ≤ N → N < R → R ≤ 2 * N →
      3 / 2 ≤ tau → tau ≤ 2 →
      ‖fordShiftedWeightedBlock sigma N R 0 ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^
          (tau * ((1 / 2 : ℝ) *
            (1 - sigma) ^ (3 / 2 : ℝ) + epsilon)) := by
  obtain ⟨C₀, hC₀, hweighted⟩ :=
    norm_pintz2023WeightedBlock_le_heathBrown_uniform 3 epsilon
      (by norm_num) hepsilon
  let A : ℝ :=
    (pintz2023DerivativeConstant 3) ^ pintz2023HBAlpha 3
  let G : ℝ :=
    (pintz2023DerivativeConstant 3) ^ (-pintz2023HBGamma 3)
  let D : ℝ := A + 1 + G
  have hApos : 0 < A := by
    dsimp only [A]
    exact Real.rpow_pos_of_pos (pintz2023DerivativeConstant_pos 3) _
  have hGpos : 0 < G := by
    dsimp only [G]
    exact Real.rpow_pos_of_pos (pintz2023DerivativeConstant_pos 3) _
  have hDpos : 0 < D := by dsimp only [D]; positivity
  refine ⟨C₀ * D, mul_pos hC₀ hDpos, ?_⟩
  intro sigma tau N R hsigmaUpper hsigmaLower hN hNR hR
    htauLower htauUpper
  have hNPos : 0 < N := by omega
  have hNReal : (0 : ℝ) < N := by positivity
  have hNOne : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have htPos : 0 < (N : ℝ) ^ tau :=
    Real.rpow_pos_of_pos hNReal _
  have hxiOne : 1 - sigma ≤ 1 := by linarith
  have hbase := hweighted (1 - sigma) N R ((N : ℝ) ^ tau)
    hxiOne hNPos hNR hR htPos
  have hab := pintz2023_abel_endpoint_scaled_le
    (r := 3) (epsilon := epsilon) (xi := 1 - sigma) (C := C₀)
    (t := (N : ℝ) ^ tau) hNPos hxiOne hC₀.le htPos
  have hscaled := pintz2023_scaled_derivative_factor_eq
    (r := 3) (N := N) (t := (N : ℝ) ^ tau)
    (xi := 1 - sigma) (epsilon := epsilon)
    (by norm_num) hNPos htPos
  have hexponents := pintz_threeQuarter_orderThree_exponents
    hsigmaUpper hsigmaLower hepsilon.le htauLower htauUpper
  let p : ℝ := tau * ((1 / 2 : ℝ) *
    (1 - sigma) ^ (3 / 2 : ℝ) + epsilon)
  have hfirstExp :
      (1 - sigma) - 1 / 2 + tau / 6 + epsilon ≤ p := by
    simpa only [p] using hexponents.1
  have hsecondExp :
      (1 - sigma) - 1 / 6 + epsilon ≤ p := by
    simpa only [p] using hexponents.2.1
  have hthirdExp :
      (1 - sigma) - tau / 9 + epsilon ≤ p := by
    simpa only [p] using hexponents.2.2
  have hfirstPow := Real.rpow_le_rpow_of_exponent_le hNOne hfirstExp
  have hsecondPow := Real.rpow_le_rpow_of_exponent_le hNOne hsecondExp
  have hthirdPow := Real.rpow_le_rpow_of_exponent_le hNOne hthirdExp
  have hA : pintz2023HBAlpha 3 = (1 / 6 : ℝ) := by
    norm_num [pintz2023HBAlpha]
  have hG : pintz2023HBGamma 3 = (1 / 9 : ℝ) := by
    norm_num [pintz2023HBGamma]
  have hpowA :
      ((N : ℝ) ^ tau) ^ pintz2023HBAlpha 3 =
        (N : ℝ) ^ (tau / 6) := by
    rw [hA]
    calc
      ((N : ℝ) ^ tau) ^ (1 / 6 : ℝ) =
          (N : ℝ) ^ (tau * (1 / 6 : ℝ)) :=
        (Real.rpow_mul hNReal.le _ _).symm
      _ = (N : ℝ) ^ (tau / 6) := by
        have hexp : tau * (1 / 6 : ℝ) = tau / 6 := by ring
        rw [hexp]
  have hpowG :
      ((N : ℝ) ^ tau) ^ (-pintz2023HBGamma 3) =
        (N : ℝ) ^ (-tau / 9) := by
    rw [hG]
    calc
      ((N : ℝ) ^ tau) ^ (-(1 / 9 : ℝ)) =
          (N : ℝ) ^ (tau * (-(1 / 9 : ℝ))) :=
        (Real.rpow_mul hNReal.le _ _).symm
      _ = (N : ℝ) ^ (-tau / 9) := by
        have hexp : tau * (-(1 / 9 : ℝ)) = -tau / 9 := by ring
        rw [hexp]
  have hfirstCombine :
      (N : ℝ) ^
          ((1 - sigma) - 1 / ((3 : ℝ) - 1) + epsilon) *
          ((N : ℝ) ^ tau) ^ pintz2023HBAlpha 3 =
        (N : ℝ) ^
          ((1 - sigma) - 1 / 2 + tau / 6 + epsilon) := by
    rw [hpowA, ← Real.rpow_add hNReal]
    apply congrArg (fun x : ℝ => (N : ℝ) ^ x)
    ring
  have hsecondShape :
      (1 - sigma) + epsilon - pintz2023HBAlpha 3 =
        (1 - sigma) - 1 / 6 + epsilon := by
    rw [hA]
    ring
  have hthirdCombine :
      (N : ℝ) ^ ((1 - sigma) + epsilon) *
          ((N : ℝ) ^ tau) ^ (-pintz2023HBGamma 3) =
        (N : ℝ) ^ ((1 - sigma) - tau / 9 + epsilon) := by
    rw [hpowG, ← Real.rpow_add hNReal]
    apply congrArg (fun x : ℝ => (N : ℝ) ^ x)
    ring
  have hpNonneg : 0 ≤ (N : ℝ) ^ p := Real.rpow_nonneg hNReal.le _
  have hAleD : A ≤ D := by dsimp only [D]; linarith
  have hOneLeD : (1 : ℝ) ≤ D := by dsimp only [D]; linarith
  have hGleD : G ≤ D := by dsimp only [D]; linarith
  have hfirstTerm :
      A * (N : ℝ) ^
          ((1 - sigma) - 1 / ((3 : ℝ) - 1) + epsilon) *
          ((N : ℝ) ^ tau) ^ pintz2023HBAlpha 3 =
        A * (N : ℝ) ^
          ((1 - sigma) - 1 / 2 + tau / 6 + epsilon) := by
    rw [mul_assoc, hfirstCombine]
  have hthirdTerm :
      G * (N : ℝ) ^ ((1 - sigma) + epsilon) *
          ((N : ℝ) ^ tau) ^ (-pintz2023HBGamma 3) =
        G * (N : ℝ) ^ ((1 - sigma) - tau / 9 + epsilon) := by
    rw [mul_assoc, hthirdCombine]
  have hsum :
      A * (N : ℝ) ^
          ((1 - sigma) - 1 / ((3 : ℝ) - 1) + epsilon) *
          ((N : ℝ) ^ tau) ^ pintz2023HBAlpha 3 +
        (N : ℝ) ^ ((1 - sigma) + epsilon - pintz2023HBAlpha 3) +
        G * (N : ℝ) ^ ((1 - sigma) + epsilon) *
          ((N : ℝ) ^ tau) ^ (-pintz2023HBGamma 3) ≤
        D * (N : ℝ) ^ p := by
    rw [hfirstTerm, hsecondShape, hthirdTerm]
    have hf : A * (N : ℝ) ^
        ((1 - sigma) - 1 / 2 + tau / 6 + epsilon) ≤
        A * (N : ℝ) ^ p := mul_le_mul_of_nonneg_left hfirstPow hApos.le
    have hs : (N : ℝ) ^ ((1 - sigma) - 1 / 6 + epsilon) ≤
        (N : ℝ) ^ p := hsecondPow
    have ht : G * (N : ℝ) ^ ((1 - sigma) - tau / 9 + epsilon) ≤
        G * (N : ℝ) ^ p := mul_le_mul_of_nonneg_left hthirdPow hGpos.le
    have hcoeff : (A + 1 + G) * (N : ℝ) ^ p =
        A * (N : ℝ) ^ p + (N : ℝ) ^ p +
          G * (N : ℝ) ^ p := by ring
    dsimp only [D]
    rw [hcoeff]
    linarith
  rw [← pintz2023WeightedBlock_one_sub_eq_ford]
  calc
    ‖pintz2023WeightedBlock (1 - sigma) N R ((N : ℝ) ^ tau)‖ ≤
        ((N + 1 : ℕ) : ℝ) ^ (-(1 - (1 - sigma))) *
          (C₀ * (N : ℝ) ^ (1 + epsilon) *
            heathBrownKthDerivativeFactor 3 N
              (pintz2023DerivativeLambda 3 N ((N : ℝ) ^ tau))) := hbase
    _ ≤ C₀ * (N : ℝ) ^ ((1 - sigma) + epsilon) *
          heathBrownKthDerivativeFactor 3 N
            (pintz2023DerivativeLambda 3 N ((N : ℝ) ^ tau)) := hab
    _ = C₀ *
        (A * (N : ℝ) ^
            ((1 - sigma) - 1 / ((3 : ℝ) - 1) + epsilon) *
              ((N : ℝ) ^ tau) ^ pintz2023HBAlpha 3 +
          (N : ℝ) ^ ((1 - sigma) + epsilon - pintz2023HBAlpha 3) +
          G * (N : ℝ) ^ ((1 - sigma) + epsilon) *
            ((N : ℝ) ^ tau) ^ (-pintz2023HBGamma 3)) := by
      rw [mul_assoc, hscaled]
      dsimp only [A, G]
      norm_num
    _ ≤ C₀ * (D * (N : ℝ) ^ p) :=
      mul_le_mul_of_nonneg_left hsum hC₀.le
    _ = (C₀ * D) * (N : ℝ) ^
          (tau * ((1 / 2 : ℝ) *
            (1 - sigma) ^ (3 / 2 : ℝ) + epsilon)) := by
      dsimp only [p]
      ring

/-- On the lower conductor range the B-process exponent is nonpositive even
at real part `3/4`. -/
theorem pintz_threeQuarter_middle_B_exponent_nonpos
    {sigma tau : ℝ} (hsigma : 3 / 4 ≤ sigma)
    (htauPos : 0 < tau) (htau : tau ≤ 3 / 2) :
    1 / 2 - sigma / tau ≤ 0 := by
  rw [sub_nonpos]
  exact (le_div_iff₀ htauPos).2 (by nlinarith)

/-- B-process branch of the three-quarter conductor-scale estimate. -/
theorem norm_fordShiftedWeightedBlock_zero_le_threeQuarter_middle_B
    {epsilon sigma t : ℝ} {N R : ℕ}
    (hepsilon : 0 < epsilon) (hsigmaUpper : sigma ≤ 1)
    (hsigmaLower : 3 / 4 ≤ sigma)
    (hN : 1024 ≤ N) (hNt : (N : ℝ) ≤ t)
    (htN : t ≤ (N : ℝ) ^ 2)
    (htauUpper : fordLambda N t ≤ 3 / 2)
    (hNR : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
      130 * t ^ ((1 / 2 : ℝ) *
        (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  have hNOne : 1 < N := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  have hNRealOne : (1 : ℝ) < N := by
    have hcast : (1024 : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN
    norm_num at hcast ⊢
    linarith
  have ht : 0 < t := hNpos.trans_le hNt
  have htOne : 1 ≤ t := (le_of_lt hNRealOne).trans hNt
  let tau : ℝ := fordLambda N t
  have htauOne : 1 ≤ tau := by
    simpa only [tau] using one_le_fordLambda hNOne hNt
  have htauPos : 0 < tau := zero_lt_one.trans_le htauOne
  have hprefix : ∀ j : ℕ, j ≤ R - N →
      ‖∑ k ∈ Finset.range j,
          fordShiftedLogPhase (N + 1 + k) 0 t‖ ≤
        130 * Real.sqrt t := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp
    · rw [← fordShiftedExponentialSum_eq_sum_range]
      exact ford_shifted_exponential_sum_B_process
        hN (by omega) (by omega) (by norm_num) (by norm_num) hNt htN
  have hblock :
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        (((N + 1 : ℕ) : ℝ) ^ (-sigma)) * (130 * Real.sqrt t) := by
    unfold fordShiftedWeightedBlock
    simp only [add_zero]
    apply ford_norm_weighted_Ioc_le_of_antitone
        (fun n => (n : ℝ) ^ (-sigma))
        (fun n => fordShiftedLogPhase n 0 t) N R
        (130 * Real.sqrt t) hNR
    · intro n _hn
      positivity
    · intro n _hnN _hnR
      apply Real.rpow_le_rpow_of_nonpos
      · exact Nat.cast_pos.mpr (by omega)
      · exact Nat.cast_le.mpr (Nat.le_succ n)
      · linarith
    · exact hprefix
  have hweight : (((N + 1 : ℕ) : ℝ) ^ (-sigma)) ≤
      (N : ℝ) ^ (-sigma) := by
    apply Real.rpow_le_rpow_of_nonpos hNpos
    · exact Nat.cast_le.mpr (Nat.le_succ N)
    · linarith
  have hmajorant : 0 ≤ 130 * Real.sqrt t := by positivity
  have hsqrt : Real.sqrt t = (N : ℝ) ^ (tau / 2) := by
    rw [Real.sqrt_eq_rpow, ← rpow_fordLambda_eq hNOne ht]
    calc
      ((N : ℝ) ^ tau) ^ (1 / 2 : ℝ) =
          (N : ℝ) ^ (tau * (1 / 2 : ℝ)) :=
        (Real.rpow_mul hNpos.le _ _).symm
      _ = (N : ℝ) ^ (tau / 2) := by
        have hexp : tau * (1 / 2 : ℝ) = tau / 2 := by ring
        rw [hexp]
  have hcombine :
      (N : ℝ) ^ (-sigma) * (130 * Real.sqrt t) =
        130 * (N : ℝ) ^ (tau / 2 - sigma) := by
    rw [hsqrt]
    calc
      (N : ℝ) ^ (-sigma) * (130 * (N : ℝ) ^ (tau / 2)) =
          130 * ((N : ℝ) ^ (-sigma) *
            (N : ℝ) ^ (tau / 2)) := by ring
      _ = 130 * (N : ℝ) ^ (-sigma + tau / 2) := by
        rw [← Real.rpow_add hNpos]
      _ = 130 * (N : ℝ) ^ (tau / 2 - sigma) := by ring
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNRealOne
  have htauLog : tau * Real.log (N : ℝ) = Real.log t := by
    dsimp only [tau, fordLambda]
    field_simp [hlogN.ne']
  have hscaleExponent :
      Real.log (N : ℝ) * (tau / 2 - sigma) =
        Real.log t * (1 / 2 - sigma / tau) := by
    rw [← htauLog]
    field_simp [htauPos.ne']
  have hscalePower :
      (N : ℝ) ^ (tau / 2 - sigma) =
        t ^ (1 / 2 - sigma / tau) := by
    rw [Real.rpow_def_of_pos hNpos, Real.rpow_def_of_pos ht,
      hscaleExponent]
  have hnonpos : 1 / 2 - sigma / tau ≤ 0 :=
    pintz_threeQuarter_middle_B_exponent_nonpos hsigmaLower htauPos
      (by simpa only [tau] using htauUpper)
  have htarget : 0 ≤ (1 / 2 : ℝ) *
      (1 - sigma) ^ (3 / 2 : ℝ) + epsilon := by
    have : 0 ≤ 1 - sigma := by linarith
    positivity
  have hpow := Real.rpow_le_rpow_of_exponent_le htOne
    (hnonpos.trans htarget)
  calc
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        (((N + 1 : ℕ) : ℝ) ^ (-sigma)) *
          (130 * Real.sqrt t) := hblock
    _ ≤ (N : ℝ) ^ (-sigma) * (130 * Real.sqrt t) :=
      mul_le_mul_of_nonneg_right hweight hmajorant
    _ = 130 * (N : ℝ) ^ (tau / 2 - sigma) := hcombine
    _ = 130 * t ^ (1 / 2 - sigma / tau) := by rw [hscalePower]
    _ ≤ 130 * t ^ ((1 / 2 : ℝ) *
        (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by gcongr

/-- Complete conductor-scale block estimate down to real part `3/4`. -/
theorem norm_fordShiftedWeightedBlock_zero_le_threeQuarter_middle
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (N R : ℕ),
      sigma ≤ 1 → 3 / 4 ≤ sigma →
      1024 ≤ N → N < R → R ≤ 2 * N →
      (N : ℝ) ≤ t → t ≤ (N : ℝ) ^ 2 →
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        C * t ^ ((1 / 2 : ℝ) *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  obtain ⟨C₃, hC₃, hthree⟩ :=
    norm_fordShiftedWeightedBlock_zero_le_threeQuarter_orderThree hepsilon
  let C : ℝ := 130 + C₃
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro sigma t N R hsigmaUpper hsigmaLower hN hNR hR hNt htN
  have hNOne : 1 < N := by omega
  have hNReal : (0 : ℝ) < N := by positivity
  have ht : 0 < t := hNReal.trans_le hNt
  have htNonneg : 0 ≤ t := ht.le
  let tau : ℝ := fordLambda N t
  have htauOne : 1 ≤ tau := by
    simpa only [tau] using one_le_fordLambda hNOne hNt
  have htauTwo : tau ≤ 2 := by
    simpa only [tau] using fordLambda_le_two_of_le_sq hNOne ht htN
  have hteq : (N : ℝ) ^ tau = t := by
    simpa only [tau] using rpow_fordLambda_eq hNOne ht
  let p : ℝ := (1 / 2 : ℝ) *
    (1 - sigma) ^ (3 / 2 : ℝ) + epsilon
  have hpowNonneg : 0 ≤ t ^ p := Real.rpow_nonneg htNonneg _
  by_cases htau : tau ≤ 3 / 2
  · have hraw :=
      norm_fordShiftedWeightedBlock_zero_le_threeQuarter_middle_B
        hepsilon hsigmaUpper hsigmaLower hN hNt htN
          (by simpa only [tau] using htau) hNR hR
    calc
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤ 130 * t ^ p := by
        simpa only [p] using hraw
      _ ≤ C * t ^ p := by
        apply mul_le_mul_of_nonneg_right _ hpowNonneg
        dsimp only [C]
        linarith
      _ = C * t ^ ((1 / 2 : ℝ) *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := rfl
  · have htauLower : 3 / 2 ≤ tau := le_of_not_ge htau
    have hraw := hthree sigma tau N R hsigmaUpper hsigmaLower hN hNR hR
      htauLower htauTwo
    have hpower :
        (N : ℝ) ^ (tau * p) = t ^ p := by
      rw [← hteq]
      exact Real.rpow_mul hNReal.le tau p
    calc
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ =
          ‖fordShiftedWeightedBlock sigma N R 0 ((N : ℝ) ^ tau)‖ := by
        rw [hteq]
      _ ≤ C₃ * (N : ℝ) ^ (tau * p) := by
        simpa only [p] using hraw
      _ = C₃ * t ^ p := by rw [hpower]
      _ ≤ C * t ^ p := by
        apply mul_le_mul_of_nonneg_right _ hpowNonneg
        dsimp only [C]
        linarith
      _ = C * t ^ ((1 / 2 : ℝ) *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := rfl

#print axioms pintz2023WeightedBlock_one_sub_eq_ford
#print axioms pintz_threeQuarter_orderThree_core
#print axioms pintz_threeQuarter_orderThree_exponents
#print axioms norm_fordShiftedWeightedBlock_zero_le_threeQuarter_orderThree
#print axioms pintz_threeQuarter_middle_B_exponent_nonpos
#print axioms norm_fordShiftedWeightedBlock_zero_le_threeQuarter_middle_B
#print axioms norm_fordShiftedWeightedBlock_zero_le_threeQuarter_middle

end

end GafniTao

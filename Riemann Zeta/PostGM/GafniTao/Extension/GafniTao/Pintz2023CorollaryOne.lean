import GafniTao.Pintz2023CorollaryOneAlgebra

/-!
# Pintz (2023), Corollary 1

This file proves the three-term estimate in equation (3.2) for the literal
weighted block from equation (3.1).  The constant is uniform in `xi`, the
interval, the height, and the dyadic scale; it depends only on `r` and
`epsilon`, as in the source.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The three monomials displayed on the right-hand side of Pintz (3.2). -/
noncomputable def pintz2023CorollaryOneMajorant
    (r N : ℕ) (epsilon xi t : ℝ) : ℝ :=
  (N : ℝ) ^ (xi - 1 / ((r : ℝ) - 1) + 3 * epsilon) *
      t ^ pintz2023HBAlpha r +
    (N : ℝ) ^ (-3 * epsilon) +
    (N : ℝ) ^ (xi + 3 * epsilon) *
      t ^ (-pintz2023HBGamma r)

theorem pintz2023CorollaryOneMajorant_nonneg
    (r N : ℕ) (epsilon xi t : ℝ) (ht : 0 ≤ t) :
    0 ≤ pintz2023CorollaryOneMajorant r N epsilon xi t := by
  unfold pintz2023CorollaryOneMajorant
  positivity

/-- The exact endpoint weight left by Abel summation is no larger than the
power of `N` needed to turn the outer `N^(1+epsilon)` into
`N^(xi+epsilon)`. -/
theorem pintz2023_abel_endpoint_scaled_le
    {r N : ℕ} {epsilon xi C t : ℝ}
    (hN : 0 < N) (hxi : xi ≤ 1) (hC : 0 ≤ C) (ht : 0 < t) :
    ((N + 1 : ℕ) : ℝ) ^ (-(1 - xi)) *
        (C * (N : ℝ) ^ (1 + epsilon) *
          heathBrownKthDerivativeFactor r N
            (pintz2023DerivativeLambda r N t)) ≤
      C * (N : ℝ) ^ (xi + epsilon) *
        heathBrownKthDerivativeFactor r N
          (pintz2023DerivativeLambda r N t) := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hNLe : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ N
  have hExp : -(1 - xi) = xi - 1 := by ring
  have hend :
      ((N + 1 : ℕ) : ℝ) ^ (xi - 1) ≤ (N : ℝ) ^ (xi - 1) :=
    Real.rpow_le_rpow_of_nonpos hNReal hNLe (by linarith)
  have hlambda : 0 < pintz2023DerivativeLambda r N t := by
    unfold pintz2023DerivativeLambda
    positivity
  have hfactor : 0 ≤ heathBrownKthDerivativeFactor r N
      (pintz2023DerivativeLambda r N t) :=
    heathBrownKthDerivativeFactor_nonneg r hNReal.le hlambda
  rw [hExp]
  calc
    _ ≤ (N : ℝ) ^ (xi - 1) *
        (C * (N : ℝ) ^ (1 + epsilon) *
          heathBrownKthDerivativeFactor r N
            (pintz2023DerivativeLambda r N t)) := by
      exact mul_le_mul_of_nonneg_right hend
        (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hNReal.le _)) hfactor)
    _ = C * ((N : ℝ) ^ (xi - 1) * (N : ℝ) ^ (1 + epsilon)) *
        heathBrownKthDerivativeFactor r N
          (pintz2023DerivativeLambda r N t) := by ring
    _ = _ := by
      rw [← Real.rpow_add hNReal]
      congr 3
      ring

/-- Uniform-in-`xi` form of the exact Abel step.  Its constant is the
unweighted derivative-test constant, hence does not change with `xi`. -/
theorem norm_pintz2023WeightedBlock_le_heathBrown_uniform
    (k : ℕ) (epsilon : ℝ) (hk : 3 ≤ k) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (xi : ℝ) (N R : ℕ) (t : ℝ),
      xi ≤ 1 → 0 < N → N < R → R ≤ 2 * N → 0 < t →
      ‖pintz2023WeightedBlock xi N R t‖ ≤
        ((N + 1 : ℕ) : ℝ) ^ (-(1 - xi)) *
          (C * (N : ℝ) ^ (1 + epsilon) *
            heathBrownKthDerivativeFactor k N
              (pintz2023DerivativeLambda k N t)) := by
  obtain ⟨C, hC, hprefix⟩ :=
    norm_pintz2023ExponentialBlock_prefix_le k epsilon hk hepsilon
  refine ⟨C, hC, ?_⟩
  intro xi N R t hxi hN hNR hR ht
  unfold pintz2023WeightedBlock
  apply ford_norm_weighted_Ioc_le_of_antitone
      (fun n => (n : ℝ) ^ (-(1 - xi)))
      (fun n => (n : ℂ) ^ (-(t : ℂ) * I)) N R
      (C * (N : ℝ) ^ (1 + epsilon) *
        heathBrownKthDerivativeFactor k N
          (pintz2023DerivativeLambda k N t)) hNR
  · intro n hn
    exact Real.rpow_nonneg (by positivity) _
  · intro n hnN hnR
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast (show 0 < n by omega)
    · exact_mod_cast Nat.le_succ n
    · exact neg_nonpos.mpr (sub_nonneg.mpr hxi)
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp only [Finset.range_zero, sum_empty, norm_zero]
      have hlambda : 0 < pintz2023DerivativeLambda k N t := by
        unfold pintz2023DerivativeLambda
        positivity
      exact mul_nonneg
        (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))
        (heathBrownKthDerivativeFactor_nonneg k (by positivity) hlambda)
    · simp_rw [Nat.cast_add, Nat.cast_one]
      rw [← pintz2023ExponentialBlock_eq_sum_range]
      exact hprefix N (N + j) t hN (by omega) (by omega) ht

/-- Pintz (2023), Corollary 1, equation (3.2), for every half-open subinterval
`I(N) = (N,R]` of `(N,2N]`. -/
theorem pintz2023_corollary_one_native
    (r : ℕ) (epsilon : ℝ) (hr : 3 ≤ r) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (xi : ℝ) (N R : ℕ) (t : ℝ),
      xi ≤ pintz2023HBAlpha r - 6 * epsilon →
      0 < N → N < R → R ≤ 2 * N → 0 < t →
      ‖pintz2023WeightedBlock xi N R t‖ ≤
        C * pintz2023CorollaryOneMajorant r N epsilon xi t := by
  obtain ⟨C₀, hC₀, hweighted⟩ :=
    norm_pintz2023WeightedBlock_le_heathBrown_uniform r epsilon hr hepsilon
  let A : ℝ :=
    (pintz2023DerivativeConstant r) ^ pintz2023HBAlpha r
  let G : ℝ :=
    (pintz2023DerivativeConstant r) ^ (-pintz2023HBGamma r)
  let D : ℝ := A + 1 + G
  have hApos : 0 < A := by
    dsimp only [A]
    exact Real.rpow_pos_of_pos (pintz2023DerivativeConstant_pos r) _
  have hGpos : 0 < G := by
    dsimp only [G]
    exact Real.rpow_pos_of_pos (pintz2023DerivativeConstant_pos r) _
  have hDpos : 0 < D := by dsimp only [D]; positivity
  refine ⟨C₀ * D, mul_pos hC₀ hDpos, ?_⟩
  intro xi N R t hxi hN hNR hR ht
  have hrTwo : 2 ≤ r := by omega
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hxiOne : xi ≤ 1 := by
    have haUpper : pintz2023HBAlpha r ≤ 1 := by
      have hrReal : (3 : ℝ) ≤ r := by exact_mod_cast hr
      unfold pintz2023HBAlpha
      have hden : 1 ≤ (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
    linarith
  have hbase := hweighted xi N R t hxiOne hN hNR hR ht
  have hab := pintz2023_abel_endpoint_scaled_le
    (r := r) (epsilon := epsilon) (xi := xi) (C := C₀) (t := t)
      hN hxiOne hC₀.le ht
  have hscaled := pintz2023_scaled_derivative_factor_eq
    (r := r) (N := N) (t := t) (xi := xi) (epsilon := epsilon) hr hN ht
  have hfirstExp :
      xi - 1 / ((r : ℝ) - 1) + epsilon ≤
        xi - 1 / ((r : ℝ) - 1) + 3 * epsilon := by linarith
  have hsecondExp :
      xi + epsilon - pintz2023HBAlpha r ≤ -3 * epsilon := by linarith
  have hthirdExp : xi + epsilon ≤ xi + 3 * epsilon := by linarith
  have hfirstPow := Real.rpow_le_rpow_of_exponent_le hNReal hfirstExp
  have hsecondPow := Real.rpow_le_rpow_of_exponent_le hNReal hsecondExp
  have hthirdPow := Real.rpow_le_rpow_of_exponent_le hNReal hthirdExp
  have hAleD : A ≤ D := by dsimp only [D]; linarith
  have hOneleD : (1 : ℝ) ≤ D := by dsimp only [D]; linarith
  have hGleD : G ≤ D := by dsimp only [D]; linarith
  have htAlpha : 0 ≤ t ^ pintz2023HBAlpha r := Real.rpow_nonneg ht.le _
  have htGamma : 0 ≤ t ^ (-pintz2023HBGamma r) := Real.rpow_nonneg ht.le _
  have hfirst :
      A * (N : ℝ) ^ (xi - 1 / ((r : ℝ) - 1) + epsilon) *
          t ^ pintz2023HBAlpha r ≤
        D * ((N : ℝ) ^
          (xi - 1 / ((r : ℝ) - 1) + 3 * epsilon) *
            t ^ pintz2023HBAlpha r) := by
    calc
      _ ≤ A * (N : ℝ) ^
            (xi - 1 / ((r : ℝ) - 1) + 3 * epsilon) *
          t ^ pintz2023HBAlpha r := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hfirstPow hApos.le) htAlpha
      _ ≤ D * (N : ℝ) ^
            (xi - 1 / ((r : ℝ) - 1) + 3 * epsilon) *
          t ^ pintz2023HBAlpha r := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hAleD (Real.rpow_nonneg (by positivity) _)) htAlpha
      _ = _ := by ring
  have hsecond :
      (N : ℝ) ^ (xi + epsilon - pintz2023HBAlpha r) ≤
        D * (N : ℝ) ^ (-3 * epsilon) := by
    calc
      _ ≤ (N : ℝ) ^ (-3 * epsilon) := hsecondPow
      _ ≤ D * (N : ℝ) ^ (-3 * epsilon) := by
        exact le_mul_of_one_le_left (Real.rpow_nonneg (by positivity) _) hOneleD
  have hthird :
      G * (N : ℝ) ^ (xi + epsilon) * t ^ (-pintz2023HBGamma r) ≤
        D * ((N : ℝ) ^ (xi + 3 * epsilon) *
          t ^ (-pintz2023HBGamma r)) := by
    calc
      _ ≤ G * (N : ℝ) ^ (xi + 3 * epsilon) *
          t ^ (-pintz2023HBGamma r) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hthirdPow hGpos.le) htGamma
      _ ≤ D * (N : ℝ) ^ (xi + 3 * epsilon) *
          t ^ (-pintz2023HBGamma r) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hGleD (Real.rpow_nonneg (by positivity) _)) htGamma
      _ = _ := by ring
  calc
    ‖pintz2023WeightedBlock xi N R t‖ ≤
        ((N + 1 : ℕ) : ℝ) ^ (-(1 - xi)) *
          (C₀ * (N : ℝ) ^ (1 + epsilon) *
            heathBrownKthDerivativeFactor r N
              (pintz2023DerivativeLambda r N t)) := hbase
    _ ≤ C₀ * (N : ℝ) ^ (xi + epsilon) *
          heathBrownKthDerivativeFactor r N
            (pintz2023DerivativeLambda r N t) := hab
    _ = C₀ *
        (A * (N : ℝ) ^ (xi - 1 / ((r : ℝ) - 1) + epsilon) *
            t ^ pintz2023HBAlpha r +
          (N : ℝ) ^ (xi + epsilon - pintz2023HBAlpha r) +
          G * (N : ℝ) ^ (xi + epsilon) *
            t ^ (-pintz2023HBGamma r)) := by
      rw [mul_assoc, hscaled]
    _ ≤ C₀ * (D * pintz2023CorollaryOneMajorant r N epsilon xi t) := by
      apply mul_le_mul_of_nonneg_left _ hC₀.le
      unfold pintz2023CorollaryOneMajorant
      linarith
    _ = (C₀ * D) * pintz2023CorollaryOneMajorant r N epsilon xi t := by ring

#print axioms pintz2023_abel_endpoint_scaled_le
#print axioms norm_pintz2023WeightedBlock_le_heathBrown_uniform
#print axioms pintz2023_corollary_one_native

end

end GafniTao

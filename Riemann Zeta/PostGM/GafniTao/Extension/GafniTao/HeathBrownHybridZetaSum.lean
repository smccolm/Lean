import GafniTao.HeathBrownHybridZetaAllBlocks
import GafniTao.FordDadaroRemainder
import GafniTao.HeathBrownLogAbsorption

/-!
# The hybrid estimate for the complete finite zeta sum

The terminal shell remains cut at the literal Dadaro endpoint.  Thus this
module does not enlarge the finite sum before applying the short- and
conductor-scale block estimates.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Summing the uniform hybrid estimate over the exact dyadic partition costs
exactly the number of retained shells. -/
theorem norm_fordDyadicWeightedShellSum_zero_le_hybrid
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (M : ℕ),
      0 ≤ sigma → sigma ≤ 1 →
      1 - 1 / 12000000 ≤ sigma → 1 ≤ t →
      1 ≤ M → M ≤ fordFiniteEndpoint t + 1 →
      ‖fordDyadicWeightedShellSum sigma (Nat.clog 2 M) M 0 t‖ ≤
        (Nat.clog 2 M : ℝ) *
          (C * t ^ (heathBrownHalfZetaKappa *
            (1 - sigma) ^ (3 / 2 : ℝ) + epsilon)) := by
  obtain ⟨C, hC, hblock⟩ :=
    norm_fordShiftedWeightedBlock_zero_le_all_zeta hepsilon
  refine ⟨C, hC, ?_⟩
  intro sigma t M hsigma hsigmaUpper hsigmaNear htOne hM hMtop
  unfold fordDyadicWeightedShellSum
  calc
    ‖∑ j ∈ Finset.range (Nat.clog 2 M),
        fordShiftedWeightedBlock sigma (2 ^ j)
          (min M (2 ^ (j + 1))) 0 t‖ ≤
        ∑ j ∈ Finset.range (Nat.clog 2 M),
          ‖fordShiftedWeightedBlock sigma (2 ^ j)
            (min M (2 ^ (j + 1))) 0 t‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (Nat.clog 2 M),
        C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
      gcongr with j hj
      have hjlt : j < Nat.clog 2 M := Finset.mem_range.mp hj
      have hjM : 2 ^ j < M := Nat.pow_lt_of_lt_clog hjlt
      have hjEndpoint : 2 ^ j ≤ fordFiniteEndpoint t :=
        Nat.lt_succ_iff.mp (hjM.trans_le hMtop)
      have hjt : ((2 ^ j : ℕ) : ℝ) ≤ t :=
        (by exact_mod_cast hjEndpoint :
          ((2 ^ j : ℕ) : ℝ) ≤ fordFiniteEndpoint t).trans
          (Nat.floor_le (by linarith))
      have hjSucc : (2 : ℕ) ^ j < 2 ^ (j + 1) :=
        pow_lt_pow_right₀ (by omega) (by omega)
      have hnonempty : 2 ^ j < min M (2 ^ (j + 1)) :=
        lt_min hjM hjSucc
      have hupper : min M (2 ^ (j + 1)) ≤ 2 * 2 ^ j := by
        calc
          min M (2 ^ (j + 1)) ≤ 2 ^ (j + 1) := min_le_right _ _
          _ = 2 * 2 ^ j := by rw [pow_succ]; omega
      exact hblock sigma t (2 ^ j) (min M (2 ^ (j + 1)))
        hsigma hsigmaUpper hsigmaNear (pow_pos (by omega) _)
        hnonempty hupper hjt
    _ = (Nat.clog 2 M : ℝ) *
        (C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon)) := by simp

/-- The exact Dadaro finite approximation, with the dyadic logarithm still
visible and no asymptotic absorption yet performed. -/
theorem norm_fordHurwitzFiniteApproximation_one_le_hybrid
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ),
      0 ≤ sigma → sigma ≤ 1 →
      1 - 1 / 12000000 ≤ sigma → 3 ≤ t →
      ‖fordHurwitzFiniteApproximation sigma 1 t‖ ≤
        1 + (Nat.clog 2 (fordFiniteEndpoint t + 1) : ℝ) *
          (C * t ^ (heathBrownHalfZetaKappa *
            (1 - sigma) ^ (3 / 2 : ℝ) + epsilon)) := by
  obtain ⟨C, hC, hshell⟩ :=
    norm_fordDyadicWeightedShellSum_zero_le_hybrid hepsilon
  refine ⟨C, hC, ?_⟩
  intro sigma t hsigma hsigmaUpper hsigmaNear ht
  let M : ℕ := fordFiniteEndpoint t + 1
  have hM : 1 ≤ M := by dsimp only [M]; omega
  rw [fordHurwitzFiniteApproximation_one_eq_partial_sum,
    fordDadaroCutoff_floor,
    partialZeta_eq_one_add_fordDyadic hM]
  calc
    ‖(1 : ℂ) + fordDyadicWeightedShellSum sigma (Nat.clog 2 M) M 0 t‖ ≤
        1 + ‖fordDyadicWeightedShellSum sigma (Nat.clog 2 M) M 0 t‖ := by
      simpa using norm_add_le (1 : ℂ)
        (fordDyadicWeightedShellSum sigma (Nat.clog 2 M) M 0 t)
    _ ≤ 1 + (Nat.clog 2 M : ℝ) *
        (C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon)) := by
      gcongr
      exact hshell sigma t M hsigma hsigmaUpper hsigmaNear
        (by linarith) hM (by simp [M])
    _ = 1 + (Nat.clog 2 (fordFiniteEndpoint t + 1) : ℝ) *
        (C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon)) := by rfl

/-- The native coefficient-`2 sqrt 6 / 9` zeta estimate required in both
small-frequency passages of Pintz's proof.  The second half of `epsilon` is
reserved for the exact dyadic shell count, and the Dadaro terms are absorbed
only after the finite approximation has been bounded. -/
theorem norm_riemannZeta_le_heathBrownHybrid
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ),
      0 ≤ sigma → sigma ≤ 1 →
      1 - 1 / 12000000 ≤ sigma → 3 ≤ t →
      ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
        C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  have hepsHalf : 0 < epsilon / 2 := by positivity
  obtain ⟨C₀, hC₀, hfinite⟩ :=
    norm_fordHurwitzFiniteApproximation_one_le_hybrid hepsHalf
  let K : ℝ := (Real.log 2)⁻¹ * heathBrownLogConstant epsilon *
    2 ^ (epsilon / 2) * C₀
  let C : ℝ := 16 + K
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (inv_nonneg.mpr hlogTwo.le)
          (heathBrownLogConstant_pos hepsilon).le)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _))
      hC₀.le
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro sigma t hsigma hsigmaUpper hsigmaNear ht
  have htPos : 0 < t := by linarith
  have htOne : 1 ≤ t := by linarith
  let M : ℕ := fordFiniteEndpoint t + 1
  have hM : 1 ≤ M := by dsimp only [M]; omega
  have hMReal : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMUpper : (M : ℝ) ≤ 2 * t := by
    dsimp only [M]
    push_cast
    have hfloor : (fordFiniteEndpoint t : ℝ) ≤ t :=
      Nat.floor_le htPos.le
    linarith
  have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hMReal
  have hclogRaw := natCast_clog_two_le_one_add_log M hM
  have hlogTwoUpper : Real.log 2 ≤ 1 := by
    linarith [Real.log_two_lt_d9]
  have honeInv : (1 : ℝ) ≤ (Real.log 2)⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hlogTwo).2 (by simpa using hlogTwoUpper)
  have hclogScale : (Nat.clog 2 M : ℝ) ≤
      (Real.log 2)⁻¹ * (1 + Real.log (M : ℝ)) := by
    calc
      (Nat.clog 2 M : ℝ) ≤ 1 + Real.log (M : ℝ) / Real.log 2 := hclogRaw
      _ ≤ (Real.log 2)⁻¹ + Real.log (M : ℝ) / Real.log 2 := by
        gcongr
      _ = (Real.log 2)⁻¹ * (1 + Real.log (M : ℝ)) := by
        rw [div_eq_mul_inv]
        ring
  have hlogAbsorb := heathBrown_one_add_log_le hM hepsilon
  have hMpower : (M : ℝ) ^ (epsilon / 2) ≤
      2 ^ (epsilon / 2) * t ^ (epsilon / 2) := by
    calc
      (M : ℝ) ^ (epsilon / 2) ≤ (2 * t) ^ (epsilon / 2) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hMUpper hepsHalf.le
      _ = 2 ^ (epsilon / 2) * t ^ (epsilon / 2) := by
        rw [Real.mul_rpow (by norm_num) htPos.le]
  have hclog : (Nat.clog 2 M : ℝ) ≤
      (Real.log 2)⁻¹ * heathBrownLogConstant epsilon *
        2 ^ (epsilon / 2) * t ^ (epsilon / 2) := by
    calc
      (Nat.clog 2 M : ℝ) ≤
          (Real.log 2)⁻¹ * (1 + Real.log (M : ℝ)) := hclogScale
      _ ≤ (Real.log 2)⁻¹ *
          (heathBrownLogConstant epsilon * (M : ℝ) ^ (epsilon / 2)) :=
        mul_le_mul_of_nonneg_left hlogAbsorb (by positivity)
      _ ≤ (Real.log 2)⁻¹ *
          (heathBrownLogConstant epsilon *
            (2 ^ (epsilon / 2) * t ^ (epsilon / 2))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hMpower
            (heathBrownLogConstant_pos hepsilon).le)
          (inv_nonneg.mpr hlogTwo.le)
      _ = (Real.log 2)⁻¹ * heathBrownLogConstant epsilon *
          2 ^ (epsilon / 2) * t ^ (epsilon / 2) := by ring
  let q : ℝ := heathBrownHalfZetaKappa *
    (1 - sigma) ^ (3 / 2 : ℝ)
  have hq : 0 ≤ q := by
    dsimp only [q, heathBrownHalfZetaKappa]
    positivity
  have htarget : 0 ≤ q + epsilon := by positivity
  have htTarget : 1 ≤ t ^ (q + epsilon) :=
    Real.one_le_rpow htOne htarget
  have hfiniteRaw := hfinite sigma t hsigma hsigmaUpper hsigmaNear ht
  have hfiniteFinal : ‖fordHurwitzFiniteApproximation sigma 1 t‖ ≤
      (1 + K) * t ^ (q + epsilon) := by
    calc
      ‖fordHurwitzFiniteApproximation sigma 1 t‖ ≤
          1 + (Nat.clog 2 M : ℝ) *
            (C₀ * t ^ (q + epsilon / 2)) := by
        simpa only [M, q] using hfiniteRaw
      _ ≤ 1 +
          ((Real.log 2)⁻¹ * heathBrownLogConstant epsilon *
            2 ^ (epsilon / 2) * t ^ (epsilon / 2)) *
              (C₀ * t ^ (q + epsilon / 2)) := by
        gcongr
      _ = 1 + K * t ^ (q + epsilon) := by
        have hpowEq : t ^ (epsilon / 2) * t ^ (q + epsilon / 2) =
            t ^ (q + epsilon) := by
          rw [← Real.rpow_add htPos]
          congr 1
          ring
        dsimp only [K]
        rw [← hpowEq]
        ring
      _ ≤ t ^ (q + epsilon) + K * t ^ (q + epsilon) :=
        by linarith
      _ = (1 + K) * t ^ (q + epsilon) := by ring
  have hrem := norm_riemannZeta_sub_fordFiniteApproximation_le_fifteen
    hsigma hsigmaUpper ht
  have hnegPower : t ^ (-sigma) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le htOne (by linarith : -sigma ≤ 0)
  calc
    ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
        ‖riemannZeta (fordComplexHeight sigma t) -
            fordHurwitzFiniteApproximation sigma 1 t‖ +
          ‖fordHurwitzFiniteApproximation sigma 1 t‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (riemannZeta (fordComplexHeight sigma t) -
          fordHurwitzFiniteApproximation sigma 1 t)
        (fordHurwitzFiniteApproximation sigma 1 t)
    _ ≤ 15 * t ^ (-sigma) + (1 + K) * t ^ (q + epsilon) :=
      add_le_add hrem hfiniteFinal
    _ ≤ 15 * 1 + (1 + K) * t ^ (q + epsilon) := by
      gcongr
    _ ≤ 15 * t ^ (q + epsilon) + (1 + K) * t ^ (q + epsilon) := by
      gcongr
    _ = C * t ^ (heathBrownHalfZetaKappa *
        (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
      dsimp only [C, q]
      ring

#print axioms norm_fordDyadicWeightedShellSum_zero_le_hybrid
#print axioms norm_fordHurwitzFiniteApproximation_one_le_hybrid
#print axioms norm_riemannZeta_le_heathBrownHybrid

end

end GafniTao

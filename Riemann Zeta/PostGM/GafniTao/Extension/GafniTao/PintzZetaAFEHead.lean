import GafniTao.PintzZetaAFEDualKernel
import GafniTao.HeathBrownHybridZetaBlock

/-!
# Residue heads and the short-conductor Dirichlet sum

This file identifies both AFE residue heads exactly.  It also sums the
Heath--Brown estimate only over dyadic shells below the square-root
conductor, so no near-one hypothesis from the longer Ford range enters.
-/

open Complex Finset
open scoped BigOperators LSeries.notation

namespace GafniTao

noncomputable section

/-- A positive zeta-series coefficient is the usual complex power. -/
theorem pintzZetaDirichletTerm_eq_cpow
    {s : ℂ} {n : ℕ} (hn : n ≠ 0) :
    pintzZetaDirichletTerm s n = (n : ℂ) ^ (-s) := by
  rw [pintzZetaDirichletTerm, LSeries.term_of_ne_zero hn,
    ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hn]
  rw [Complex.cpow_neg]
  simp

/-- The original-side residue is exactly its ordinary Dirichlet
coefficient. -/
theorem pintzZetaAFETermNumerator_zero_original
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (n : ℕ) :
    pintzZetaAFETermNumerator s s n 0 = pintzZetaDirichletTerm s n := by
  rw [pintzZetaAFETermNumerator_zero]
  unfold pintzZetaAFENormalization
  have hs : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h1s : 1 - s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hgamma := Complex.Gammaℝ_ne_zero_of_re_pos hs0
  field_simp

/-- The dual residue exposes exactly the functional-equation Gamma
quotient. -/
theorem pintzZetaAFETermNumerator_zero_dual
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (n : ℕ) :
    pintzZetaAFETermNumerator s (1 - s) n 0 =
      (Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s) *
        pintzZetaDirichletTerm (1 - s) n := by
  rw [pintzZetaAFETermNumerator_zero]
  unfold pintzZetaAFENormalization
  have hs : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h1s : 1 - s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hgammaS := Complex.Gammaℝ_ne_zero_of_re_pos hs0
  have hgammaDual : Complex.Gammaℝ (1 - s) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  field_simp
  ring

/-- The original residue head is exactly the finite zeta Dirichlet
polynomial at the physical height. -/
theorem pintzZetaAFEHeadResidue_original_eq
    {sigma t : ℝ} (hsigmaLower : 0 < sigma) (hsigmaUpper : sigma < 1)
    (M : ℕ) :
    pintzZetaAFEHeadResidue (fordComplexHeight sigma t)
        (fordComplexHeight sigma t) (Finset.Icc 1 M) =
      ∑ n ∈ Finset.Icc 1 M,
        (n : ℂ) ^ (-fordComplexHeight sigma t) := by
  unfold pintzZetaAFEHeadResidue
  apply Finset.sum_congr rfl
  intro n hn
  rw [pintzZetaAFETermNumerator_zero_original
    (by simpa [fordComplexHeight] using hsigmaLower)
    (by simpa [fordComplexHeight] using hsigmaUpper)]
  exact pintzZetaDirichletTerm_eq_cpow (by
    have hnOne : 1 ≤ n := Finset.mem_Icc.mp hn |>.1
    omega)

/-- The dual residue head is the functional-equation Gamma quotient times
the finite Dirichlet polynomial at reflected real part and opposite height. -/
theorem pintzZetaAFEHeadResidue_dual_eq
    {sigma t : ℝ} (hsigmaLower : 0 < sigma) (hsigmaUpper : sigma < 1)
    (M : ℕ) :
    pintzZetaAFEHeadResidue (fordComplexHeight sigma t)
        (1 - fordComplexHeight sigma t) (Finset.Icc 1 M) =
      (Complex.Gammaℝ (1 - fordComplexHeight sigma t) /
          Complex.Gammaℝ (fordComplexHeight sigma t)) *
        ∑ n ∈ Finset.Icc 1 M,
          (n : ℂ) ^ (-fordComplexHeight (1 - sigma) (-t)) := by
  have hreflect :
      (1 : ℂ) - fordComplexHeight sigma t =
        fordComplexHeight (1 - sigma) (-t) := by
    apply Complex.ext <;> simp [fordComplexHeight]
  unfold pintzZetaAFEHeadResidue
  calc
    ∑ n ∈ Finset.Icc 1 M,
        pintzZetaAFETermNumerator (fordComplexHeight sigma t)
          (1 - fordComplexHeight sigma t) n 0 =
        ∑ n ∈ Finset.Icc 1 M,
          (Complex.Gammaℝ (1 - fordComplexHeight sigma t) /
              Complex.Gammaℝ (fordComplexHeight sigma t)) *
            pintzZetaDirichletTerm
              (1 - fordComplexHeight sigma t) n := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact pintzZetaAFETermNumerator_zero_dual
        (by simpa [fordComplexHeight] using hsigmaLower)
        (by simpa [fordComplexHeight] using hsigmaUpper) n
    _ = (Complex.Gammaℝ (1 - fordComplexHeight sigma t) /
          Complex.Gammaℝ (fordComplexHeight sigma t)) *
        ∑ n ∈ Finset.Icc 1 M,
          pintzZetaDirichletTerm
            (1 - fordComplexHeight sigma t) n := by rw [Finset.mul_sum]
    _ = (Complex.Gammaℝ (1 - fordComplexHeight sigma t) /
          Complex.Gammaℝ (fordComplexHeight sigma t)) *
        ∑ n ∈ Finset.Icc 1 M,
          (n : ℂ) ^ (-fordComplexHeight (1 - sigma) (-t)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [pintzZetaDirichletTerm_eq_cpow (by
        have hnOne : 1 ≤ n := Finset.mem_Icc.mp hn |>.1
        omega), hreflect]

/-- Every positive block below the square-root conductor has the
Heath--Brown half-range exponent, including the finitely many small blocks.
-/
theorem norm_fordShiftedWeightedBlock_zero_le_all_short_zeta
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (N R : ℕ),
      0 ≤ sigma → sigma ≤ 1 → 0 < N → N < R → R ≤ 2 * N →
      (N : ℝ) ^ 2 ≤ t →
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  obtain ⟨Cshort, hCshort, hshort⟩ :=
    norm_fordShiftedWeightedBlock_zero_le_half_zeta hepsilon
  let C : ℝ := Cshort + 1024 * fordQualitativeCoefficient
  have hC : 0 < C := by
    dsimp only [C]
    nlinarith [fordQualitativeCoefficient_nonneg]
  refine ⟨C, hC, ?_⟩
  intro sigma t N R hsigma hsigmaUpper hN hNR hR hNt
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have htOne : 1 ≤ t := by
    have hNsq : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    exact hNsq.trans hNt
  let p : ℝ := heathBrownHalfZetaKappa *
    (1 - sigma) ^ (3 / 2 : ℝ) + epsilon
  have hp : 0 ≤ p := by
    dsimp only [p, heathBrownHalfZetaKappa]
    positivity
  have htp : 1 ≤ t ^ p := Real.one_le_rpow htOne hp
  by_cases hlarge : 1024 ≤ N
  · have hraw := hshort sigma t N R hsigma hsigmaUpper hlarge hNR hR hNt
    exact hraw.trans (by
      apply mul_le_mul_of_nonneg_right
      · dsimp only [C]
        nlinarith [fordQualitativeCoefficient_nonneg]
      · positivity)
  · have hNtop : N ≤ 1024 := by omega
    have hNleT : (N : ℝ) ≤ t := by
      have hNsqN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      exact hNsqN.trans hNt
    have hraw := norm_fordShiftedWeightedBlock_zero_le_general
      ford_exponential_sum_qualitative fordQualitativeCoefficient_nonneg
      hsigma hN hNleT hNR hR
    have hweight : (((N + 1 : ℕ) : ℝ) ^ (-sigma)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast (show 1 ≤ N + 1 by omega)
      · linarith
    have hexponent :
        1 - 1 / (3000000 * fordLambda N t ^ 2) ≤ 1 := by
      have : 0 ≤ 1 / (3000000 * fordLambda N t ^ 2) := by positivity
      linarith
    have hpow : (N : ℝ) ^
        (1 - 1 / (3000000 * fordLambda N t ^ 2)) ≤ (N : ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hNOne hexponent
    have hmajorant :
        fordGeneralMajorant fordQualitativeCoefficient 3000000 N t ≤
          fordQualitativeCoefficient * (N : ℝ) := by
      unfold fordGeneralMajorant
      exact mul_le_mul_of_nonneg_left hpow fordQualitativeCoefficient_nonneg
    have hsmall :
        ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
          1024 * fordQualitativeCoefficient := by
      calc
        ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
            (((N + 1 : ℕ) : ℝ) ^ (-sigma)) *
              fordGeneralMajorant fordQualitativeCoefficient 3000000 N t := by
          simpa only [Nat.cast_add, Nat.cast_one] using hraw
        _ ≤ 1 * fordGeneralMajorant fordQualitativeCoefficient 3000000 N t :=
          mul_le_mul_of_nonneg_right hweight (by
            unfold fordGeneralMajorant
            exact mul_nonneg fordQualitativeCoefficient_nonneg
              (Real.rpow_nonneg (Nat.cast_nonneg N) _))
        _ ≤ 1 * (fordQualitativeCoefficient * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hmajorant (by norm_num)
        _ ≤ 1024 * fordQualitativeCoefficient := by
          rw [one_mul]
          have hNtopReal : (N : ℝ) ≤ 1024 := by exact_mod_cast hNtop
          nlinarith [fordQualitativeCoefficient_nonneg]
    calc
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
          1024 * fordQualitativeCoefficient := hsmall
      _ ≤ C * 1 := by
        dsimp only [C]
        nlinarith [hCshort, fordQualitativeCoefficient_nonneg]
      _ ≤ C * t ^ p := mul_le_mul_of_nonneg_left htp hC.le
      _ = C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := rfl

/-- The exact finite Dirichlet head below a square-root conductor, with only
the dyadic shell count left visible. -/
theorem norm_pintzZeta_short_head_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (M : ℕ),
      0 ≤ sigma → sigma ≤ 1 → 1 ≤ M → (M : ℝ) ^ 2 ≤ t →
      ‖∑ n ∈ Finset.Icc 1 M,
          (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
        1 + (Nat.clog 2 M : ℝ) *
          (C * t ^ (heathBrownHalfZetaKappa *
            (1 - sigma) ^ (3 / 2 : ℝ) + epsilon)) := by
  obtain ⟨C, hC, hblock⟩ :=
    norm_fordShiftedWeightedBlock_zero_le_all_short_zeta hepsilon
  refine ⟨C, hC, ?_⟩
  intro sigma t M hsigma hsigmaUpper hM hMt
  rw [partialZeta_eq_one_add_fordDyadic hM]
  calc
    ‖(1 : ℂ) + fordDyadicWeightedShellSum sigma (Nat.clog 2 M) M 0 t‖ ≤
        1 + ‖fordDyadicWeightedShellSum sigma (Nat.clog 2 M) M 0 t‖ := by
      simpa using norm_add_le (1 : ℂ)
        (fordDyadicWeightedShellSum sigma (Nat.clog 2 M) M 0 t)
    _ ≤ 1 + ∑ _j ∈ Finset.range (Nat.clog 2 M),
        C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
      unfold fordDyadicWeightedShellSum
      gcongr
      calc
        ‖∑ j ∈ Finset.range (Nat.clog 2 M),
            fordShiftedWeightedBlock sigma (2 ^ j)
              (min M (2 ^ (j + 1))) 0 t‖ ≤
          ∑ j ∈ Finset.range (Nat.clog 2 M),
            ‖fordShiftedWeightedBlock sigma (2 ^ j)
              (min M (2 ^ (j + 1))) 0 t‖ := norm_sum_le _ _
        _ ≤ _ := by
          gcongr with j hj
          have hjlt : j < Nat.clog 2 M := Finset.mem_range.mp hj
          have hjM : 2 ^ j < M := Nat.pow_lt_of_lt_clog hjlt
          have hjSq : (((2 ^ j : ℕ) : ℝ) ^ 2) ≤ t := by
            have hjReal : ((2 ^ j : ℕ) : ℝ) ≤ M := by exact_mod_cast hjM.le
            exact (sq_le_sq₀ (by positivity) (by positivity)).2 hjReal |>.trans hMt
          have hjSucc : (2 : ℕ) ^ j < 2 ^ (j + 1) :=
            pow_lt_pow_right₀ (by omega) (by omega)
          exact hblock sigma t (2 ^ j) (min M (2 ^ (j + 1)))
            hsigma hsigmaUpper (pow_pos (by omega) _)
            (lt_min hjM hjSucc)
            (by
              calc
                min M (2 ^ (j + 1)) ≤ 2 ^ (j + 1) := min_le_right _ _
                _ = 2 * 2 ^ j := by rw [pow_succ]; omega)
            hjSq
    _ = 1 + (Nat.clog 2 M : ℝ) *
        (C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon)) := by simp

/-- The original residue head inherits the square-root-conductor
Heath--Brown estimate with no near-one restriction. -/
theorem norm_pintzZetaAFEHeadResidue_original_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (M : ℕ),
      0 < sigma → sigma < 1 → 1 ≤ M → (M : ℝ) ^ 2 ≤ t →
      ‖pintzZetaAFEHeadResidue (fordComplexHeight sigma t)
          (fordComplexHeight sigma t) (Finset.Icc 1 M)‖ ≤
        1 + (Nat.clog 2 M : ℝ) *
          (C * t ^ (heathBrownHalfZetaKappa *
            (1 - sigma) ^ (3 / 2 : ℝ) + epsilon)) := by
  obtain ⟨C, hC, hhead⟩ := norm_pintzZeta_short_head_le hepsilon
  refine ⟨C, hC, ?_⟩
  intro sigma t M hsigmaLower hsigmaUpper hM hMt
  rw [pintzZetaAFEHeadResidue_original_eq hsigmaLower hsigmaUpper]
  exact hhead sigma t M hsigmaLower.le hsigmaUpper.le hM hMt

/-- The dual residue head is bounded by its exact Gamma conductor factor
times the reflected finite zeta polynomial. -/
theorem norm_pintzZetaAFEHeadResidue_dual_le
    {epsilon sigma : ℝ} (hepsilon : 0 < epsilon)
    (hsigmaLower : 1 / 2 < sigma) (hsigmaUpper : sigma < 1) :
    ∃ Cgamma Chead : ℝ, 0 < Cgamma ∧ 0 < Chead ∧
      ∀ (t : ℝ) (M : ℕ), 4 ≤ t → 1 ≤ M →
        (M : ℝ) ^ 2 ≤ t →
        ‖pintzZetaAFEHeadResidue (fordComplexHeight sigma t)
            (1 - fordComplexHeight sigma t) (Finset.Icc 1 M)‖ ≤
          Real.exp (Cgamma + Real.log (t / 4 + 2) * (1 / 2 - sigma)) *
            (1 + (Nat.clog 2 M : ℝ) *
              (Chead * t ^ (heathBrownHalfZetaKappa *
                sigma ^ (3 / 2 : ℝ) + epsilon))) := by
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    exists_norm_GammaR_dual_ratio_le hsigmaLower hsigmaUpper
  obtain ⟨Chead, hChead, hhead⟩ := norm_pintzZeta_short_head_le hepsilon
  refine ⟨Cgamma, Chead, hCgamma, hChead, ?_⟩
  intro t M ht hM hMt
  have hgammaBound := hgamma t ht
  have hsum := hhead (1 - sigma) t M
    (by linarith) (by linarith) hM hMt
  rw [show 1 - (1 - sigma) = sigma by ring] at hsum
  rw [pintzZetaAFEHeadResidue_dual_eq
    (by linarith) hsigmaUpper, norm_mul]
  have hGammaEq :
      ‖Complex.Gammaℝ (1 - fordComplexHeight sigma t) /
          Complex.Gammaℝ (fordComplexHeight sigma t)‖ =
        ‖Complex.Gammaℝ (((1 - sigma : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) /
          Complex.Gammaℝ ((sigma : ℂ) + (t : ℂ) * I)‖ := by
    congr 3
    · apply Complex.ext <;> simp [fordComplexHeight]
  rw [hGammaEq, norm_partialZeta_height_abs]
  rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ t)]
  exact mul_le_mul hgammaBound hsum (norm_nonneg _) (Real.exp_pos _).le

#print axioms pintzZetaDirichletTerm_eq_cpow
#print axioms pintzZetaAFETermNumerator_zero_original
#print axioms pintzZetaAFETermNumerator_zero_dual
#print axioms pintzZetaAFEHeadResidue_original_eq
#print axioms pintzZetaAFEHeadResidue_dual_eq
#print axioms norm_fordShiftedWeightedBlock_zero_le_all_short_zeta
#print axioms norm_pintzZeta_short_head_le
#print axioms norm_pintzZetaAFEHeadResidue_original_le
#print axioms norm_pintzZetaAFEHeadResidue_dual_le

end

end GafniTao

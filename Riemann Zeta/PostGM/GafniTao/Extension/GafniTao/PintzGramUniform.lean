import GafniTao.PintzPhysicalDetector

/-!
# A uniform physical majorant for Pintz's Gram matrix

The selected detector ordinates lie in a bounded displacement of the
original zero box.  This file turns the two-regime partial-zeta estimate into
one explicit bound valid for every difference of selected ordinates.  Both
the short-cutoff and Euler--Maclaurin regimes remain visible in the sum.
-/

namespace GafniTao

noncomputable section

/-- A nonnegative sum majorizing both branches of
`pintzPartialZetaMajorant` on the height interval `3 <= |t| <= B`. -/
noncomputable def pintzUniformPartialZetaMajorant
    (sigma : ℝ) (M : ℕ) (B : ℝ) : ℝ :=
  pintzShortCutoffMajorant sigma B +
    pintzLongCutoffMajorant sigma M B

theorem pintzMobiusCutoff_pos (lambda : ℝ) :
    1 ≤ pintzMobiusCutoff lambda := by
  unfold pintzMobiusCutoff
  exact Nat.one_le_ceil_iff.mpr (Real.exp_pos (lambda + 3))

theorem pintzShortCutoffMajorant_nonneg
    {sigma t : ℝ} (ht : 1 ≤ |t|) :
    0 ≤ pintzShortCutoffMajorant sigma t := by
  unfold pintzShortCutoffMajorant
  have hlog : 0 ≤ Real.log |t| := Real.log_nonneg ht
  have hc : 0 ≤ 1 + 1.569 * (3000000 : ℝ) ^ ((1 : ℝ) / 3) *
      Real.log |t| ^ ((2 : ℝ) / 3) := by positivity
  have hp : 0 ≤ |t| ^
      (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
    Real.rpow_nonneg (abs_nonneg t) _
  exact add_nonneg (by norm_num)
    (mul_nonneg fordQualitativeCoefficient_nonneg (mul_nonneg hp hc))

theorem pintzLongCutoffMajorant_nonneg
    {sigma t : ℝ} {M : ℕ} (ht : 1 ≤ |t|) :
    0 ≤ pintzLongCutoffMajorant sigma M t := by
  unfold pintzLongCutoffMajorant
  have hlog : 0 ≤ Real.log |t| := Real.log_nonneg ht
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg fordQualitativeGlobalCoefficient_nonneg
        (Real.rpow_nonneg (abs_nonneg t) _))
      (Real.rpow_nonneg hlog _))
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg M) _))

/-- Monotonicity in the physical height variable, with no choice of cutoff
regime suppressed. -/
theorem pintzPartialZetaMajorant_le_uniform
    {sigma t B : ℝ} {M : ℕ}
    (hsigmaUpper : sigma ≤ 1)
    (htLower : 3 ≤ |t|) (htUpper : |t| ≤ B) :
    pintzPartialZetaMajorant sigma M t ≤
      pintzUniformPartialZetaMajorant sigma M B := by
  have hB : 1 ≤ B := by linarith
  have htOne : 1 ≤ |t| := by linarith
  have hgap : 0 ≤ 1 - sigma := by linarith
  have hsourceB : 0 ≤ fordSourceB 3000000 :=
    le_trans (by norm_num) four_le_fordSourceB_three_million
  have hexponent :
      0 ≤ fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ) := by
    positivity
  have hheightPower :
      |t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) ≤
        B ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
    Real.rpow_le_rpow (abs_nonneg t) htUpper hexponent
  have hlogMono : Real.log |t| ≤ Real.log B :=
    Real.log_le_log (by positivity) htUpper
  have hlogT : 0 ≤ Real.log |t| := Real.log_nonneg htOne
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlogPower :
      Real.log |t| ^ (2 / 3 : ℝ) ≤ Real.log B ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hlogT hlogMono (by norm_num)
  have hscaleNonneg :
      0 ≤ 1.569 * (3000000 : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hparenT :
      0 ≤ 1 + 1.569 * (3000000 : ℝ) ^ ((1 : ℝ) / 3) *
        Real.log |t| ^ ((2 : ℝ) / 3) := by positivity
  have hparen :
      1 + 1.569 * (3000000 : ℝ) ^ ((1 : ℝ) / 3) *
          Real.log |t| ^ ((2 : ℝ) / 3) ≤
        1 + 1.569 * (3000000 : ℝ) ^ ((1 : ℝ) / 3) *
          Real.log B ^ ((2 : ℝ) / 3) := by
    gcongr
  have hproduct :
      |t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * (3000000 : ℝ) ^ ((1 : ℝ) / 3) *
            Real.log |t| ^ ((2 : ℝ) / 3)) ≤
        B ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * (3000000 : ℝ) ^ ((1 : ℝ) / 3) *
            Real.log B ^ ((2 : ℝ) / 3)) := by
    exact mul_le_mul hheightPower hparen hparenT
      (Real.rpow_nonneg (by linarith) _)
  have hshort :
      pintzShortCutoffMajorant sigma t ≤
        pintzShortCutoffMajorant sigma B := by
    unfold pintzShortCutoffMajorant
    rw [abs_of_nonneg (by linarith : 0 ≤ B)]
    exact add_le_add_right
      (mul_le_mul_of_nonneg_left hproduct fordQualitativeCoefficient_nonneg) 1
  have hlong :
      pintzLongCutoffMajorant sigma M t ≤
        pintzLongCutoffMajorant sigma M B := by
    unfold pintzLongCutoffMajorant
    rw [abs_of_nonneg (by linarith : 0 ≤ B)]
    have hlogProduct :
        |t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
            Real.log |t| ^ (2 / 3 : ℝ) ≤
          B ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
            Real.log B ^ (2 / 3 : ℝ) := by
      exact mul_le_mul hheightPower hlogPower
        (Real.rpow_nonneg hlogT _)
        (Real.rpow_nonneg (by linarith) _)
    have hfordProduct :
        fordQualitativeGlobalCoefficient *
            |t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
              Real.log |t| ^ (2 / 3 : ℝ) ≤
          fordQualitativeGlobalCoefficient *
            B ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
              Real.log B ^ (2 / 3 : ℝ) := by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hlogProduct
          fordQualitativeGlobalCoefficient_nonneg)
    exact add_le_add_left hfordProduct _
  have hshortNonneg := pintzShortCutoffMajorant_nonneg
    (sigma := sigma) (t := B) (by simpa [abs_of_nonneg (by linarith : 0 ≤ B)])
  have hlongNonneg := pintzLongCutoffMajorant_nonneg
    (sigma := sigma) (M := M) (t := B)
      (by simpa [abs_of_nonneg (by linarith : 0 ≤ B)])
  unfold pintzPartialZetaMajorant pintzUniformPartialZetaMajorant
  exact max_le (hshort.trans (le_add_of_nonneg_right hlongNonneg))
    (hlong.trans (le_add_of_nonneg_left hshortNonneg))

/-- The physical uniform Gram envelope after inserting `xi = 2 eta`, the
literal cutoff `ceil(exp(lambda+3))`, and the selected-height bound `4T`. -/
noncomputable def pintzPhysicalGramMajorant
    (eta lambda T : ℝ) : ℝ :=
  pintzUniformPartialZetaMajorant (1 - 4 * eta)
    (pintzMobiusCutoff lambda) (4 * T)

theorem pintzPhysicalGramMajorant_nonneg
    {eta lambda T : ℝ} (hT : 1 / 4 ≤ T) :
    0 ≤ pintzPhysicalGramMajorant eta lambda T := by
  unfold pintzPhysicalGramMajorant pintzUniformPartialZetaMajorant
  have hbase : 1 ≤ |4 * T| := by
    rw [abs_of_nonneg (by linarith : 0 ≤ 4 * T)]
    linarith
  exact add_nonneg
    (pintzShortCutoffMajorant_nonneg hbase)
    (pintzLongCutoffMajorant_nonneg hbase)

/-- Every separated pair of physically selected ordinates is controlled by
the single explicit Gram envelope. -/
theorem norm_pintzGramCorrelation_le_physicalMajorant
    {eta lambda T t u : ℝ}
    (heta : 0 ≤ eta) (hetaUpper : eta ≤ 1 / 8)
    (hsep : 3 ≤ |u - t|)
    (ht : |t| ≤ T + 2 * lambda) (hu : |u| ≤ T + 2 * lambda)
    (hLambdaHeight : 2 * lambda ≤ T) :
    ‖pintzGramCorrelation (2 * eta) (pintzMobiusCutoff lambda) t u‖ ≤
      pintzPhysicalGramMajorant eta lambda T := by
  have hxi : 0 ≤ 2 * eta := by positivity
  have hxiUpper : 2 * eta ≤ 1 / 4 := by linarith
  have hY := pintzMobiusCutoff_pos lambda
  have hdiffUpper : |u - t| ≤ 4 * T := by
    calc
      |u - t| ≤ |u| + |t| := abs_sub _ _
      _ ≤ 2 * (T + 2 * lambda) := by linarith
      _ ≤ 4 * T := by linarith
  have hraw := norm_pintzGramCorrelation_le_majorant
    hxi hxiUpper hsep hY
  have hsigmaEq : 1 - 2 * (2 * eta) = 1 - 4 * eta := by ring
  rw [hsigmaEq] at hraw
  have hsigmaUpper : (1 - 4 * eta : ℝ) ≤ 1 := by linarith
  exact hraw.trans (by
    unfold pintzPhysicalGramMajorant
    exact pintzPartialZetaMajorant_le_uniform
      hsigmaUpper hsep hdiffUpper)

#print axioms pintzPartialZetaMajorant_le_uniform
#print axioms norm_pintzGramCorrelation_le_physicalMajorant

end

end GafniTao

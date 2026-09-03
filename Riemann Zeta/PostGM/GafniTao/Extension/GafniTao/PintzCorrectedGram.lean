import GafniTao.PintzPartialZetaDyadic
import GafniTao.PintzPhysicalDetector

/-!
# Corrected uniform Gram bound for the Pintz density argument

Pintz's printed auxiliary majorant includes finite Dirichlet sums whose
cutoff can exceed their oscillation height.  The unconditional dyadic bound
in `PintzPartialZetaDyadic` keeps the missing endpoint cancellation visible.
This file makes that correction uniform on a separated family: Ford controls
the shells below the frequency and the terminal Kusmin--Landau estimate
contributes the explicit `M^(1-sigma) / G` term.
-/

open Complex Finset Metric
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem pintzMobiusCutoff_one_le (lambda : ℝ) :
    1 ≤ pintzMobiusCutoff lambda := by
  unfold pintzMobiusCutoff
  exact Nat.one_le_ceil_iff.mpr (Real.exp_pos (lambda + 3))

/-- The corrected arbitrary-cutoff envelope, uniform for frequencies in
`[G,B]`. -/
noncomputable def pintzCorrectedUniformPartialZetaEnvelope
    (sigma : ℝ) (M : ℕ) (B G : ℝ) : ℝ :=
  1 + fordQualitativeCoefficient *
      (B ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
        (1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
          Real.log B ^ (2 / 3 : ℝ))) +
    (Nat.clog 2 M : ℝ) *
      (6 * Real.pi * (M : ℝ) ^ (1 - sigma) / G)

/-- Uniformization of the corrected dyadic partial-zeta estimate. -/
theorem pintzCorrectedPartialZetaEnvelope_le_uniform
    {sigma B G t : ℝ} {M : ℕ}
    (hsigmaUpper : sigma ≤ 1)
    (hG : 0 < G) (hGt : G ≤ |t|)
    (ht : 1 < |t|) (htB : |t| ≤ B) :
    pintzCorrectedPartialZetaEnvelope sigma M |t| ≤
      pintzCorrectedUniformPartialZetaEnvelope sigma M B G := by
  have hB : 1 ≤ B := ht.le.trans htB
  have htOne : 1 ≤ |t| := ht.le
  have hgap : 0 ≤ 1 - sigma := by linarith
  have hexponent :
      0 ≤ fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ) := by
    exact mul_nonneg (by linarith [four_le_fordSourceB_three_million])
      (Real.rpow_nonneg hgap _)
  have hheightPower :
      |t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) ≤
        B ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) :=
    Real.rpow_le_rpow (abs_nonneg t) htB hexponent
  have hlogMono : Real.log |t| ≤ Real.log B :=
    Real.log_le_log (abs_pos.mpr (by
      intro htZero
      rw [htZero, abs_zero] at ht
      linarith)) htB
  have hlogT : 0 ≤ Real.log |t| := Real.log_nonneg htOne
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlogPower :
      Real.log |t| ^ (2 / 3 : ℝ) ≤ Real.log B ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hlogT hlogMono (by norm_num)
  have hparenT :
      0 ≤ 1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
        Real.log |t| ^ (2 / 3 : ℝ) := by positivity
  have hparen :
      1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
          Real.log |t| ^ (2 / 3 : ℝ) ≤
        1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
          Real.log B ^ (2 / 3 : ℝ) := by
    gcongr
  have hford :
      fordQualitativeCoefficient *
          (|t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
            (1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
              Real.log |t| ^ (2 / 3 : ℝ))) ≤
        fordQualitativeCoefficient *
          (B ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
            (1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
              Real.log B ^ (2 / 3 : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ fordQualitativeCoefficient_nonneg
    exact mul_le_mul hheightPower hparen hparenT
      (Real.rpow_nonneg (by linarith) _)
  have hterminalNumerator :
      0 ≤ 6 * Real.pi * (M : ℝ) ^ (1 - sigma) := by positivity
  have hterminal :
      6 * Real.pi * (M : ℝ) ^ (1 - sigma) / |t| ≤
        6 * Real.pi * (M : ℝ) ^ (1 - sigma) / G :=
    div_le_div_of_nonneg_left hterminalNumerator hG hGt
  unfold pintzCorrectedPartialZetaEnvelope
  unfold pintzCorrectedUniformPartialZetaEnvelope
  gcongr

/-- The physical Gram envelope with cutoff `ceil(exp(lambda+3))`, upper
frequency `4T`, and an explicit separation scale `G`. -/
noncomputable def pintzCorrectedPhysicalGramMajorant
    (eta lambda T G : ℝ) : ℝ :=
  pintzCorrectedUniformPartialZetaEnvelope (1 - 4 * eta)
    (pintzMobiusCutoff lambda) (4 * T) G

theorem pintzCorrectedPhysicalGramMajorant_nonneg
    {eta lambda T G : ℝ} (hT : 1 / 4 ≤ T) (hG : 0 < G) :
    0 ≤ pintzCorrectedPhysicalGramMajorant eta lambda T G := by
  unfold pintzCorrectedPhysicalGramMajorant
  unfold pintzCorrectedUniformPartialZetaEnvelope
  have hB : 1 ≤ 4 * T := by linarith
  have hBnonneg : 0 ≤ 4 * T := zero_le_one.trans hB
  have hlog : 0 ≤ Real.log (4 * T) := Real.log_nonneg hB
  have hcutoff : (0 : ℝ) < pintzMobiusCutoff lambda := by
    exact_mod_cast pintzMobiusCutoff_one_le lambda
  have hfordPower :
      0 ≤ (4 * T) ^
        (fordSourceB 3000000 * (1 - (1 - 4 * eta)) ^ (3 / 2 : ℝ)) :=
    Real.rpow_nonneg hBnonneg _
  have hfordParen :
      0 ≤ 1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
        Real.log (4 * T) ^ (2 / 3 : ℝ) := by positivity
  have hford :
      0 ≤ fordQualitativeCoefficient *
        ((4 * T) ^
            (fordSourceB 3000000 * (1 - (1 - 4 * eta)) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * (3000000 : ℝ) ^ (1 / 3 : ℝ) *
            Real.log (4 * T) ^ (2 / 3 : ℝ))) :=
    mul_nonneg fordQualitativeCoefficient_nonneg
      (mul_nonneg hfordPower hfordParen)
  have hterminal :
      0 ≤ (Nat.clog 2 (pintzMobiusCutoff lambda) : ℝ) *
        (6 * Real.pi * (pintzMobiusCutoff lambda : ℝ) ^
          (1 - (1 - 4 * eta)) / G) := by positivity
  linarith

/-- Every pair in the selected physical height window is bounded by the
corrected envelope.  The separation variable is retained because it is the
quantity that pays for the long-cutoff terminal shells. -/
theorem norm_pintzGramCorrelation_le_correctedPhysicalMajorant
    {eta lambda T G t u : ℝ}
    (heta : 0 ≤ eta) (hetaUpper : eta ≤ 1 / 4)
    (hG : 3 ≤ G) (hsep : G ≤ dist t u)
    (ht : |t| ≤ T + 2 * lambda) (hu : |u| ≤ T + 2 * lambda)
    (hLambdaHeight : 2 * lambda ≤ T) :
    ‖pintzGramCorrelation (2 * eta) (pintzMobiusCutoff lambda) t u‖ ≤
      pintzCorrectedPhysicalGramMajorant eta lambda T G := by
  have hdiff : G ≤ |u - t| := by
    simpa [Real.dist_eq, abs_sub_comm] using hsep
  have hdiffOne : 1 < |u - t| := lt_of_lt_of_le (by linarith) hdiff
  have hdiffUpper : |u - t| ≤ 4 * T := by
    calc
      |u - t| ≤ |u| + |t| := abs_sub _ _
      _ ≤ 2 * (T + 2 * lambda) := by linarith
      _ ≤ 4 * T := by linarith
  rw [pintzGramCorrelation_eq_shifted_sum]
  have hsigmaNonneg : 0 ≤ 1 - 4 * eta := by linarith
  have hsigmaUpper : (1 - 4 * eta : ℝ) ≤ 1 := by linarith
  have hsigmaEq : 1 - 2 * (2 * eta) = 1 - 4 * eta := by ring
  rw [hsigmaEq]
  have hheight :
      fordComplexHeight (1 - 4 * eta) (u - t) =
        ((1 - 4 * eta : ℝ) : ℂ) + I * (u - t) := by
    simp [fordComplexHeight, mul_comm]
  rw [← hheight]
  exact (norm_partialZeta_le_correctedEnvelope hsigmaNonneg hsigmaUpper
    hdiffOne (pintzMobiusCutoff_one_le lambda)).trans
      (by
        unfold pintzCorrectedPhysicalGramMajorant
        exact pintzCorrectedPartialZetaEnvelope_le_uniform
          hsigmaUpper (by linarith) hdiff hdiffOne hdiffUpper)

#print axioms pintzCorrectedPartialZetaEnvelope_le_uniform
#print axioms pintzMobiusCutoff_one_le
#print axioms norm_pintzGramCorrelation_le_correctedPhysicalMajorant

end

end GafniTao

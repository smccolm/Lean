import Tao2026.VinogradovFiniteDegree
import Tao2026.VinogradovWooleyCoefficient

/-!
# Optimal critical coefficients from Wooley data

This module identifies the optimal normalized critical VMVT coefficient with
the explicit upper bound produced by retained p-adic concentration data.  It
therefore joins the optimal scalar residual to the source-level Wooley
residual without an arbitrary choice of a mean-value witness.
-/

namespace Tao2026

noncomputable section

open scoped BigOperators NNReal

/-- Retained p-adic concentration data bound the optimal critical coefficient
by the exact Section-12 expression. -/
theorem vinogradovOptimalCriticalCoefficient_le_of_wooleyConcentrationData
    {R p : ℕ} (hR : 1 ≤ R) (hp : p.Prime)
    {C : ℝ} (hC : 0 < C) (B0 : ℕ)
    (hconcentration : ∀ (Q h : ℕ), 1 ≤ Q → B0 ≤ R * h → Q < p ^ h →
      (GafniTao.wooleyPadicCount
        (GafniTao.fordVinogradovKappa R) R Q p (R * h) : ℝ) ≤
          C * (p ^ (R * h) : ℝ) ^
              (vinogradovCriticalEpsilon R / (R : ℝ)) *
            (Q : ℝ) ^ GafniTao.fordVinogradovKappa R) :
    vinogradovOptimalCriticalCoefficient R ≤
      C * ((p ^ (B0 + 1) * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^
        vinogradovCriticalEpsilon R := by
  have hε : 0 < vinogradovCriticalEpsilon R :=
    vinogradovCriticalEpsilon_pos hR
  have hmoment := critical_fordMomentBound_of_wooleyConcentrationData
    hR hp hε hC B0 hconcentration
  apply vinogradovOptimalCriticalCoefficient_le_of_meanValueBound
  intro V hV
  have hlocal := vinogradovMeanValueCount_le_of_fordVinogradovMomentBound
    hmoment V hV
  simpa only [GafniTao.fordLambda34_critical] using hlocal

/-- After the critical root is extracted, the same p-adic data bound the
optimal coefficient by exactly the rooted expression already exposed in the
Wooley data contract. -/
theorem vinogradovOptimalCriticalRootCoefficient_le_of_wooleyConcentrationData
    {R p : ℕ} (hR : 1 ≤ R) (hp : p.Prime)
    {C : ℝ} (hC : 0 < C) (B0 : ℕ)
    (hconcentration : ∀ (Q h : ℕ), 1 ≤ Q → B0 ≤ R * h → Q < p ^ h →
      (GafniTao.wooleyPadicCount
        (GafniTao.fordVinogradovKappa R) R Q p (R * h) : ℝ) ≤
          C * (p ^ (R * h) : ℝ) ^
              (vinogradovCriticalEpsilon R / (R : ℝ)) *
            (Q : ℝ) ^ GafniTao.fordVinogradovKappa R) :
    vinogradovOptimalCriticalRootCoefficient R ≤
      ((C * ((p ^ (B0 + 1) * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^
          vinogradovCriticalEpsilon R) ^ 2 *
        (((3 * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^ (2 * R))) ^
          (1 / ((GafniTao.fordVinogradovKappa R *
            (2 * GafniTao.fordVinogradovKappa R) : ℕ) : ℝ)) := by
  have hε : 0 < vinogradovCriticalEpsilon R :=
    vinogradovCriticalEpsilon_pos hR
  have hmoment := critical_fordMomentBound_of_wooleyConcentrationData
    hR hp hε hC B0 hconcentration
  apply vinogradovOptimalCriticalRootCoefficient_le_of_meanValueBound hR
  intro V hV
  have hlocal := vinogradovMeanValueCount_le_of_fordVinogradovMomentBound
    hmoment V hV
  simpa only [GafniTao.fordLambda34_critical] using hlocal

/-- The source-level Wooley residual implies the equivalent optimal scalar
residual from degree `40` onward. -/
theorem vinogradovOptimalCriticalRootCoefficientBoundFrom40At_of_wooleyData
    {A : ℝ} (hA : WooleyCriticalDataRootCoefficientBoundAt A) :
    VinogradovOptimalCriticalRootCoefficientBoundFromAt 40 A := by
  apply (vinogradovCriticalRootCoefficientBoundFromAt_iff_optimal
    (by norm_num : 1 ≤ (40 : ℕ))).mp
  refine ⟨hA.1, ?_⟩
  intro R hR
  obtain ⟨C, hC, hmean, hroot⟩ :=
    (vinogradovCriticalRootCoefficientBoundAt_of_wooleyData hA).2 R hR
  refine ⟨C, hC, ?_, hroot⟩
  intro V hV
  simpa only [vinogradovCriticalEpsilon] using hmean V hV

/-- The native concentration theorem may be specialized at a Bertrand prime,
so its prime parameter always satisfies the quantitative bound `p ≤ 2R`. -/
theorem native_wooleyCriticalData_exists_with_prime_le_two_mul
    {R : ℕ} (hR : 1 ≤ R) :
    ∃ (p : ℕ) (C : ℝ) (B0 : ℕ),
      p.Prime ∧ R < p ∧ p ≤ 2 * R ∧ 0 < C ∧
      ∀ (Q h : ℕ), 1 ≤ Q → B0 ≤ R * h → Q < p ^ h →
        (GafniTao.wooleyPadicCount
          (GafniTao.fordVinogradovKappa R) R Q p (R * h) : ℝ) ≤
            C * (p ^ (R * h) : ℝ) ^
                (vinogradovCriticalEpsilon R / (R : ℝ)) *
              (Q : ℝ) ^ GafniTao.fordVinogradovKappa R := by
  obtain ⟨p, hp, hRp, hpUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul R (by omega)
  let hnative : GafniTao.WooleyMonomialPadicConcentration :=
    GafniTao.wooleyMonomialPadicConcentration_of_polynomialCorollary32
      GafniTao.wooleyPolynomialCorollary32_native
  have hδ : 0 < vinogradovCriticalEpsilon R / (R : ℝ) := by
    exact div_pos (vinogradovCriticalEpsilon_pos hR) (by exact_mod_cast hR)
  obtain ⟨C, hC, B0, hbound⟩ := hnative.specialize hp hRp hδ
  exact ⟨p, C, B0, hp, hRp, hpUpper, hC, hbound⟩

/-- Exact remaining p-adic tail contract, with the concentration prime already
restricted to the Bertrand range. -/
def WooleyCriticalDataRootCoefficientBoundFromAt
    (M : ℕ) (A : ℝ) : Prop :=
  1 ≤ A ∧ ∀ R : ℕ, M ≤ R →
    ∃ (p : ℕ) (C : ℝ) (B0 : ℕ),
      p.Prime ∧ R < p ∧ p ≤ 2 * R ∧ 0 < C ∧
      (∀ (Q h : ℕ), 1 ≤ Q → B0 ≤ R * h → Q < p ^ h →
        (GafniTao.wooleyPadicCount
          (GafniTao.fordVinogradovKappa R) R Q p (R * h) : ℝ) ≤
            C * (p ^ (R * h) : ℝ) ^
                (vinogradovCriticalEpsilon R / (R : ℝ)) *
              (Q : ℝ) ^ GafniTao.fordVinogradovKappa R) ∧
      ((C * ((p ^ (B0 + 1) * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^
          vinogradovCriticalEpsilon R) ^ 2 *
        (((3 * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^ (2 * R))) ^
          (1 / ((GafniTao.fordVinogradovKappa R *
            (2 * GafniTao.fordVinogradovKappa R) : ℕ) : ℝ)) ≤ A

theorem vinogradovOptimalCriticalRootCoefficientBoundFromAt_of_wooleyTail
    {M : ℕ} {A : ℝ} (hM : 1 ≤ M)
    (hA : WooleyCriticalDataRootCoefficientBoundFromAt M A) :
    VinogradovOptimalCriticalRootCoefficientBoundFromAt M A := by
  refine ⟨hA.1, ?_⟩
  intro R hR
  obtain ⟨p, C, B0, hp, hRp, hpUpper, hC, hconcentration, hroot⟩ :=
    hA.2 R hR
  exact (vinogradovOptimalCriticalRootCoefficient_le_of_wooleyConcentrationData
    (hM.trans hR) hp hC B0 hconcentration).trans hroot

abbrev WooleyCriticalDataRootCoefficientBoundFrom1000At (A : ℝ) : Prop :=
  WooleyCriticalDataRootCoefficientBoundFromAt 1000 A

/-- The bounded-prime p-adic tail inequality alone supplies the source-facing
nontrivial bilinear estimate. -/
theorem vinogradovBilinearPolynomialNontrivialEstimateAt_of_wooleyTail1000
    {A : ℝ} (hA : WooleyCriticalDataRootCoefficientBoundFrom1000At A) :
    VinogradovBilinearPolynomialNontrivialEstimateAt
      (2 * max vinogradovFiniteDegreeRootEnvelope A) :=
  vinogradovBilinearPolynomialNontrivialEstimateAt_of_optimal_from1000
    (vinogradovOptimalCriticalRootCoefficientBoundFromAt_of_wooleyTail
      (by norm_num) hA)

/-- Root-free formulation of the p-adic tail: the exact Section-12
coefficient may grow like one fixed base to `κ_R²`. -/
def WooleyCriticalDataCoefficientGrowthBoundFromAt
    (M : ℕ) (A : ℝ) : Prop :=
  1 ≤ A ∧ ∀ R : ℕ, M ≤ R →
    ∃ (p : ℕ) (C : ℝ) (B0 : ℕ),
      p.Prime ∧ R < p ∧ p ≤ 2 * R ∧ 0 < C ∧
      (∀ (Q h : ℕ), 1 ≤ Q → B0 ≤ R * h → Q < p ^ h →
        (GafniTao.wooleyPadicCount
          (GafniTao.fordVinogradovKappa R) R Q p (R * h) : ℝ) ≤
            C * (p ^ (R * h) : ℝ) ^
                (vinogradovCriticalEpsilon R / (R : ℝ)) *
              (Q : ℝ) ^ GafniTao.fordVinogradovKappa R) ∧
      C * ((p ^ (B0 + 1) * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^
          vinogradovCriticalEpsilon R ≤
        A ^ (GafniTao.fordVinogradovKappa R ^ 2)

/-- The root-free p-adic growth contract directly bounds the optimal VMVT
coefficient at the exact admissible exponential scale. -/
theorem vinogradovOptimalCriticalCoefficientGrowthBoundFromAt_of_wooleyData
    {M : ℕ} {A : ℝ} (hM : 1 ≤ M)
    (hA : WooleyCriticalDataCoefficientGrowthBoundFromAt M A) :
    VinogradovOptimalCriticalCoefficientGrowthBoundFromAt M A := by
  refine ⟨hA.1, ?_⟩
  intro R hR
  obtain ⟨p, C, B0, hp, hRp, hpUpper, hC, hconcentration, hgrowth⟩ :=
    hA.2 R hR
  exact (vinogradovOptimalCriticalCoefficient_le_of_wooleyConcentrationData
    (hM.trans hR) hp hC B0 hconcentration).trans hgrowth

abbrev WooleyCriticalDataCoefficientGrowthBoundFrom1000At (A : ℝ) : Prop :=
  WooleyCriticalDataCoefficientGrowthBoundFromAt 1000 A

/-- Final source-facing consumer of the single explicit p-adic coefficient
growth inequality on `R ≥ 1000`. -/
theorem vinogradovBilinearPolynomialNontrivialEstimateAt_of_wooleyCoefficientGrowth1000
    {A : ℝ}
    (hA : WooleyCriticalDataCoefficientGrowthBoundFrom1000At A) :
    VinogradovBilinearPolynomialNontrivialEstimateAt
      (2 * max vinogradovFiniteDegreeRootEnvelope (3 * A)) :=
  vinogradovBilinearPolynomialNontrivialEstimateAt_of_coefficientGrowth_from1000
    (vinogradovOptimalCriticalCoefficientGrowthBoundFromAt_of_wooleyData
      (by norm_num) hA)

end

end Tao2026

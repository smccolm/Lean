import TaoTrudgianYang2025.HeathBrownSourceTail
import TaoTrudgianYang2025.HeathBrownPhysicalMajorant
import GafniTao.HeathBrownKthDerivativeSetup

/-!
# Actual model-sum deduction from the kth-derivative source theorem

The only supplied analytic input is the explicitly named Heath--Brown
derivative theorem. The model sign, derivative scale, interval length,
endpoints, source sum and every uniform constant are derived here.
-/

noncomputable section

open Expdb Set
open scoped ContDiff FourierTransform BigOperators

namespace TaoTrudgianYang2025

theorem heathBrownCharacterSum_eq_source (L : ℕ) (f : ℝ → ℝ) :
    heathBrownCharacterSum L f = GafniTao.heathBrownExponentialSum L f := rfl

theorem heathBrownDerivativeMajorant_eq_source (k : ℕ) (η L lambda : ℝ) :
    heathBrownDerivativeMajorant k η L lambda =
      L^(1+η)*GafniTao.heathBrownKthDerivativeFactor k L lambda := by
  simp only [heathBrownDerivativeMajorant,heathBrownDerivativeExponent,
    heathBrownInverseExponent,GafniTao.heathBrownKthDerivativeFactor,
    div_eq_mul_inv,one_mul,neg_mul]

theorem source_exponentialSum_heathBrown_bound_of_derivative
    (hHB : GafniTao.HeathBrownKthDerivativeTheorem)
    {k : ℕ} (hk : 3 ≤ k) {σ η : ℝ} (hσ : 0 < σ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 1 ≤ P ∧ ∃ K : ℝ, 1 ≤ K ∧
      ∀ (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ),
        0 < T → 1 ≤ N → N ≤ (a : ℝ) → ((a+L : ℕ) : ℝ) ≤ 2*N →
        IsApproximateModelPhaseFunction F σ P δ →
        ‖exponentialSumAt F T N a (a+L)‖ ≤ K*heathBrownPowerMajorant k η T N := by
  let p := k-1
  have hp : p+1 = k := Nat.sub_add_cancel (by omega)
  let c := modelPhaseJetLower σ p
  have hc : 0 < c := modelPhaseJetLower_pos hσ p
  let A := (modelPhaseJetCoefficient σ p+1)/c
  have hA : 0 < A := div_pos (by
    have hcoef := modelPhaseJetCoefficient_nonneg σ p
    linarith) hc
  obtain ⟨C,hC,hsource⟩ := hHB k A η hk hA hη
  let B := c^(heathBrownDerivativeExponent k)+1+c^(-heathBrownInverseExponent k)
  have hB : 0 < B := by dsimp only [B]; positivity
  let K := 1+C*B
  have hK : 1 ≤ K := by
    dsimp only [K]
    have hprod := mul_pos hC hB
    linarith
  refine ⟨min c 1,lt_min hc (by norm_num),p,by dsimp only [p]; omega,K,hK,?_⟩
  intro F T N a L hT hN ha hb hF
  have hNpos := zero_lt_one.trans_le hN
  have htail := norm_exponentialSumAt_le_one_add_heathBrownTail F T N a L
  have hMone := one_le_heathBrownPowerMajorant hk hη.le hT hN
  by_cases hL : 0 < L
  · have hLpos : (0 : ℝ) < L := Nat.cast_pos.mpr hL
    have hb' : (a : ℝ)+(L : ℝ) ≤ 2*N := by simpa only [Nat.cast_add] using hb
    have hLN : (L : ℝ) ≤ N := by linarith
    let lambda := c*T/N^k
    have hlambda : 0 < lambda := by dsimp only [lambda]; positivity
    let f := heathBrownPhysicalPhase F T N a (modelPhaseJetSign σ p)
    have hf := heathBrownPhysicalPhase_contDiffOn hF.1 hNpos ha hb' T (modelPhaseJetSign σ p)
    have hderiv : ∀ x ∈ Ioo (0 : ℝ) (L : ℝ),
        lambda ≤ iteratedDeriv k f x ∧ iteratedDeriv k f x ≤ A*lambda := by
      intro x hx
      have hj := heathBrownPhysicalPhase_signed_derivative_bounds
        hσ hT hNpos ha hb' hF hx p le_rfl le_rfl
      rw [hp] at hj
      have he : A*lambda = (modelPhaseJetCoefficient σ p+1)*T/N^k := by
        dsimp only [A,lambda]
        field_simp
      rw [he]
      exact hj
    have hraw := hsource L lambda f hL hlambda hf.continuousOn
      ((hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).mono Ioo_subset_Icc_self)
      hderiv
    have hraw' : ‖heathBrownCharacterSum L f‖ ≤
        C*heathBrownDerivativeMajorant k η L lambda := by
      simpa only [heathBrownCharacterSum_eq_source,heathBrownDerivativeMajorant_eq_source,
        mul_assoc] using hraw
    have hmono := heathBrownDerivativeMajorant_mono_length hk hη.le hLpos hLN hlambda
    have hphysical := heathBrownDerivativeMajorant_le_powerMajorant hk hc hT hNpos η
    have hnorm : ‖heathBrownSourceTail F T N a L‖ ≤ C*B*heathBrownPowerMajorant k η T N := by
      rw [norm_heathBrownSourceTail_eq_signed_characterSum F T N σ a L p]
      apply hraw'.trans
      have htotal := hmono.trans hphysical
      have hscaled := mul_le_mul_of_nonneg_left htotal hC.le
      simpa only [B,lambda,mul_assoc] using hscaled
    dsimp only [K]
    nlinarith
  · have hzero : L = 0 := by omega
    subst L
    have htailzero : heathBrownSourceTail F T N a 0 = 0 := by
      simp [heathBrownSourceTail]
    simp only [htailzero,norm_zero,add_zero] at htail
    have hnonneg : 0 ≤ heathBrownPowerMajorant k η T N := zero_le_one.trans hMone
    have hprod := mul_le_mul_of_nonneg_right hK hnonneg
    exact htail.trans (hMone.trans (by simpa only [one_mul] using hprod))

end TaoTrudgianYang2025

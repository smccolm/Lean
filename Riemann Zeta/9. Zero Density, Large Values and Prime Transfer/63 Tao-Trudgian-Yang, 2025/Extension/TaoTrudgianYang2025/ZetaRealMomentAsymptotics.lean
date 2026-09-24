import TaoTrudgianYang2025.ZetaRealMomentTransfer
import TaoTrudgianYang2025.ZetaMomentAsymptotics

/-!
# Dyadic and logarithmic normalization of arbitrary real zeta moments

The order p is any real number at least one, and the dyadic exponent M
is any real number. The moment bound is an explicit analytic input.
-/

noncomputable section
open Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem eventually_zetaMomentLogLoss_rpow_le_rpow {p : ℝ} (hp : 0 ≤ p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, zetaMomentLogLoss T ^ p ≤ T ^ ε := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop p hε).const_mul_left
    ((7 : ℝ) ^ p)
  have hbound := hsmall.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, eventually_ge_atTop (4 : ℝ),
    eventually_ge_atTop (Real.exp 1)] with T hbound hT hExp
  have hTpos : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  simp only [Real.norm_eq_abs, one_mul] at hbound
  rw [abs_of_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hlog p)),
    abs_of_nonneg (Real.rpow_nonneg hTpos.le ε)] at hbound
  calc
    _ ≤ (7 * Real.log T) ^ p :=
      Real.rpow_le_rpow (zetaMomentLogLoss_pos T).le (zetaMomentLogLoss_le_seven_log hT hExp) hp
    _ = 7 ^ p * Real.log T ^ p := Real.mul_rpow (by norm_num) hlog
    _ ≤ _ := hbound


theorem zetaLineMoment_le_three_dyadic {c p T : ℝ} (hc1 : c ≠ 1) (hp : 1 ≤ p) (hT : 0 < T) :
    zetaLineMoment c p T ≤
      (∫ u in T / 2..T, zetaMomentLineNorm c u ^ p) +
      (∫ u in T..2 * T, zetaMomentLineNorm c u ^ p) +
      (∫ u in 2 * T..4 * T, zetaMomentLineNorm c u ^ p) := by
  have hc := (continuous_zetaMomentLineNorm hc1).rpow_const (p := p) (fun _ => Or.inr (by linarith))
  have hlast : (∫ u in 2 * T..3 * T, zetaMomentLineNorm c u ^ p) ≤
      ∫ u in 2 * T..4 * T, zetaMomentLineNorm c u ^ p := by
    apply intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
    · exact Filter.Eventually.of_forall fun u => Real.rpow_nonneg (norm_nonneg _) p
    · exact hc.intervalIntegrable _ _
  unfold zetaLineMoment
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (T / 2) T)
    (hc.intervalIntegrable T (3 * T)),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable T (2 * T))
      (hc.intervalIntegrable (2 * T) (3 * T))]
  linarith



/-- Dyadic normalization for arbitrary real M. In particular, no sign
assumption on the claimed moment exponent is silently added. -/
theorem zetaLineMoment_le_of_dyadic
    {c p C M T₀ T : ℝ} (hc1 : c ≠ 1) (hp : 1 ≤ p)
    (hT : 0 < T) (hStart : 2*T₀ ≤ T)
    (hDyadic : ∀ H : ℝ, T₀ ≤ H → 0 < H →
      (∫ u in H..2*H, zetaMomentLineNorm c u^p) ≤ C*H^M) :
    zetaLineMoment c p T ≤ C*((2 : ℝ)^(-M)+1+(2 : ℝ)^M)*T^M := by
  have hhalf := hDyadic (T/2) (by linarith) (by positivity)
  have hmiddle := hDyadic T (by linarith) hT
  have hlast := hDyadic (2*T) (by linarith) (by positivity)
  have hhalfPow : (T/2)^M = (2 : ℝ)^(-M)*T^M := by
    rw [Real.div_rpow hT.le (by norm_num), Real.rpow_neg (by norm_num)]
    ring
  have hmulPow : (2*T)^M = (2 : ℝ)^M*T^M :=
    Real.mul_rpow (by norm_num) hT.le
  have h := zetaLineMoment_le_three_dyadic hc1 hp hT
  rw [show 2*(T/2) = T by ring, hhalfPow] at hhalf
  rw [show 2*(2*T) = 4*T by ring, hmulPow] at hlast
  nlinarith

/-- The actual rounded logarithmic loss and all three dyadic intervals
are absorbed with explicit epsilon quantifiers. -/
theorem eventually_zetaLineMomentLoss_of_dyadic
    {c p M : ℝ} (hc1 : c ≠ 1) (hp : 1 ≤ p)
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2*H, zetaMomentLineNorm c u^p) ≤ C*H^(M+η))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      zetaMomentLogLoss T^p*zetaLineMoment c p T ≤ T^(M+ε) := by
  have hthird : 0 < ε/3 := by linarith
  obtain ⟨C,T₀,hC,hbound⟩ := hDyadic (ε/3) hthird
  let K : ℝ := C*((2 : ℝ)^(-(M+ε/3))+1+(2 : ℝ)^(M+ε/3))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hconst : ∀ᶠ T : ℝ in atTop, K ≤ T^(ε/3) :=
    (tendsto_rpow_atTop hthird).eventually (eventually_ge_atTop K)
  filter_upwards [eventually_zetaMomentLogLoss_rpow_le_rpow (by linarith : 0 ≤ p) hthird,
    hconst,eventually_ge_atTop (2*T₀),eventually_gt_atTop (0 : ℝ)] with
      T hlog hconstant hStart hT
  have hmoment : zetaLineMoment c p T ≤ K*T^(M+ε/3) :=
    zetaLineMoment_le_of_dyadic hc1 hp hT hStart hbound
  calc
    _ ≤ zetaMomentLogLoss T^p*(K*T^(M+ε/3)) :=
      mul_le_mul_of_nonneg_left hmoment (Real.rpow_nonneg (zetaMomentLogLoss_pos T).le p)
    _ ≤ T^(ε/3)*(T^(ε/3)*T^(M+ε/3)) :=
      mul_le_mul hlog (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hT.le _))
        (mul_nonneg hK (Real.rpow_nonneg hT.le _)) (Real.rpow_nonneg hT.le _)
    _ = _ := by
      rw [← Real.rpow_add hT,← Real.rpow_add hT]
      congr 1
      ring

theorem zetaPattern_realMoment_cardinality_of_dyadic_and_convolution
    {c p M : ℝ} (hc1 : c ≠ 1) (hp : 1 ≤ p)
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2*H, zetaMomentLineNorm c u^p) ≤ C*H^(M+η))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ P : ZetaLargeValuePattern, T₀ ≤ P.T →
      ∀ C : ℝ, 0 < C →
        (∀ t ∈ P.ordinates, P.V ≤ C*P.N^c*zetaLineMomentConvolution c P.T t) →
        (P.ordinates.card : ℝ)*P.V^p ≤ C^p*P.N^(c*p)*P.T^(M+ε) := by
  obtain ⟨T₀,hbound⟩ := Filter.eventually_atTop.mp
    (eventually_zetaLineMomentLoss_of_dyadic hc1 hp hDyadic hε)
  refine ⟨max 1 T₀,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro P hT C hC hEntry
  have hmoment := hbound P.T ((le_max_right _ _).trans hT)
  have hfinite := P.realMoment_cardinality_of_convolution hc1 hp hC hEntry
  calc
    _ ≤ C^p*P.N^(c*p)*(zetaMomentLogLoss P.T^p*zetaLineMoment c p P.T) := by
      simpa only [mul_assoc] using hfinite
    _ ≤ _ := mul_le_mul_of_nonneg_left hmoment
      (mul_nonneg (Real.rpow_nonneg hC.le p)
        (Real.rpow_nonneg (zero_lt_one.trans P.one_lt_N).le _))

end TaoTrudgianYang2025

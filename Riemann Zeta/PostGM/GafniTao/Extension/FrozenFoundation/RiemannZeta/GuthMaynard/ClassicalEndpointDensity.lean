import RiemannZeta.GuthMaynard.ClassicalEndpointSlab
import RiemannZeta.GuthMaynard.MediumTypeIEndpoint
import RiemannZeta.GuthMaynard.TypeIIFourthMomentReduction

open Asymptotics Filter Topology
open Complex Finset MeasureTheory Real Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap

namespace RiemannZeta.GuthMaynard

/-!
# Classical positive-slab endpoint density

This module is the source-facing consumer of the finite classical detector.
The only intermediate interface isolated below is the genuinely narrower
medium Type-I reflection case.  The final native theorem is exported only
after the imported native medium-consumer theorem discharges that interface.
-/

/-- The exact positive-slab endpoint density proposition. -/
def ClassicalEndpointPositiveSlabDensity (σ τ₀ : ℝ) : Prop :=
  EpsilonPowerBound
    (fun T => (zeroCountRect σ 1 T (2 * T) : ℝ))
    (fun T => T ^ (3 * (1 - σ) / τ₀))

/-! ## Arithmetic of the medium source-deweighting route -/

/-- At physical length comparable with the height, the classical
Montgomery--Halasz--Huxley exponent collapses to `2 - 2σ` throughout the
critical strip. -/
theorem classicalMHHExponent_one_le_two_sub_two_mul
    {σ : ℝ} (_hσLower : 1 / 2 ≤ σ) :
    classicalMHHExponent σ 1 ≤ 2 - 2 * σ := by
  rw [classicalMHHExponent, max_le_iff]
  constructor
  · exact le_rfl
  · convert min_le_left (1 + 1 - 2 * σ) (1 + 4 - 6 * σ) using 1
    · ring

/-- If the endpoint scale is at most `3/2`, the length-`T` MHH exponent is
no larger than the required endpoint density exponent. -/
theorem two_sub_two_mul_le_endpoint_exponent
    {σ τ₀ : ℝ} (hσUpper : σ ≤ 1) (hτ₀ : 0 < τ₀)
    (hτ₀Upper : τ₀ ≤ 3 / 2) :
    2 - 2 * σ ≤ 3 * (1 - σ) / τ₀ := by
  rw [le_div_iff₀ hτ₀]
  have hOneSigma : 0 ≤ 1 - σ := by linarith
  nlinarith

/-- Below `σ = 5/6`, either numerical endpoint represented by a complete
certificate has `τ₀ ≤ 3/2`. -/
theorem endpointScaleCertificate_tau0_le_three_halves
    {σ τ₀ : ℝ} (hσLower : 1 / 2 ≤ σ) (hσUpper : σ < 1)
    (hσFiveSixths : σ ≤ 5 / 6)
    (hcert : EndpointScaleCertificate σ τ₀) :
    τ₀ ≤ 3 / 2 := by
  rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
  · linarith
  · linarith

/-- The exact exponent comparison needed after source Fourier deweighting
in the non-Weyl medium range. -/
theorem classicalMHHExponent_one_le_endpoint_of_sigma_le_five_sixths
    {σ τ₀ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hσFiveSixths : σ ≤ 5 / 6)
    (hcert : EndpointScaleCertificate σ τ₀) :
    classicalMHHExponent σ 1 ≤ 3 * (1 - σ) / τ₀ := by
  exact (classicalMHHExponent_one_le_two_sub_two_mul hσLower.le).trans
    (two_sub_two_mul_le_endpoint_exponent hσUpper.le hcert.tau0_pos
      (endpointScaleCertificate_tau0_le_three_halves hσLower.le hσUpper
        hσFiveSixths hcert))

/-- The small part of the nominal medium gap is still a direct MHH range.
The numerical split at `11/10` is source-independent and leaves a fixed
positive growth exponent for the genuinely reflected dual length. -/
theorem classicalMHHExponent_le_endpoint_of_short_gap
    {σ τ₀ τ : ℝ} (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hτ₀ : τ₀ < τ) (hτ : τ ≤ 11 / 10) :
    classicalMHHExponent σ τ ≤ (3 * (1 - σ) / τ₀) * τ := by
  have hOneSigma : 0 < 1 - σ := by linarith
  have hτ₀Upper : τ₀ < 11 / 10 := hτ₀.trans_le hτ
  have hTarget : (5 / 2) * (1 - σ) ≤
      (3 * (1 - σ) / τ₀) * τ := by
    rw [show (3 * (1 - σ) / τ₀) * τ =
      (3 * (1 - σ) * τ) / τ₀ by ring, le_div_iff₀ hcert.tau0_pos]
    exact (calc
        (5 / 2) * (1 - σ) * τ₀ ≤ 3 * (1 - σ) * τ₀ := by
          have hnonneg : 0 ≤ (1 - σ) * τ₀ :=
            mul_nonneg hOneSigma.le hcert.tau0_pos.le
          nlinarith
        _ < 3 * (1 - σ) * τ := by
          exact mul_lt_mul_of_pos_left hτ₀ (by positivity)).le
  have hCore : classicalMHHExponent σ τ ≤ (5 / 2) * (1 - σ) := by
    rw [classicalMHHExponent, max_le_iff]
    constructor
    · nlinarith
    · by_cases hGap : 1 / 5 ≤ 1 - σ
      · exact (min_le_left _ _).trans (by linarith)
      · exact (min_le_right _ _).trans (by
          have hGap' : 1 - σ < 1 / 5 := lt_of_not_ge hGap
          linarith)
  exact hCore.trans hTarget

/-- Power form of the preceding short-gap exponent comparison at the actual
finite Type-I length. -/
theorem rpow_classicalMHHExponent_le_endpoint_of_short_gap
    {σ τ₀ T : ℝ} {Q : ℕ}
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hT : 0 < T) (hQ : 1 < Q)
    (hτ₀ : τ₀ < typeILogarithmicScale T Q)
    (hτ : typeILogarithmicScale T Q ≤ 11 / 10) :
    (Q : ℝ) ^ classicalMHHExponent σ (typeILogarithmicScale T Q) ≤
      T ^ (3 * (1 - σ) / τ₀) := by
  let tau := typeILogarithmicScale T Q
  have hExp := classicalMHHExponent_le_endpoint_of_short_gap
    hσUpper hcert (by simpa only [tau] using hτ₀)
      (by simpa only [tau] using hτ)
  have hQOne : (1 : ℝ) ≤ Q := by exact_mod_cast hQ.le
  calc
    (Q : ℝ) ^ classicalMHHExponent σ tau ≤
        (Q : ℝ) ^ ((3 * (1 - σ) / τ₀) * tau) := by
      exact Real.rpow_le_rpow_of_exponent_le hQOne hExp
    _ = ((Q : ℝ) ^ tau) ^ (3 * (1 - σ) / τ₀) := by
      rw [mul_comm, Real.rpow_mul (by positivity)]
    _ = T ^ (3 * (1 - σ) / τ₀) := by
      rw [rpow_typeILogarithmicScale_eq hT hQ]

/-- Arbitrary polynomial decay of the fixed Fourier profile used for every
interior source block.  The constant depends only on the fixed line `σ`. -/
theorem typeIInteriorFourier_polynomial_decay (σ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ,
      |ξ| ^ n *
        ‖SchwartzMap.fourierTransformCLM ℂ
          (typeIInteriorLogProfileSchwartz σ) ξ‖ ≤ C := by
  let F : SchwartzMap ℝ ℂ := SchwartzMap.fourierTransformCLM ℂ
    (typeIInteriorLogProfileSchwartz σ)
  let C : ℝ := SchwartzMap.seminorm ℝ n 0 F
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ξ
  have hSem := SchwartzMap.le_seminorm' (𝕜 := ℝ) n 0 F ξ
  rw [iteratedDeriv_zero] at hSem
  simpa only [F, C, Real.norm_eq_abs] using hSem

/-- Quantitative `L¹` tail of the same fixed Fourier profile. -/
theorem exists_typeIInteriorFourier_tail_bound (σ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H →
      ∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ,
          ‖SchwartzMap.fourierTransformCLM ℂ
            (typeIInteriorLogProfileSchwartz σ) ξ‖ ≤ C * H ^ (-3 : ℝ) := by
  obtain ⟨C₀, hC₀, hDecay⟩ := typeIInteriorFourier_polynomial_decay σ 4
  let C : ℝ := max 1 (2 * C₀ / 3)
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro H hH
  have hHPos : 0 < H := zero_lt_one.trans_le hH
  let F : SchwartzMap ℝ ℂ := SchwartzMap.fourierTransformCLM ℂ
    (typeIInteriorLogProfileSchwartz σ)
  have hFInt : Integrable (fun ξ : ℝ => ‖F ξ‖) := F.integrable.norm
  have hDomInt : IntegrableOn (fun ξ : ℝ => C₀ * |ξ| ^ (-4 : ℝ))
      (Set.Icc (-H) H)ᶜ := by
    exact (integrableOn_abs_rpow_compl_Icc (by norm_num) hHPos).const_mul C₀
  have hPoint : ∀ᵐ ξ : ℝ ∂MeasureTheory.volume.restrict (Set.Icc (-H) H)ᶜ,
      ‖F ξ‖ ≤ C₀ * |ξ| ^ (-4 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with ξ hξ
    have hAbs : H < |ξ| := by
      by_contra hnot
      exact hξ (abs_le.mp (le_of_not_gt hnot))
    have hAbsPos : 0 < |ξ| := hHPos.trans hAbs
    have hRaw := hDecay ξ
    change |ξ| ^ 4 * ‖F ξ‖ ≤ C₀ at hRaw
    rw [show |ξ| ^ (-4 : ℝ) = (|ξ| ^ (4 : ℕ))⁻¹ by
      rw [Real.rpow_neg hAbsPos.le]
      norm_num]
    rw [le_mul_inv_iff₀ (pow_pos hAbsPos 4)]
    simpa only [mul_comm] using hRaw
  calc
    ∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ,
        ‖SchwartzMap.fourierTransformCLM ℂ
          (typeIInteriorLogProfileSchwartz σ) ξ‖
        ≤ ∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ, C₀ * |ξ| ^ (-4 : ℝ) := by
          exact integral_mono_ae hFInt.integrableOn hDomInt hPoint
    _ = (2 * C₀ / 3) * H ^ (-3 : ℝ) := by
      rw [integral_const_mul, integral_abs_rpow_compl_Icc (by norm_num) hHPos]
      ring_nf
    _ ≤ C * H ^ (-3 : ℝ) := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hHPos.le _)

/-! ## Bounded ordinate displacement and reseparation -/

/-- A pointwise displacement of a one-separated finite family by at most
`H` has a one-separated subfamily after losing only the explicit local
occupancy factor `2 * (2 * ceil H + 1)`.  Fibres of the displacement map are
counted with their full multiplicity, so this lemma is safe to use inside the
analytic-multiplicity reduction. -/
theorem exists_separated_bounded_shift_image
    (W : Finset ℝ) (shift : ℝ → ℝ) (H : ℝ)
    (_hH : 0 ≤ H) (hSeparated : IsSeparated 1 W)
    (hShift : ∀ t ∈ W, |t - shift t| ≤ H) :
    ∃ U ⊆ W.image shift, IsSeparated 1 U ∧
      W.card ≤ 2 * (2 * ⌈H⌉₊ + 1) * U.card := by
  classical
  let weight : ℝ → ℕ := fun _ => 1
  let shiftedWeight : ℝ → ℕ := fun u =>
    ∑ t ∈ W.filter (fun x => shift x = u), weight t
  have hLocalOriginal : ∀ z : ℤ,
      ∑ t ∈ W.filter
          (fun x => (z : ℝ) ≤ x ∧ x < (z : ℝ) + 1), weight t ≤ 1 := by
    intro z
    have hCard :
        (W.filter (fun x => (z : ℝ) ≤ x ∧ x < (z : ℝ) + 1)).card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro x y hx hy
      simp only [Finset.mem_filter] at hx hy
      by_contra hxy
      have hSep := hSeparated x hx.1 y hy.1 hxy
      rw [Real.dist_eq] at hSep
      have hlt : |x - y| < 1 := by
        rw [abs_lt]
        constructor <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
      linarith
    simpa only [weight, Finset.sum_const, nsmul_eq_mul, mul_one] using hCard
  have hLocalShifted : ∀ z : ℤ,
      ∑ u ∈ (W.image shift).filter
          (fun v => (z : ℝ) ≤ v ∧ v < (z : ℝ) + 1), shiftedWeight u ≤
        2 * ⌈H⌉₊ + 1 := by
    intro z
    simpa only [shiftedWeight, weight, mul_one] using
      shifted_bin_weight_le_of_unit_bin_weight W weight id shift H 1
        (by simpa only [id_eq] using hShift) hLocalOriginal z
  obtain ⟨U, hUImage, hUSep, hWeight⟩ :=
    weighted_separated_selection (W.image shift) shiftedWeight
      (2 * ⌈H⌉₊ + 1) hLocalShifted
  have hAll : W.filter (fun t => shift t ∈ W.image shift) = W := by
    apply Finset.filter_eq_self.mpr
    intro t ht
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  have hFiber := Finset.sum_fiberwise_eq_sum_filter W (W.image shift)
    shift weight
  rw [hAll] at hFiber
  have hTotal : ∑ u ∈ W.image shift, shiftedWeight u = W.card := by
    simpa only [shiftedWeight, weight, Finset.sum_const, nsmul_eq_mul,
      mul_one] using hFiber
  refine ⟨U, hUImage, hUSep, ?_⟩
  rw [← hTotal]
  simpa only [mul_assoc] using hWeight

/-! ## The direct part of the apparent medium gap -/

set_option maxHeartbeats 2000000 in
/-- The actual Type-I dichotomy witness is still a direct MHH input when its
physical scale is at most `11/10`, even if it lies just above `tau0`.  This
consumer retains the original multiplicity bound and absorbs the literal
detector, harmonic, displacement and coefficient-normalization losses. -/
theorem actual_typeI_short_gap_dichotomy_witness_consumer
    {σ τ₀ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ r ∈ Finset.range (Nat.clog 2 A), ∀ W : Finset ℝ,
          IsSeparated 1 W →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-d ^ 4) / 2)) / Nat.clog 2 A ≤
              ‖dirichletPoly (2 ^ r * Y)
                (classicalZetaLongLineCoeff A σ) t‖) →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          zeroCountRect σ 1 T (2 * T) ≤
            4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) * W.card →
          τ₀ < typeILogarithmicScale T (2 ^ r * Y) →
          typeILogarithmicScale T (2 ^ r * Y) ≤ 11 / 10 →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  intro ε hε
  have hσ : 0 < σ := by linarith
  let εs : ℝ := ε / 100
  have hεs : 0 < εs := by dsimp only [εs]; positivity
  let d := classicalEndpointLossParameter σ τ₀ εs
  have hdSpec := classicalEndpointLossParameter_spec hσLower hσUpper hcert.tau0_pos hεs
  dsimp only at hdSpec
  rcases hdSpec with ⟨hd, hdEps, hdEpsTau, _hdReflected, _hdHalfGap, _hdUpperGap, _hdSigma,
    hdSmall, _hdHalf, hdOne, _hdSigmaStrict⟩
  let s : ℝ := d ^ 2
  let u : ℝ := d ^ 4
  have hs : 0 < s := by dsimp only [s]; positivity
  have hu : 0 < u := by dsimp only [u]; positivity
  have huLeD : u ≤ d := by
    dsimp only [u]
    have hdSq : d ^ 2 ≤ d := by
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hdOne)]
    have hdFourth : (d ^ 2) ^ 2 ≤ d ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hdSq)]
    calc
      d ^ 4 = (d ^ 2) ^ 2 := by ring
      _ ≤ d ^ 2 := hdFourth
      _ ≤ d := hdSq
  have hdEpsFull : d ≤ ε / 1000 := by
    dsimp only [εs] at hdEps
    linarith
  have huEpsTau : u ≤ ε * τ₀ / 1000 := by
    exact huLeD.trans (by
      dsimp only [εs] at hdEpsTau
      linarith)
  obtain ⟨K, hK, hMHH⟩ := actual_typeI_normalized_dichotomy_witness_mhh_native
  obtain ⟨Closs, hCloss, Tloss, hTloss, hLoss⟩ :=
    eventually_endpoint_loss_bundle_le typeIDirectPowerLossConstant K d u τ₀ ε 1
      typeIDirectPowerLossConstant_pos.le hK.le hd hu hcert.tau0_pos hε
      (by omega) hdEpsFull huEpsTau
  obtain ⟨Tscale, hTscale, hScale⟩ := eventually_typeI_logarithmic_scale_upper s hs
  have hdOneStrict : d < 1 := by
    have hDen : 0 < 1000 * (1 + τ₀) := by nlinarith [hcert.tau0_pos]
    have hSmallStrict : 1 / (1000 * (1 + τ₀)) < 1 := by
      rw [div_lt_one hDen]
      nlinarith [hcert.tau0_pos]
    exact hdSmall.trans_lt hSmallStrict
  obtain ⟨Thalf, hThalf, hHalf⟩ := eventually_rpow_le_half_self d hdOneStrict
  let T₀ := max Tloss (max Tscale Thalf)
  refine ⟨Closs, hCloss, T₀, hTloss.trans (le_max_left _ _), ?_⟩
  intro T hT
  dsimp only
  intro r hr W hSep hLarge hRange hCount hTau0 hTauUpper
  have hTLoss : Tloss ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tscale Thalf ≤ T := (le_max_right _ _).trans hT
  have hTScale : Tscale ≤ T := (le_max_left _ _).trans hRest
  have hTHalf : Thalf ≤ T := (le_max_right _ _).trans hRest
  have hTEight : 8 ≤ T := hTloss.trans hTLoss
  have hTPos : 0 < T := by linarith
  have hDisp : T ^ d ≤ T / 2 := hHalf T hTHalf
  let Y := ⌊T ^ s⌋₊
  let A := ⌊sharpZetaCutoff T⌋₊
  let N := 2 ^ r * Y
  have hNOne : 1 < N := by
    have hscaleAt := hScale T r hTScale
    simpa only [Y, N] using hscaleAt.1
  have hN : 0 < N := lt_trans Nat.zero_lt_one hNOne
  by_cases hW : W.Nonempty
  · obtain ⟨t, ht⟩ := hW
    let L : ℝ := ((3 / 4) * (T ^ (-u) / 2)) / Nat.clog 2 A
    have hAOne : 1 < A := by
      dsimp only [A]
      apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
      apply Nat.le_floor
      exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
        (four_mul_lt_sharpZetaCutoff T).le
    have hNC : N < A := by
      have hLPos : 0 < L := by
        dsimp only [L]
        have hClog : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hAOne
        positivity
      exact typeI_start_lt_cutoff_of_positive_large_value A N σ t L hLPos
        (by simpa only [L, N, Y, A, u, s] using hLarge t ht)
    have hBase : (1 : ℝ) < N := by exact_mod_cast hNOne
    have hTauTwo : typeILogarithmicScale T N ≤ 2 :=
      hTauUpper.trans (by norm_num)
    have hTN : T ≤ (N : ℝ) ^ (2 : ℕ) := by
      simpa only [Real.rpow_two] using
        (Real.logb_le_iff_le_rpow hBase hTPos).mp hTauTwo
    let P : ℝ := 1 + classicalTypeIIPowerLoss
      typeIDirectPowerLossConstant u T 1 N
    have hP : 1 ≤ P := by
      dsimp only [P, classicalTypeIIPowerLoss]
      apply le_add_of_nonneg_right
      have hLog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg typeIDirectPowerLossConstant_pos.le
            (Real.rpow_nonneg (by positivity) _)) (by norm_num))
        (by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hLog)
    have hPDirect := typeIDirectThresholdLoss_le_classicalTypeIIPowerLoss
      (A := A) (N := N) (d := u) hTEight hu.le hNOne
        (by dsimp only [A]; exact le_rfl) hTN
    have hPDirectPos : 0 < typeIDirectThresholdLoss T A u := by
      unfold typeIDirectThresholdLoss
      positivity
    have hThresholdDirect := typeI_direct_normalized_threshold_lower
      (d := u) (N := N) (σ := σ) hTPos hAOne
    have hThreshold : (N : ℝ) ^ σ / P ≤ (N : ℝ) ^ σ * L := by
      calc
        (N : ℝ) ^ σ / P ≤
            (N : ℝ) ^ σ / typeIDirectThresholdLoss T A u := by
          exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
            hPDirectPos (by simpa only [P] using hPDirect)
        _ ≤ (N : ℝ) ^ σ * L := by
          simpa only [L, u] using hThresholdDirect
    have hLPos : 0 < L := by
      dsimp only [L]
      have hClog : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hAOne
      positivity
    have hMHHAt := hMHH A N σ d T L W hσ.le hN (by linarith)
      hLPos hDisp hSep (by simpa only [L, N, Y, A, u, s] using hRange)
      (by simpa only [L, N, Y, A, u, s] using hLarge)
    have hEndpointPower :=
      rpow_classicalMHHExponent_le_endpoint_of_short_gap hσUpper hcert
        hTPos hNOne (by simpa only [N, Y, s] using hTau0)
          (by simpa only [N, Y, s] using hTauUpper)
    have hEndpoint := endpoint_witness_count_le_of_mhh_power_factor
      (τ₀ := τ₀) (R := 1) hTPos hNOne
      (by omega : 0 < (1 : ℕ)) hP hThreshold (by simpa using hEndpointPower)
      (by simpa only [N, Y, A] using hCount)
      (by simp : (W.card : ℝ) ≤ (1 : ℕ) * (W.card : ℝ)) hK.le hMHHAt
    have hLossAt := hLoss T N 1 hTLoss hNOne (by omega) (by omega)
      (by
        have hLower : 2 * τ₀ / 3 < typeILogarithmicScale T N := by
          nlinarith [hcert.tau0_pos, hTau0]
        exact hLower.le)
    have hTargetNonneg : 0 ≤ T ^ (3 * (1 - σ) / τ₀) :=
      Real.rpow_nonneg hTPos.le _
    have hEndpoint' :
        (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
          ((4 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
            ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
            1 * (K * (1 + (((harmonic N : ℚ) : ℝ)))) *
              (6 * P ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀)) := by
      simpa only [A, d, εs, P, s, Nat.cast_one, one_mul, mul_one] using hEndpoint
    have hLossAt' :
        ((4 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
            ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
            1 * (K * (1 + (((harmonic N : ℚ) : ℝ)))) *
              (6 * P ^ (6 : ℕ)) ≤ Closs * T ^ ε := by
      simpa only [d, u, P, Nat.cast_one] using hLossAt
    calc
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤ _ := hEndpoint'
      _ = (((4 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
            ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
            1 * (K * (1 + (((harmonic N : ℚ) : ℝ)))) *
              (6 * P ^ (6 : ℕ))) * T ^ (3 * (1 - σ) / τ₀) := by ring
      _ ≤ Closs * T ^ ε * T ^ (3 * (1 - σ) / τ₀) :=
        mul_le_mul_of_nonneg_right hLossAt' hTargetNonneg
  · have hWCard : W.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hW)
    have hZero : zeroCountRect σ 1 T (2 * T) = 0 := by
      rw [hWCard, mul_zero] at hCount
      omega
    rw [hZero]
    norm_num
    exact mul_nonneg
      (mul_nonneg hCloss.le (Real.rpow_nonneg hTPos.le _))
      (Real.rpow_nonneg hTPos.le _)

/-- Assembly of the real detector dichotomy once the narrower medium
reflection consumer is available.  The proof invokes the detector itself,
unpacks all three alternatives, and retains the analytic-multiplicity factor
present in each witness branch. -/
theorem classical_endpoint_positive_slab_of_medium_native
    (hMedium : ClassicalMediumTypeIWitnessConsumer)
    {σ τ₀ : ℝ}
    (hσLower : 1 / 2 < σ)
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ClassicalEndpointPositiveSlabDensity σ τ₀ := by
  intro ε hε
  let εs : ℝ := ε / 100
  have hεs : 0 < εs := by dsimp only [εs]; positivity
  let d := classicalEndpointLossParameter σ τ₀ εs
  have hdSpec := classicalEndpointLossParameter_spec hσLower hσUpper hcert.tau0_pos hεs
  dsimp only at hdSpec
  rcases hdSpec with ⟨hd, _hdEps, _hdEpsTau, _hdReflected, _hdGap, _hdUpperGap, _hdSigma,
    _hdSmall, _hdHalf, hdOne, hdSigmaStrict⟩
  have hdTwo : 0 < d ^ 2 := by dsimp only [d]; positivity
  have hdFour : 0 < d ^ 4 := by dsimp only [d]; positivity
  have hdSqOne : d ^ 2 ≤ 1 := by
    have hdLeOne : d ≤ 1 := by simpa only [d] using hdOne
    nlinarith [sq_nonneg d]
  have hOrder : d ^ 4 / 2 ≤ d ^ 2 := by
    have hdSqNonneg : 0 ≤ d ^ 2 := sq_nonneg d
    have hdFourthLe : d ^ 4 ≤ d ^ 2 := by nlinarith [sq_nonneg (d ^ 2)]
    linarith
  have hdFourSigma : d ^ 4 < σ := by
    have hdLeOne : d ≤ 1 := by simpa only [d] using hdOne
    have hdFourthLe : d ^ 4 ≤ d := by nlinarith
    exact hdFourthLe.trans_lt (by simpa only [d] using hdSigmaStrict)
  obtain ⟨Tdich, hTdich, hDich⟩ := classical_typeI_typeII_dichotomy_native
    σ d (d ^ 2) (d ^ 4) hσLower hσUpper.le hd hdTwo hdFour
      hOrder hdSqOne hdFourSigma
  obtain ⟨Cb, hCb, Tb, hTb, hBasic⟩ :=
    actual_typeI_basic_window_dichotomy_witness_consumer
      hσLower hσUpper hcert εs hεs
  obtain ⟨Cp, hCp, Tp, hTp, hPowered⟩ :=
    actual_typeI_powered_window_dichotomy_witness_consumer
      hσLower hσUpper hcert ε hε
  obtain ⟨Cl, hCl, Tl, hTl, hLow⟩ :=
    actual_typeI_low_window_dichotomy_witness_consumer
      hσLower hσUpper hcert ε hε
  obtain ⟨Cs, hCs, Ts, hTs, hShort⟩ :=
    actual_typeI_short_gap_dichotomy_witness_consumer
      hσLower hσUpper hcert ε hε
  obtain ⟨Cm, hCm, Tm, hTm, hMediumAt⟩ :=
    hMedium hσLower hσUpper hcert ε hε
  obtain ⟨Ci, hCi, Ti, hTi, hTypeII⟩ :=
    actual_typeII_dichotomy_witness_consumer
      hσLower hσUpper hcert εs hεs
  let C : ℝ := max Cb (max Cp (max Cl (max Cs (max Cm Ci))))
  let T₀ : ℝ := max 8
    (max Tdich (max Tb (max Tp (max Tl (max Ts (max Tm Ti))))))
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have hT8 : 8 ≤ T := (le_max_left _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hRest : max Tdich (max Tb (max Tp (max Tl (max Ts (max Tm Ti))))) ≤ T :=
    (le_max_right _ _).trans hT
  have hTDich : Tdich ≤ T := (le_max_left _ _).trans hRest
  have hRest₁ : max Tb (max Tp (max Tl (max Ts (max Tm Ti)))) ≤ T :=
    (le_max_right _ _).trans hRest
  have hTB : Tb ≤ T := (le_max_left _ _).trans hRest₁
  have hRest₂ : max Tp (max Tl (max Ts (max Tm Ti))) ≤ T :=
    (le_max_right _ _).trans hRest₁
  have hTP : Tp ≤ T := (le_max_left _ _).trans hRest₂
  have hRest₃ : max Tl (max Ts (max Tm Ti)) ≤ T :=
    (le_max_right _ _).trans hRest₂
  have hTL : Tl ≤ T := (le_max_left _ _).trans hRest₃
  have hRest₄ : max Ts (max Tm Ti) ≤ T := (le_max_right _ _).trans hRest₃
  have hTS : Ts ≤ T := (le_max_left _ _).trans hRest₄
  have hRest₅ : max Tm Ti ≤ T := (le_max_right _ _).trans hRest₄
  have hTM : Tm ≤ T := (le_max_left _ _).trans hRest₅
  have hTI : Ti ≤ T := (le_max_right _ _).trans hRest₅
  have hEpsMono : T ^ εs ≤ T ^ ε := by
    apply Real.rpow_le_rpow_of_exponent_le hTOne
    dsimp only [εs]
    linarith
  have hTargetNonneg : 0 ≤ T ^ (3 * (1 - σ) / τ₀) :=
    Real.rpow_nonneg hTPos.le _
  have hCbC : Cb ≤ C := le_max_left _ _
  have hCpC : Cp ≤ C := le_max_of_le_right (le_max_left _ _)
  have hClC : Cl ≤ C :=
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hCsC : Cs ≤ C :=
    le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _)))
  have hCmC : Cm ≤ C :=
    le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
  have hCiC : Ci ≤ C :=
    le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))
  have hCnonneg : 0 ≤ C := hCb.le.trans hCbC
  have hPowerTargetNonneg :
      0 ≤ T ^ ε * T ^ (3 * (1 - σ) / τ₀) :=
    mul_nonneg (Real.rpow_nonneg hTPos.le _) hTargetNonneg
  have hLiftSmall {K : ℝ} (hK : 0 ≤ K)
      (h : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        K * T ^ εs * T ^ (3 * (1 - σ) / τ₀)) :
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        K * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
    exact h.trans (by gcongr)
  have hLiftConstant {K : ℝ} (hKC : K ≤ C)
      (h : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        K * T ^ ε * T ^ (3 * (1 - σ) / τ₀)) :
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
    calc
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
          K * (T ^ ε * T ^ (3 * (1 - σ) / τ₀)) := by
            simpa only [mul_assoc] using h
      _ ≤ C * (T ^ ε * T ^ (3 * (1 - σ) / τ₀)) :=
        mul_le_mul_of_nonneg_right hKC hPowerTargetNonneg
      _ = C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by ring
  have hDichAt := hDich T hTDich
  dsimp only [ClassicalTypeITypeIIDichotomyConclusion] at hDichAt
  rcases hDichAt with hZero | hTypeI | hTypeIIAlt
  · rw [hZero]
    simp only [Nat.cast_zero, abs_zero]
    simpa only [norm_zero] using mul_nonneg hCnonneg
      (norm_nonneg (T ^ ε * |T ^ (3 * (1 - σ) / τ₀)|))
  · rcases hTypeI with ⟨r, hr, W, hSep, hLarge, hLong, hRange, hCount⟩
    let Y := ⌊T ^ (d ^ 2)⌋₊
    let A := ⌊sharpZetaCutoff T⌋₊
    let τ := typeILogarithmicScale T (2 ^ r * Y)
    have hBound : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
      by_cases hLowScale : τ < 2 * τ₀ / 3
      · have h := hLow T hTL r (by simpa only [A] using hr) W hSep
            (by simpa only [d, Y, A] using hLarge)
            (by simpa only [d] using hRange)
            (by simpa only [d, A] using hCount)
            (by simpa only [τ, Y] using hLowScale)
        exact hLiftConstant hClC h
      · have hTauLower : 2 * τ₀ / 3 ≤ τ := le_of_not_gt hLowScale
        by_cases hBasicScale : τ ≤ τ₀
        · have h := hBasic T hTB r (by simpa only [A] using hr) W hSep
              (by simpa only [d, Y, A] using hLarge)
              (by simpa only [d] using hRange)
              (by simpa only [d, A] using hCount)
              (by simpa only [τ, Y] using hTauLower)
              (by simpa only [τ, Y] using hBasicScale)
          exact hLiftConstant hCbC (hLiftSmall hCb.le h)
        · have hTau0 : τ₀ < τ := lt_of_not_ge hBasicScale
          by_cases hRaised : 4 * τ₀ / 3 ≤ τ
          · have h := hPowered T hTP r (by simpa only [A] using hr) W hSep
                (by simpa only [d, Y, A] using hLarge)
                (by simpa only [d] using hRange)
                (by simpa only [d, A] using hCount)
                (by simpa only [τ, Y] using hRaised)
            exact hLiftConstant hCpC h
          · have hGapUpper : τ < 4 * τ₀ / 3 := lt_of_not_ge hRaised
            by_cases hShortScale : τ ≤ 11 / 10
            · have h := hShort T hTS r (by simpa only [A] using hr) W hSep
                (by simpa only [d, Y, A] using hLarge)
                (by simpa only [d] using hRange)
                (by simpa only [d, A] using hCount)
                (by simpa only [τ, Y] using hTau0)
                (by simpa only [τ, Y] using hShortScale)
              exact hLiftConstant hCsC h
            · have h := hMediumAt T hTM r (by simpa only [A] using hr) W hSep
                (by simpa only [d, Y, A] using hLarge)
                (by simpa only [d, Y, A] using hLong)
                (by simpa only [d] using hRange)
                (by simpa only [d, A] using hCount)
                (by simpa only [τ, Y] using hTau0)
                (by simpa only [τ, Y] using lt_of_not_ge hShortScale)
                (by simpa only [τ, Y] using hGapUpper)
              exact hLiftConstant hCmC h
    have hCountNonneg : (0 : ℝ) ≤
        (zeroCountRect σ 1 T (2 * T) : ℝ) := Nat.cast_nonneg _
    simp only [Real.norm_eq_abs, abs_abs]
    rw [abs_of_nonneg hCountNonneg, abs_of_nonneg hTargetNonneg,
      abs_of_nonneg hPowerTargetNonneg]
    simpa only [mul_assoc] using hBound
  · have hTypeIIAlt' :
        let X := ⌊T ^ (d ^ 4 / 2)⌋₊
        let Y := ⌊T ^ (d ^ 2)⌋₊
        (∃ r ∈ Finset.range (Nat.clog 2 Y), ∃ W : Finset ℝ,
          IsSeparated 1 W ∧
          (∀ t ∈ W, (9 / 16 : ℝ) / Nat.clog 2 Y ≤
            ‖dirichletPoly (2 ^ r * X)
              (sharpMollifiedLineCoeff Y X σ) t‖) ∧
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) ∧
          zeroCountRect σ 1 T (2 * T) ≤
            4 * Nat.clog 2 Y *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) *
                W.card) := by
      dsimp only
      rcases hTypeIIAlt with ⟨r, hr, W, hSep, hLarge, hRange, hCount⟩
      refine ⟨r, hr, W, hSep, ?_, hRange, hCount⟩
      intro t ht
      simpa only [show (3 / 4 : ℝ) * (3 / 4) = 9 / 16 by norm_num] using
        hLarge t ht
    have h := hTypeII T hTI (by
        simpa only [d] using hTypeIIAlt')
    have h' := hLiftSmall hCi.le h
    have hCountNonneg : (0 : ℝ) ≤
        (zeroCountRect σ 1 T (2 * T) : ℝ) := Nat.cast_nonneg _
    simp only [Real.norm_eq_abs, abs_abs]
    rw [abs_of_nonneg hCountNonneg, abs_of_nonneg hTargetNonneg,
      abs_of_nonneg hPowerTargetNonneg]
    simpa only [mul_assoc] using hLiftConstant hCiC h'

/-- Native classical endpoint density on the positive slab.  The proof term
uses the actual detector dichotomy and the native medium Type-I consumer; the
other Type-I and Type-II alternatives are consumed inside
`classical_endpoint_positive_slab_of_medium_native`. -/
theorem classical_endpoint_positive_slab_native
    {σ τ₀ : ℝ}
    (hσLower : 1 / 2 < σ)
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ClassicalEndpointPositiveSlabDensity σ τ₀ :=
  classical_endpoint_positive_slab_of_medium_native
    classical_medium_typeI_witness_consumer_native hσLower hσUpper hcert

/-- Ingham endpoint specialization of the native positive-slab density
theorem. -/
theorem ingham_endpoint_positive_slab_native
    {σ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1) :
    ClassicalEndpointPositiveSlabDensity σ (2 - σ) :=
  classical_endpoint_positive_slab_native hσLower hσUpper
    (ingham_endpoint_scale_certificate hσLower hσUpper)

/-- Huxley endpoint specialization of the native positive-slab density
theorem. -/
theorem huxley_endpoint_positive_slab_native
    {σ : ℝ} (hσLower : 3 / 4 < σ) (hσUpper : σ < 1) :
    ClassicalEndpointPositiveSlabDensity σ (3 * σ - 1) :=
  classical_endpoint_positive_slab_native (by linarith) hσUpper
    (huxley_endpoint_scale_certificate hσLower hσUpper)

end RiemannZeta.GuthMaynard

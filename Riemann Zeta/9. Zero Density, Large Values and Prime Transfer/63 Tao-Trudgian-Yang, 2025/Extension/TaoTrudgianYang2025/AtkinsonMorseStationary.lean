import TaoTrudgianYang2025.AtkinsonStationaryZetaSource
import TaoTrudgianYang2025.BetaQuadraticLocalRemainder
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Exact Morse entry for the actual Atkinson stationary integral

The physical integral, positive Jacobian, phase, central amplitude and existing
Fresnel main term are retained exactly. Actual inverse jets and amplitude
derivatives give a source-band remainder C*G^2*T^(-alpha)*L/sqrt(T). The literal
divisor sum and tail give O_delta(G), and both actual zeta consumers give
O_delta(G log T), on the full power-width range. The complete sharp printed
source-form bridge remains a separate obligation.
-/

noncomputable section
open Set Filter MeasureTheory
open RiemannZeta.GuthMaynard
open scoped ContDiff Topology FourierTransform
namespace TaoTrudgianYang2025

theorem contDiffAt_atkinsonRootPhase_infty (T b : ℝ) {y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ ∞ (atkinsonRootPhase T b) y := by
  unfold atkinsonRootPhase
  fun_prop (disch := exact hy.ne')

theorem deriv_deriv_atkinsonRootPhase (T b : ℝ) {y : ℝ} (hy : 0 < y) :
    deriv (deriv (atkinsonRootPhase T b)) y = -T/(Real.pi*y^2)-2 := by
  have he : deriv (atkinsonRootPhase T b) =ᶠ[𝓝 y] atkinsonRootSlope T b := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact (hasDerivAt_atkinsonRootPhase T b hx).deriv
  rw [he.deriv_eq]
  exact (hasDerivAt_atkinsonRootSlope T b hy).deriv

def atkinsonRootMorseCurvature (T b y : ℝ) : ℝ :=
  -segmentTaylorAverage (deriv (deriv (atkinsonRootPhase T b)))
    (atkinsonSaddleRoot (T/(2*Real.pi)) b) 0 y

def atkinsonRootMorseCoordinate (T b y : ℝ) : ℝ :=
  (y-atkinsonSaddleRoot (T/(2*Real.pi)) b)*Real.sqrt (atkinsonRootMorseCurvature T b y)

theorem atkinsonRootMorseCurvature_contDiffAt {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ ∞ (atkinsonRootMorseCurvature T b) y := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have hjet : ∀ x ∈ Ioo (0:ℝ) (r+y+1),
      ContDiffAt ℝ ∞ (deriv (deriv (atkinsonRootPhase T b))) x := by
    intro x hx
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      contDiffAt_iteratedDeriv_infty (contDiffAt_atkinsonRootPhase_infty T b hx.1) 2
  have ha : r ∈ Ioo (0:ℝ) (r+y+1) := ⟨hr,by linarith⟩
  have hx : y ∈ Ioo (0:ℝ) (r+y+1) := ⟨hy,by linarith⟩
  exact ((segmentTaylorAverage_contDiffOn hjet ha 0).contDiffAt
    (isOpen_Ioo.mem_nhds hx)).neg

theorem atkinsonRoot_deficit_eq_morseCurvature {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) :
    atkinsonRootPhase T b (atkinsonSaddleRoot (T/(2*Real.pi)) b) -
      atkinsonRootPhase T b y =
        (y-atkinsonSaddleRoot (T/(2*Real.pi)) b)^2*atkinsonRootMorseCurvature T b y := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have ha : r ∈ Ioo (0:ℝ) (r+y+1) := ⟨hr,by linarith⟩
  have hx : y ∈ Ioo (0:ℝ) (r+y+1) := ⟨hy,by linarith⟩
  have ht := segmentTaylorAverage_second
    (fun x (hx : x ∈ Ioo (0:ℝ) (r+y+1)) => contDiffAt_atkinsonRootPhase_infty T b hx.1) ha hx
  have hs : deriv (atkinsonRootPhase T b) r = 0 := by
    rw [(hasDerivAt_atkinsonRootPhase T b hr).deriv, atkinsonRootSlope_factored hT b hr]
    simp only [r,sub_self,mul_zero,zero_mul]
  rw [hs,mul_zero,sub_zero] at ht
  change atkinsonRootPhase T b r-atkinsonRootPhase T b y =
    (y-r)^2 * (-segmentTaylorAverage (deriv (deriv (atkinsonRootPhase T b))) r 0 y)
  linarith only [ht]

theorem one_le_atkinsonRootMorseCurvature {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) : 1 ≤ atkinsonRootMorseCurvature T b y := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have ha : r ∈ Ioo (0:ℝ) (r+y+1) := ⟨hr,by linarith⟩
  have hx : y ∈ Ioo (0:ℝ) (r+y+1) := ⟨hy,by linarith⟩
  have hj : ∀ x ∈ Ioo (0:ℝ) (r+y+1),
      ContDiffAt ℝ ∞ (deriv (deriv (atkinsonRootPhase T b))) x := by
    intro x hx
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      contDiffAt_iteratedDeriv_infty (contDiffAt_atkinsonRootPhase_infty T b hx.1) 2
  have hi := segmentTaylorAverage_integrable hj ha hx 0
  simp only [pow_zero,mul_one,iteratedDeriv_zero] at hi
  have hic : IntervalIntegrable (fun t : ℝ => (1-t)*
      deriv (deriv (atkinsonRootPhase T b)) (r+t*(y-r))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hi
  have hc : IntervalIntegrable (fun t : ℝ => -2*(1-t)) volume 0 1 := by
    exact (by fun_prop : Continuous (fun t : ℝ => -2*(1-t))).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hic hc (by
    intro t ht
    have hpos := (affineSegment_mem_Ioo ha hx ht).1
    rw [deriv_deriv_atkinsonRootPhase T b hpos]
    rw [neg_div]
    have hnonneg : 0 ≤ T/(Real.pi*(r+t*(y-r))^2) := by positivity
    nlinarith [mul_nonneg (by linarith [ht.2] : 0 ≤ 1-t) hnonneg])
  have he : (∫ t : ℝ in (0:ℝ)..1, -2*(1-t)) = -1 := by
    have hconst : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1 := intervalIntegrable_const
    have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 1 := continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hconst hid]
    norm_num [integral_id]
  rw [he] at hmono
  unfold atkinsonRootMorseCurvature
  rw [segmentTaylorAverage_zero_eq_intervalIntegral]
  change 1 ≤ -(∫ t : ℝ in (0:ℝ)..1,
    (1-t)*deriv (deriv (atkinsonRootPhase T b)) (r+t*(y-r)))
  linarith only [hmono]

theorem atkinsonRootMorseCoordinate_normalForm {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) :
    atkinsonRootPhase T b y =
      atkinsonRootPhase T b (atkinsonSaddleRoot (T/(2*Real.pi)) b) -
        (atkinsonRootMorseCoordinate T b y)^2 := by
  have hk := one_le_atkinsonRootMorseCurvature hT b hy
  have hd := atkinsonRoot_deficit_eq_morseCurvature hT b hy
  rw [atkinsonRootMorseCoordinate,mul_pow,Real.sq_sqrt (by linarith :
    0 ≤ atkinsonRootMorseCurvature T b y)]
  linarith only [hd]

theorem atkinsonRootMorseCoordinate_contDiffAt {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ ∞ (atkinsonRootMorseCoordinate T b) y := by
  have hk := one_le_atkinsonRootMorseCurvature hT b hy
  exact (contDiffAt_id.sub contDiffAt_const).mul
    ((atkinsonRootMorseCurvature_contDiffAt hT b hy).sqrt (by linarith))

theorem atkinsonRootMorseCoordinate_at_saddle (T b : ℝ) :
    atkinsonRootMorseCoordinate T b (atkinsonSaddleRoot (T/(2*Real.pi)) b) = 0 := by
  simp only [atkinsonRootMorseCoordinate,sub_self,zero_mul]

theorem atkinsonRootMorseCurvature_at_saddle {T : ℝ} (hT : 0 < T) (b : ℝ) :
    atkinsonRootMorseCurvature T b (atkinsonSaddleRoot (T/(2*Real.pi)) b) =
      1+T/(2*Real.pi*(atkinsonSaddleRoot (T/(2*Real.pi)) b)^2) := by
  rw [atkinsonRootMorseCurvature,segmentTaylorAverage_at_center,
    deriv_deriv_atkinsonRootPhase T b (atkinsonSaddleRoot_pos (by positivity) b)]
  ring

theorem atkinsonRootMorseCoordinate_hasDerivAt_saddle {T : ℝ} (hT : 0 < T) (b : ℝ) :
    HasDerivAt (atkinsonRootMorseCoordinate T b)
      (Real.sqrt (atkinsonRootMorseCurvature T b (atkinsonSaddleRoot (T/(2*Real.pi)) b)))
      (atkinsonSaddleRoot (T/(2*Real.pi)) b) := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have hk := one_le_atkinsonRootMorseCurvature hT b hr
  have hg := ((atkinsonRootMorseCurvature_contDiffAt hT b hr).sqrt (by linarith)).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hd := ((hasDerivAt_id r).sub_const r).mul hg.hasDerivAt
  simpa only [id_eq,sub_self,zero_mul,one_mul,add_zero] using hd

theorem atkinsonRootMorseCoordinate_deriv_of_ne {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) (hne : y ≠ atkinsonSaddleRoot (T/(2*Real.pi)) b) :
    deriv (atkinsonRootMorseCoordinate T b) y =
      (1+(atkinsonSaddleRoot (T/(2*Real.pi)) b-b)/y)/
        Real.sqrt (atkinsonRootMorseCurvature T b y) := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  have hk := one_le_atkinsonRootMorseCurvature hT b hy
  have hs : 0 < Real.sqrt (atkinsonRootMorseCurvature T b y) := Real.sqrt_pos.2 (by linarith)
  have hd := (hasDerivAt_const y (atkinsonRootPhase T b r)).sub
    (((atkinsonRootMorseCoordinate_contDiffAt hT b hy).differentiableAt
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt.pow 2)
  have he : (fun x => atkinsonRootPhase T b r-(atkinsonRootMorseCoordinate T b x)^2)
      =ᶠ[𝓝 y] atkinsonRootPhase T b := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact (atkinsonRootMorseCoordinate_normalForm hT b hx).symm
  have he' := he.deriv_eq
  change HasDerivAt (fun x => atkinsonRootPhase T b r-(atkinsonRootMorseCoordinate T b x)^2)
    (0-(2:ℝ)*atkinsonRootMorseCoordinate T b y^(2-1)*deriv (atkinsonRootMorseCoordinate T b) y) y at hd
  rw [hd.deriv,(hasDerivAt_atkinsonRootPhase T b hy).deriv,
    atkinsonRootSlope_factored hT b hy] at he'
  simp only [Nat.reduceSub,pow_one,zero_sub] at he'
  rw [atkinsonRootMorseCoordinate] at he'
  apply (eq_div_iff hs.ne').2
  apply mul_left_cancel₀ (sub_ne_zero.mpr hne)
  change (y-r)*(deriv (atkinsonRootMorseCoordinate T b) y *
    Real.sqrt (atkinsonRootMorseCurvature T b y)) = (y-r)*(1+(r-b)/y)
  linear_combination -he'/2

theorem atkinsonRootMorseCoordinate_deriv_pos {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) : 0 < deriv (atkinsonRootMorseCoordinate T b) y := by
  have hk := one_le_atkinsonRootMorseCurvature hT b hy
  by_cases heq : y = atkinsonSaddleRoot (T/(2*Real.pi)) b
  · subst y
    rw [(atkinsonRootMorseCoordinate_hasDerivAt_saddle hT b).deriv]
    exact Real.sqrt_pos.2 (by linarith)
  · rw [atkinsonRootMorseCoordinate_deriv_of_ne hT b hy heq]
    have hr := atkinsonSaddleRoot_sub_pos (by positivity : 0 < T/(2*Real.pi)) b
    exact div_pos (by positivity) (Real.sqrt_pos.2 (by linarith))

theorem atkinsonRootMorseCoordinate_strictMonoOn {T : ℝ} (hT : 0 < T) (b : ℝ) :
    StrictMonoOn (atkinsonRootMorseCoordinate T b) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (0:ℝ))
  · exact fun y hy => (atkinsonRootMorseCoordinate_contDiffAt hT b hy).continuousAt.continuousWithinAt
  · intro y hy
    exact atkinsonRootMorseCoordinate_deriv_pos hT b (interior_subset hy)

def atkinsonRootMorseRange (T b : ℝ) : Set ℝ :=
  atkinsonRootMorseCoordinate T b '' Ioi 0

def atkinsonRootMorseInverse (T b : ℝ) : ℝ → ℝ :=
  Function.invFunOn (atkinsonRootMorseCoordinate T b) (Ioi 0)

theorem atkinsonRootMorseInverse_coordinate {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) :
    atkinsonRootMorseInverse T b (atkinsonRootMorseCoordinate T b y) = y :=
  (atkinsonRootMorseCoordinate_strictMonoOn hT b).injOn.leftInvOn_invFunOn hy

theorem atkinsonRootMorseInverse_pos {T : ℝ} (hT : 0 < T) (b : ℝ)
    {z : ℝ} (hz : z ∈ atkinsonRootMorseRange T b) :
    0 < atkinsonRootMorseInverse T b z := by
  rcases hz with ⟨y,hy,rfl⟩
  rwa [atkinsonRootMorseInverse_coordinate hT b hy]

theorem atkinsonRootMorseCoordinate_inverse {T b z : ℝ}
    (hz : z ∈ atkinsonRootMorseRange T b) :
    atkinsonRootMorseCoordinate T b (atkinsonRootMorseInverse T b z) = z :=
  Function.invFunOn_eq hz

theorem atkinsonRootMorseCoordinate_hasStrictDerivAt {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) :
    HasStrictDerivAt (atkinsonRootMorseCoordinate T b)
      (deriv (atkinsonRootMorseCoordinate T b) y) y :=
  (atkinsonRootMorseCoordinate_contDiffAt hT b hy).hasStrictDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)

theorem atkinsonRootMorseInverse_hasStrictDerivAt {T : ℝ} (hT : 0 < T) (b : ℝ)
    {z : ℝ} (hz : z ∈ atkinsonRootMorseRange T b) :
    HasStrictDerivAt (atkinsonRootMorseInverse T b)
      (deriv (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b z))⁻¹ z := by
  rcases hz with ⟨y,hy,rfl⟩
  rw [atkinsonRootMorseInverse_coordinate hT b hy]
  have hd := atkinsonRootMorseCoordinate_hasStrictDerivAt hT b hy
  apply hd.to_local_left_inverse (atkinsonRootMorseCoordinate_deriv_pos hT b hy).ne'
  filter_upwards [Ioi_mem_nhds hy] with x hx
  exact atkinsonRootMorseInverse_coordinate hT b hx

theorem atkinsonRootMorseRange_isOpen {T : ℝ} (hT : 0 < T) (b : ℝ) :
    IsOpen (atkinsonRootMorseRange T b) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨y,hy,rfl⟩
  have hd := atkinsonRootMorseCoordinate_hasStrictDerivAt hT b hy
  have hi := Filter.image_mem_map (m := atkinsonRootMorseCoordinate T b) (Ioi_mem_nhds hy)
  rwa [hd.map_nhds_eq (atkinsonRootMorseCoordinate_deriv_pos hT b hy).ne'] at hi

theorem atkinsonRootMorseInverse_contDiffAt {T : ℝ} (hT : 0 < T) (b : ℝ)
    {z : ℝ} (hz : z ∈ atkinsonRootMorseRange T b) :
    ContDiffAt ℝ ∞ (atkinsonRootMorseInverse T b) z := by
  rcases hz with ⟨y,hy,rfl⟩
  have hc := atkinsonRootMorseCoordinate_contDiffAt hT b hy
  have hd := atkinsonRootMorseCoordinate_hasStrictDerivAt hT b hy
  have he := hd.hasStrictFDerivAt_equiv (atkinsonRootMorseCoordinate_deriv_pos hT b hy).ne'
  have hg : ∀ᶠ x in 𝓝 y,
      atkinsonRootMorseInverse T b (atkinsonRootMorseCoordinate T b x) = x := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact atkinsonRootMorseInverse_coordinate hT b hx
  exact (hc.to_localInverse he.hasFDerivAt (by simp)).congr_of_eventuallyEq
    (he.localInverse_unique hg)

theorem atkinsonRootMorseInverse_deriv_pos {T : ℝ} (hT : 0 < T) (b : ℝ)
    {z : ℝ} (hz : z ∈ atkinsonRootMorseRange T b) :
    0 < deriv (atkinsonRootMorseInverse T b) z := by
  rw [(atkinsonRootMorseInverse_hasStrictDerivAt hT b hz).hasDerivAt.deriv]
  exact inv_pos.2 (atkinsonRootMorseCoordinate_deriv_pos hT b
    (atkinsonRootMorseInverse_pos hT b hz))

theorem atkinsonRootMorseInverse_injOn (T b : ℝ) :
    InjOn (atkinsonRootMorseInverse T b) (atkinsonRootMorseRange T b) := by
  intro z hz w hw he
  have h := congrArg (atkinsonRootMorseCoordinate T b) he
  simpa only [atkinsonRootMorseCoordinate_inverse hz,atkinsonRootMorseCoordinate_inverse hw] using h

theorem atkinsonRootMorseInverse_image {T : ℝ} (hT : 0 < T) (b : ℝ) :
    atkinsonRootMorseInverse T b '' atkinsonRootMorseRange T b = Ioi 0 := by
  apply Subset.antisymm
  · rintro y ⟨z,hz,rfl⟩
    exact atkinsonRootMorseInverse_pos hT b hz
  · intro y hy
    exact ⟨atkinsonRootMorseCoordinate T b y,⟨y,hy,rfl⟩,
      atkinsonRootMorseInverse_coordinate hT b hy⟩

theorem atkinsonRoot_integral_eq_morseIntegral {T : ℝ} (hT : 0 < T) (b : ℝ)
    (g : ℝ → ℂ) :
    (∫ y in Ioi (0:ℝ), g y) =
      ∫ z in atkinsonRootMorseRange T b,
        ((deriv (atkinsonRootMorseInverse T b) z : ℝ) : ℂ)*g (atkinsonRootMorseInverse T b z) := by
  have hd : ∀ z ∈ atkinsonRootMorseRange T b,
      HasDerivWithinAt (atkinsonRootMorseInverse T b)
        (deriv (atkinsonRootMorseInverse T b) z) (atkinsonRootMorseRange T b) z :=
    fun _ hz => (atkinsonRootMorseInverse_hasStrictDerivAt hT b hz).hasDerivAt
      |>.differentiableAt.hasDerivAt.hasDerivWithinAt
  have hs := (atkinsonRootMorseRange_isOpen hT b).measurableSet
  have h := integral_image_eq_integral_abs_deriv_smul hs hd (atkinsonRootMorseInverse_injOn T b) g
  rw [atkinsonRootMorseInverse_image hT b] at h
  exact h.trans (setIntegral_congr_fun hs (fun z hz => by
    rw [abs_of_pos (atkinsonRootMorseInverse_deriv_pos hT b hz),Complex.real_smul]))

theorem atkinsonPowerIntegral_eq_root_Ioi {T : ℝ} (hT : 0 < T) (G L α b : ℝ) :
    atkinsonPowerIntegral T G L α b =
      2*∫ y in Ioi (0:ℝ), atkinsonPowerWeight T G L α (y^2)*atkinsonRootKernel T b y := by
  have hd : ∀ y ∈ Ioi (0:ℝ), HasDerivWithinAt (fun y : ℝ => y^2) (2*y) (Ioi 0) y := by
    intro y _
    simpa using ((hasDerivAt_id y).pow 2).hasDerivWithinAt
  have hi : InjOn (fun y : ℝ => y^2) (Ioi 0) := by
    intro y hy x hx he
    nlinarith [show 0 < y+x from add_pos hy hx]
  have himage : (fun y : ℝ => y^2) '' Ioi 0 = Ioi 0 := by
    apply Subset.antisymm
    · rintro _ ⟨y,hy,rfl⟩
      exact sq_pos_of_pos (show (0:ℝ) < y from hy)
    · intro x hx
      exact ⟨Real.sqrt x,Real.sqrt_pos.2 hx,Real.sq_sqrt hx.le⟩
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hi
    (atkinsonPowerIntegrand T G L α b)
  rw [himage] at h
  unfold atkinsonPowerIntegral
  rw [h,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  dsimp only
  have hy0 : 0 < y := hy
  rw [abs_of_pos (by positivity : 0 < 2*y)]
  exact atkinsonPowerIntegrand_sq hT hy G L α b

theorem atkinsonRootKernel_morseInverse {T : ℝ} (hT : 0 < T) (b : ℝ)
    {z : ℝ} (hz : z ∈ atkinsonRootMorseRange T b) :
    atkinsonRootKernel T b (atkinsonRootMorseInverse T b z) =
      atkinsonRootKernel T b (atkinsonSaddleRoot (T/(2*Real.pi)) b)*betaQuadraticKernel 2 z := by
  have he := atkinsonRootMorseCoordinate_normalForm hT b (atkinsonRootMorseInverse_pos hT b hz)
  rw [atkinsonRootMorseCoordinate_inverse hz] at he
  rw [atkinsonRootKernel,he]
  unfold atkinsonRootKernel betaQuadraticKernel
  simp only [Real.fourierChar_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

def atkinsonMorseWeight (T G L α b z : ℝ) : ℂ :=
  ((deriv (atkinsonRootMorseInverse T b) z : ℝ) : ℂ)*
    atkinsonPowerWeight T G L α ((atkinsonRootMorseInverse T b z)^2)

theorem atkinsonPowerIntegral_eq_morse {T : ℝ} (hT : 0 < T) (G L α b : ℝ) :
    atkinsonPowerIntegral T G L α b =
      2*atkinsonRootKernel T b (atkinsonSaddleRoot (T/(2*Real.pi)) b)*
        ∫ z in atkinsonRootMorseRange T b, atkinsonMorseWeight T G L α b z*betaQuadraticKernel 2 z := by
  rw [atkinsonPowerIntegral_eq_root_Ioi hT,
    atkinsonRoot_integral_eq_morseIntegral hT b,mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (atkinsonRootMorseRange_isOpen hT b).measurableSet
  intro z hz
  dsimp only
  rw [atkinsonRootKernel_morseInverse hT b hz]
  unfold atkinsonMorseWeight
  ring

theorem zero_mem_atkinsonRootMorseRange {T : ℝ} (hT : 0 < T) (b : ℝ) :
    0 ∈ atkinsonRootMorseRange T b :=
  ⟨atkinsonSaddleRoot (T/(2*Real.pi)) b,atkinsonSaddleRoot_pos (by positivity) b,
    atkinsonRootMorseCoordinate_at_saddle T b⟩

theorem atkinsonRootMorseInverse_zero {T : ℝ} (hT : 0 < T) (b : ℝ) :
    atkinsonRootMorseInverse T b 0 = atkinsonSaddleRoot (T/(2*Real.pi)) b := by
  have h := atkinsonRootMorseInverse_coordinate hT b
    (atkinsonSaddleRoot_pos (by positivity : 0 < T/(2*Real.pi)) b)
  rwa [atkinsonRootMorseCoordinate_at_saddle] at h

theorem atkinsonRootMorseInverse_deriv_zero {T : ℝ} (hT : 0 < T) (b : ℝ) :
    deriv (atkinsonRootMorseInverse T b) 0 = (Real.sqrt (atkinsonSaddleCurvature T b))⁻¹ := by
  rw [(atkinsonRootMorseInverse_hasStrictDerivAt hT b
    (zero_mem_atkinsonRootMorseRange hT b)).hasDerivAt.deriv,
    atkinsonRootMorseInverse_zero hT b,(atkinsonRootMorseCoordinate_hasDerivAt_saddle hT b).deriv,
    atkinsonRootMorseCurvature_at_saddle hT b]
  congr 2
  unfold atkinsonSaddleCurvature
  ring

theorem atkinsonStationaryMain_eq_morse_main {T : ℝ} (hT : 0 < T) (G L α b : ℝ) :
    atkinsonStationaryMain T G L α b =
      2*atkinsonRootKernel T b (atkinsonSaddleRoot (T/(2*Real.pi)) b)*
        (atkinsonMorseWeight T G L α b 0*fresnelGaussianValue 1) := by
  have hc : 0 < atkinsonSaddleCurvature T b := by linarith [one_lt_atkinsonSaddleCurvature hT b]
  unfold atkinsonStationaryMain atkinsonMorseWeight
  rw [atkinsonRootMorseInverse_zero hT b,atkinsonRootMorseInverse_deriv_zero hT b,
    fresnelGaussianValue_eq_cartesian hc,fresnelGaussianValue_eq_cartesian (by norm_num : (0:ℝ) < 1)]
  simp only [Real.sqrt_one]
  push_cast
  ring

theorem atkinsonRootMorseCurvature_le {T a : ℝ} (hT : 0 < T) (b : ℝ) (ha : 0 < a)
    (har : a ≤ atkinsonSaddleRoot (T/(2*Real.pi)) b) {y : ℝ} (hay : a ≤ y) :
    atkinsonRootMorseCurvature T b y ≤ 1+T/(2*Real.pi*a^2) := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have hy : 0 < y := ha.trans_le hay
  have hra : r ∈ Ioo (0:ℝ) (r+y+1) := ⟨hr,by linarith⟩
  have hya : y ∈ Ioo (0:ℝ) (r+y+1) := ⟨hy,by linarith⟩
  have hj : ∀ x ∈ Ioo (0:ℝ) (r+y+1),
      ContDiffAt ℝ ∞ (deriv (deriv (atkinsonRootPhase T b))) x := by
    intro x hx
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      contDiffAt_iteratedDeriv_infty (contDiffAt_atkinsonRootPhase_infty T b hx.1) 2
  have hi := segmentTaylorAverage_integrable hj hra hya 0
  simp only [pow_zero,mul_one,iteratedDeriv_zero] at hi
  have hic : IntervalIntegrable (fun t : ℝ => (1-t)*
      deriv (deriv (atkinsonRootPhase T b)) (r+t*(y-r))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact hi
  let C : ℝ := -(T/(Real.pi*a^2)+2)
  have hc : IntervalIntegrable (fun t : ℝ => (1-t)*C) volume 0 1 := by
    exact (by fun_prop : Continuous (fun t : ℝ => (1-t)*C)).intervalIntegrable _ _
  have hm := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hc hic (by
    intro t ht
    have hlow : a ≤ r+t*(y-r) := by
      nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hay),
        mul_nonneg (by linarith [ht.2] : 0 ≤ 1-t) (sub_nonneg.mpr har)]
    have hpos : 0 < r+t*(y-r) := ha.trans_le hlow
    rw [deriv_deriv_atkinsonRootPhase T b hpos,neg_div]
    have hdiv : T/(Real.pi*(r+t*(y-r))^2) ≤ T/(Real.pi*a^2) := by gcongr
    dsimp [C]
    nlinarith [mul_nonneg (by linarith [ht.2] : 0 ≤ 1-t) (sub_nonneg.mpr hdiv)])
  have he : (∫ t : ℝ in (0:ℝ)..1, (1-t)*C) = C/2 := by
    have hconst : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 1 := intervalIntegrable_const
    have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 1 := continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_sub hconst hid]
    norm_num [integral_id]
    ring
  rw [he] at hm
  unfold atkinsonRootMorseCurvature
  rw [segmentTaylorAverage_zero_eq_intervalIntegral]
  change -(∫ t : ℝ in (0:ℝ)..1,
    (1-t)*deriv (deriv (atkinsonRootPhase T b)) (r+t*(y-r))) ≤ _
  dsimp [C] at hm
  have heq : T/(2*Real.pi*a^2) = (T/(Real.pi*a^2))/2 := by ring
  rw [heq]
  linarith only [hm]

theorem atkinsonRootMorseCurvature_physical_bounds {T b y : ℝ} (hT : 0 < T)
    (hb : |b| ≤ Real.sqrt T/100) (hy : Real.sqrt T/4 ≤ y) :
    1 ≤ atkinsonRootMorseCurvature T b y ∧ atkinsonRootMorseCurvature T b y ≤ 4 := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hr := (atkinsonSaddleRoot_small_frequency hT hb).1
  refine ⟨one_le_atkinsonRootMorseCurvature hT b (by linarith),?_⟩
  have h := atkinsonRootMorseCurvature_le hT b (by positivity : 0 < Real.sqrt T/4)
    (by linarith) hy
  have he : 1+T/(2*Real.pi*(Real.sqrt T/4)^2) = 1+8/Real.pi := by
    rw [div_pow,Real.sq_sqrt hT.le]
    field_simp
    ring
  rw [he] at h
  have hp : 8/Real.pi ≤ (3:ℝ) := (div_le_iff₀ Real.pi_pos).2 (by linarith [Real.pi_gt_three])
  linarith

theorem atkinsonRootMorseCoordinate_physical_deriv_bounds {T b y : ℝ} (hT : 0 < T)
    (hb : |b| ≤ Real.sqrt T/100) (hy : Real.sqrt T/4 ≤ y) :
    1/2 ≤ deriv (atkinsonRootMorseCoordinate T b) y ∧
      deriv (atkinsonRootMorseCoordinate T b) y ≤ 4 := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hy0 : 0 < y := by linarith
  obtain ⟨hK,hK4⟩ := atkinsonRootMorseCurvature_physical_bounds hT hb hy
  have hS : 1 ≤ Real.sqrt (atkinsonRootMorseCurvature T b y) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hK
  have hS2 : Real.sqrt (atkinsonRootMorseCurvature T b y) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ atkinsonRootMorseCurvature T b y),
      Real.sqrt_nonneg (atkinsonRootMorseCurvature T b y)]
  by_cases heq : y = atkinsonSaddleRoot (T/(2*Real.pi)) b
  · rw [heq,(atkinsonRootMorseCoordinate_hasDerivAt_saddle hT b).deriv]
    rw [heq] at hS hS2
    constructor <;> linarith
  · rw [atkinsonRootMorseCoordinate_deriv_of_ne hT b hy0 heq]
    have hr := (atkinsonSaddleRoot_small_frequency hT hb).2
    have hrp := atkinsonSaddleRoot_sub_pos (by positivity : 0 < T/(2*Real.pi)) b
    have hn0 : 0 ≤ (atkinsonSaddleRoot (T/(2*Real.pi)) b-b)/y := by positivity
    have hn3 : (atkinsonSaddleRoot (T/(2*Real.pi)) b-b)/y ≤ 3 := by
      apply (div_le_iff₀ hy0).2
      linarith [(abs_le.mp hb).1]
    constructor
    · apply (le_div_iff₀ (by linarith : 0 < Real.sqrt (atkinsonRootMorseCurvature T b y))).2
      linarith
    · apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (atkinsonRootMorseCurvature T b y))).2
      linarith

theorem norm_atkinsonPowerIntegral_sub_stationary_eq_morseRemainder {T : ℝ}
    (hT : 0 < T) (G L α b : ℝ) :
    ‖atkinsonPowerIntegral T G L α b-atkinsonStationaryMain T G L α b‖ =
      2*‖(∫ z in atkinsonRootMorseRange T b,
        atkinsonMorseWeight T G L α b z*betaQuadraticKernel 2 z)-
          atkinsonMorseWeight T G L α b 0*fresnelGaussianValue 1‖ := by
  rw [atkinsonPowerIntegral_eq_morse hT,atkinsonStationaryMain_eq_morse_main hT,
    ← mul_sub,norm_mul,norm_mul,Complex.norm_ofNat,norm_atkinsonRootKernel,mul_one]

theorem atkinsonRootMorseCoordinate_tendsto_atTop {T : ℝ} (hT : 0 < T) (b : ℝ) :
    Tendsto (atkinsonRootMorseCoordinate T b) atTop atTop := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  rw [tendsto_atTop]
  intro B
  filter_upwards [eventually_ge_atTop (max (r+1) (B+r))] with y hy
  have hyr : r+1 ≤ y := (le_max_left _ _).trans hy
  have hyB : B+r ≤ y := (le_max_right _ _).trans hy
  have hk := one_le_atkinsonRootMorseCurvature hT b (by linarith : 0 < y)
  have hs : 1 ≤ Real.sqrt (atkinsonRootMorseCurvature T b y) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hk
  change B ≤ (y-r)*Real.sqrt (atkinsonRootMorseCurvature T b y)
  nlinarith [mul_nonneg (by linarith : 0 ≤ y-r) (sub_nonneg.mpr hs)]

theorem atkinsonRootPhase_tendsto_atBot {T : ℝ} (hT : 0 < T) (b : ℝ) :
    Tendsto (atkinsonRootPhase T b) (𝓝[>] (0:ℝ)) atBot := by
  have hlog := Real.tendsto_log_nhdsGT_zero.const_mul_atBot
    (by positivity : 0 < T/Real.pi)
  have hc : Tendsto (fun y : ℝ => -y^2+2*b*y) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : ContinuousAt (fun y : ℝ => -y^2+2*b*y) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  convert hlog.atBot_add hc using 1
  funext y
  unfold atkinsonRootPhase
  ring

theorem atkinsonRootMorseCoordinate_tendsto_atBot {T : ℝ} (hT : 0 < T) (b : ℝ) :
    Tendsto (atkinsonRootMorseCoordinate T b) (𝓝[>] (0:ℝ)) atBot := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  rw [tendsto_atBot]
  intro B
  have he := (atkinsonRootPhase_tendsto_atBot hT b).eventually_le_atBot
    (atkinsonRootPhase T b r-(|B|+1)^2)
  have hsmall : ∀ᶠ y in 𝓝[>] (0:ℝ), y < r :=
    nhdsWithin_le_nhds (Iio_mem_nhds hr)
  filter_upwards [he,hsmall,self_mem_nhdsWithin] with y hy hyr hy0
  have hypos : 0 < y := hy0
  have hn := atkinsonRootMorseCoordinate_normalForm hT b hypos
  have hnegative : atkinsonRootMorseCoordinate T b y < 0 := by
    unfold atkinsonRootMorseCoordinate
    have hk := one_le_atkinsonRootMorseCurvature hT b hypos
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hyr) (Real.sqrt_pos.2 (by linarith))
  have hsq : (|B|+1)^2 ≤ (atkinsonRootMorseCoordinate T b y)^2 := by
    dsimp [r] at hy
    linarith only [hn,hy]
  have hneg : atkinsonRootMorseCoordinate T b y ≤ -(|B|+1) := by
    nlinarith [abs_nonneg B]
  linarith [neg_abs_le B]

theorem atkinsonRootMorseRange_eq_univ {T : ℝ} (hT : 0 < T) (b : ℝ) :
    atkinsonRootMorseRange T b = univ := by
  apply Set.eq_univ_of_univ_subset
  exact isPreconnected_Ioi.intermediate_value_Iii
    (l₁ := 𝓝[>] (0:ℝ)) (l₂ := atTop) inf_le_right
    (le_principal_iff.mpr (eventually_gt_atTop (0:ℝ)))
    (fun y hy => (atkinsonRootMorseCoordinate_contDiffAt hT b hy).continuousAt.continuousWithinAt)
    (atkinsonRootMorseCoordinate_tendsto_atBot hT b)
    (atkinsonRootMorseCoordinate_tendsto_atTop hT b)

theorem contDiff_atkinsonRootMorseInverse {T : ℝ} (hT : 0 < T) (b : ℝ) :
    ContDiff ℝ ∞ (atkinsonRootMorseInverse T b) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  exact atkinsonRootMorseInverse_contDiffAt hT b (by rw [atkinsonRootMorseRange_eq_univ hT b]; trivial)

theorem contDiffAt_atkinsonPowerWeight_infty {T G : ℝ} (hT : 0 < T) (hG : G ≠ 0)
    (L α : ℝ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ (atkinsonPowerWeight T G L α) x := by
  have hw := contDiff_zetaDivisorWeight
  have hc := contDiff_zetaDivisorBandCutoff T G L
  have hg := contDiff_zetaGaussianQuadraticIntegral T hG
  have hcast : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  unfold atkinsonPowerWeight atkinsonPowerProfile zetaMainMellinProfile
  fun_prop (disch := positivity)

theorem contDiff_atkinsonMorseWeight {T G : ℝ} (hT : 0 < T) (hG : G ≠ 0)
    (L α b : ℝ) : ContDiff ℝ ∞ (atkinsonMorseWeight T G L α b) := by
  have hi := contDiff_atkinsonRootMorseInverse hT b
  have hd : ContDiff ℝ ∞ (deriv (atkinsonRootMorseInverse T b)) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    simpa only [iteratedDeriv_one] using contDiffAt_iteratedDeriv_infty (hi.contDiffAt (x := z)) 1
  rw [contDiff_iff_contDiffAt]
  intro z
  have hz : z ∈ atkinsonRootMorseRange T b := by rw [atkinsonRootMorseRange_eq_univ hT b]; trivial
  have hp := atkinsonRootMorseInverse_pos hT b hz
  have hf := contDiffAt_atkinsonPowerWeight_infty (x := (atkinsonRootMorseInverse T b z)^2)
    hT hG L α (sq_pos_of_pos hp)
  have hcomp : ContDiffAt ℝ ∞ (fun x => atkinsonPowerWeight T G L α
      ((atkinsonRootMorseInverse T b x)^2)) z := by
    apply ContDiffAt.comp z (g := atkinsonPowerWeight T G L α) hf
    exact hi.contDiffAt.pow 2
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hd.contDiffAt).mul hcomp

theorem iteratedDeriv_atkinsonRootMorseCurvature {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) (k : ℕ) :
    iteratedDeriv k (atkinsonRootMorseCurvature T b) y =
      -segmentTaylorAverage (deriv (deriv (atkinsonRootPhase T b)))
        (atkinsonSaddleRoot (T/(2*Real.pi)) b) k y := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
      let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
      have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
      have hj : ∀ x ∈ Ioo (0:ℝ) (r+y+1),
          ContDiffAt ℝ ∞ (deriv (deriv (atkinsonRootPhase T b))) x := by
        intro x hx
        simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
          contDiffAt_iteratedDeriv_infty (contDiffAt_atkinsonRootPhase_infty T b hx.1) 2
      have hd := (segmentTaylorAverage_hasDerivAt hj
        (show r ∈ Ioo (0:ℝ) (r+y+1) from ⟨hr,by linarith⟩)
        (show y ∈ Ioo (0:ℝ) (r+y+1) from ⟨hy,by linarith⟩) k).neg
      have he : iteratedDeriv k (atkinsonRootMorseCurvature T b) =ᶠ[𝓝 y]
          fun x => -segmentTaylorAverage (deriv (deriv (atkinsonRootPhase T b))) r k x := by
        filter_upwards [Ioi_mem_nhds hy] with x hx
        exact ih hx
      rw [iteratedDeriv_succ,he.deriv_eq]
      exact hd.deriv

theorem atkinsonRootPhase_third (T b : ℝ) {y : ℝ} (hy : 0 < y) :
    iteratedDeriv 1 (deriv (deriv (atkinsonRootPhase T b))) y =
      2*T/(Real.pi*y^3) := by
  have he : deriv (deriv (atkinsonRootPhase T b)) =ᶠ[𝓝 y]
      fun x => -T/(Real.pi*x^2)-2 := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact deriv_deriv_atkinsonRootPhase T b hx
  have hd := ((hasDerivAt_const y (-T)).div
    (((hasDerivAt_id y).pow 2).const_mul Real.pi)
      (by change Real.pi*y^2 ≠ 0; positivity)).sub_const 2
  simp only [Pi.div_apply,Pi.pow_apply,id_eq] at hd
  rw [iteratedDeriv_one,he.deriv_eq,hd.deriv]
  field_simp
  ring

theorem atkinsonRootPhase_fourth (T b : ℝ) {y : ℝ} (hy : 0 < y) :
    iteratedDeriv 2 (deriv (deriv (atkinsonRootPhase T b))) y =
      -6*T/(Real.pi*y^4) := by
  have he : iteratedDeriv 1 (deriv (deriv (atkinsonRootPhase T b))) =ᶠ[𝓝 y]
      fun x => 2*T/(Real.pi*x^3) := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact atkinsonRootPhase_third T b hx
  have hd := (hasDerivAt_const y (2*T)).div
    (((hasDerivAt_id y).pow 3).const_mul Real.pi)
      (by change Real.pi*y^3 ≠ 0; positivity)
  simp only [Pi.pow_apply,id_eq] at hd
  rw [show 2 = 1+1 from rfl,iteratedDeriv_succ,he.deriv_eq]
  change deriv ((fun _ : ℝ => 2*T)/(fun x : ℝ => Real.pi*x^3)) y = _
  rw [hd.deriv]
  field_simp
  ring

theorem atkinsonRootMorseCurvature_jet_bounds {T b y a : ℝ} (hT : 0 < T)
    (ha : 0 < a) (hr : a ≤ atkinsonSaddleRoot (T/(2*Real.pi)) b) (hy : a ≤ y) :
    |deriv (atkinsonRootMorseCurvature T b) y| ≤ 2*T/(Real.pi*a^3) ∧
      |iteratedDeriv 2 (atkinsonRootMorseCurvature T b) y| ≤ 6*T/(Real.pi*a^4) := by
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  have hy0 := ha.trans_le hy
  have hr' : r ∈ Icc a (max r y) := ⟨hr,le_max_left _ _⟩
  have hy' : y ∈ Icc a (max r y) := ⟨hy,le_max_right _ _⟩
  constructor
  · rw [← iteratedDeriv_one,iteratedDeriv_atkinsonRootMorseCurvature hT b hy0 1,abs_neg]
    apply abs_segmentTaylorAverage_le_closed hr' hy' 1
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    rw [atkinsonRootPhase_third T b (ha.trans_le hx.1),abs_of_nonneg (by positivity)]
    gcongr
    exact hx.1
  · rw [iteratedDeriv_atkinsonRootMorseCurvature hT b hy0 2,abs_neg]
    apply abs_segmentTaylorAverage_le_closed hr' hy' 2
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    rw [atkinsonRootPhase_fourth T b hx0]
    have hn : -6*T/(Real.pi*x^4) = -(6*T/(Real.pi*x^4)) := by ring
    rw [hn,abs_neg,abs_of_pos (by positivity : 0 < 6*T/(Real.pi*x^4))]
    gcongr
    exact hx.1

theorem atkinsonRootMorseCurvature_physical_jet_bounds {T b y : ℝ} (hT : 0 < T)
    (hb : |b| ≤ Real.sqrt T/100) (hy : Real.sqrt T/4 ≤ y) :
    |deriv (atkinsonRootMorseCurvature T b) y| ≤ 128/Real.sqrt T ∧
      |iteratedDeriv 2 (atkinsonRootMorseCurvature T b) y| ≤ 1536/T := by
  have hs := Real.sqrt_pos.2 hT
  have hr := (atkinsonSaddleRoot_small_frequency hT hb).1
  obtain ⟨h1,h2⟩ := atkinsonRootMorseCurvature_jet_bounds (b := b) hT (by positivity : 0 < Real.sqrt T/4)
    (by linarith) hy
  have hp : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have he1 : 2*T/(Real.pi*(Real.sqrt T/4)^3) = 128/(Real.pi*Real.sqrt T) := by
    field_simp
    nlinarith [Real.sq_sqrt hT.le]
  have he2 : 6*T/(Real.pi*(Real.sqrt T/4)^4) = 1536/(Real.pi*T) := by
    field_simp
    nlinarith [Real.sq_sqrt hT.le, sq_nonneg (T-(Real.sqrt T)^2)]
  rw [he1] at h1
  rw [he2] at h2
  constructor
  · apply h1.trans
    apply div_le_div_of_nonneg_left (by norm_num) hs
    nlinarith
  · apply h2.trans
    apply div_le_div_of_nonneg_left (by norm_num) hT
    nlinarith

theorem atkinsonRootMorseCoordinate_deriv {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) :
    deriv (atkinsonRootMorseCoordinate T b) y =
      (1+(atkinsonSaddleRoot (T/(2*Real.pi)) b-b)/y)/
        Real.sqrt (atkinsonRootMorseCurvature T b y) := by
  by_cases he : y = atkinsonSaddleRoot (T/(2*Real.pi)) b
  · subst y
    let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
    have hr : 0 < r := hy
    have hK := one_le_atkinsonRootMorseCurvature hT b hr
    have hS : 0 < Real.sqrt (atkinsonRootMorseCurvature T b r) := Real.sqrt_pos.2 (by linarith)
    rw [(atkinsonRootMorseCoordinate_hasDerivAt_saddle hT b).deriv]
    apply (eq_div_iff hS.ne').2
    rw [← pow_two,Real.sq_sqrt (by linarith : 0 ≤ atkinsonRootMorseCurvature T b r),
      atkinsonRootMorseCurvature_at_saddle hT b]
    have hreq := atkinsonSaddleRoot_equation (by positivity : 0 < T/(2*Real.pi)) b
    change 1+T/(2*Real.pi*r^2) = 1+(r-b)/r
    change r^2-b*r = T/(2*Real.pi) at hreq
    rw [eq_div_iff (by positivity : 2*Real.pi ≠ 0)] at hreq
    field_simp
    nlinarith [hreq]
  · exact atkinsonRootMorseCoordinate_deriv_of_ne hT b hy he

theorem atkinsonRootMorseCoordinate_second {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) :
    iteratedDeriv 2 (atkinsonRootMorseCoordinate T b) y =
      -(atkinsonSaddleRoot (T/(2*Real.pi)) b-b)/
        (y^2*Real.sqrt (atkinsonRootMorseCurvature T b y))-
      (1+(atkinsonSaddleRoot (T/(2*Real.pi)) b-b)/y)*
        deriv (atkinsonRootMorseCurvature T b) y/
          (2*(Real.sqrt (atkinsonRootMorseCurvature T b y))^3) := by
  let c := atkinsonSaddleRoot (T/(2*Real.pi)) b-b
  let K := atkinsonRootMorseCurvature T b
  have hK : 0 < K y := by linarith [one_le_atkinsonRootMorseCurvature hT b hy]
  have hs : 0 < Real.sqrt (K y) := Real.sqrt_pos.2 hK
  have hn : HasDerivAt (fun x : ℝ => 1+c/x) (-c/y^2) y := by
    convert ((hasDerivAt_const y c).fun_div (hasDerivAt_id y) hy.ne').const_add 1 using 1
    simp
  have hk := ((atkinsonRootMorseCurvature_contDiffAt hT b hy).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt
  have hd := hn.fun_div (hk.sqrt hK.ne') hs.ne'
  have he : deriv (atkinsonRootMorseCoordinate T b) =ᶠ[𝓝 y]
      fun x => (1+c/x)/Real.sqrt (K x) := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact atkinsonRootMorseCoordinate_deriv hT b hx
  rw [iteratedDeriv_succ,iteratedDeriv_one,he.deriv_eq]
  rw [hd.deriv]
  dsimp only [c,K]
  field_simp

theorem atkinsonRootMorseCoordinate_third {T : ℝ} (hT : 0 < T) (b : ℝ)
    {y : ℝ} (hy : 0 < y) :
    iteratedDeriv 3 (atkinsonRootMorseCoordinate T b) y =
      2*(atkinsonSaddleRoot (T/(2*Real.pi)) b-b)/
        (y^3*Real.sqrt (atkinsonRootMorseCurvature T b y))+
      (atkinsonSaddleRoot (T/(2*Real.pi)) b-b)*
        deriv (atkinsonRootMorseCurvature T b) y/
          (y^2*(Real.sqrt (atkinsonRootMorseCurvature T b y))^3)-
      (1+(atkinsonSaddleRoot (T/(2*Real.pi)) b-b)/y)*
        iteratedDeriv 2 (atkinsonRootMorseCurvature T b) y/
          (2*(Real.sqrt (atkinsonRootMorseCurvature T b y))^3)+
      3*(1+(atkinsonSaddleRoot (T/(2*Real.pi)) b-b)/y)*
        (deriv (atkinsonRootMorseCurvature T b) y)^2/
          (4*(Real.sqrt (atkinsonRootMorseCurvature T b y))^5) := by
  let c := atkinsonSaddleRoot (T/(2*Real.pi)) b-b
  let K := atkinsonRootMorseCurvature T b
  have hK : 0 < K y := by linarith [one_le_atkinsonRootMorseCurvature hT b hy]
  have hs : 0 < Real.sqrt (K y) := Real.sqrt_pos.2 hK
  have hc := atkinsonRootMorseCurvature_contDiffAt hT b hy
  have hk := (hc.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt
  have hk' : HasDerivAt (deriv K) (iteratedDeriv 2 K y) y := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      ((contDiffAt_iteratedDeriv_infty hc 1).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt
  have hs' := hk.sqrt hK.ne'
  have hn : HasDerivAt (fun x : ℝ => 1+c/x) (-c/y^2) y := by
    convert ((hasDerivAt_const y c).fun_div (hasDerivAt_id y) hy.ne').const_add 1 using 1
    simp
  have hd := ((hasDerivAt_const y (-c)).fun_div
    (((hasDerivAt_id y).pow 2).mul hs') (by change y^2*Real.sqrt (K y) ≠ 0; positivity)).sub
      ((hn.mul hk').fun_div ((hs'.pow 3).const_mul 2)
        (by change 2*(Real.sqrt (K y))^3 ≠ 0; positivity))
  have he : iteratedDeriv 2 (atkinsonRootMorseCoordinate T b) =ᶠ[𝓝 y]
      fun x => -c/(x^2*Real.sqrt (K x))-
        (1+c/x)*deriv K x/(2*(Real.sqrt (K x))^3) := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    exact atkinsonRootMorseCoordinate_second hT b hx
  rw [iteratedDeriv_succ,he.deriv_eq]
  convert hd.deriv using 1
  dsimp only [c,K,Pi.mul_apply,Pi.pow_apply,id_eq]
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
  field_simp
  ring

theorem atkinsonRootMorseCoordinate_physical_jet_bounds {T b y : ℝ} (hT : 0 < T)
    (hb : |b| ≤ Real.sqrt T/100) (hy : Real.sqrt T/4 ≤ y) :
    |iteratedDeriv 2 (atkinsonRootMorseCoordinate T b) y| ≤ 512/Real.sqrt T ∧
      |iteratedDeriv 3 (atkinsonRootMorseCoordinate T b) y| ≤ 65536/T := by
  let c := atkinsonSaddleRoot (T/(2*Real.pi)) b-b
  let S := Real.sqrt (atkinsonRootMorseCurvature T b y)
  let R := 1/Real.sqrt T
  have hs := Real.sqrt_pos.2 hT
  have hy0 : 0 < y := by linarith
  have hc : 0 < c := atkinsonSaddleRoot_sub_pos (by positivity) b
  have hR : 0 < R := by positivity
  have hS : 1 ≤ S := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (one_le_atkinsonRootMorseCurvature hT b hy0)
  have hS0 : 0 < S := by linarith
  have hR2 : R^2 = 1/T := by dsimp [R]; rw [div_pow,one_pow,Real.sq_sqrt hT.le]
  have hu : 1/y ≤ 4*R := by dsimp [R]; apply (div_le_iff₀ hy0).2; field_simp; nlinarith
  have hv : c/y ≤ 3 := by
    apply (div_le_iff₀ hy0).2
    dsimp [c]
    linarith [(atkinsonSaddleRoot_small_frequency hT hb).2,(abs_le.mp hb).1]
  have hn : 1+c/y ≤ 4 := by linarith
  obtain ⟨hK1,hK2⟩ := atkinsonRootMorseCurvature_physical_jet_bounds hT hb hy
  have hk1 : |deriv (atkinsonRootMorseCurvature T b) y| ≤ 128*R := by
    simpa only [R,mul_one_div] using hK1
  have hk2 : |iteratedDeriv 2 (atkinsonRootMorseCurvature T b) y| ≤ 1536*R^2 := by
    simpa only [hR2,mul_one_div] using hK2
  have hA : |-(c/y)*(1/y)/S| ≤ 12*R := by
    rw [abs_div,abs_mul,abs_neg,abs_of_pos (by positivity : 0 < c/y),
      abs_of_pos (by positivity : 0 < 1/y),abs_of_pos hS0]
    calc
      _ ≤ 3*(4*R)/1 := by gcongr
      _ = _ := by ring
  have hB : |(1+c/y)*deriv (atkinsonRootMorseCurvature T b) y/(2*S^3)| ≤ 256*R := by
    rw [abs_div,abs_mul,abs_of_pos (by positivity : 0 < 1+c/y),
      abs_of_pos (by positivity : 0 < 2*S^3)]
    calc
      _ ≤ 4*(128*R)/(2*1^3) := by gcongr
      _ = _ := by ring
  have hC : |2*(c/y)*(1/y)^2/S| ≤ 96*R^2 := by
    rw [abs_of_pos (by positivity : 0 < 2*(c/y)*(1/y)^2/S)]
    calc
      _ ≤ 2*3*(4*R)^2/1 := by gcongr
      _ = _ := by ring
  have hD : |(c/y)*(1/y)*deriv (atkinsonRootMorseCurvature T b) y/S^3| ≤ 1536*R^2 := by
    rw [abs_div,abs_mul,abs_mul,abs_of_pos (by positivity : 0 < c/y),
      abs_of_pos (by positivity : 0 < 1/y),abs_of_pos (by positivity : 0 < S^3)]
    calc
      _ ≤ 3*(4*R)*(128*R)/1^3 := by gcongr
      _ = _ := by ring
  have hE : |(1+c/y)*iteratedDeriv 2 (atkinsonRootMorseCurvature T b) y/(2*S^3)| ≤ 3072*R^2 := by
    rw [abs_div,abs_mul,abs_of_pos (by positivity : 0 < 1+c/y),
      abs_of_pos (by positivity : 0 < 2*S^3)]
    calc
      _ ≤ 4*(1536*R^2)/(2*1^3) := by gcongr
      _ = _ := by ring
  have hF : |3*(1+c/y)*(deriv (atkinsonRootMorseCurvature T b) y)^2/(4*S^5)| ≤ 49152*R^2 := by
    rw [abs_div,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3),
      abs_of_pos (by positivity : 0 < 1+c/y),abs_pow,abs_of_pos (by positivity : 0 < 4*S^5)]
    calc
      _ ≤ 3*4*(128*R)^2/(4*1^5) := by gcongr
      _ = _ := by ring
  constructor
  · rw [atkinsonRootMorseCoordinate_second hT b hy0]
    have he : -c/(y^2*S) = -(c/y)*(1/y)/S := by field_simp
    change |-c/(y^2*S)-(1+c/y)*deriv (atkinsonRootMorseCurvature T b) y/(2*S^3)| ≤ _
    rw [he]
    have h := (abs_sub _ _).trans (add_le_add hA hB)
    rw [show 512/Real.sqrt T = 512*R by dsimp [R]; ring]
    linarith
  · rw [atkinsonRootMorseCoordinate_third hT b hy0]
    have he1 : 2*c/(y^3*S) = 2*(c/y)*(1/y)^2/S := by field_simp
    have he2 : c*deriv (atkinsonRootMorseCurvature T b) y/(y^2*S^3) =
        (c/y)*(1/y)*deriv (atkinsonRootMorseCurvature T b) y/S^3 := by field_simp
    change |2*c/(y^3*S)+c*deriv (atkinsonRootMorseCurvature T b) y/(y^2*S^3)-
      (1+c/y)*iteratedDeriv 2 (atkinsonRootMorseCurvature T b) y/(2*S^3)+
      3*(1+c/y)*(deriv (atkinsonRootMorseCurvature T b) y)^2/(4*S^5)| ≤ _
    rw [he1,he2]
    apply (abs_add_le _ _).trans
    apply (add_le_add ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl).trans
    apply (add_le_add (add_le_add (add_le_add hC hD) hE) hF).trans
    rw [show 65536/T = 65536*R^2 by rw [hR2]; ring]
    nlinarith [sq_nonneg R]

theorem atkinsonRootMorseInverse_second {T : ℝ} (hT : 0 < T) (b z : ℝ) :
    iteratedDeriv 2 (atkinsonRootMorseInverse T b) z =
      -iteratedDeriv 2 (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b z)/
        (deriv (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b z))^3 := by
  have hz : z ∈ atkinsonRootMorseRange T b := by rw [atkinsonRootMorseRange_eq_univ hT b]; trivial
  have hy := atkinsonRootMorseInverse_pos hT b hz
  have hi := (atkinsonRootMorseInverse_hasStrictDerivAt hT b hz).hasDerivAt
  have hc := atkinsonRootMorseCoordinate_contDiffAt hT b hy
  have hq := ((contDiffAt_iteratedDeriv_infty hc 1).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt
  have hq' : HasDerivAt (deriv (atkinsonRootMorseCoordinate T b))
      (iteratedDeriv 2 (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b z))
        (atkinsonRootMorseInverse T b z) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hq
  have hp := atkinsonRootMorseCoordinate_deriv_pos hT b hy
  have hd := (hq'.comp z hi).inv hp.ne'
  have he : deriv (atkinsonRootMorseInverse T b) =ᶠ[𝓝 z]
      fun x => (deriv (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b x))⁻¹ := by
    filter_upwards [] with x
    exact (atkinsonRootMorseInverse_hasStrictDerivAt hT b
      (by rw [atkinsonRootMorseRange_eq_univ hT b]; trivial)).hasDerivAt.deriv
  rw [iteratedDeriv_succ,iteratedDeriv_one,he.deriv_eq]
  convert hd.deriv using 1
  dsimp only [Function.comp_apply]
  field_simp

theorem atkinsonRootMorseInverse_third {T : ℝ} (hT : 0 < T) (b z : ℝ) :
    iteratedDeriv 3 (atkinsonRootMorseInverse T b) z =
      3*(iteratedDeriv 2 (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b z))^2/
        (deriv (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b z))^5-
      iteratedDeriv 3 (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b z)/
        (deriv (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b z))^4 := by
  have hz : z ∈ atkinsonRootMorseRange T b := by rw [atkinsonRootMorseRange_eq_univ hT b]; trivial
  have hy := atkinsonRootMorseInverse_pos hT b hz
  have hi := (atkinsonRootMorseInverse_hasStrictDerivAt hT b hz).hasDerivAt
  have hc := atkinsonRootMorseCoordinate_contDiffAt hT b hy
  have hq1 : HasDerivAt (deriv (atkinsonRootMorseCoordinate T b))
      (iteratedDeriv 2 (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b z))
        (atkinsonRootMorseInverse T b z) := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      ((contDiffAt_iteratedDeriv_infty hc 1).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt
  have hq2 : HasDerivAt (iteratedDeriv 2 (atkinsonRootMorseCoordinate T b))
      (iteratedDeriv 3 (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b z))
        (atkinsonRootMorseInverse T b z) := by
    simpa only [iteratedDeriv_succ] using
      ((contDiffAt_iteratedDeriv_infty hc 2).differentiableAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt
  have hp := atkinsonRootMorseCoordinate_deriv_pos hT b hy
  have hd := ((hq2.comp z hi).neg).fun_div ((hq1.comp z hi).pow 3)
    (by change (deriv (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b z))^3 ≠ 0; positivity)
  have he : iteratedDeriv 2 (atkinsonRootMorseInverse T b) =ᶠ[𝓝 z]
      fun x => -iteratedDeriv 2 (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b x)/
        (deriv (atkinsonRootMorseCoordinate T b) (atkinsonRootMorseInverse T b x))^3 := by
    filter_upwards [] with x
    exact atkinsonRootMorseInverse_second hT b x
  rw [iteratedDeriv_succ,he.deriv_eq]
  convert hd.deriv using 1
  dsimp only [Function.comp_apply,Pi.neg_apply,Pi.pow_apply]
  norm_num only [Nat.cast_ofNat,Nat.reduceSub]
  field_simp
  ring

theorem atkinsonRootMorseInverse_physical_jet_bounds {T b z : ℝ} (hT : 0 < T)
    (hb : |b| ≤ Real.sqrt T/100)
    (hy : Real.sqrt T/4 ≤ atkinsonRootMorseInverse T b z) :
    |deriv (atkinsonRootMorseInverse T b) z| ≤ 2 ∧
      |iteratedDeriv 2 (atkinsonRootMorseInverse T b) z| ≤ 4096/Real.sqrt T ∧
      |iteratedDeriv 3 (atkinsonRootMorseInverse T b) z| ≤ 33554432/T := by
  have hz : z ∈ atkinsonRootMorseRange T b := by rw [atkinsonRootMorseRange_eq_univ hT b]; trivial
  obtain ⟨h1,_⟩ := atkinsonRootMorseCoordinate_physical_deriv_bounds hT hb hy
  obtain ⟨h2,h3⟩ := atkinsonRootMorseCoordinate_physical_jet_bounds hT hb hy
  have hp := atkinsonRootMorseCoordinate_deriv_pos hT b (atkinsonRootMorseInverse_pos hT b hz)
  refine ⟨?_,?_,?_⟩
  · rw [(atkinsonRootMorseInverse_hasStrictDerivAt hT b hz).hasDerivAt.deriv,
      abs_of_pos (inv_pos.2 hp)]
    calc
      _ ≤ (1/2:ℝ)⁻¹ := inv_anti₀ (by norm_num) h1
      _ = 2 := by norm_num
  · rw [atkinsonRootMorseInverse_second hT b z,abs_div,abs_neg,
      abs_of_pos (pow_pos hp 3)]
    calc
      _ ≤ (512/Real.sqrt T)/(1/2)^3 := by gcongr
      _ = _ := by ring
  · rw [atkinsonRootMorseInverse_third hT b z]
    apply (abs_sub _ _).trans
    rw [abs_div,abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3),
      abs_pow,abs_of_pos (pow_pos hp 5),abs_of_pos (pow_pos hp 4)]
    calc
      _ ≤ 3*(512/Real.sqrt T)^2/(1/2)^5+(65536/T)/(1/2)^4 := by gcongr
      _ ≤ _ := by
        rw [div_pow,Real.sq_sqrt hT.le]
        field_simp
        norm_num

theorem exists_atkinsonMorseWeight_physical_second_bound (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ,
      0 < T → 1 ≤ G → G^2 ≤ 2*T → 1 ≤ L → 8*L ≤ G →
      |b| ≤ Real.sqrt T/100 → ∀ z : ℝ,
      atkinsonRootMorseInverse T b z ∈ Icc (Real.sqrt T/4) (Real.sqrt T) →
      ‖atkinsonMorseWeight T G L α b z‖ ≤ C*G*T^(-α) ∧
      ‖iteratedDeriv 2 (atkinsonMorseWeight T G L α b) z‖ ≤ C*G^3*T^(-α)/T := by
  obtain ⟨A,hA,hbound⟩ := exists_intervalC2Bound_atkinsonPowerWeight_root_natural α
  refine ⟨33580000*A,by positivity,?_⟩
  intro T G L b hT hG hGT hL hwidth hb z hz
  let f := fun y : ℝ => atkinsonPowerWeight T G L α (y^2)
  let g := atkinsonRootMorseInverse T b
  let J := fun x : ℝ => ((deriv g x : ℝ):ℂ)
  let M := A*G*T^(-α)
  let R := G/Real.sqrt T
  have hM : 0 < M := by dsimp [M]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hf : IntervalC2Bound f (Real.sqrt T/4) (Real.sqrt T) M R := hbound T G L hT hG hGT hL hwidth
  have hg : ContDiff ℝ ∞ g := contDiff_atkinsonRootMorseInverse hT b
  have hg2 : ContDiffAt ℝ 2 g z := hg.contDiffAt.of_le
    (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top 2)))
  have hgd : ContDiffAt ℝ 2 (deriv g) z := by
    simpa only [iteratedDeriv_one] using
      (contDiffAt_iteratedDeriv_infty (hg.contDiffAt (x := z)) 1).of_le
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top 2)))
  have hJ : ContDiffAt ℝ 2 J z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hgd
  have hfg : ContDiffAt ℝ 2 (fun x => f (g x)) z :=
    ContDiffAt.comp z (g := f) (hf.smooth (g z) hz) hg2
  obtain ⟨hg1,hg2b,hg3⟩ := atkinsonRootMorseInverse_physical_jet_bounds hT hb hz.1
  have hs := Real.sqrt_pos.2 hT
  have hbase : 1/Real.sqrt T ≤ R := by dsimp [R]; gcongr
  have hg2R : |iteratedDeriv 2 g z| ≤ 4096*R := by
    apply hg2b.trans
    calc
      4096/Real.sqrt T = 4096*(1/Real.sqrt T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by norm_num)
  have hg3R : |iteratedDeriv 3 g z| ≤ 33554432*R^2 := by
    apply hg3.trans
    have he : 1/T = (1/Real.sqrt T)^2 := by rw [div_pow,one_pow,Real.sq_sqrt hT.le]
    rw [div_eq_mul_inv,← one_div,he]
    gcongr
  have hJ0 : ‖J z‖ ≤ 2 := by simpa only [J,Complex.norm_real,Real.norm_eq_abs] using hg1
  have hJ1 : ‖deriv J z‖ ≤ 4096*R := by
    have he := iteratedDeriv_ofReal_fun (hgd.of_le (by norm_num : (1:WithTop ℕ∞) ≤ 2))
    simp only [iteratedDeriv_one] at he
    change ‖deriv (fun x => ((deriv g x : ℝ):ℂ)) z‖ ≤ _
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hg2R
  have hJ2 : ‖iteratedDeriv 2 J z‖ ≤ 33554432*R^2 := by
    have he := iteratedDeriv_ofReal_fun hgd
    change ‖iteratedDeriv 2 (fun x => ((deriv g x : ℝ):ℂ)) z‖ ≤ _
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    simpa only [iteratedDeriv_succ'] using hg3R
  have hf0 : ‖f (g z)‖ ≤ M := hf.norm_le _ hz
  have hf1 : ‖deriv (fun x => f (g x)) z‖ ≤ 2*M*R := by
    have hd := ((hf.smooth (g z) hz).differentiableAt (by norm_num)).hasDerivAt.scomp z
      (hg2.differentiableAt (by norm_num)).hasDerivAt
    change ‖deriv (f ∘ g) z‖ ≤ _
    rw [hd.deriv,norm_smul,Real.norm_eq_abs]
    apply (mul_le_mul hg1 (hf.deriv_le _ hz) (norm_nonneg _) (by norm_num)).trans_eq
    ring
  have hf2 : ‖iteratedDeriv 2 (fun x => f (g x)) z‖ ≤ 4100*M*R^2 := by
    rw [iteratedDeriv_two_comp_real (hf.smooth (g z) hz) hg2]
    apply (norm_add_le _ _).trans
    simp only [norm_smul,Real.norm_eq_abs,abs_pow]
    calc
      _ ≤ 2^2*(M*R^2)+(4096*R)*(M*R) := by
        apply add_le_add
        · exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hg1 2) (hf.second_le _ hz)
            (norm_nonneg _) (by norm_num)
        · exact mul_le_mul hg2R (hf.deriv_le _ hz) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hW0 : ‖atkinsonMorseWeight T G L α b z‖ ≤ 2*M := by
    change ‖J z*f (g z)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul hJ0 hf0 (norm_nonneg _) (by norm_num)
  have hW2 : ‖iteratedDeriv 2 (atkinsonMorseWeight T G L α b) z‖ ≤ 33580000*M*R^2 := by
    change ‖iteratedDeriv 2 (fun x => J x*f (g x)) z‖ ≤ _
    rw [iteratedDeriv_two_mul hJ hfg]
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_add_le _ _) le_rfl).trans
    simp only [norm_mul,Complex.norm_ofNat]
    calc
      _ ≤ 2*(4100*M*R^2)+2*(4096*R)*(2*M*R)+(33554432*R^2)*M := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul hJ0 hf2 (norm_nonneg _) (by norm_num)
          · exact mul_le_mul (mul_le_mul_of_nonneg_left hJ1 (by norm_num)) hf1
              (norm_nonneg _) (by positivity)
        · exact mul_le_mul hJ2 hf0 (norm_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hM.le (sq_nonneg R)]
  constructor
  · apply hW0.trans
    change 2*M ≤ 33580000*A*G*T^(-α)
    nlinarith [hM]
  · apply hW2.trans_eq
    dsimp [M,R]
    rw [div_pow,Real.sq_sqrt hT.le]
    ring

theorem support_atkinsonMorseWeight_physical {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G) (α b : ℝ) :
    Function.support (atkinsonMorseWeight T G L α b) ⊆
      (atkinsonRootMorseInverse T b) ⁻¹' Icc (Real.sqrt T/4) (Real.sqrt T) := by
  intro z hz
  have hc : zetaDivisorBandCutoff T G L ((atkinsonRootMorseInverse T b z)^2) ≠ 0 := by
    intro he
    exact hz (by simp [atkinsonMorseWeight,atkinsonPowerWeight,he])
  have hp := atkinsonRootMorseInverse_pos hT b
    (show z ∈ atkinsonRootMorseRange T b by rw [atkinsonRootMorseRange_eq_univ hT b]; trivial)
  have hsq := support_zetaDivisorBandCutoff_physical hT hG hL hwidth hc
  have hs := Real.sqrt_pos.2 hT
  change atkinsonRootMorseInverse T b z ∈ Icc (Real.sqrt T/4) (Real.sqrt T)
  constructor <;> nlinarith [hsq.1,hsq.2,Real.sq_sqrt hT.le]

theorem support_iteratedDeriv_atkinsonMorseWeight_physical {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G) (α b : ℝ) (k : ℕ) :
    Function.support (iteratedDeriv k (atkinsonMorseWeight T G L α b)) ⊆
      (atkinsonRootMorseInverse T b) ⁻¹' Icc (Real.sqrt T/4) (Real.sqrt T) := by
  have hs : tsupport (iteratedDeriv k (atkinsonMorseWeight T G L α b)) ⊆
      tsupport (atkinsonMorseWeight T G L α b) := by
    induction k with
    | zero => simp
    | succ k ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih
  exact (subset_tsupport _).trans (hs.trans
    (closure_minimal (support_atkinsonMorseWeight_physical hT hG hL hwidth α b)
      (isClosed_Icc.preimage (contDiff_atkinsonRootMorseInverse hT b).continuous)))

theorem exists_atkinsonMorseWeight_global_second_bound (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ,
      0 < T → 1 ≤ G → G^2 ≤ 2*T → 1 ≤ L → 8*L ≤ G →
      |b| ≤ Real.sqrt T/100 → ∀ z : ℝ,
      ‖atkinsonMorseWeight T G L α b z‖ ≤ C*G*T^(-α) ∧
      ‖iteratedDeriv 2 (atkinsonMorseWeight T G L α b) z‖ ≤ C*G^3*T^(-α)/T := by
  obtain ⟨C,hC,hbound⟩ := exists_atkinsonMorseWeight_physical_second_bound α
  refine ⟨C,hC,?_⟩
  intro T G L b hT hG hGT hL hwidth hb z
  have hG0 : 0 < G := by linarith
  have hL0 : 0 < L := by linarith
  constructor
  · by_cases hz : atkinsonMorseWeight T G L α b z = 0
    · rw [hz,norm_zero]; positivity
    · exact (hbound T G L b hT hG hGT hL hwidth hb z
        (support_atkinsonMorseWeight_physical hT hG0 hL0 hwidth α b hz)).1
  · by_cases hz : iteratedDeriv 2 (atkinsonMorseWeight T G L α b) z = 0
    · rw [hz,norm_zero]; positivity
    · exact (hbound T G L b hT hG hGT hL hwidth hb z
        (support_iteratedDeriv_atkinsonMorseWeight_physical hT hG0 hL0 hwidth α b 2 hz)).2

theorem abs_atkinsonSaddleRoot_sub_sqrt_le {A : ℝ} (hA : 0 < A) (b : ℝ) :
    |atkinsonSaddleRoot A b-Real.sqrt A| ≤ |b| := by
  have hr := atkinsonSaddleRoot_pos hA b
  have hs := Real.sqrt_pos.2 hA
  have he := atkinsonSaddleRoot_equation hA b
  have hp : (atkinsonSaddleRoot A b-Real.sqrt A)*(atkinsonSaddleRoot A b+Real.sqrt A) =
      b*atkinsonSaddleRoot A b := by nlinarith [Real.sq_sqrt hA.le]
  have ha := congrArg abs hp
  rw [abs_mul,abs_of_pos (add_pos hr hs),abs_mul,abs_of_pos hr] at ha
  have hle : |atkinsonSaddleRoot A b-Real.sqrt A| * atkinsonSaddleRoot A b ≤
      |b| * atkinsonSaddleRoot A b := by
    nlinarith [mul_nonneg (abs_nonneg (atkinsonSaddleRoot A b-Real.sqrt A)) hs.le]
  nlinarith only [hle,hr]

theorem atkinsonRootBand_distance_from_center {T G L y : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G)
    (hy : y ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L)) :
    |y-Real.sqrt (T/(2*Real.pi))| ≤ 2*Real.sqrt T*(L/G) := by
  have hu0 : 0 ≤ L/G := by positivity
  have hu1 : L/G ≤ 1 := (div_le_iff₀ hG).2 (by linarith)
  have he := exp_sub_one_le_two_mul hu0 hu1
  have hl := Real.add_one_le_exp (-(L/G))
  have hA : T/(2*Real.pi) ≤ T := by
    apply (div_le_iff₀ (by positivity : 0 < 2*Real.pi)).2
    nlinarith [Real.pi_gt_three]
  have hS := Real.sqrt_le_sqrt hA
  have hlo := hy.1
  have hhi := hy.2
  rw [atkinsonRootBandLower,sqrt_zetaDivisorBandEdge hT,
    show -2*L/G/2 = -(L/G) by ring] at hlo
  rw [atkinsonRootBandUpper,sqrt_zetaDivisorBandEdge hT,
    show 2*L/G/2 = L/G by ring] at hhi
  have hmul1 := mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg (T/(2*Real.pi)))
  have hmul2 := mul_le_mul_of_nonneg_left hl (Real.sqrt_nonneg (T/(2*Real.pi)))
  have hmul3 := mul_le_mul_of_nonneg_right hS hu0
  apply abs_le.mpr
  constructor <;> nlinarith

theorem support_atkinsonMorseWeight_window {T G L b : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G)
    (hb : |b| ≤ Real.sqrt T/100) (hfrequency : |b| ≤ 7*Real.sqrt T*(L/G)) (α : ℝ) :
    Function.support (atkinsonMorseWeight T G L α b) ⊆
      Ioo (-(20*Real.sqrt T*(L/G))) (20*Real.sqrt T*(L/G)) := by
  intro z hz
  let y := atkinsonRootMorseInverse T b z
  let r := atkinsonSaddleRoot (T/(2*Real.pi)) b
  have hyrange : z ∈ atkinsonRootMorseRange T b := by rw [atkinsonRootMorseRange_eq_univ hT b]; trivial
  have hy0 : 0 < y := atkinsonRootMorseInverse_pos hT b hyrange
  have hphysical := support_atkinsonMorseWeight_physical hT hG hL hwidth α b hz
  have hc : zetaDivisorBandCutoff T G L (y^2) ≠ 0 := by
    intro he
    dsimp only [y] at he
    exact hz (by simp [atkinsonMorseWeight,atkinsonPowerWeight,he])
  have hband := support_zetaDivisorBandCutoff hT hG hL hc
  have hyband : y ∈ Icc (atkinsonRootBandLower T G L) (atkinsonRootBandUpper T G L) := by
    have hl := Real.sqrt_le_sqrt hband.1
    have hu := Real.sqrt_le_sqrt hband.2
    rw [Real.sqrt_sq hy0.le] at hl hu
    exact ⟨hl,hu⟩
  have hyc := atkinsonRootBand_distance_from_center hT hG hL hwidth hyband
  have hrc := abs_atkinsonSaddleRoot_sub_sqrt_le (by positivity : 0 < T/(2*Real.pi)) b
  have hyr : |y-r| ≤ 9*Real.sqrt T*(L/G) := by
    have h := abs_sub_le y (Real.sqrt (T/(2*Real.pi))) r
    rw [abs_sub_comm (Real.sqrt (T/(2*Real.pi))) r] at h
    dsimp [r]
    dsimp [r] at h
    linarith
  obtain ⟨hK,hK4⟩ := atkinsonRootMorseCurvature_physical_bounds hT hb hphysical.1
  have hS : Real.sqrt (atkinsonRootMorseCurvature T b y) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ atkinsonRootMorseCurvature T b y),
      Real.sqrt_nonneg (atkinsonRootMorseCurvature T b y)]
  have hzbound : |z| ≤ 18*Real.sqrt T*(L/G) := by
    rw [← atkinsonRootMorseCoordinate_inverse hyrange,atkinsonRootMorseCoordinate,
      abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (mul_le_mul hyr hS (Real.sqrt_nonneg _) (by positivity)).trans_eq
    ring
  have hgap : 18*Real.sqrt T*(L/G) < 20*Real.sqrt T*(L/G) := by
    nlinarith [show 0 < Real.sqrt T*(L/G) by positivity]
  exact abs_lt.mp (hzbound.trans_lt hgap)

theorem atkinsonMorseIntegral_eq_window {T G L b : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8*L ≤ G)
    (hb : |b| ≤ Real.sqrt T/100) (hfrequency : |b| ≤ 7*Real.sqrt T*(L/G)) (α : ℝ) :
    (∫ z in atkinsonRootMorseRange T b,
      atkinsonMorseWeight T G L α b z*betaQuadraticKernel 2 z) =
    ∫ z in (-(20*Real.sqrt T*(L/G)))..(20*Real.sqrt T*(L/G)),
      atkinsonMorseWeight T G L α b z*betaQuadraticKernel 2 z := by
  rw [atkinsonRootMorseRange_eq_univ hT b,Measure.restrict_univ]
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro z hz
  have hw : atkinsonMorseWeight T G L α b z ≠ 0 := by
    intro he
    exact hz (by simp [he])
  exact Ioo_subset_Ioc_self (support_atkinsonMorseWeight_window hT hG hL hwidth hb hfrequency α hw)

theorem fresnelGaussianValue_one_eq_beta_main :
    fresnelGaussianValue 1 = (𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt 2 : ℂ) := by
  rw [fresnelGaussianValue_eq_phase (by norm_num : (0:ℝ) < 1)]
  norm_num only [mul_one]
  congr 1
  simp only [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem exists_atkinsonPowerIntegral_morse_error (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L b : ℝ,
      0 < T → 1 ≤ G → G^2 ≤ 2*T → 1 ≤ L → 8*L ≤ G →
      |b| ≤ Real.sqrt T/100 → |b| ≤ 7*Real.sqrt T*(L/G) →
      ‖atkinsonPowerIntegral T G L α b-atkinsonStationaryMain T G L α b‖ ≤
        C*G^2*T^(-α)*L/Real.sqrt T := by
  obtain ⟨A,hA,hbound⟩ := exists_atkinsonMorseWeight_global_second_bound α
  refine ⟨128*A,by positivity,?_⟩
  intro T G L b hT hG hGT hL hwidth hb hfrequency
  have hG0 : 0 < G := by linarith
  have hL0 : 0 < L := by linarith
  have hs := Real.sqrt_pos.2 hT
  let H := 20*Real.sqrt T*(L/G)
  let M₀ := A*G*T^(-α)
  let M₂ := A*G^3*T^(-α)/T
  let X := A*G^2*T^(-α)*L/Real.sqrt T
  have hH : 0 < H := by dsimp [H]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have he := norm_complex_quadratic_window_remainder_le_secondDeriv
    (contDiff_atkinsonMorseWeight hT hG0.ne' L α b) (by norm_num : (0:ℝ) < 2) hH
    (hbound T G L b hT hG hGT hL hwidth hb 0).1
    (fun z _ => (hbound T G L b hT hG hGT hL hwidth hb z).2)
  rw [norm_atkinsonPowerIntegral_sub_stationary_eq_morseRemainder hT,
    atkinsonMorseIntegral_eq_window hT hG0 hL0 hwidth hb hfrequency,
    fresnelGaussianValue_one_eq_beta_main]
  apply (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 2)).trans
  have hfirst : M₀/H ≤ X := by
    have heq : M₀/H = X/(20*L^2) := by dsimp [M₀,H,X]; field_simp
    rw [heq]
    exact div_le_self hX.le (by nlinarith)
  have hsecond : H*M₂ = 20*X := by
    dsimp [H,M₂,X]
    field_simp
    nlinarith [Real.sq_sqrt hT.le]
  change 2*(2*(4*M₀/H+3*H*M₂)/(Real.pi*2)) ≤ 128*A*G^2*T^(-α)*L/Real.sqrt T
  have heq : 2*(2*(4*M₀/H+3*H*M₂)/(Real.pi*2)) =
      (8*(M₀/H)+6*(H*M₂))/Real.pi := by ring
  rw [heq,hsecond]
  have hnum : 8*(M₀/H)+6*(20*X) ≤ 128*X := by linarith
  apply (div_le_div_of_nonneg_right hnum Real.pi_pos.le).trans
  have hp : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  apply (div_le_self (by positivity : 0 ≤ 128*X) hp).trans_eq
  dsimp [X]
  ring

theorem atkinsonSourceCutoff_frequency_natural {T G L : ℝ}
    (hT : 1 ≤ T) (hG : 0 < G) (hupper : G ≤ Real.sqrt T) (hL : 1 ≤ L)
    {n : ℕ} (hn : n < atkinsonSourceCutoff T G L) :
    |Real.sqrt (n:ℝ)| ≤ 7*Real.sqrt T*(L/G) := by
  have hT0 : 0 < T := by linarith
  have hnR : (n:ℝ) ≤ atkinsonSourceCutoff T G L := by exact_mod_cast hn.le
  have hN := atkinsonSourceCutoff_le_natural hT hG hupper hL
  have hsq : (Real.sqrt (n:ℝ))^2 ≤ (7*Real.sqrt T*(L/G))^2 := by
    rw [Real.sq_sqrt (Nat.cast_nonneg n),mul_pow,mul_pow,Real.sq_sqrt hT0.le,div_pow]
    have hterm : 0 ≤ T*L^2/G^2 := by positivity
    have he : (7:ℝ)^2*T*(L^2/G^2) = 37*T*L^2/G^2+12*(T*L^2/G^2) := by ring
    rw [he]
    linarith
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith [Real.sqrt_nonneg (n:ℝ),show 0 < 7*Real.sqrt T*(L/G) by positivity]

theorem exists_atkinsonPowerIntegral_morse_pair (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ,
      40000 ≤ T → 1 ≤ G → G ≤ Real.sqrt T → 1 ≤ L → 1200*L ≤ G →
      ∀ n : ℕ, n < atkinsonSourceCutoff T G L →
      ‖atkinsonPowerIntegral T G L α (Real.sqrt n)-atkinsonStationaryMain T G L α (Real.sqrt n)‖ ≤
        C*G^2*T^(-α)*L/Real.sqrt T ∧
      ‖atkinsonPowerIntegral T G L α (-Real.sqrt n)-atkinsonStationaryMain T G L α (-Real.sqrt n)‖ ≤
        C*G^2*T^(-α)*L/Real.sqrt T := by
  obtain ⟨C,hC,hbound⟩ := exists_atkinsonPowerIntegral_morse_error α
  refine ⟨C,hC,?_⟩
  intro T G L hT hG hupper hL hwidth n hn
  have hT0 : 0 < T := by linarith
  have hG0 : 0 < G := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hGT : G^2 ≤ 2*T := by nlinarith [Real.sq_sqrt hT0.le]
  have hwidth8 : 8*L ≤ G := by linarith
  have hcut := atkinsonSourceCutoff_le_small hT hG0 hL0 hwidth
  have hnR : (n:ℝ) ≤ atkinsonSourceCutoff T G L := by exact_mod_cast hn.le
  have hnsmall : 10000*(n:ℝ) ≤ T := by linarith
  have hsmall : |Real.sqrt (n:ℝ)| ≤ Real.sqrt T/100 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n),Real.sq_sqrt hT0.le,
      Real.sqrt_nonneg (n:ℝ),Real.sqrt_nonneg T]
  have hnatural := atkinsonSourceCutoff_frequency_natural (by linarith : 1 ≤ T) hG0 hupper hL hn
  refine ⟨hbound T G L (Real.sqrt n) hT0 hG hGT hL hwidth8 hsmall hnatural,?_⟩
  exact hbound T G L (-Real.sqrt n) hT0 hG hGT hL hwidth8
    (by simpa only [abs_neg] using hsmall) (by simpa only [abs_neg] using hnatural)

theorem exists_norm_atkinsonLeadingTerm_sub_stationary_morse_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 40000 ≤ T →
      1 ≤ G → G ≤ Real.sqrt T → 1 ≤ L → 1200*L ≤ G →
      ∀ n : ℕ, n < atkinsonSourceCutoff T G L →
      ‖atkinsonLeadingTerm T G L n-atkinsonStationaryLeadingTerm T G L n‖ ≤
        C*G^2*T^(-(3/4 : ℝ))*L*‖divisorDirichletTerm (1/4) n‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_atkinsonPowerIntegral_morse_pair (1/4)
  let q : ℝ := Real.sqrt Real.pi/Real.pi
  let D : ℝ := 1+‖neumannLeadingPlus‖+‖neumannLeadingMinus‖
  have hq : 0 < q := by dsimp [q]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨2*Real.pi*q*(4*Real.pi)^(-(1/2 : ℝ))*D*C,by positivity,?_⟩
  intro T G L hT hlower hupper hL hwidth n hn
  have hT0 : 0 < T := by linarith
  have hG : 0 < G := by linarith
  obtain ⟨hp,hm⟩ := hbound T G L hT hlower hupper hL hwidth n hn
  have hscale : C*G^2*T^(-(1/4:ℝ))*L/Real.sqrt T = C*G^2*T^(-(3/4:ℝ))*L := by
    have ht : T^(-(1/4:ℝ))/Real.sqrt T = T^(-(3/4:ℝ)) := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_sub hT0]
      norm_num
    calc
      _ = C*G^2*(T^(-(1/4:ℝ))/Real.sqrt T)*L := by ring
      _ = _ := by rw [ht]
  rw [hscale] at hp hm
  let E : ℝ := C*G^2*T^(-(3/4 : ℝ))*L
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpair : ‖neumannLeadingPlus*(atkinsonPowerIntegral T G L (1/4) (Real.sqrt n)-
      atkinsonStationaryMain T G L (1/4) (Real.sqrt n)) +
    neumannLeadingMinus*(atkinsonPowerIntegral T G L (1/4) (-Real.sqrt n)-
      atkinsonStationaryMain T G L (1/4) (-Real.sqrt n))‖ ≤ D*E := by
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul]
    apply (add_le_add (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hm (norm_nonneg _))).trans
    change ‖neumannLeadingPlus‖*E+‖neumannLeadingMinus‖*E ≤ D*E
    dsimp [D]
    nlinarith
  have he : atkinsonLeadingTerm T G L n-atkinsonStationaryLeadingTerm T G L n =
      divisorWeight n * (-(2*Real.pi) : ℂ) * (Real.sqrt Real.pi/Real.pi : ℂ) *
        (atkinsonBesselScale (1/4) n : ℂ) *
          (neumannLeadingPlus*(atkinsonPowerIntegral T G L (1/4) (Real.sqrt n)-
            atkinsonStationaryMain T G L (1/4) (Real.sqrt n)) +
          neumannLeadingMinus*(atkinsonPowerIntegral T G L (1/4) (-Real.sqrt n)-
            atkinsonStationaryMain T G L (1/4) (-Real.sqrt n))) := by
    unfold atkinsonLeadingTerm atkinsonLeadingIntegral atkinsonStationaryLeadingTerm
      atkinsonStationaryLeadingIntegral
    ring
  have hpi : ‖(-(2*Real.pi) : ℂ)‖ = 2*Real.pi := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hqn : ‖(Real.sqrt Real.pi/Real.pi : ℂ)‖ = q := by
    simp [q,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hs : ‖(atkinsonBesselScale (1/4) n : ℂ)‖ = atkinsonBesselScale (1/4) n := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (atkinsonBesselScale_nonneg _ _)]
  have hd := norm_divisorDirichletTerm_real (1/4) n
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hd
  rw [he,norm_mul,norm_mul,norm_mul,norm_mul,hpi,hqn,hs,hd]
  apply (mul_le_mul_of_nonneg_left hpair (by
    exact mul_nonneg (by positivity) (atkinsonBesselScale_nonneg _ _))).trans_eq
  dsimp [E,atkinsonBesselScale]
  norm_num only [show (-2 : ℝ)*(1/4) = -(1/2) by norm_num]
  ring

theorem exists_norm_atkinsonLeadingFiniteSum_sub_stationary_mass_morse_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 40000 ≤ T →
      1 ≤ G → G ≤ Real.sqrt T → 1 ≤ L → 1200*L ≤ G →
      ∀ N : ℕ, N ≤ atkinsonSourceCutoff T G L →
      ‖atkinsonLeadingFiniteSum T G L N-atkinsonStationaryLeadingFiniteSum T G L N‖ ≤
        C*G^2*T^(-(3/4 : ℝ))*L*
          ∑ n ∈ Finset.range N, ‖divisorDirichletTerm (1/4) n‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_norm_atkinsonLeadingTerm_sub_stationary_morse_le
  refine ⟨C,hC,?_⟩
  intro T G L hT hlower hupper hL hwidth N hN
  unfold atkinsonLeadingFiniteSum atkinsonStationaryLeadingFiniteSum
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  apply hbound T G L hT hlower hupper hL hwidth n
  exact lt_of_lt_of_le (Finset.mem_range.mp hn) hN

theorem exists_norm_atkinsonLeadingFiniteSum_sub_stationary_morse_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 40000 ≤ T →
      1 ≤ G → G ≤ Real.sqrt T → 1 ≤ L → 1200*L ≤ G →
      ∀ N : ℕ, N ≤ atkinsonSourceCutoff T G L →
      ‖atkinsonLeadingFiniteSum T G L N-atkinsonStationaryLeadingFiniteSum T G L N‖ ≤
        C*G^2*T^(-(3/4 : ℝ))*L*(N:ℝ)^(3/4+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_norm_atkinsonLeadingFiniteSum_sub_stationary_mass_morse_le
  obtain ⟨D,hD,hprefix⟩ := exists_sum_norm_divisorDirichletTerm_quarter_le hε
  refine ⟨C*D,by positivity,?_⟩
  intro T G L hT hlower hupper hL hwidth N hN
  have hT0 : 0 < T := by linarith
  have hG : 0 < G := by linarith
  apply (hbound T G L hT hlower hupper hL hwidth N hN).trans
  apply (mul_le_mul_of_nonneg_left (hprefix N) (by positivity)).trans_eq
  ring

theorem atkinsonMorse_cutoff_scale_le {T G L q : ℝ}
    (hT : 1 ≤ T) (hG : 1 ≤ G) (hupper : G ≤ Real.sqrt T) (hL : 1 ≤ L)
    (hq : 3/4 ≤ q) (hq1 : q ≤ 1) :
    G^2*T^(-(3/4:ℝ))*L*(atkinsonSourceCutoff T G L : ℝ)^q ≤
      37*Real.sqrt G*T^(q-3/4)*L^3 := by
  have hT0 : 0 < T := by linarith
  have hG0 : 0 < G := by linarith
  have h := atkinsonStationary_cutoff_scale_le hT hG hupper hL hq hq1
  have he1 : T^(-(3/4:ℝ)) = T^(-(1/2:ℝ))*T^(-(1/4:ℝ)) := by
    rw [← Real.rpow_add hT0]
    norm_num
  have he2 : T^(q-1/2)*T^(-(1/4:ℝ)) = T^(q-3/4) := by
    rw [← Real.rpow_add hT0]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_right h
    (show 0 ≤ Real.sqrt G*T^(-(1/4:ℝ))*L by positivity)
  have hleft : G*Real.sqrt G*T^(-(1/2:ℝ))*(atkinsonSourceCutoff T G L : ℝ)^q*
      (Real.sqrt G*T^(-(1/4:ℝ))*L) =
      G^2*T^(-(3/4:ℝ))*L*(atkinsonSourceCutoff T G L : ℝ)^q := by
    rw [he1]
    have hs := Real.sq_sqrt hG0.le
    linear_combination G*T^(-(1/2:ℝ))*T^(-(1/4:ℝ))*L*
      (atkinsonSourceCutoff T G L : ℝ)^q*hs
  have hright : 37*T^(q-1/2)*L^2*(Real.sqrt G*T^(-(1/4:ℝ))*L) =
      37*Real.sqrt G*T^(q-3/4)*L^3 := by
    calc
      _ = 37*Real.sqrt G*(T^(q-1/2)*T^(-(1/4:ℝ)))*L^3 := by ring
      _ = _ := by rw [he2]
  rwa [hleft,hright] at hmul

theorem exists_atkinsonStationary_finite_full_width_error {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      ‖atkinsonLeadingFiniteSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T))-
        atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤ C*G := by
  let ε : ℝ := min (δ/4) (1/4)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεδ : ε ≤ δ/4 := min_le_left _ _
  have hεmax : ε ≤ 1/4 := min_le_right _ _
  obtain ⟨C,hC,hbound⟩ := exists_norm_atkinsonLeadingFiniteSum_sub_stationary_morse_le hε
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T^δ ≤ G → G ≤ T^(1/2-δ) →
      ‖atkinsonLeadingFiniteSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T))-
        atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤ (37*C)*G := by
    filter_upwards [eventually_zeta_source_log_window_scales hδ,
      eventually_const_log_pow_le_rpow 1200 (by norm_num) 1 hδ,
      eventually_const_log_pow_le_rpow 1 (by norm_num) 3 (by positivity : 0 < δ/4),
      eventually_ge_atTop (40000:ℝ)] with T hscale hwidth hlogs hT
    intro G hlower hupper
    have hT1 : 1 ≤ T := by linarith
    have hT0 : 0 < T := by linarith
    have hG1 : 1 ≤ G := (Real.one_le_rpow hT1 hδ.le).trans hlower
    have hG0 : 0 < G := by linarith
    have hGS : G ≤ Real.sqrt T := hupper.trans (by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hT1 (by linarith))
    have hL : 1 ≤ Real.log T := hscale.2.1
    have hL0 : 0 < Real.log T := by linarith
    have hw : 1200*Real.log T ≤ G := by simpa only [pow_one] using hwidth.trans hlower
    have hw8 : 8*Real.log T ≤ G := by linarith
    rw [atkinsonStationaryLeadingSum_eq_finite hT0 hG0 hL0 hw8]
    have hfinite := hbound T G (Real.log T) hT hG1 hGS hL hw
      (atkinsonSourceCutoff T G (Real.log T)) le_rfl
    have hcut := atkinsonMorse_cutoff_scale_le hT1 hG1 hGS hL
      (q := 3/4+ε) (by linarith) (by linarith)
    have hcut' := mul_le_mul_of_nonneg_left hcut hC.le
    norm_num only [show (3/4+ε-3/4:ℝ) = ε by ring] at hcut'
    have hcutnorm : C*G^2*T^(-(3/4:ℝ))*Real.log T*
        (atkinsonSourceCutoff T G (Real.log T):ℝ)^(3/4+ε) ≤
      37*C*Real.sqrt G*T^ε*(Real.log T)^3 := by convert hcut' using 1 <;> ring
    have hroot : T^(δ/2) ≤ Real.sqrt G := by
      have h := Real.sqrt_le_sqrt hlower
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul hT0.le] at h
      convert h using 1; congr 1; ring
    have hexp : T^(ε+δ/4) ≤ T^(δ/2) :=
      Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
    simp only [one_mul] at hlogs
    apply (hfinite.trans hcutnorm).trans
    calc
      _ ≤ 37*C*Real.sqrt G*T^ε*T^(δ/4) := by gcongr
      _ = 37*C*Real.sqrt G*T^(ε+δ/4) := by rw [mul_assoc,← Real.rpow_add hT0]
      _ ≤ 37*C*Real.sqrt G*Real.sqrt G := by gcongr; exact hexp.trans hroot
      _ = _ := by rw [mul_assoc,← pow_two,Real.sq_sqrt hG0.le]
  obtain ⟨B,hB⟩ := eventually_atTop.mp hev
  refine ⟨37*C,by positivity,max 40000 B,le_max_left _ _,?_⟩
  intro T G hT hlower hupper
  exact hB T ((le_max_right _ _).trans hT) G hlower hupper

theorem exists_atkinsonLeadingSum_sub_stationary_full_width {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      ‖atkinsonLeadingSum T G (Real.log T)-atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤ C*G := by
  obtain ⟨A,hA,B,hB,hfinite⟩ := exists_atkinsonStationary_finite_full_width_error hδ
  obtain ⟨D,hD,E,_,htail⟩ := exists_atkinsonLeading_source_band_bound hδ
  refine ⟨A+D,by positivity,max B E,hB.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper
  have hf := hfinite T G ((le_max_left _ _).trans hT) hlower hupper
  have ht := htail T G ((le_max_right _ _).trans hT) hlower hupper
    (atkinsonSourceCutoff T G (Real.log T)) (atkinsonSourceCutoff_lower _ _ _)
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add ht hf).trans ?_)
  linarith

theorem exists_zetaSquarePhysicalGaussian_stationary_full_width {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2)-
        2*(atkinsonStationaryLeadingSum T G (Real.log T)).re| ≤ C*G*Real.log T := by
  obtain ⟨C,hC,B,_,hsource⟩ := exists_zetaSquarePhysicalGaussian_atkinson_leading_approximation hδ
  obtain ⟨D,hD,E,hE,herror⟩ := exists_atkinsonLeadingSum_sub_stationary_full_width hδ
  refine ⟨C+2*D,by positivity,max B E,hE.trans (le_max_right _ _),?_⟩
  intro T G hT hlower hupper
  have hTlarge : 40000 ≤ T := hE.trans ((le_max_right _ _).trans hT)
  have hT0 : 0 < T := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hlog : 1 ≤ Real.log T := by
    apply (Real.le_log_iff_exp_le hT0).2
    have h := exp_sub_one_le_two_mul (by norm_num : (0:ℝ) ≤ 1) le_rfl
    linarith
  have hGlog : G ≤ G*Real.log T := le_mul_of_one_le_right hG.le hlog
  have hm := hsource T G ((le_max_left _ _).trans hT) hlower hupper
  have he := herror T G ((le_max_right _ _).trans hT) hlower hupper
  have hr := (Complex.abs_re_le_norm (atkinsonLeadingSum T G (Real.log T)-
    atkinsonStationaryLeadingSum T G (Real.log T))).trans he
  simp only [Complex.sub_re] at hr
  have hd := mul_le_mul_of_nonneg_left hGlog hD.le
  apply abs_le.mpr
  constructor <;> nlinarith [(abs_le.mp hm).1,(abs_le.mp hm).2,(abs_le.mp hr).1,(abs_le.mp hr).2]

theorem exists_zetaSquareLocalMean_le_stationary_full_width {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      (∫ t in T-G..T+G, zetaMomentCriticalNorm t^2) ≤
        2*Real.exp 1*(atkinsonStationaryLeadingSum T G (Real.log T)).re+C*G*Real.log T := by
  obtain ⟨C,hC,B,_,hsource⟩ := exists_zetaSquareLocalMean_le_atkinson_leading hδ
  obtain ⟨D,hD,E,hE,herror⟩ := exists_atkinsonLeadingSum_sub_stationary_full_width hδ
  refine ⟨C+2*Real.exp 1*D,by positivity,max B E,hE.trans (le_max_right _ _),?_⟩
  intro T G hT hlower hupper
  have hTlarge : 40000 ≤ T := hE.trans ((le_max_right _ _).trans hT)
  have hT0 : 0 < T := by linarith
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hlog : 1 ≤ Real.log T := by
    apply (Real.le_log_iff_exp_le hT0).2
    have h := exp_sub_one_le_two_mul (by norm_num : (0:ℝ) ≤ 1) le_rfl
    linarith
  have hGlog : G ≤ G*Real.log T := le_mul_of_one_le_right hG.le hlog
  have hm := hsource T G ((le_max_left _ _).trans hT) hlower hupper
  have he := herror T G ((le_max_right _ _).trans hT) hlower hupper
  have hr := (Complex.re_le_norm (atkinsonLeadingSum T G (Real.log T)-
    atkinsonStationaryLeadingSum T G (Real.log T))).trans he
  simp only [Complex.sub_re] at hr
  have hscaled := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2*Real.exp 1)
  have hGscaled := mul_le_mul_of_nonneg_left hGlog (by positivity : 0 ≤ 2*Real.exp 1*D)
  nlinarith

theorem exists_zetaSquarePhysicalGaussian_signedMain_full_width {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) →
      |(∫ t : ℝ, zetaGaussianWeight T G t*zetaMomentCriticalNorm t^2)-
        2*(atkinsonCommonMainPhase T*
          (atkinsonPositiveMainSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T))-
            atkinsonNegativeMainSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T)))).re| ≤
        C*G*Real.log T := by
  obtain ⟨C,hC,A,hA,hsource⟩ := exists_zetaSquarePhysicalGaussian_stationary_full_width hδ
  obtain ⟨B,hB⟩ := eventually_atTop.mp (eventually_zetaSmoothDivisorTest_support_physical hδ)
  refine ⟨C,hC,max A B,hA.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper
  have hAT : A ≤ T := (le_max_left _ _).trans hT
  have hBT : B ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith [hA.trans hAT]
  obtain ⟨hG,hL,hwidth,_⟩ := (hB T hBT).2 G hlower
  have h := hsource T G hAT hlower hupper
  rwa [atkinsonStationaryLeadingSum_eq_signed hT0 hG hL hwidth] at h

end TaoTrudgianYang2025

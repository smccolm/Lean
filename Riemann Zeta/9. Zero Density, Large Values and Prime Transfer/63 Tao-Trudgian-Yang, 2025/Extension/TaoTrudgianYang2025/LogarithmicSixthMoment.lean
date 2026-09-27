import TaoTrudgianYang2025.ParabolaBilinearLocalization
import TaoTrudgianYang2025.BetaSmoothCutoff
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! The normalized logarithmic sixth moment for actual integer frequencies.

The endpoint is `exists_logarithmic_sixth`: for every epsilon > 0, one constant
bounds the literal square/log sixth moment by C B^6 (T+N) N^(3+epsilon),
uniformly in N >= 1, T >= 0, finite source arrays and coefficient fibers.
Specific log-curve decoupling, native quadratic VMVT, physical weight and
grid transport, low frequencies and shell recombination are all proved.
No logarithmic moment or general curved decoupling theorem is assumed.

This closes the normalized moment input, not the later square/product count,
cubic eighth moment or generic Sargos D-process. -/

noncomputable section
open Set Filter MeasureTheory GafniTao
open scoped Topology ContDiff BigOperators FourierTransform ENNReal NNReal
namespace TaoTrudgianYang2025.LogarithmicSixth

def logQuadraticError (x : ℝ) : ℝ := Real.log (1+x)-x+x^2/2

private theorem analyticAt_dslope_zero {f : ℝ → ℝ} {x : ℝ}
    (hzero : AnalyticAt ℝ f 0) (hx : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (dslope f 0) x := by
  by_cases h : x=0
  · subst x
    obtain ⟨p,hp⟩ := hzero
    exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩
  · have hq : AnalyticAt ℝ (fun y => y⁻¹*(f y-f 0)) x :=
      (analyticAt_id.inv h).mul (hx.sub analyticAt_const)
    apply hq.congr
    filter_upwards [eventually_ne_nhds h] with y hy
    simp [dslope_of_ne _ hy,slope_def_field,div_eq_inv_mul]

theorem logQuadraticError_analytic {x : ℝ} (hx : -1<x) :
    AnalyticAt ℝ logQuadraticError x := by
  unfold logQuadraticError
  exact (((analyticAt_const.add analyticAt_id).log (by change 0<1+x; linarith)).sub
    analyticAt_id).add ((analyticAt_id.pow 2).div analyticAt_const (by norm_num))

theorem logQuadraticError_cubic_bound {x : ℝ} (hx : |x|≤1/2) :
    |logQuadraticError x|≤2*|x|^3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x)
    (by rw [abs_neg]; linarith) 2
  norm_num [Finset.sum_range_succ] at h
  have he : -x+x^2/2+Real.log (1+x)=logQuadraticError x := by
    unfold logQuadraticError
    ring
  rw [he] at h
  apply h.trans
  apply (div_le_iff₀ (by linarith : 0<1-|x|)).mpr
  nlinarith [pow_nonneg (abs_nonneg x) 3]

private theorem logQuadraticError_zero : logQuadraticError 0=0 := by
  simp [logQuadraticError]

private theorem logQuadraticError_deriv_zero : deriv logQuadraticError 0=0 := by
  have h := ((((hasDerivAt_id (0:ℝ)).const_add 1).log (by norm_num)).sub
    (hasDerivAt_id 0)).add (((hasDerivAt_id 0).pow 2).div_const 2)
  simpa [logQuadraticError] using h.deriv

private theorem logQuadraticError_second_slope_zero :
    dslope (dslope logQuadraticError 0) 0 0=0 := by
  rw [dslope_same]
  apply HasDerivAt.deriv
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto (fun x : ℝ => 2*|x|) (𝓝[≠] 0) (𝓝 0) := by
    simpa using ((continuous_const.mul continuous_abs :
      Continuous (fun x : ℝ => 2*|x|)).tendsto 0).mono_left nhdsWithin_le_nhds
  apply squeeze_zero_norm' _ hlim
  have hsmall : ∀ᶠ x : ℝ in 𝓝[≠] 0, |x|≤1/2 := by
    have h : ∀ᶠ x : ℝ in 𝓝 0, |x|<1/2 :=
      (continuous_abs.tendsto 0).eventually
        (Iio_mem_nhds (by norm_num : |(0:ℝ)|<1/2))
    exact (h.filter_mono nhdsWithin_le_nhds).mono fun _ hh => hh.le
  filter_upwards [hsmall,self_mem_nhdsWithin] with x hx hne
  have hxne : x≠0 := hne
  rw [slope_def_field,dslope_same,logQuadraticError_deriv_zero,
    dslope_of_ne _ hxne,slope_def_field,logQuadraticError_zero]
  simp only [sub_zero,Real.norm_eq_abs,abs_div]
  have hp : 0 < |x| := abs_pos.mpr hxne
  have hb := logQuadraticError_cubic_bound hx
  calc
    |logQuadraticError x|/|x|/|x| ≤ (2*|x|^3)/|x|/|x| := by gcongr
    _ = 2*|x| := by field_simp

def logCubicProfile : ℝ → ℝ :=
  dslope (dslope (dslope logQuadraticError 0) 0) 0

/-- Removable Taylor division is analytic also at the zero-scale endpoint. -/
theorem logCubicProfile_analytic {x : ℝ} (hx : -1<x) :
    AnalyticAt ℝ logCubicProfile x := by
  have h0 := logQuadraticError_analytic (x:=0) (by norm_num)
  have h1 := analyticAt_dslope_zero h0 h0
  have h2 := analyticAt_dslope_zero h1 h1
  exact analyticAt_dslope_zero h2
    (analyticAt_dslope_zero h1 (analyticAt_dslope_zero h0 (logQuadraticError_analytic hx)))

/-- An exact identity, including x=0; it is not a supplied remainder bound. -/
theorem logCubicProfile_identity (x : ℝ) :
    x^3*logCubicProfile x=Real.log (1+x)-x+x^2/2 := by
  have h1 := sub_smul_dslope logQuadraticError 0 x
  have h2 := sub_smul_dslope (dslope logQuadraticError 0) 0 x
  have h3 := sub_smul_dslope (dslope (dslope logQuadraticError 0) 0) 0 x
  simp only [sub_zero,smul_eq_mul,logQuadraticError_zero,dslope_same,
    logQuadraticError_deriv_zero] at h1 h2
  rw [logQuadraticError_second_slope_zero] at h3
  simp only [sub_zero,smul_eq_mul] at h3
  change x*logCubicProfile x=dslope (dslope logQuadraticError 0) 0 x at h3
  calc
    _ = x*(x*(x*logCubicProfile x)) := by ring
    _ = logQuadraticError x := by rw [h3,h2,h1]
    _ = _ := rfl

private def smoothLogCubicProfile (x : ℝ) : ℝ :=
  modelPhaseBufferedCutoff (-1) 1 (1/4) x*logCubicProfile x

private theorem smoothLogCubicProfile_smooth : ContDiff ℝ ∞ smoothLogCubicProfile := by
  apply smoothCutoff_mul_contDiff (modelPhaseBufferedCutoff_contDiff _ _ _)
  intro x hx
  have hs := modelPhaseBufferedCutoff_tsupport (by norm_num : (0:ℝ)<1/4) hx
  exact (logCubicProfile_analytic (by linarith [hs.1])).contDiffAt

private theorem smoothLogCubicProfile_agrees {x : ℝ} (hx : |x|≤1/2) :
    smoothLogCubicProfile x=logCubicProfile x := by
  unfold smoothLogCubicProfile
  rw [modelPhaseBufferedCutoff_one (by norm_num)
    (by linarith [(abs_le.mp hx).1]) (by linarith [(abs_le.mp hx).2]),one_mul]

private def logRemainderCutoff (p : ℝ × ℝ) (s : ℝ) : ℂ :=
  (modelPhaseBufferedCutoff (-2) 2 (1/2) s : ℂ)*
    fordAdditiveCharacter (p.1*s^3*smoothLogCubicProfile (p.2*s))

private theorem logRemainderCutoff_joint_smooth :
    ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => logRemainderCutoff q.1 q.2) := by
  have hcut : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ =>
      (modelPhaseBufferedCutoff (-2) 2 (1/2) q.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((modelPhaseBufferedCutoff_contDiff _ _ _).comp contDiff_snd)
  have hprofile : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ =>
      smoothLogCubicProfile (q.1.2*q.2)) :=
    smoothLogCubicProfile_smooth.comp ((contDiff_fst.snd).mul contDiff_snd)
  have hphase : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ =>
      q.1.1*q.2^3*smoothLogCubicProfile (q.1.2*q.2)) :=
    (((contDiff_fst.fst).mul (contDiff_snd.pow 3))).mul hprofile
  unfold logRemainderCutoff fordAdditiveCharacter
  exact hcut.mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hphase)).cexp)

private theorem logRemainderCutoff_smooth (p : ℝ × ℝ) :
    ContDiff ℝ ∞ (logRemainderCutoff p) := by
  have hm : ContDiff ℝ ∞ (fun s : ℝ => (p,s)) := contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def] using logRemainderCutoff_joint_smooth.comp hm

private theorem logRemainderCutoff_support (p : ℝ × ℝ) :
    tsupport (logRemainderCutoff p) ⊆ Icc (-2:ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  have hk : s∈tsupport (modelPhaseBufferedCutoff (-2) 2 (1/2)) := by
    apply subset_closure
    intro hz
    exact hs (by rw [logRemainderCutoff,hz,Complex.ofReal_zero,zero_mul])
  have hb := modelPhaseBufferedCutoff_tsupport (by norm_num : (0:ℝ)<1/2) hk
  constructor <;> linarith [hb.1,hb.2]

private theorem norm_slice_iteratedFDeriv
    (F : (ℝ × ℝ) × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (p : ℝ × ℝ) (s : ℝ) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun x => F (p,x)) s‖≤‖iteratedFDeriv ℝ j F (p,s)‖ := by
  let L : ℝ →L[ℝ] (ℝ × ℝ) × ℝ := ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ
  have hL : ‖L‖=1 := ContinuousLinearMap.norm_inr ℝ (ℝ × ℝ) ℝ
  have hf : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => F ((p,0)+q)) :=
    hF.comp (contDiff_const.add contDiff_id)
  have he : (fun x => F (p,x))=(fun q => F ((p,0)+q)) ∘ L := by
    ext x; simp [L]
  rw [he,L.iteratedFDeriv_comp_right hf s (i:=j)
    (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤)),iteratedFDeriv_comp_add_left]
  have hp : (p,0)+L s=(p,s) := by simp [L]
  rw [hp]
  have h := (iteratedFDeriv ℝ j F (p,s)).norm_compContinuousLinearMap_le
    (fun _ : Fin j => L)
  simpa only [hL,Finset.prod_const_one,mul_one] using h

/-- Compactness is applied to the actual jointly smooth log remainder.
The constant is chosen before both coefficients and before the cutoff variable. -/
theorem logRemainderCutoff_jet_bound (j : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∀ a∈Icc (-1:ℝ) 1, ∀ b∈Icc (-(1/4):ℝ) (1/4),
      ∀ s : ℝ, ‖iteratedDeriv j (logRemainderCutoff (a,b)) s‖≤C := by
  let F := fun q : (ℝ × ℝ) × ℝ => logRemainderCutoff q.1 q.2
  have hcont : Continuous (fun q => ‖iteratedFDeriv ℝ j F q‖) :=
    (logRemainderCutoff_joint_smooth.continuous_iteratedFDeriv
      (m:=j) (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))).norm
  obtain ⟨M,hM⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_bound_of_continuousOn
      (s:=(Icc (-1:ℝ) 1 ×ˢ Icc (-(1/4):ℝ) (1/4)) ×ˢ Icc (-2:ℝ) 2)
      hcont.continuousOn
  refine ⟨max M 1,le_max_right _ _,?_⟩
  intro a ha b hb s
  by_cases hs : s∈Icc (-2:ℝ) 2
  · have h := norm_slice_iteratedFDeriv F logRemainderCutoff_joint_smooth (a,b) s j
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
    exact h.trans (by simpa only [norm_norm] using
      (hM ((a,b),s) ⟨⟨ha,hb⟩,hs⟩).trans (le_max_left M 1))
  · have hz : iteratedFDeriv ℝ j (logRemainderCutoff (a,b)) s=0 := by
      apply Function.notMem_support.mp
      intro h
      exact hs (logRemainderCutoff_support (a,b)
        (tsupport_iteratedFDeriv_subset j (subset_closure h)))
    rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv,hz,norm_zero]
    exact zero_le_one.trans (le_max_right M 1)

theorem logRemainderCutoff_fourier_decay (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ a∈Icc (-1:ℝ) 1, ∀ b∈Icc (-(1/4):ℝ) (1/4),
      ∀ ξ : ℝ, (1+|ξ|)^j*‖𝓕 (logRemainderCutoff (a,b)) ξ‖≤C := by
  obtain ⟨C,hC,hzero⟩ := logRemainderCutoff_jet_bound 0
  obtain ⟨D,hD,hjet⟩ := logRemainderCutoff_jet_bound j
  refine ⟨(2:ℝ)^j*4*(C+D),by positivity,?_⟩
  intro a ha b hb ξ
  have h := RiemannZeta.GuthMaynard.one_add_abs_fourier_decay_of_support_of_bounds_order j
    (logRemainderCutoff_smooth (a,b)) (by norm_num : (-2:ℝ)≤2)
    ((subset_tsupport _).trans (logRemainderCutoff_support (a,b)))
    (by linarith : 0≤C) (by linarith : 0≤D)
    (hzero a ha b hb) (hjet a ha b hb) ξ
  simpa only [show (2:ℝ)-(-2)=4 by norm_num] using h

/-- Uniform Fourier representation of the actual logarithmic cubic remainder,
including b=0. Its high-order decay is derived, not supplied by the caller. -/
theorem exists_logCubic_multiplier_kernel :
    ∃ C : ℝ, 0<C ∧ ∀ a∈Icc (-1:ℝ) 1, ∀ b∈Icc (-(1/4):ℝ) (1/4),
      ∃ K : ℝ → ℂ, Continuous K ∧
        Integrable (fun ξ => (1+|ξ|)^100*‖K ξ‖) ∧
        (∫ ξ : ℝ, (1+|ξ|)^100*‖K ξ‖)≤C ∧
        (∀ ξ : ℝ, ‖K ξ‖≤C/(1+|ξ|)^102) ∧
        ∀ s∈Icc (-1:ℝ) 1,
          fordAdditiveCharacter (a*s^3*logCubicProfile (b*s))=
            ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s) := by
  obtain ⟨D,hD,hdecay⟩ := logRemainderCutoff_fourier_decay 102
  refine ⟨max D (D*Real.pi),hD.trans_le (le_max_left _ _),?_⟩
  intro a ha b hb
  let f := logRemainderCutoff (a,b)
  let K : ℝ → ℂ := 𝓕 f
  have hc : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (logRemainderCutoff_support (a,b))
  have hi : Integrable f :=
    (logRemainderCutoff_smooth (a,b)).continuous.integrable_of_hasCompactSupport hc
  have hKc : Continuous K :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi
  have hdom (ξ : ℝ) : (1+|ξ|)^100*‖K ξ‖≤D*(1+ξ^2)⁻¹ := by
    have hs : 1+ξ^2≤(1+|ξ|)^2 := by nlinarith [sq_abs ξ,abs_nonneg ξ]
    have hp : (1+ξ^2)*((1+|ξ|)^100*‖K ξ‖)≤D := by
      calc
        _ ≤ (1+|ξ|)^2*((1+|ξ|)^100*‖K ξ‖) :=
          mul_le_mul_of_nonneg_right hs (by positivity)
        _ = (1+|ξ|)^102*‖K ξ‖ := by
          rw [show (102:ℕ)=2+100 by omega,pow_add]
          ring
        _ ≤ D := hdecay a ha b hb ξ
    rw [←div_eq_mul_inv,le_div_iff₀ (by positivity)]
    simpa only [mul_comm] using hp
  have hcont : Continuous (fun ξ : ℝ => (1+|ξ|)^100*‖K ξ‖) :=
    ((continuous_const.add continuous_abs).pow 100).mul hKc.norm
  have hKi : Integrable (fun ξ : ℝ => (1+|ξ|)^100*‖K ξ‖) :=
    (integrable_inv_one_add_sq.const_mul D).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall (fun ξ => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0≤
          (1+|ξ|)^100*‖K ξ‖ by positivity)] using hdom ξ))
  have hmass : (∫ ξ : ℝ, (1+|ξ|)^100*‖K ξ‖)≤D*Real.pi := by
    have h := integral_mono hKi (integrable_inv_one_add_sq.const_mul D) hdom
    simpa only [integral_const_mul,integral_univ_inv_one_add_sq] using h
  have hK : Integrable K := hKi.mono' hKc.aestronglyMeasurable
    (Eventually.of_forall (fun ξ => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (one_le_pow₀ (by linarith [abs_nonneg ξ]) : (1:ℝ)≤(1+|ξ|)^100)
        (norm_nonneg (K ξ))))
  refine ⟨K,hKc,hKi,hmass.trans (le_max_right _ _),?_,?_⟩
  · intro ξ
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using (hdecay a ha b hb ξ).trans (le_max_left D (D*Real.pi))
  intro s hs
  have hbs : |b*s|≤1/2 := by
    rw [abs_mul]
    have hh := mul_le_mul (abs_le.mpr hb) (abs_le.mpr hs)
      (abs_nonneg s) (by norm_num : (0:ℝ)≤1/4)
    linarith
  have hcut : f s=fordAdditiveCharacter (a*s^3*logCubicProfile (b*s)) := by
    dsimp only [f,logRemainderCutoff]
    rw [modelPhaseBufferedCutoff_one (by norm_num)
      (by linarith [hs.1]) (by linarith [hs.2]),Complex.ofReal_one,one_mul,
      smoothLogCubicProfile_agrees hbs]
  have hinv := congrFun
    ((logRemainderCutoff_smooth (a,b)).continuous.fourierInv_fourier_eq hi hK) s
  rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul] at hinv
  calc
    _ = f s := hcut.symm
    _ = _ := hinv.symm
    _ = ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s) := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [smul_eq_mul,fordAdditiveCharacter]
      have he : (↑(-2*Real.pi*ξ*(-s)) : ℂ)*Complex.I=
          2*(Real.pi:ℂ)*Complex.I*↑(ξ*s) := by push_cast; ring
      rw [he]
      exact mul_comm _ _

/-- Exact entry from the physical square/log phase, with linked Taylor scales. -/
theorem logarithmic_physical_phase {A : ℝ} (hA : 0<A)
    (α t δ s : ℝ) (hs : 0<A+δ*s) :
    α*(A+δ*s)^2+t*Real.log (A+δ*s)=
      (α*A^2+t*Real.log A)+(2*A*δ*α+δ*t/A)*s+
        (δ^2*α-δ^2*t/(2*A^2))*s^2+
        (t*δ^3/A^3)*s^3*logCubicProfile (δ/A*s) := by
  have hn : 0<1+δ/A*s := by
    have he : 1+δ/A*s=(A+δ*s)/A := by field_simp
    rw [he]
    exact div_pos hs hA
  have hfactor : A+δ*s=A*(1+δ/A*s) := by field_simp
  have hlog : Real.log (A+δ*s)=Real.log A+Real.log (1+δ/A*s) := by
    rw [hfactor,Real.log_mul hA.ne' hn.ne']
  have he := logCubicProfile_identity (δ/A*s)
  rw [hlog]
  have hm := congrArg (fun x : ℝ => t*x) he
  field_simp at hm ⊢
  nlinarith only [hm]

/-- The integer-centered shear needed to retain the short physical t-range.
Both output coefficients are those of the actual logarithmic phase above. -/
theorem logarithmic_integer_center_shear (A α t : ℝ) (hA : A≠0) :
    (2*A*α+t/A)-2*A*(α-t/(2*A^2))=2*t/A := by
  field_simp
  ring

/-- Reuse of the already-proved finite Fourier-multiplier sixth-power theorem;
the weighted Hölder proof is not duplicated. -/
theorem exists_logCubic_finite_moment :
    ∃ C : ℝ, 0<C ∧ ∀ a∈Icc (-1:ℝ) 1, ∀ b∈Icc (-(1/4):ℝ) (1/4),
      ∀ {ι : Type} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        ‖∑ i∈S, z i*fordAdditiveCharacter (a*(s i)^3*logCubicProfile (b*s i))‖^6≤
          C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            ‖∑ i∈S, z i*fordAdditiveCharacter (ξ*s i)‖^6) := by
  obtain ⟨C,hC,hkern⟩ := exists_logCubic_multiplier_kernel
  refine ⟨C^6,by positivity,?_⟩
  intro a ha b hb ι S z s hs
  obtain ⟨K,hKc,hKi,hmass,henv,hrep⟩ := hkern a ha b hb
  have hK : Integrable K := hKi.mono' hKc.aestronglyMeasurable
    (Eventually.of_forall (fun ξ => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (one_le_pow₀ (by linarith [abs_nonneg ξ]) : (1:ℝ)≤(1+|ξ|)^100)
        (norm_nonneg (K ξ))))
  have hterm (i : ι) :
      Integrable (fun ξ : ℝ => z i*(K ξ*fordAdditiveCharacter (ξ*s i))) := by
    have hc : Continuous (fun ξ : ℝ => fordAdditiveCharacter (ξ*s i)) := by
      unfold fordAdditiveCharacter
      fun_prop
    exact (hK.mul_bdd hc.aestronglyMeasurable
      (Eventually.of_forall (fun ξ => (sargos_character_norm (ξ*s i)).le))).const_mul _
  have he : (∑ i∈S, z i*fordAdditiveCharacter (a*(s i)^3*logCubicProfile (b*s i)))=
      ∫ ξ : ℝ, K ξ*(∑ i∈S, z i*fordAdditiveCharacter (ξ*s i)) := by
    calc
      _ = ∑ i∈S, z i*(∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s i)) :=
        Finset.sum_congr rfl (fun i hi => congrArg (fun v => z i*v) (hrep (s i) (hs i hi)))
      _ = ∑ i∈S, ∫ ξ : ℝ, z i*(K ξ*fordAdditiveCharacter (ξ*s i)) := by
        simp only [integral_const_mul]
      _ = ∫ ξ : ℝ, ∑ i∈S, z i*(K ξ*fordAdditiveCharacter (ξ*s i)) :=
        (integral_finsetSum S (fun i _ => hterm i)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with ξ
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [he]
  exact bourgain_finite_multiplier_moment S z s hKc hKi hC hmass henv

/-- The bounded-remainder transfer consumes the real square/log source sum.
The radius, cubic coefficient and normalized scale are physically linked. -/
theorem exists_logarithmic_physical_sixth_transfer :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i∈S, s i∈Icc (-1:ℝ) 1) → ∀ (A δ t α : ℝ), 0<A →
      |δ/A|≤1/4 → |t*δ^3/A^3|≤1 →
      ‖∑ i∈S, z i*fordAdditiveCharacter
        (α*(A+δ*s i)^2+t*Real.log (A+δ*s i))‖^6≤
        C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
          ‖∑ i∈S, z i*fordAdditiveCharacter
            ((2*A*δ*α+δ*t/A+ξ)*s i+(δ^2*α-δ^2*t/(2*A^2))*(s i)^2)‖^6) := by
  obtain ⟨C,hC,hbound⟩ := exists_logCubic_finite_moment
  refine ⟨C,hC,?_⟩
  intro ι S z s hs A δ t α hA hδ ht
  let l := 2*A*δ*α+δ*t/A
  let q := δ^2*α-δ^2*t/(2*A^2)
  let z' := fun i => z i*fordAdditiveCharacter (l*s i+q*(s i)^2)
  have h := hbound (t*δ^3/A^3) (abs_le.mp ht) (δ/A) (abs_le.mp hδ) S z' s hs
  have hpos (i : ι) (hi : i∈S) : 0<A+δ*s i := by
    have hb : |δ/A*s i|≤1/4 := by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul hδ (abs_le.mpr (hs i hi))
        (abs_nonneg (s i)) (by norm_num : (0:ℝ)≤1/4)
    have he : A+δ*s i=A*(1+δ/A*s i) := by field_simp
    rw [he]
    apply mul_pos hA
    linarith [(abs_le.mp hb).1]
  have hleft :
      (∑ i∈S, z i*fordAdditiveCharacter (α*(A+δ*s i)^2+t*Real.log (A+δ*s i)))=
        fordAdditiveCharacter (α*A^2+t*Real.log A)*
          (∑ i∈S, z' i*fordAdditiveCharacter
            ((t*δ^3/A^3)*(s i)^3*logCubicProfile (δ/A*s i))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [logarithmic_physical_phase hA α t δ (s i) (hpos i hi)]
    dsimp only [z',l,q]
    simp only [fordAdditiveCharacter_add]
    ring
  have hright (ξ : ℝ) :
      (∑ i∈S, z' i*fordAdditiveCharacter (ξ*s i))=
        ∑ i∈S, z i*fordAdditiveCharacter ((l+ξ)*s i+q*(s i)^2) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [z']
    rw [mul_assoc,←fordAdditiveCharacter_add]
    congr 2
    ring
  rw [hleft,norm_mul,sargos_character_norm,one_mul]
  simpa only [hright,l,q] using h

/-- The actual normalized logarithmic graph, continuously including the parabola. -/
def logCurve (κ s : ℝ) : ℝ := s^2-2*κ*s^3*logCubicProfile (κ*s)

theorem logCurve_identity (κ s : ℝ) :
    κ^2*logCurve κ s=2*(κ*s-Real.log (1+κ*s)) := by
  have h := logCubicProfile_identity (κ*s)
  unfold logCurve
  nlinarith only [h]

private theorem logCurve_eq_log {κ : ℝ} (hκ : κ≠0) (s : ℝ) :
    logCurve κ s=2*(κ*s-Real.log (1+κ*s))/κ^2 := by
  apply (eq_div_iff (pow_ne_zero 2 hκ)).mpr
  simpa only [mul_comm] using logCurve_identity κ s

/-- Exact closure of the specific logarithmic family under cell rescaling.
No general curved-decoupling theorem is invoked or assumed here. -/
theorem logCurve_rescaling (κ a h s : ℝ)
    (ha : 0<1+κ*a) (hs : 0<1+κ*(a+h*s)) :
    logCurve κ (a+h*s)=logCurve κ a+(2*a*h/(1+κ*a))*s+
      (h^2/(1+κ*a)^2)*logCurve (κ*h/(1+κ*a)) s := by
  by_cases hκ : κ=0
  · subst κ
    simp [logCurve]
    ring
  by_cases hh : h=0
  · subst h
    simp
  have hnew : κ*h/(1+κ*a)≠0 := div_ne_zero (mul_ne_zero hκ hh) ha.ne'
  have hfactor : 1+κ*(a+h*s)=(1+κ*a)*(1+(κ*h/(1+κ*a))*s) := by
    field_simp
    ring
  have hright : 0<1+(κ*h/(1+κ*a))*s := by
    rw [hfactor] at hs
    exact (mul_pos_iff_of_pos_left ha).mp hs
  have hlog : Real.log (1+κ*(a+h*s))=
      Real.log (1+κ*a)+Real.log (1+(κ*h/(1+κ*a))*s) := by
    rw [hfactor,Real.log_mul ha.ne' hright.ne']
  rw [logCurve_eq_log hκ,logCurve_eq_log hκ,logCurve_eq_log hnew,hlog]
  field_simp
  ring

theorem logCurve_hasDerivAt (κ s : ℝ) (hs : 1+κ*s≠0) :
    HasDerivAt (logCurve κ) (2*s/(1+κ*s)) s := by
  by_cases hκ : κ=0
  · subst κ
    have hz : logCurve 0=(fun x : ℝ => x^2) := by funext x; simp [logCurve]
    rw [hz]
    simpa using hasDerivAt_pow 2 s
  rw [show logCurve κ=(fun x => 2*(κ*x-Real.log (1+κ*x))/κ^2) from
    funext (logCurve_eq_log hκ)]
  have h := (((hasDerivAt_id s).const_mul κ).sub
    ((((hasDerivAt_id s).const_mul κ).const_add 1).log hs)).const_mul 2 |>.div_const (κ^2)
  convert h using 1
  dsimp only [id_eq]
  field_simp [hs,hκ]
  have hc : (1+s*κ)*(1+s*κ)⁻¹=1 := mul_inv_cancel₀ (by simpa only [mul_comm] using hs)
  simp only [div_eq_mul_inv,one_mul]
  nlinarith only [hc]

/-- Curvature of the exact family, including the zero-parameter parabola. -/
theorem logCurve_second_derivative (κ s : ℝ) (hs : 1+κ*s≠0) :
    HasDerivAt (deriv (logCurve κ)) (2/(1+κ*s)^2) s := by
  have he : deriv (logCurve κ)=ᶠ[𝓝 s] (fun x => 2*x/(1+κ*x)) := by
    have hn : ∀ᶠ x : ℝ in 𝓝 s, 1+κ*x≠0 :=
      ((continuous_const.add (continuous_const.mul continuous_id)).continuousAt.eventually_ne hs)
    filter_upwards [hn] with x hx
    exact (logCurve_hasDerivAt κ x hx).deriv
  have h := ((hasDerivAt_id s).const_mul 2).div
    (((hasDerivAt_id s).const_mul κ).const_add 1) hs
  have hd : HasDerivAt (fun x : ℝ => 2*x/(1+κ*x)) (2/(1+κ*s)^2) s := by
    convert h using 1
    dsimp only [id_eq]
    ring
  exact hd.congr_of_eventuallyEq he

/-- The rescaled parameters stay in one compact family on every retained cell. -/
theorem logCurve_rescaled_parameter {κ a h : ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4)) (ha : 0≤a) (hh : h∈Icc (0:ℝ) 1) :
    κ*h/(1+κ*a)∈Icc (0:ℝ) (1/4) := by
  have hp : 0<1+κ*a := by nlinarith [mul_nonneg hκ.1 ha]
  constructor
  · exact div_nonneg (mul_nonneg hκ.1 hh.1) hp.le
  · apply (div_le_iff₀ hp).mpr
    have hn : κ*h≤κ := by nlinarith [hκ.1,hh.2]
    nlinarith [hκ.1,hκ.2,mul_nonneg hκ.1 ha]

/-- Exact source entry using the square-frequency coordinate. This retains
the physical coefficients, including the factor 1/4 in the curved direction. -/
theorem logCurve_square_source_phase {A n κ s : ℝ}
    (hA : 0<A) (hn : 0<n) (hcoord : n^2=A^2*(1+κ*s)) (α t : ℝ) :
    α*n^2+t*Real.log n=(α*A^2+t*Real.log A)+
      (α*A^2*κ+t*κ/2)*s-(t*κ^2/4)*logCurve κ s := by
  have hq : 0<1+κ*s := by
    have h := sq_pos_of_pos hn
    rw [hcoord] at h
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hA)).mp h
  have hlog : 2*Real.log n=2*Real.log A+Real.log (1+κ*s) := by
    have he := congrArg Real.log hcoord
    rw [Real.log_mul (pow_ne_zero 2 hA.ne') hq.ne',Real.log_pow,Real.log_pow] at he
    norm_num only [Nat.cast_ofNat] at he
    exact he
  have hc := logCurve_identity κ s
  rw [hcoord]
  linear_combination (t/2)*hlog+(t/4)*hc

/-- Both directions of the local logarithmic/parabolic sixth-power comparison.
This is the bounded-parameter step, not the missing all-scale decoupling theorem.
The same actual log curve occurs on both sides; no cell norm is supplied. -/
theorem exists_logCurve_local_two_way_sixth_transfer :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i∈S, s i∈Icc (-1:ℝ) 1) → ∀ κ∈Icc (0:ℝ) (1/4),
      ∀ α β : ℝ, |2*κ*β|≤1 →
      (‖∑ i∈S, z i*fordAdditiveCharacter (α*s i+β*logCurve κ (s i))‖^6≤
        C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
          ‖∑ i∈S, z i*fordAdditiveCharacter ((α+ξ)*s i+β*(s i)^2)‖^6)) ∧
      (‖∑ i∈S, z i*fordAdditiveCharacter (α*s i+β*(s i)^2)‖^6≤
        C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
          ‖∑ i∈S, z i*fordAdditiveCharacter ((α+ξ)*s i+β*logCurve κ (s i))‖^6)) := by
  obtain ⟨C,hC,hbound⟩ := exists_logCubic_finite_moment
  refine ⟨C,hC,?_⟩
  intro ι S z s hs κ hκ α β hβ
  have hk : κ∈Icc (-(1/4):ℝ) (1/4) := ⟨by linarith [hκ.1],hκ.2⟩
  have hneg : -2*κ*β∈Icc (-1:ℝ) 1 := by
    have hh := abs_le.mp hβ
    constructor <;> linarith [hh.1,hh.2]
  have hp := hbound (-2*κ*β) hneg κ hk S
    (fun i => z i*fordAdditiveCharacter (α*s i+β*(s i)^2)) s hs
  have hm := hbound (2*κ*β) (abs_le.mp hβ) κ hk S
    (fun i => z i*fordAdditiveCharacter (α*s i+β*logCurve κ (s i))) s hs
  have hprod (θ ψ : ι → ℝ) :
      (∑ i∈S, (z i*fordAdditiveCharacter (θ i))*fordAdditiveCharacter (ψ i))=
        ∑ i∈S, z i*fordAdditiveCharacter (θ i+ψ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc,←fordAdditiveCharacter_add]
  simp only [hprod] at hp hm
  have he₁ (i : ι) : α*s i+β*(s i)^2+(-2*κ*β)*(s i)^3*logCubicProfile (κ*s i)=
      α*s i+β*logCurve κ (s i) := by unfold logCurve; ring
  have he₂ (i : ι) : α*s i+β*logCurve κ (s i)+(2*κ*β)*(s i)^3*logCubicProfile (κ*s i)=
      α*s i+β*(s i)^2 := by unfold logCurve; ring
  have he₃ (ξ : ℝ) (i : ι) : α*s i+β*(s i)^2+ξ*s i=(α+ξ)*s i+β*(s i)^2 := by ring
  have he₄ (ξ : ℝ) (i : ι) : α*s i+β*logCurve κ (s i)+ξ*s i=
      (α+ξ)*s i+β*logCurve κ (s i) := by ring
  exact ⟨by simpa only [he₁,he₃] using hp,by simpa only [he₂,he₄] using hm⟩

/-- Direct finite-localization route: separated coordinates on the same
short interval have a genuine logarithmic frequency gap. -/
theorem logCurve_separated_secant {κ d u ν x y : ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4)) (hν : 0<ν) (hu : u≤ν)
    (hd : 3*ν≤|d|) (hl : -1≤d) (hr : d+u≤1)
    (hx : x∈Icc d (d+u)) (hy : y∈Icc d (d+u)) :
    2*ν*|x-y|≤|logCurve κ x-logCurve κ y| := by
  have hden (v : ℝ) (hv : v∈Icc d (d+u)) : 0<1+κ*v ∧ 1+κ*v≤2 := by
    have hv₁ : -1≤v := hl.trans hv.1
    have hv₂ : v≤1 := hv.2.trans hr
    have hlow := mul_le_mul_of_nonneg_left hv₁ hκ.1
    have hhigh := mul_le_mul_of_nonneg_left hv₂ hκ.1
    constructor <;> nlinarith [hκ.2]
  have hfar (v : ℝ) (hv : v∈Icc d (d+u)) : 2*ν≤|v| := by
    rcases le_total 0 d with hd₀|hd₀
    · rw [abs_of_nonneg hd₀] at hd
      exact (by linarith [hv.1] : 2*ν≤v).trans (le_abs_self v)
    · rw [abs_of_nonpos hd₀] at hd
      have hv₀ : v≤0 := by linarith [hv.2]
      rw [abs_of_nonpos hv₀]
      linarith [hv.2]
  have hordered (a b : ℝ) (ha : a∈Icc d (d+u)) (hb : b∈Icc d (d+u))
      (hab : a<b) : 2*ν*|b-a|≤|logCurve κ b-logCurve κ a| := by
    have hsub : Icc a b⊆Icc d (d+u) := Icc_subset_Icc ha.1 hb.2
    obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope (logCurve κ)
      (fun v => 2*v/(1+κ*v)) hab
      (fun v hv => (logCurve_hasDerivAt κ v (hden v (hsub hv)).1.ne').continuousAt.continuousWithinAt)
      (fun v hv => logCurve_hasDerivAt κ v (hden v (hsub (Ioo_subset_Icc_self hv))).1.ne')
    have hcI := hsub (Ioo_subset_Icc_self hc)
    have hderiv : 2*ν≤|2*c/(1+κ*c)| := by
      apply (hfar c hcI).trans
      rw [abs_div,abs_mul,abs_of_pos (hden c hcI).1]
      rw [abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
      apply (le_div_iff₀ (hden c hcI).1).mpr
      nlinarith [mul_le_mul_of_nonneg_left (hden c hcI).2 (abs_nonneg c)]
    have he' : (2*c/(1+κ*c))*(b-a)=logCurve κ b-logCurve κ a :=
      (eq_div_iff (sub_ne_zero.mpr hab.ne')).mp he
    have hh := mul_le_mul_of_nonneg_right hderiv (abs_nonneg (b-a))
    simpa only [←abs_mul,he'] using hh
  rcases lt_trichotomy x y with hxy|hxy|hxy
  · simpa only [abs_sub_comm] using hordered x y hx hy hxy
  · subst y
    simp
  · exact hordered y x hy hx hxy

/-- The positive small-frequency values lie between zero and the parabola.
This signed bound recovers the same localization constant as the proved
parabolic recurrence, instead of introducing a new numerical budget. -/
theorem logCurve_nonneg_le_sq {κ y : ℝ} (hκ : 0≤κ) (hy : 0≤y) :
    0≤logCurve κ y ∧ logCurve κ y≤y^2 := by
  have hp (v : ℝ) (hv : 0≤v) : 0<1+κ*v := by nlinarith [mul_nonneg hκ hv]
  have hd (v : ℝ) (hv : 0≤v) := logCurve_hasDerivAt κ v (hp v hv).ne'
  have hmono : MonotoneOn (logCurve κ) (Ici (0:ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ))
      (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
      (fun v hv => (hd v (interior_subset hv)).hasDerivWithinAt)
      (fun v hv => div_nonneg (mul_nonneg (by norm_num) (show 0≤v from interior_subset hv))
        (hp v (interior_subset hv)).le)
  have hg (v : ℝ) (hv : 0≤v) :
      HasDerivAt (fun t : ℝ => t^2-logCurve κ t) (2*v-2*v/(1+κ*v)) v := by
    convert ((hasDerivAt_id v).pow 2).sub (hd v hv) using 1
    simp
  have hg₀ (v : ℝ) (hv : 0≤v) : 0≤2*v-2*v/(1+κ*v) := by
    have hh : 2*v/(1+κ*v)≤2*v := by
      apply (div_le_iff₀ (hp v hv)).mpr
      nlinarith [mul_nonneg hv (mul_nonneg hκ hv)]
    linarith
  have hmonog : MonotoneOn (fun t : ℝ => t^2-logCurve κ t) (Ici (0:ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0:ℝ))
      (fun v hv => (hg v hv).continuousAt.continuousWithinAt)
      (fun v hv => (hg v (interior_subset hv)).hasDerivWithinAt)
      (fun v hv => hg₀ v (interior_subset hv))
  have hz : logCurve κ 0=0 := by simp [logCurve]
  have hlow := hmono (show (0:ℝ)∈Ici (0:ℝ) by simp) hy hy
  have hupp := hmonog (show (0:ℝ)∈Ici (0:ℝ) by simp) hy hy
  change (0:ℝ)^2-logCurve κ 0≤y^2-logCurve κ y at hupp
  rw [hz] at hlow hupp
  exact ⟨hlow,by nlinarith only [hupp]⟩

theorem logCurve_small_frequency_bound {κ w y : ℝ}
    (hκ : 0≤κ) (hw : 0≤w) (hy : y∈Icc 0 w) :
    |logCurve κ y|≤2*w^2 := by
  have hderiv (v : ℝ) (hv : v∈Icc 0 w) :
      HasDerivWithinAt (logCurve κ) (2*v/(1+κ*v)) (Icc 0 w) v :=
    (logCurve_hasDerivAt κ v (ne_of_gt (by nlinarith [mul_nonneg hκ hv.1]))).hasDerivWithinAt
  have hbound (v : ℝ) (hv : v∈Icc 0 w) : ‖2*v/(1+κ*v)‖≤2*w := by
    have hden : 0<1+κ*v := by nlinarith [mul_nonneg hκ hv.1]
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (by linarith [hv.1]) hden.le)]
    apply (div_le_iff₀ hden).mpr
    nlinarith [hv.2,mul_nonneg hκ hv.1,mul_nonneg hw (mul_nonneg hκ hv.1)]
  have hh := (convex_Icc (0:ℝ) w).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound ⟨le_rfl,hw⟩ hy
  simp only [logCurve,zero_pow (by norm_num : (2:ℕ)≠0),zero_pow (by norm_num : (3:ℕ)≠0),
    mul_zero,zero_mul,sub_zero,Real.norm_eq_abs,abs_of_nonneg hy.1] at hh
  change |logCurve κ y|≤2*w^2
  have he : logCurve κ y=y^2-2*κ*y^3*logCubicProfile (κ*y) := rfl
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hy.2 (by linarith : 0≤2*w)]

/-- A six-frequency cancellation gate for the actual log curve. It uses the
proved secant estimate and actual small-frequency values, not a moment premise. -/
theorem logCurve_sixth_frequency_gap {κ d u ν x x' y₁ y₂ y₃ y₄ w b : ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4)) (hν : 0<ν) (hu : u≤ν)
    (hd : 3*ν≤|d|) (hl : -1≤d) (hr : d+u≤1)
    (hx : x∈Icc d (d+u)) (hx' : x'∈Icc d (d+u)) (hw : 0≤w)
    (h₁ : y₁∈Icc 0 w) (h₂ : y₂∈Icc 0 w)
    (h₃ : y₃∈Icc 0 w) (h₄ : y₄∈Icc 0 w)
    (hgap : (b+2*w^2)/(2*ν) < |x-x'|) :
    b < |logCurve κ x+logCurve κ y₁+logCurve κ y₂-
      (logCurve κ x'+logCurve κ y₃+logCurve κ y₄)| := by
  have hxgap := logCurve_separated_secant hκ hν hu hd hl hr hx hx'
  have hvalue {v : ℝ} (hv : v∈Icc (0:ℝ) w) : 0≤logCurve κ v ∧ logCurve κ v≤w^2 := by
    have h := logCurve_nonneg_le_sq hκ.1 hv.1
    exact ⟨h.1,h.2.trans ((pow_le_pow_iff_left₀ hv.1 hw (by norm_num : (2:ℕ)≠0)).mpr hv.2)⟩
  have hy₁ := hvalue h₁
  have hy₂ := hvalue h₂
  have hy₃ := hvalue h₃
  have hy₄ := hvalue h₄
  by_contra! hn
  have hb := abs_le.mp hn
  have hxupper : |logCurve κ x-logCurve κ x'|≤b+2*w^2 := by
    apply abs_le.mpr
    constructor <;> linarith [hy₁.1,hy₁.2,hy₂.1,hy₂.2,hy₃.1,hy₃.2,hy₄.1,hy₄.2,hb.1,hb.2]
  have hg := (div_lt_iff₀ (by positivity : 0<2*ν)).mp hgap
  nlinarith only [hxgap,hxupper,hg]

/-- Actual sinc-kernel cancellation for the six logarithmic frequencies.
This consumes the derived gap and reuses the existing planar Fourier kernel. -/
theorem integral_logCurve_sixth_kernel_eq_zero
    {κ x x' y₁ y₂ y₃ y₄ w d u ν a b : ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4))
    (hw : 0<w) (hν : 0<ν) (ha : 0<a) (hb : 0<b)
    (hwidth : b≤w^2) (hu : u≤ν) (hd : 3*ν≤|d|)
    (hl : -1≤d) (hr : d+u≤1)
    (hx : x∈Icc d (d+u)) (hx' : x'∈Icc d (d+u))
    (h₁ : y₁∈Icc 0 w) (h₂ : y₂∈Icc 0 w)
    (h₃ : y₃∈Icc 0 w) (h₄ : y₄∈Icc 0 w)
    (hgap : 2*w^2/ν≤|x-x'|) (c e : ℝ) :
    (∫ α : ℝ, ∫ γ : ℝ,
      sargosPlanarKernelTerm a b c e
        (x+y₁+y₂-(x'+y₃+y₄))
        (logCurve κ x+logCurve κ y₁+logCurve κ y₂-
          (logCurve κ x'+logCurve κ y₃+logCurve κ y₄)) α γ)=0 := by
  apply integral_sargosPlanarKernelTerm_eq_zero ha hb (Or.inr ?_)
  apply le_of_lt
  apply logCurve_sixth_frequency_gap hκ hν hu hd hl hr hx hx' hw.le h₁ h₂ h₃ h₄
  have hg := (div_le_iff₀ hν).mp hgap
  apply (div_lt_iff₀ (by positivity : 0<2*ν)).mpr
  nlinarith [sq_pos_of_pos hw]

def logCurveBandGauge (κ ξ η : ℝ) : ℝ :=
  (1+κ)^2*parabolaBandGauge (ξ/(1+κ)) η

private theorem logCurve_slope_band {κ a : ℝ} (hκ : 0≤κ) (ha : a∈Icc (0:ℝ) 1)
    (ξ η : ℝ) : |η-(2*a/(1+κ*a))*ξ|≤parabolaBandGauge (ξ/(1+κ)) η := by
  have hA : 0<1+κ*a := by nlinarith [mul_nonneg hκ ha.1]
  have hK : 0<1+κ := by linarith
  have hb : (1+κ)*a/(1+κ*a)∈Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (mul_nonneg hK.le ha.1) hA.le
    · apply (div_le_one hA).mpr
      nlinarith [ha.2]
  have h := parabolaBandGauge_slope_le hb (ξ/(1+κ)) η
  convert h using 1
  congr 1
  field_simp

/-- Exact adapted Fourier-band stability for the actual logarithmic family.
The curvature normalization removes any accumulated constant loss in rescaling. -/
theorem logCurveBandGauge_rescale {κ a σ : ℝ}
    (hκ : 0≤κ) (ha : 0≤a) (hσ : 0≤σ) (haσ : a+σ≤1) (ξ η : ℝ) :
    σ^2*logCurveBandGauge (κ*σ/(1+κ*a)) ξ η≤
      logCurveBandGauge κ (σ*ξ)
        ((2*a/(1+κ*a))*σ*ξ+(σ^2/(1+κ*a)^2)*η) := by
  let A := 1+κ*a
  let B := 1+κ*(a+σ)
  let k := κ*σ/A
  let V := (2*a/A)*σ*ξ+(σ^2/A^2)*η
  have hA : 0<A := by dsimp [A]; nlinarith [mul_nonneg hκ ha]
  have hB : 0<B := by dsimp [B]; nlinarith [mul_nonneg hκ (add_nonneg ha hσ)]
  have hK : 0<1+κ := by linarith
  have hk : 0≤k := div_nonneg (mul_nonneg hκ hσ) hA.le
  have hk₁ : 0<1+k := by linarith
  have h1 := logCurve_slope_band hκ (show a∈Icc (0:ℝ) 1 from ⟨ha,by linarith⟩)
    (σ*ξ) V
  have h2 := logCurve_slope_band hκ
    (show a+σ∈Icc (0:ℝ) 1 from ⟨add_nonneg ha hσ,haσ⟩) (σ*ξ) V
  have he1 : V-(2*a/(1+κ*a))*(σ*ξ)=(σ^2/A^2)*η := by dsimp [V,A]; ring
  have he2 : V-(2*(a+σ)/(1+κ*(a+σ)))*(σ*ξ)=
      (σ^2/A^2)*(η-2*(ξ/(1+k))) := by
    dsimp [V,k,A]
    field_simp
    ring
  rw [he1,abs_mul,abs_of_nonneg (by positivity : 0≤σ^2/A^2)] at h1
  rw [he2,abs_mul,abs_of_nonneg (by positivity : 0≤σ^2/A^2)] at h2
  have hlocal : (σ^2/A^2)*parabolaBandGauge (ξ/(1+k)) η≤
      parabolaBandGauge ((σ*ξ)/(1+κ)) V := by
    unfold parabolaBandGauge
    rw [mul_max_of_nonneg _ _ (by positivity : 0≤σ^2/A^2)]
    exact max_le h1 h2
  have hBA : A*(1+k)=B := by dsimp [A,B,k]; field_simp; ring
  have hBle : B≤1+κ := by dsimp [B]; nlinarith [mul_le_mul_of_nonneg_left haσ hκ]
  have hn : (1+k)^2≤(1+κ)^2/A^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hA)).mpr
    have hh := mul_self_le_mul_self hB.le hBle
    rw [←hBA] at hh
    nlinarith only [hh]
  have hc : σ^2*(1+k)^2≤(1+κ)^2*(σ^2/A^2) := by
    have hh := mul_le_mul_of_nonneg_left hn (sq_nonneg σ)
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  change σ^2*((1+k)^2*parabolaBandGauge (ξ/(1+k)) η)≤
    (1+κ)^2*parabolaBandGauge ((σ*ξ)/(1+κ)) V
  calc
    _ = (σ^2*(1+k)^2)*parabolaBandGauge (ξ/(1+k)) η := by ring
    _ ≤ ((1+κ)^2*(σ^2/A^2))*parabolaBandGauge (ξ/(1+k)) η :=
      mul_le_mul_of_nonneg_right hc (parabolaBandGauge_nonneg _ _)
    _ = (1+κ)^2*((σ^2/A^2)*parabolaBandGauge (ξ/(1+k)) η) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlocal (sq_nonneg (1+κ))

/-- Exact finite source-sum rescaling for the specific logarithmic family. -/
theorem logCurve_sum_rescale {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) (κ a σ α γ : ℝ)
    (hσ : σ≠0) (ha : 0<1+κ*a) (hx : ∀ i∈S, 0<1+κ*x i) :
    sargosPlanarSum S z x (fun i => logCurve κ (x i)) α γ=
      fordAdditiveCharacter (a*α+logCurve κ a*γ)*
        sargosPlanarSum S z (fun i => (x i-a)/σ)
          (fun i => logCurve (κ*σ/(1+κ*a)) ((x i-a)/σ))
          (σ*α+(2*a*σ/(1+κ*a))*γ) ((σ^2/(1+κ*a)^2)*γ) := by
  unfold sargosPlanarSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show fordAdditiveCharacter (a*α+logCurve κ a*γ)*
      (z i*fordAdditiveCharacter (((x i-a)/σ)*(σ*α+(2*a*σ/(1+κ*a))*γ)+
        logCurve (κ*σ/(1+κ*a)) ((x i-a)/σ)*((σ^2/(1+κ*a)^2)*γ)))=
      z i*(fordAdditiveCharacter (a*α+logCurve κ a*γ)*
        fordAdditiveCharacter (((x i-a)/σ)*(σ*α+(2*a*σ/(1+κ*a))*γ)+
          logCurve (κ*σ/(1+κ*a)) ((x i-a)/σ)*((σ^2/(1+κ*a)^2)*γ))) by ring,
    ←fordAdditiveCharacter_add]
  congr 2
  have he : a+σ*((x i-a)/σ)=x i := by field_simp; ring
  have hc := logCurve_rescaling κ a σ ((x i-a)/σ) ha (by rw [he]; exact hx i hi)
  rw [he] at hc
  dsimp only
  rw [hc]
  field_simp
  ring

/-- The translated six-frequency gap lies outside the actual adapted band.
All shifted log values are derived from the proved rescaling identity. -/
theorem logCurve_band_sixth_gap {κ x x' y₁ y₂ y₃ y₄ w a β u ν δ : ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4)) (hw : 0<w) (hν : 0<ν)
    (hβ : β∈Icc (0:ℝ) 1) (ha : 0≤a) (har : a+u≤1)
    (hwidth : δ^2≤w^2) (hu : u≤ν) (hd : 3*ν≤|a-β|)
    (hx : x∈Icc a (a+u)) (hx' : x'∈Icc a (a+u))
    (h₁ : y₁∈Icc β (β+w)) (h₂ : y₂∈Icc β (β+w))
    (h₃ : y₃∈Icc β (β+w)) (h₄ : y₄∈Icc β (β+w))
    (hgap : 2*w^2/ν≤|x-x'|) :
    δ^2≤logCurveBandGauge κ (x+y₁+y₂-(x'+y₃+y₄))
      (logCurve κ x+logCurve κ y₁+logCurve κ y₂-
        (logCurve κ x'+logCurve κ y₃+logCurve κ y₄)) := by
  let A := 1+κ*β
  let k := κ/A
  have hA : 0<A := by dsimp [A]; nlinarith [mul_nonneg hκ.1 hβ.1]
  have hk : k∈Icc (0:ℝ) (1/4) := by
    simpa only [mul_one] using logCurve_rescaled_parameter hκ hβ.1
      (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num)
  have hmem {v : ℝ} (hv : v∈Icc β (β+w)) : v-β∈Icc (0:ℝ) w :=
    ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have hxp : x-β∈Icc (a-β) (a-β+u) := ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hxp' : x'-β∈Icc (a-β) (a-β+u) := ⟨by linarith [hx'.1],by linarith [hx'.2]⟩
  have hg : (δ^2+2*w^2)/(2*ν) < |(x-β)-(x'-β)| := by
    rw [show (x-β)-(x'-β)=x-x' by ring]
    have hh := (div_le_iff₀ hν).mp hgap
    apply (div_lt_iff₀ (by positivity : 0<2*ν)).mpr
    nlinarith [sq_pos_of_pos hw]
  have hgap' := logCurve_sixth_frequency_gap hk hν hu hd
    (by linarith [hβ.2] : -1≤a-β) (by linarith [hβ.1] : a-β+u≤1)
    hxp hxp' hw.le (hmem h₁) (hmem h₂) (hmem h₃) (hmem h₄) hg
  have hid (v : ℝ) (hv : 0≤v) :
      A^2*(logCurve κ v-logCurve κ β-(2*β/A)*(v-β))=logCurve k (v-β) := by
    have hp : 0<1+κ*v := by nlinarith [mul_nonneg hκ.1 hv]
    have heq : β+1*(v-β)=v := by ring
    have hh := logCurve_rescaling κ β 1 (v-β) hA (by rwa [heq])
    rw [heq] at hh
    simp only [mul_one,one_pow] at hh
    change logCurve κ v=logCurve κ β+(2*β/A)*(v-β)+(1/A^2)*logCurve k (v-β) at hh
    rw [hh]
    field_simp
    ring
  let ξ := x+y₁+y₂-(x'+y₃+y₄)
  let η := logCurve κ x+logCurve κ y₁+logCurve κ y₂-
    (logCurve κ x'+logCurve κ y₃+logCurve κ y₄)
  have he : logCurve k (x-β)+logCurve k (y₁-β)+logCurve k (y₂-β)-
      (logCurve k (x'-β)+logCurve k (y₃-β)+logCurve k (y₄-β))=
      A^2*(η-(2*β/A)*ξ) := by
    rw [←hid x (ha.trans hx.1),←hid x' (ha.trans hx'.1),
      ←hid y₁ (hβ.1.trans h₁.1),←hid y₂ (hβ.1.trans h₂.1),
      ←hid y₃ (hβ.1.trans h₃.1),←hid y₄ (hβ.1.trans h₄.1)]
    dsimp [ξ,η]
    ring
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg A)] at hgap'
  have hAle : A≤1+κ := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hβ.2 hκ.1]
  have hsquare : A^2≤(1+κ)^2 := by nlinarith [mul_self_le_mul_self hA.le hAle]
  have hbound := logCurve_slope_band hκ.1 hβ ξ η
  change δ^2≤(1+κ)^2*parabolaBandGauge (ξ/(1+κ)) η
  exact hgap'.le.trans (mul_le_mul hsquare hbound
    (abs_nonneg _) (sq_nonneg (1+κ)))

private def logCurveRescaling (κ a σ : ℝ) (hσ : σ≠0) (hA : 1+κ*a≠0) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun p := (σ*p.1+(2*a*σ/(1+κ*a))*p.2,(σ^2/(1+κ*a)^2)*p.2)
  invFun p := (p.1/σ-(2*a*(1+κ*a)/σ^2)*p.2,((1+κ*a)^2/σ^2)*p.2)
  left_inv p := by
    ext <;> dsimp <;> field_simp
    ring
  right_inv p := by
    ext <;> dsimp <;> field_simp
    ring
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' c p := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem logCurve_haar_factor (e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    ∃ c : ℝ≥0, 0<c ∧ Measure.map e (volume : Measure (ℝ × ℝ))=(c : ℝ≥0∞) • volume := by
  haveI : (Measure.map e (volume : Measure (ℝ × ℝ))).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map volume
  exact ⟨Measure.addHaarScalarFactor (Measure.map e volume) volume,
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,
    Measure.isAddLeftInvariant_eq_smul _ _⟩

private theorem logCurve_rescaling_integrable
    (e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) {W : ℝ × ℝ → ℝ} (hW : Integrable W) :
    Integrable (fun p => W (e p)) := by
  obtain ⟨c,hc,he⟩ := logCurve_haar_factor e
  apply (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv W).mp
  change Integrable W (Measure.map e volume)
  rw [he]
  exact hW.smul_measure ENNReal.coe_ne_top

private theorem logCurve_rescaling_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    ∃ c : ℝ, 0<c ∧ ∀ f : ℝ × ℝ → F,
      (∫ p : ℝ × ℝ, f (e p))=c • ∫ p : ℝ × ℝ, f p := by
  obtain ⟨c,hc,he⟩ := logCurve_haar_factor e
  refine ⟨c,hc,fun f => ?_⟩
  calc
    (∫ p : ℝ × ℝ, f (e p))=∫ p, f p ∂Measure.map e volume :=
      (integral_map_equiv (μ:=volume) e.toHomeomorph.toMeasurableEquiv f).symm
    _ = _ := by rw [he,integral_smul_measure,ENNReal.coe_toReal]

/-- Literal nonnegative Fourier-band weights for the rescaling-closed
logarithmic family. This is a support condition, not a decoupling estimate. -/
def LogCurveWeightBand (κ δ : ℝ) (W : ℝ × ℝ → ℝ) : Prop :=
  (∀ p, 0≤W p) ∧ Integrable W ∧ ∀ ξ η : ℝ, δ^2≤logCurveBandGauge κ ξ η →
    (∫ p : ℝ × ℝ, (W p : ℂ)*fordAdditiveCharacter (ξ*p.1+η*p.2))=0

theorem LogCurveWeightBand.rescale {κ δ a σ : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : LogCurveWeightBand κ δ W) (hκ : 0≤κ) (hσ : 0<σ)
    (ha : 0≤a) (haσ : a+σ≤1) :
    LogCurveWeightBand (κ*σ/(1+κ*a)) (δ/σ)
      (fun p => W (p.1/σ-(2*a*(1+κ*a)/σ^2)*p.2,((1+κ*a)^2/σ^2)*p.2)) := by
  have hA : 0<1+κ*a := by nlinarith [mul_nonneg hκ ha]
  let e := logCurveRescaling κ a σ hσ.ne' hA.ne'
  refine ⟨fun p => hW.1 _,logCurve_rescaling_integrable e.symm hW.2.1,?_⟩
  intro ξ η hgap
  obtain ⟨c,hc,hint⟩ := logCurve_rescaling_integral (F:=ℂ) e.symm
  let f := fun p : ℝ × ℝ => (W p : ℂ)*fordAdditiveCharacter (ξ*(e p).1+η*(e p).2)
  have heq : (∫ p : ℝ × ℝ,
      (W (p.1/σ-(2*a*(1+κ*a)/σ^2)*p.2,((1+κ*a)^2/σ^2)*p.2) : ℂ)*
        fordAdditiveCharacter (ξ*p.1+η*p.2))=∫ p : ℝ × ℝ, f (e.symm p) := by
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [f]
    rw [e.apply_symm_apply]
    rfl
  rw [heq,hint f]
  have hg := (mul_le_mul_of_nonneg_left hgap (sq_nonneg σ)).trans
    (logCurveBandGauge_rescale hκ ha hσ.le haσ ξ η)
  have hcancel : σ^2*(δ/σ)^2=δ^2 := by field_simp
  rw [hcancel] at hg
  have hz := hW.2.2 (σ*ξ) ((2*a/(1+κ*a))*σ*ξ+(σ^2/(1+κ*a)^2)*η) hg
  have he (p : ℝ × ℝ) : ξ*(e p).1+η*(e p).2=
      (σ*ξ)*p.1+((2*a/(1+κ*a))*σ*ξ+(σ^2/(1+κ*a)^2)*η)*p.2 := by
    dsimp [e,logCurveRescaling]
    ring
  dsimp only [f]
  simp_rw [he]
  rw [hz,smul_zero]

/-- The already proved parabolic Fourier band supplies genuine logarithmic
band weights after a fixed scale adjustment; no new weight is postulated. -/
theorem ParabolaWeightBand.to_logCurveWeightBand {κ δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hκ : 0≤κ) (hW : ParabolaWeightBand (δ/(1+κ)) W) :
    LogCurveWeightBand κ δ W := by
  have hK : 0<1+κ := by linarith
  refine ⟨hW.1,hW.2.1,fun ξ η hgap => hW.2.2 ξ η ?_⟩
  have hfrac : (1/(1+κ):ℝ)∈Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hK).mpr (by linarith)
  have hband := parabolaBandGauge_slope_le hfrac ξ η
  have hband' : |η-2*(ξ/(1+κ))|≤parabolaBandGauge ξ η := by
    convert hband using 1
    congr 1
    ring
  have hb : parabolaBandGauge (ξ/(1+κ)) η≤parabolaBandGauge ξ η :=
    max_le (le_max_left _ _) hband'
  have hg : δ^2≤(1+κ)^2*parabolaBandGauge ξ η :=
    hgap.trans (mul_le_mul_of_nonneg_left hb (sq_nonneg (1+κ)))
  rw [div_pow]
  exact (div_le_iff₀ (sq_pos_of_pos hK)).mpr (by nlinarith only [hg])

theorem exists_logCurveWeightBand_nonzero {κ δ : ℝ} (hκ : 0≤κ) (hδ : 0<δ) :
    ∃ W : ℝ × ℝ → ℝ, LogCurveWeightBand κ δ W ∧ 1≤W (0,0) := by
  obtain ⟨W,hW,hW₀⟩ := exists_parabolaWeightBand_nonzero
    (show 0<δ/(1+κ) by positivity)
  exact ⟨W,ParabolaWeightBand.to_logCurveWeightBand hκ hW,hW₀⟩

def logCurveWeightedBilinearMoment {ι τ : Type*}
    (κ : ℝ) (W : ℝ × ℝ → ℝ) (S : Finset ι) (V : Finset τ)
    (z : ι → ℂ) (c : τ → ℂ) (x : ι → ℝ) (y : τ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, W p*
    ‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖^2*
    ‖sargosPlanarSum V c y (fun i => logCurve κ (y i)) p.1 p.2‖^4

/-- One positive Haar factor rescales the full logarithmic moment and all
of its cells. Actual finite sums enter through the proved phase identity. -/
theorem exists_logCurveWeightedBilinearMoment_rescale (κ a σ : ℝ)
    (hσ : σ≠0) (hA : 0<1+κ*a) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι τ : Type} (W : ℝ × ℝ → ℝ)
      (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
      (x : ι → ℝ) (y : τ → ℝ),
      (∀ i∈S, 0<1+κ*x i) → (∀ j∈V, 0<1+κ*y j) →
      logCurveWeightedBilinearMoment (κ*σ/(1+κ*a))
        (fun p => W (p.1/σ-(2*a*(1+κ*a)/σ^2)*p.2,((1+κ*a)^2/σ^2)*p.2))
        S V z c (fun i => (x i-a)/σ) (fun j => (y j-a)/σ)=
      C*logCurveWeightedBilinearMoment κ W S V z c x y := by
  let e := logCurveRescaling κ a σ hσ hA.ne'
  obtain ⟨C,hC,hint⟩ := logCurve_rescaling_integral (F:=ℝ) e.symm
  refine ⟨C,hC,?_⟩
  intro ι τ W S V z c x y hx hy
  have hn {ρ : Type} (T : Finset ρ) (v : ρ → ℂ) (s : ρ → ℝ)
      (hs : ∀ i∈T, 0<1+κ*s i) (p : ℝ × ℝ) :
      ‖sargosPlanarSum T v s (fun i => logCurve κ (s i)) (e.symm p).1 (e.symm p).2‖=
        ‖sargosPlanarSum T v (fun i => (s i-a)/σ)
          (fun i => logCurve (κ*σ/(1+κ*a)) ((s i-a)/σ)) p.1 p.2‖ := by
    have h := congrArg norm (logCurve_sum_rescale T v s κ a σ
      (e.symm p).1 (e.symm p).2 hσ hA hs)
    rw [norm_mul,sargos_character_norm,one_mul] at h
    change _ = ‖sargosPlanarSum T v (fun i => (s i-a)/σ)
      (fun i => logCurve (κ*σ/(1+κ*a)) ((s i-a)/σ)) (e (e.symm p)).1
        (e (e.symm p)).2‖ at h
    simpa only [e.apply_symm_apply] using h
  let f := fun p : ℝ × ℝ => W p*
    ‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖^2*
    ‖sargosPlanarSum V c y (fun i => logCurve κ (y i)) p.1 p.2‖^4
  calc
    _ = ∫ p : ℝ × ℝ, f (e.symm p) := by
      apply integral_congr_ae
      filter_upwards with p
      dsimp only [f]
      rw [hn S z x hx,hn V c y hy]
      rfl
    _ = _ := by simpa only [f,logCurveWeightedBilinearMoment,smul_eq_mul] using hint f

def logCurveWeightedSixNorm {ι : Type*} (κ : ℝ) (W : ℝ × ℝ → ℝ)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) : ℝ :=
  lpNorm (fun p : ℝ × ℝ => sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2)
    6 (volume.withDensity (fun p => ENNReal.ofReal (W p)))

private theorem logCurveWeighted_memLp {ι : Type*} (κ : ℝ) {W : ℝ × ℝ → ℝ}
    (hW : Integrable W) (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    MemLp (fun p : ℝ × ℝ => sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2)
      6 (volume.withDensity (fun p => ENNReal.ofReal (W p))) := by
  letI := isFiniteMeasure_withDensity_ofReal hW.2
  have hc : Continuous (fun p : ℝ × ℝ =>
      sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  exact MemLp.of_bound hc.aestronglyMeasurable (∑ i∈S, ‖z i‖)
    (Filter.Eventually.of_forall fun p =>
      norm_sargosPlanarSum_le_sum_norm S z x (fun i => logCurve κ (x i)) p.1 p.2)

theorem logCurveWeightedSixNorm_nonneg {ι : Type*} (κ : ℝ) (W : ℝ × ℝ → ℝ)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    0≤logCurveWeightedSixNorm κ W S z x := lpNorm_nonneg

theorem logCurveWeightedSixNorm_pow_six {ι : Type*} (κ : ℝ) (W : ℝ × ℝ → ℝ)
    (hW₀ : ∀ p, 0≤W p) (hW : Integrable W)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    (logCurveWeightedSixNorm κ W S z x)^6=logCurveWeightedBilinearMoment κ W S S z z x x := by
  unfold logCurveWeightedSixNorm
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (logCurveWeighted_memLp κ hW S z x).aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat,show (6:ℝ)=((6:ℕ):ℝ) from rfl,Real.rpow_natCast]
  simp only [one_div]
  have hroot (m : ℝ) (hm : 0 ≤ m) : (m^((6:ℝ)⁻¹))^6=m := by
    simpa only [Nat.cast_ofNat] using Real.rpow_inv_natCast_pow hm (by norm_num : (6:ℕ)≠0)
  rw [hroot _ (integral_nonneg fun _ => by positivity)]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hW.1.aemeasurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold logCurveWeightedBilinearMoment
  apply integral_congr_ae
  filter_upwards with p
  rw [ENNReal.toReal_ofReal (hW₀ p)]
  dsimp only [smul_eq_mul]
  norm_num only [Real.rpow_ofNat]
  ring

theorem logCurveWeightedSixNorm_sum_le {τ ι : Type*} (κ : ℝ) (J : Finset τ)
    (S : τ → Finset ι) (z : τ → ι → ℂ) (x : τ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW : Integrable W) :
    logCurveWeightedSixNorm κ W (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2)≤∑ i∈J, logCurveWeightedSixNorm κ W (S i) (z i) (x i) := by
  unfold logCurveWeightedSixNorm
  have he : (fun p : ℝ × ℝ => sargosPlanarSum (J.sigma S)
      (fun ij => z ij.1 ij.2) (fun ij => x ij.1 ij.2)
      (fun ij => logCurve κ (x ij.1 ij.2)) p.1 p.2)=
      ∑ i∈J, fun p : ℝ × ℝ =>
        sargosPlanarSum (S i) (z i) (x i) (fun k => logCurve κ (x i k)) p.1 p.2 := by
    ext p
    simp only [sargosPlanarSum,Finset.sum_sigma,Finset.sum_apply]
  rw [he]
  exact lpNorm_sum_le (fun i _ => logCurveWeighted_memLp κ hW (S i) (z i) (x i)) (by norm_num)

theorem logCurveWeightedSixNorm_sq_le_card {τ ι : Type*} (κ : ℝ) (J : Finset τ)
    (S : τ → Finset ι) (z : τ → ι → ℂ) (x : τ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW : Integrable W) :
    (logCurveWeightedSixNorm κ W (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2))^2≤
      (J.card:ℝ)*∑ i∈J, (logCurveWeightedSixNorm κ W (S i) (z i) (x i))^2 :=
  (pow_le_pow_left₀ (logCurveWeightedSixNorm_nonneg _ _ _ _ _)
    (logCurveWeightedSixNorm_sum_le κ J S z x W hW) 2).trans sq_sum_le_card_mul_sum_sq

theorem exists_logCurveWeightedSixNorm_rescale (κ a σ : ℝ)
    (hσ : σ≠0) (hA : 0<1+κ*a) :
    ∃ C : ℝ, 0<C ∧ ∀ (ι : Type) (W : ℝ × ℝ → ℝ),
      (∀ p, 0≤W p) → Integrable W → ∀ (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ),
      (∀ i∈S, 0<1+κ*x i) →
      logCurveWeightedSixNorm (κ*σ/(1+κ*a))
        (fun p => W (p.1/σ-(2*a*(1+κ*a)/σ^2)*p.2,((1+κ*a)^2/σ^2)*p.2))
        S z (fun i => (x i-a)/σ)=C*logCurveWeightedSixNorm κ W S z x := by
  obtain ⟨d,hd,hscale⟩ := exists_logCurveWeightedBilinearMoment_rescale κ a σ hσ hA
  let C := d^((6:ℝ)⁻¹)
  have hC : 0<C := Real.rpow_pos_of_pos hd _
  have hCpow : C^6=d := by
    simpa only [C,Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hd.le (by norm_num : (6:ℕ)≠0)
  refine ⟨C,hC,fun ι W hW₀ hW S z x hx => ?_⟩
  let e := logCurveRescaling κ a σ hσ hA.ne'
  let W' : ℝ × ℝ → ℝ := fun p => W (e.symm p)
  have hW' : Integrable W' := logCurve_rescaling_integrable e.symm hW
  have hW'₀ : ∀ p, 0≤W' p := fun p => hW₀ _
  change logCurveWeightedSixNorm (κ*σ/(1+κ*a)) W' S z (fun i => (x i-a)/σ)=
    C*logCurveWeightedSixNorm κ W S z x
  apply (pow_left_inj₀ (logCurveWeightedSixNorm_nonneg _ _ _ _ _)
    (mul_nonneg hC.le (logCurveWeightedSixNorm_nonneg _ _ _ _ _))
    (by norm_num : (6:ℕ)≠0)).mp
  rw [logCurveWeightedSixNorm_pow_six _ W' hW'₀ hW',mul_pow,hCpow,
    logCurveWeightedSixNorm_pow_six _ W hW₀ hW]
  exact hscale W S S z z x x hx hx

private theorem logCurveMoment_integrable {ι τ : Type*}
    (κ : ℝ) (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {W : ℝ × ℝ → ℝ} (hW : Integrable W) :
    Integrable (fun p : ℝ × ℝ => W p*
      ‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖^2*
      ‖sargosPlanarSum V c y (fun i => logCurve κ (y i)) p.1 p.2‖^4) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      ‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖^2*
      ‖sargosPlanarSum V c y (fun i => logCurve κ (y i)) p.1 p.2‖^4) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hb (p : ℝ × ℝ) :
      ‖‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖^2*
        ‖sargosPlanarSum V c y (fun i => logCurve κ (y i)) p.1 p.2‖^4‖≤
        (∑ i∈S, ‖z i‖)^2*(∑ j∈V, ‖c j‖)^4 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul
      (pow_le_pow_left₀ (norm_nonneg _) (norm_sargosPlanarSum_le_sum_norm S z x _ p.1 p.2) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (norm_sargosPlanarSum_le_sum_norm V c y _ p.1 p.2) 4)
      (by positivity) (by positivity)
  simpa only [mul_assoc] using hW.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- The actual logarithmic squared Hölder swap. Its integrability follows
from the finite source sums, and positivity yields the scalar discriminant. -/
theorem logCurveWeightedBilinearMoment_holder_swap {ι τ : Type*}
    (κ : ℝ) (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0≤W p) (hW : Integrable W)
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) :
    (logCurveWeightedBilinearMoment κ W S V z c x y)^2≤
      logCurveWeightedBilinearMoment κ W V S c z y x*
        logCurveWeightedBilinearMoment κ W V V c c y y := by
  let A := fun p : ℝ × ℝ => ‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖
  let B := fun p : ℝ × ℝ => ‖sargosPlanarSum V c y (fun i => logCurve κ (y i)) p.1 p.2‖
  let M := logCurveWeightedBilinearMoment κ W S V z c x y
  let N := logCurveWeightedBilinearMoment κ W V S c z y x
  let E := logCurveWeightedBilinearMoment κ W V V c c y y
  have hMi : Integrable (fun p => W p*(A p)^2*(B p)^4) :=
    logCurveMoment_integrable κ S V z c x y hW
  have hNi : Integrable (fun p => W p*(B p)^2*(A p)^4) :=
    logCurveMoment_integrable κ V S c z y x hW
  have hEi : Integrable (fun p => W p*(B p)^2*(B p)^4) :=
    logCurveMoment_integrable κ V V c c y y hW
  have hquad (t : ℝ) : 0≤N*(t*t)+(-2*M)*t+E := by
    have hp : 0≤∫ p : ℝ × ℝ, W p*(t*(A p)^2*B p-(B p)^3)^2 :=
      integral_nonneg (fun p => mul_nonneg (hW₀ p) (sq_nonneg _))
    have he (p : ℝ × ℝ) : W p*(t*(A p)^2*B p-(B p)^3)^2=
        t^2*(W p*(B p)^2*(A p)^4)-(2*t)*(W p*(A p)^2*(B p)^4)+
          W p*(B p)^2*(B p)^4 := by ring
    simp_rw [he] at hp
    have h1 : Integrable (fun p => t^2*(W p*(B p)^2*(A p)^4)) := hNi.const_mul _
    have h2 : Integrable (fun p => (2*t)*(W p*(A p)^2*(B p)^4)) := hMi.const_mul _
    have h12 : Integrable (fun p => t^2*(W p*(B p)^2*(A p)^4)-
        (2*t)*(W p*(A p)^2*(B p)^4)) := h1.sub h2
    rw [integral_add h12 hEi,integral_sub h1 h2,integral_const_mul,integral_const_mul] at hp
    change 0≤t^2*N-(2*t)*M+E at hp
    nlinarith only [hp]
  have hdisc := discrim_le_zero hquad
  unfold discrim at hdisc
  change M^2≤N*E
  nlinarith only [hdisc]

theorem logCurveWeightedBilinearMoment_le_sixNorm {ι τ : Type*}
    (κ : ℝ) (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0≤W p) (hW : Integrable W)
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) :
    logCurveWeightedBilinearMoment κ W S V z c x y≤
      (logCurveWeightedSixNorm κ W S z x)^2*(logCurveWeightedSixNorm κ W V c y)^4 := by
  let M := logCurveWeightedBilinearMoment κ W S V z c x y
  let N := logCurveWeightedBilinearMoment κ W V S c z y x
  let A := logCurveWeightedSixNorm κ W S z x
  let B := logCurveWeightedSixNorm κ W V c y
  have hM : 0≤M := integral_nonneg fun p =>
    mul_nonneg (mul_nonneg (hW₀ p) (sq_nonneg _)) (by positivity)
  have hA : 0≤A := logCurveWeightedSixNorm_nonneg _ _ _ _ _
  have hB : 0≤B := logCurveWeightedSixNorm_nonneg _ _ _ _ _
  have hMN : M^2≤N*B^6 := by
    simpa only [M,N,B,logCurveWeightedSixNorm_pow_six κ W hW₀ hW] using
      logCurveWeightedBilinearMoment_holder_swap κ W hW₀ hW S V z c x y
  have hNM : N^2≤M*A^6 := by
    simpa only [M,N,A,logCurveWeightedSixNorm_pow_six κ W hW₀ hW] using
      logCurveWeightedBilinearMoment_holder_swap κ W hW₀ hW V S c z y x
  have hfour : M^4≤M*A^6*B^12 := by
    calc
      M^4=(M^2)^2 := by ring
      _ ≤ (N*B^6)^2 := pow_le_pow_left₀ (sq_nonneg M) hMN 2
      _ = N^2*B^12 := by ring
      _ ≤ M*A^6*B^12 := mul_le_mul_of_nonneg_right hNM (pow_nonneg hB 12)
  change M≤A^2*B^4
  by_cases hz : M=0
  · rw [hz]
    positivity
  have hMp := lt_of_le_of_ne hM (Ne.symm hz)
  have hcube : M^3≤(A^2*B^4)^3 := by
    apply (mul_le_mul_iff_right₀ hMp).mp
    nlinarith only [hfour]
  exact (pow_le_pow_iff_left₀ hM (by positivity) (by norm_num : (3:ℕ)≠0)).mp hcube

/-- The uniform all-scale target for the specific log family; this definition
is not analytic provenance. The nontrivial dyadic bound remains to be proved. -/
def LogCurveDecouplingBound (n : ℕ) (D : ℝ) : Prop :=
  0≤D ∧ ∀ κ∈Icc (0:ℝ) (1/4), ∀ (ι : Type) (W : ℝ × ℝ → ℝ),
    LogCurveWeightBand κ (1/(n:ℝ)) W →
    ∀ (S : Fin n → Finset ι) (z : Fin n → ι → ℂ) (x : Fin n → ι → ℝ),
      (∀ j, ∀ k∈S j, x j k∈Icc ((j:ℕ)/(n:ℝ)) (((j:ℕ)+1)/(n:ℝ))) →
      (logCurveWeightedSixNorm κ W (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^2≤
        D^2*∑ j, (logCurveWeightedSixNorm κ W (S j) (z j) (x j))^2

theorem logCurveDecouplingBound_trivial (n : ℕ) : LogCurveDecouplingBound n (Real.sqrt n) := by
  refine ⟨Real.sqrt_nonneg _,fun κ _ ι W hW S z x _ => ?_⟩
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa only [Finset.card_univ,Fintype.card_fin] using
    logCurveWeightedSixNorm_sq_le_card κ Finset.univ S z x W hW.2.1

/-- A proved unit-grid bound implies the exact subinterval bound for the
same compact log family, with one common norm factor cancelling. -/
theorem LogCurveDecouplingBound.rescale {n : ℕ} {D κ a σ : ℝ}
    (hD : LogCurveDecouplingBound n D) (hκ : κ∈Icc (0:ℝ) (1/4))
    (hσ : 0<σ) (ha : 0≤a) (haσ : a+σ≤1)
    (ι : Type) (W : ℝ × ℝ → ℝ) (hW : LogCurveWeightBand κ (σ/(n:ℝ)) W)
    (S : Fin n → Finset ι) (z : Fin n → ι → ℂ) (x : Fin n → ι → ℝ)
    (hx : ∀ j, ∀ k∈S j,
      x j k∈Icc (a+σ*((j:ℕ)/(n:ℝ))) (a+σ*(((j:ℕ)+1)/(n:ℝ)))) :
    (logCurveWeightedSixNorm κ W (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^2≤
      D^2*∑ j, (logCurveWeightedSixNorm κ W (S j) (z j) (x j))^2 := by
  let W' : ℝ × ℝ → ℝ := fun p =>
    W (p.1/σ-(2*a*(1+κ*a)/σ^2)*p.2,((1+κ*a)^2/σ^2)*p.2)
  have hW' : LogCurveWeightBand (κ*σ/(1+κ*a)) (1/(n:ℝ)) W' := by
    have he : (σ/(n:ℝ))/σ=1/(n:ℝ) := by rw [div_right_comm,div_self hσ.ne']
    simpa only [he,W'] using hW.rescale hκ.1 hσ ha haσ
  have hx' (j : Fin n) (k : ι) (hk : k∈S j) :
      (x j k-a)/σ∈Icc ((j:ℕ)/(n:ℝ)) (((j:ℕ)+1)/(n:ℝ)) := by
    constructor
    · apply (le_div_iff₀ hσ).mpr
      nlinarith [(hx j k hk).1]
    · apply (div_le_iff₀ hσ).mpr
      nlinarith [(hx j k hk).2]
  have hxpos (j : Fin n) (k : ι) (hk : k∈S j) : 0<1+κ*x j k := by
    have hx₀ : 0≤x j k := by
      have hp : 0≤σ*((j:ℕ)/(n:ℝ)) := by positivity
      linarith [(hx j k hk).1]
    nlinarith [mul_nonneg hκ.1 hx₀]
  have h := hD.2 _ (logCurve_rescaled_parameter hκ ha ⟨hσ.le,by linarith⟩)
    ι W' hW' S z (fun j k => (x j k-a)/σ) hx'
  have hA : 0<1+κ*a := by nlinarith [mul_nonneg hκ.1 ha]
  obtain ⟨C,hC,hscale⟩ := exists_logCurveWeightedSixNorm_rescale κ a σ hσ.ne' hA
  have ht := hscale (Sigma fun _ : Fin n => ι) W hW.1 hW.2.1 (Finset.univ.sigma S)
    (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2)
    (fun jk hjk => hxpos jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
  have hi (j : Fin n) := hscale ι W hW.1 hW.2.1 (S j) (z j) (x j) (hxpos j)
  change logCurveWeightedSixNorm _ W' _ _ _ = _ at ht
  change ∀ j, logCurveWeightedSixNorm _ W' _ _ _ = _ at hi
  rw [ht] at h
  simp_rw [hi,mul_pow] at h
  rw [←Finset.mul_sum] at h
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hC)).mp
  nlinarith only [h]

/-- Actual finite asymmetric log-curve moments at two grid scales. This is
the recurrence contract, not an assumed logarithmic sixth-moment estimate. -/
def LogCurveBilinearSixBound (δ : ℝ) (p q : ℕ) (ν K : ℝ) : Prop :=
  0≤K ∧ ∀ κ∈Icc (0:ℝ) (1/4), ∀ (ι τ : Type) (W : ℝ × ℝ → ℝ),
    LogCurveWeightBand κ δ W → ∀ (a b : ℝ),
    0≤a → a+δ*p≤1 → 0≤b → b+δ*q≤1 →
    (a+δ*p+3*ν≤b ∨ b+δ*q+3*ν≤a) →
    ∀ (S : Fin p → Finset ι) (V : Fin q → Finset τ)
      (z : Fin p → ι → ℂ) (c : Fin q → τ → ℂ)
      (x : Fin p → ι → ℝ) (y : Fin q → τ → ℝ),
    (∀ j, ∀ k∈S j, x j k∈Icc (a+δ*(j:ℕ)) (a+δ*((j:ℕ)+1))) →
    (∀ j, ∀ k∈V j, y j k∈Icc (b+δ*(j:ℕ)) (b+δ*((j:ℕ)+1))) →
    logCurveWeightedBilinearMoment κ W (Finset.univ.sigma S) (Finset.univ.sigma V)
      (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
      (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)≤
      K*(∑ j, (logCurveWeightedSixNorm κ W (S j) (z j) (x j))^2)*
        (∑ j, (logCurveWeightedSixNorm κ W (V j) (c j) (y j))^2)^2

private theorem logCurve_grid_rescale_bound {n : ℕ} {D κ δ a : ℝ}
    (hn : 0<n) (hδ : 0<δ) (hD : LogCurveDecouplingBound n D)
    (hκ : κ∈Icc (0:ℝ) (1/4)) (ha : 0≤a) (haδ : a+δ*n≤1)
    (ι : Type) (W : ℝ × ℝ → ℝ) (hW : LogCurveWeightBand κ δ W)
    (S : Fin n → Finset ι) (z : Fin n → ι → ℂ) (x : Fin n → ι → ℝ)
    (hx : ∀ j, ∀ k∈S j, x j k∈Icc (a+δ*(j:ℕ)) (a+δ*((j:ℕ)+1))) :
    (logCurveWeightedSixNorm κ W (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^2≤
      D^2*∑ j, (logCurveWeightedSixNorm κ W (S j) (z j) (x j))^2 := by
  have hn' : (n:ℝ)≠0 := by positivity
  apply hD.rescale hκ (a:=a) (σ:=δ*n) (by positivity) ha haδ ι W
    (by simpa only [mul_div_cancel_right₀ _ hn'] using hW) S z x
  intro j k hk
  have h := hx j k hk
  have hleft : δ*n*((j:ℕ)/(n:ℝ))=δ*(j:ℕ) := by field_simp
  have hright : δ*n*(((j:ℕ)+1)/(n:ℝ))=δ*((j:ℕ)+1) := by field_simp
  simpa only [hleft,hright] using h

theorem logCurveBilinearSixBound_of_linear {p q : ℕ} {δ ν A B : ℝ}
    (hp : 0<p) (hq : 0<q) (hδ : 0<δ)
    (hA : LogCurveDecouplingBound p A) (hB : LogCurveDecouplingBound q B) :
    LogCurveBilinearSixBound δ p q ν (A^2*B^4) := by
  refine ⟨by positivity,fun κ hκ ι τ W hW a b ha haδ hb hbδ _ S V z c x y hx hy => ?_⟩
  have hS := logCurve_grid_rescale_bound hp hδ hA hκ ha haδ ι W hW S z x hx
  have hV := logCurve_grid_rescale_bound hq hδ hB hκ hb hbδ τ W hW V c y hy
  have hm := logCurveWeightedBilinearMoment_le_sixNorm κ W hW.1 hW.2.1
    (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)
  refine hm.trans ?_
  have hV₂ := pow_le_pow_left₀ (sq_nonneg _) hV 2
  have hs := mul_le_mul hS hV₂ (sq_nonneg _) (by positivity)
  convert hs using 1 <;> ring

theorem LogCurveBilinearSixBound.holder_swap {p q : ℕ} {δ ν K B : ℝ}
    (hq : 0<q) (hδ : 0<δ) (hK : LogCurveBilinearSixBound δ q p ν K)
    (hB : LogCurveDecouplingBound q B) :
    LogCurveBilinearSixBound δ p q ν (Real.sqrt K*B^3) := by
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hB.1 3),
    fun κ hκ ι τ W hW a b ha haδ hb hbδ hsep S V z c x y hx hy => ?_⟩
  let ES := ∑ j, (logCurveWeightedSixNorm κ W (S j) (z j) (x j))^2
  let EV := ∑ j, (logCurveWeightedSixNorm κ W (V j) (c j) (y j))^2
  let M := logCurveWeightedBilinearMoment κ W (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)
  let N := logCurveWeightedBilinearMoment κ W (Finset.univ.sigma V) (Finset.univ.sigma S)
    (fun jk => c jk.1 jk.2) (fun jk => z jk.1 jk.2)
    (fun jk => y jk.1 jk.2) (fun jk => x jk.1 jk.2)
  let Q := logCurveWeightedSixNorm κ W (Finset.univ.sigma V)
    (fun jk => c jk.1 jk.2) (fun jk => y jk.1 jk.2)
  have hES : 0≤ES := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEV : 0≤EV := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM : 0≤M := integral_nonneg fun r =>
    mul_nonneg (mul_nonneg (hW.1 r) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) 4)
  have hN : N≤K*EV*ES^2 :=
    hK.2 κ hκ τ ι W hW b a hb hbδ ha haδ hsep.symm V S c z y x hy hx
  have hQ : Q^2≤B^2*EV :=
    logCurve_grid_rescale_bound hq hδ hB hκ hb hbδ τ W hW V c y hy
  have hMN : M^2≤N*Q^6 := by
    simpa only [M,N,Q,logCurveWeightedSixNorm_pow_six κ W hW.1 hW.2.1] using
      logCurveWeightedBilinearMoment_holder_swap κ W hW.1 hW.2.1
        (Finset.univ.sigma S) (Finset.univ.sigma V)
        (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
        (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)
  have hQ₆ : Q^6≤B^6*EV^3 := by
    convert pow_le_pow_left₀ (sq_nonneg Q) hQ 3 using 1 <;> ring
  have hprod := mul_le_mul hN hQ₆ (by positivity : 0≤Q^6)
    (mul_nonneg (mul_nonneg hK.1 hEV) (sq_nonneg ES))
  have he : (Real.sqrt K*B^3*ES*EV^2)^2=(K*EV*ES^2)*(B^6*EV^3) := by
    rw [show (Real.sqrt K*B^3*ES*EV^2)^2=(Real.sqrt K)^2*B^6*ES^2*EV^4 by ring,
      Real.sq_sqrt hK.1]
    ring
  have hB₀ := hB.1
  change M≤Real.sqrt K*B^3*ES*EV^2
  apply (pow_le_pow_iff_left₀ hM (by positivity) (by norm_num : (2:ℕ)≠0)).mp
  rw [he]
  exact hMN.trans hprod

private theorem logCurve_product_sum {ι τ : Type*}
    (κ : ℝ) (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (α γ : ℝ) :
    sargosPlanarSum ((S ×ˢ V) ×ˢ V)
      (fun ij => z ij.1.1*c ij.1.2*c ij.2)
      (fun ij => x ij.1.1+y ij.1.2+y ij.2)
      (fun ij => logCurve κ (x ij.1.1)+logCurve κ (y ij.1.2)+logCurve κ (y ij.2)) α γ =
    sargosPlanarSum S z x (fun i => logCurve κ (x i)) α γ *
      (sargosPlanarSum V c y (fun k => logCurve κ (y k)) α γ)^2 := by
  rw [←planarSum_mul (S ×ˢ V) V (fun ij => z ij.1*c ij.2) c
    (fun ij => x ij.1+y ij.2) (fun ij => logCurve κ (x ij.1)+logCurve κ (y ij.2)) y
    (fun k => logCurve κ (y k)) α γ,
    ←planarSum_mul S V z c x (fun i => logCurve κ (x i)) y
      (fun k => logCurve κ (y k)) α γ]
  ring

private theorem logCurve_family_product_sum {ι τ : Type*}
    (κ : ℝ) (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
    (z : ℤ → ι → ℂ) (c : τ → ℂ)
    (x : ℤ → ι → ℝ) (y : τ → ℝ) (α γ : ℝ) :
    sargosPlanarSum (J.sigma (fun i => (S i ×ˢ V) ×ˢ V))
      (fun ij => z ij.1 ij.2.1.1*c ij.2.1.2*c ij.2.2)
      (fun ij => x ij.1 ij.2.1.1+y ij.2.1.2+y ij.2.2)
      (fun ij => logCurve κ (x ij.1 ij.2.1.1)+logCurve κ (y ij.2.1.2)+
        logCurve κ (y ij.2.2)) α γ =
    sargosPlanarSum (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2) (fun ij => logCurve κ (x ij.1 ij.2)) α γ *
      (sargosPlanarSum V c y (fun k => logCurve κ (y k)) α γ)^2 := by
  change (∑ ij ∈ J.sigma (fun i => (S i ×ˢ V) ×ˢ V), _) = _
  rw [Finset.sum_sigma]
  change (∑ i ∈ J, sargosPlanarSum ((S i ×ˢ V) ×ˢ V)
    (fun ij => z i ij.1.1*c ij.1.2*c ij.2)
    (fun ij => x i ij.1.1+y ij.1.2+y ij.2)
    (fun ij => logCurve κ (x i ij.1.1)+logCurve κ (y ij.1.2)+logCurve κ (y ij.2)) α γ) = _
  simp_rw [logCurve_product_sum]
  rw [←Finset.sum_mul]
  congr 1
  simp only [sargosPlanarSum,Finset.sum_sigma]

def logCurveBilinearMoment {ι τ : Type*}
    (κ : ℝ) (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (a b r t : ℝ) : ℝ :=
  ∫ α : ℝ, ∫ γ : ℝ,
    sargosSincKernel a (α-r)*sargosSincKernel b (γ-t)*
      ‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) α γ‖^2 *
      ‖sargosPlanarSum V c y (fun k => logCurve κ (y k)) α γ‖^4

private theorem logCurveMoment_flat {ι τ : Type*}
    (κ : ℝ) (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (a b r t : ℝ) :
    logCurveBilinearMoment κ S V z c x y a b r t =
      ∫ α : ℝ, ∫ γ : ℝ,
        sargosWeightedPlanarIntegrand ((S ×ˢ V) ×ˢ V)
          (fun ij => z ij.1.1*c ij.1.2*c ij.2)
          (fun ij => x ij.1.1+y ij.1.2+y ij.2)
          (fun ij => logCurve κ (x ij.1.1)+logCurve κ (y ij.1.2)+logCurve κ (y ij.2))
          a b r t α γ := by
  unfold logCurveBilinearMoment sargosWeightedPlanarIntegrand
  congr 1
  funext α
  congr 1
  funext γ
  rw [logCurve_product_sum,norm_mul,norm_pow]
  ring

private theorem logCurve_block_gap {i j : ℤ} {m : ℕ} {x x' d w ν : ℝ}
    (hm : 2/ν≤(m : ℝ))
    (hx : x∈Icc (d+w^2*(i : ℝ)) (d+w^2*((i : ℝ)+1)))
    (hx' : x'∈Icc (d+w^2*(j : ℝ)) (d+w^2*((j : ℝ)+1)))
    (hij : (m : ℤ) < |i-j|) :
    2*w^2/ν≤|x-x'| := by
  have hm' : 2*w^2/ν≤w^2*(m : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hm (sq_nonneg w)
    convert h using 1
    ring
  rcases le_total i j with h|h
  · have hji : (m : ℤ)+1 ≤ j-i := by
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hij
      omega
    have hji' : (m : ℝ)+1≤(j : ℝ)-(i : ℝ) := by exact_mod_cast hji
    have hp := mul_le_mul_of_nonneg_left hji' (sq_nonneg w)
    have hg : w^2*(m : ℝ)≤x'-x := by nlinarith [hx.2,hx'.1]
    exact (hm'.trans hg).trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · have hij' : (m : ℤ)+1 ≤ i-j := by
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hij
      omega
    have hij'' : (m : ℝ)+1≤(i : ℝ)-(j : ℝ) := by exact_mod_cast hij'
    have hp := mul_le_mul_of_nonneg_left hij'' (sq_nonneg w)
    have hg : w^2*(m : ℝ)≤x-x' := by nlinarith [hx.1,hx'.2]
    exact (hm'.trans hg).trans (le_abs_self _)

/-- Finite bilinear localization for the actual logarithmic curve.
The off-diagonal kernel is derived from its secants; no moment or
orthogonality hypothesis is supplied. Closed cells and multiplicities remain. -/
theorem logCurveBilinearMoment_localization {ι τ : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
    (z : ℤ → ι → ℂ) (c : τ → ℂ)
    (x : ℤ → ι → ℝ) (y : τ → ℝ)
    {κ w d u ν a b : ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4))
    (hw : 0<w) (hν : 0<ν) (hν₁ : ν≤1)
    (ha : 0<a) (hb : 0<b) (hwidth : b≤w^2)
    (hu : u≤ν) (hd : 3*ν≤|d|) (hl : -1≤d) (hr : d+u≤1)
    (hx : ∀ i∈J, ∀ k∈S i, x i k∈Icc d (d+u))
    (hy : ∀ k∈V, y k∈Icc 0 w)
    (hblock : ∀ i∈J, ∀ k∈S i,
      x i k∈Icc (d+w^2*(i : ℝ)) (d+w^2*((i : ℝ)+1)))
    (r t : ℝ) :
    logCurveBilinearMoment κ (J.sigma S) V
      (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y a b r t≤
      (7/ν)*∑ i∈J, logCurveBilinearMoment κ (S i) V (z i) c (x i) y a b r t := by
  classical
  let m := ⌈2/ν⌉₊
  have hm : 2/ν≤(m : ℝ) := Nat.le_ceil _
  have hceil : (m : ℝ)<2/ν+1 := Nat.ceil_lt_add_one (by positivity)
  have hfac : 2*(m : ℝ)+1≤7/ν := by
    have hn := (lt_div_iff₀ hν).mp (show (m : ℝ)-1<2/ν by linarith)
    apply (le_div_iff₀ hν).mpr
    nlinarith
  let F := fun i : ℤ => (S i ×ˢ V) ×ˢ V
  let Z := fun i : ℤ => fun ij : (ι × τ) × τ => z i ij.1.1*c ij.1.2*c ij.2
  let X := fun i : ℤ => fun ij : (ι × τ) × τ => x i ij.1.1+y ij.1.2+y ij.2
  let Y := fun i : ℤ => fun ij : (ι × τ) × τ =>
    logCurve κ (x i ij.1.1)+logCurve κ (y ij.1.2)+logCurve κ (y ij.2)
  have hmain := sargosPlanarFamily_banded_bound J F Z X Y ha hb r t m (by
    intro i hi j hj hij p hp q hq
    have hp' := Finset.mem_product.mp hp
    have hq' := Finset.mem_product.mp hq
    have hps := Finset.mem_product.mp hp'.1
    have hqs := Finset.mem_product.mp hq'.1
    have hgap := logCurve_block_gap hm (hblock i hi _ hps.1) (hblock j hj _ hqs.1) hij
    exact integral_logCurve_sixth_kernel_eq_zero hκ hw hν ha hb hwidth hu hd hl hr
      (hx i hi _ hps.1) (hx j hj _ hqs.1) (hy _ hps.2) (hy _ hp'.2)
      (hy _ hqs.2) (hy _ hq'.2) hgap r t)
  have heq : logCurveBilinearMoment κ (J.sigma S) V
      (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y a b r t=
      ∫ α : ℝ, ∫ γ : ℝ, sargosWeightedPlanarIntegrand (J.sigma F)
        (fun ij => Z ij.1 ij.2) (fun ij => X ij.1 ij.2) (fun ij => Y ij.1 ij.2)
        a b r t α γ := by
    unfold logCurveBilinearMoment sargosWeightedPlanarIntegrand
    congr 1
    funext α
    congr 1
    funext γ
    dsimp only [F,Z,X,Y]
    rw [logCurve_family_product_sum,norm_mul,norm_pow]
    ring
  rw [heq]
  have hsum : (∑ i∈J, ∫ α : ℝ, ∫ γ : ℝ,
      sargosWeightedPlanarIntegrand (F i) (Z i) (X i) (Y i) a b r t α γ)=
      ∑ i∈J, logCurveBilinearMoment κ (S i) V (z i) c (x i) y a b r t := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (logCurveMoment_flat _ _ _ _ _ _ _ _ _ _ _).symm
  rw [hsum] at hmain
  refine hmain.trans (mul_le_mul_of_nonneg_right hfac ?_)
  apply Finset.sum_nonneg
  intro i hi
  unfold logCurveBilinearMoment
  apply integral_nonneg
  intro α
  apply integral_nonneg
  intro γ
  exact mul_nonneg (mul_nonneg
    (mul_nonneg (sargosSincKernel_nonneg ha.le _) (sargosSincKernel_nonneg hb.le _))
    (sq_nonneg _)) (by positivity)

/-- Weighted finite localization for the actual rescaling-stable logarithmic
band. The Fourier cancellation is derived from its translated curve gap. -/
theorem logCurveWeightedBilinearMoment_localization_closed {ι τ : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
    (z : ℤ → ι → ℂ) (c : τ → ℂ)
    (x : ℤ → ι → ℝ) (y : τ → ℝ)
    {κ w a β u ν δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4)) (hW : LogCurveWeightBand κ δ W)
    (hw : 0<w) (hν : 0<ν) (hν₁ : ν≤1) (hβ : β∈Icc (0:ℝ) 1)
    (ha : 0≤a) (har : a+u≤1) (hwidth : δ^2≤w^2) (hu : u≤ν) (hd : 3*ν≤|a-β|)
    (hx : ∀ i∈J, ∀ k∈S i, x i k∈Icc a (a+u))
    (hy : ∀ k∈V, y k∈Icc β (β+w))
    (hblock : ∀ i∈J, ∀ k∈S i,
      x i k∈Icc (a+w^2*(i : ℝ)) (a+w^2*((i : ℝ)+1))) :
    logCurveWeightedBilinearMoment κ W (J.sigma S) V
      (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y≤
      (7/ν)*∑ i∈J, logCurveWeightedBilinearMoment κ W (S i) V (z i) c (x i) y := by
  classical
  let m := ⌈2/ν⌉₊
  have hm : 2/ν≤(m : ℝ) := Nat.le_ceil _
  have hceil : (m : ℝ)<2/ν+1 := Nat.ceil_lt_add_one (by positivity)
  have hfac : 2*(m : ℝ)+1≤7/ν := by
    have hn := (lt_div_iff₀ hν).mp (show (m : ℝ)-1<2/ν by linarith)
    apply (le_div_iff₀ hν).mpr
    nlinarith
  let F := fun i : ℤ => (S i ×ˢ V) ×ˢ V
  let Z := fun i : ℤ => fun ij : (ι × τ) × τ => z i ij.1.1*c ij.1.2*c ij.2
  let X := fun i : ℤ => fun ij : (ι × τ) × τ => x i ij.1.1+y ij.1.2+y ij.2
  let Y := fun i : ℤ => fun ij : (ι × τ) × τ =>
    logCurve κ (x i ij.1.1)+logCurve κ (y ij.1.2)+logCurve κ (y ij.2)
  have hmain := sargosWeightedPlanarFamily_banded_bound J F Z X Y W hW.1 hW.2.1 m (by
    intro i hi j hj hij p hp q hq
    apply hW.2.2
    have hp' := Finset.mem_product.mp hp
    have hq' := Finset.mem_product.mp hq
    have hps := Finset.mem_product.mp hp'.1
    have hqs := Finset.mem_product.mp hq'.1
    have hgap := logCurve_block_gap hm (hblock i hi _ hps.1) (hblock j hj _ hqs.1) hij
    exact logCurve_band_sixth_gap hκ hw hν hβ ha har hwidth hu hd
      (hx i hi _ hps.1) (hx j hj _ hqs.1) (hy _ hps.2) (hy _ hp'.2)
      (hy _ hqs.2) (hy _ hq'.2) hgap)
  have heq : logCurveWeightedBilinearMoment κ W (J.sigma S) V
      (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y=
      ∫ p : ℝ × ℝ, W p*‖sargosPlanarSum (J.sigma F)
        (fun ij => Z ij.1 ij.2) (fun ij => X ij.1 ij.2) (fun ij => Y ij.1 ij.2) p.1 p.2‖^2 := by
    unfold logCurveWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [F,Z,X,Y]
    rw [logCurve_family_product_sum,norm_mul,norm_pow]
    ring
  have hsingle (i : ℤ) : (∫ p : ℝ × ℝ,
      W p*‖sargosPlanarSum (F i) (Z i) (X i) (Y i) p.1 p.2‖^2)=
      logCurveWeightedBilinearMoment κ W (S i) V (z i) c (x i) y := by
    unfold logCurveWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [F,Z,X,Y]
    rw [logCurve_product_sum,norm_mul,norm_pow]
    ring
  rw [←heq] at hmain
  simp_rw [hsingle] at hmain
  refine hmain.trans (mul_le_mul_of_nonneg_right hfac ?_)
  apply Finset.sum_nonneg
  intro i hi
  unfold logCurveWeightedBilinearMoment
  exact integral_nonneg (fun p => mul_nonneg (mul_nonneg (hW.1 p) (sq_nonneg _)) (by positivity))

private theorem logCurve_finGrid_sum {k l : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin (k*l) → A) :
    ∑ r, f r=∑ i : Fin k, ∑ j : Fin l, f (finProdFinEquiv (i,j)) := by
  simpa only [Fintype.sum_prod_type] using (Equiv.sum_comp finProdFinEquiv f).symm

private def logCurveIntGridIndex (k : ℕ) (hk : 0 < k) (i : ℤ) : Fin k :=
  ⟨i.toNat % k,Nat.mod_lt _ hk⟩

private theorem logCurveIntGridIndex_cast {k : ℕ} (hk : 0 < k) (i : Fin k) :
    logCurveIntGridIndex k hk (i:ℕ) = i := by
  apply Fin.ext
  simp [logCurveIntGridIndex,Nat.mod_eq_of_lt i.isLt]

private theorem logCurveIntGridIndex_val {k : ℕ} (hk : 0 < k) {i : ℤ}
    (hi : i ∈ Finset.Ico 0 (k:ℤ)) :
    ((logCurveIntGridIndex k hk i : Fin k):ℕ) = i.toNat := by
  have hh := Finset.mem_Ico.mp hi
  simp only [logCurveIntGridIndex]
  exact Nat.mod_eq_of_lt (by omega)

private theorem logCurve_intGrid_sum {k : ℕ} (hk : 0 < k)
    {A : Type*} [AddCommMonoid A] (f : Fin k → A) :
    ∑ i ∈ Finset.Ico 0 (k:ℤ), f (logCurveIntGridIndex k hk i) = ∑ j, f j := by
  classical
  symm
  refine Finset.sum_bij (fun j _ => (j:ℤ)) ?_ ?_ ?_ ?_
  · intro j _
    dsimp only
    apply Finset.mem_Ico.mpr
    constructor
    · exact_mod_cast (Nat.zero_le (j:ℕ))
    · exact_mod_cast j.isLt
  · intro i _ j _ h
    dsimp only at h
    apply Fin.ext
    exact_mod_cast h
  · intro i hi
    have hh := Finset.mem_Ico.mp hi
    refine ⟨⟨i.toNat,by omega⟩,Finset.mem_univ _,?_⟩
    dsimp
    omega
  · intro i _
    rw [logCurveIntGridIndex_cast]

private theorem logCurveWeightedBilinearMoment_fin_localization {k : ℕ}
    (hk : 0 < k) {ι τ : Type*}
    (S : Fin k → Finset ι) (V : Finset τ)
    (z : Fin k → ι → ℂ) (c : τ → ℂ) (x : Fin k → ι → ℝ) (y : τ → ℝ)
    {κ w a β u ν δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hκ : κ∈Icc (0:ℝ) (1/4)) (hW : LogCurveWeightBand κ δ W)
    (hw : 0 < w) (hν : 0 < ν) (hν₁ : ν ≤ 1) (hβ : β ∈ Icc 0 1)
    (ha : 0≤a) (har : a+u≤1)
    (hwidth : δ^2 ≤ w^2) (hu : u ≤ ν) (hd : 3*ν ≤ |a-β|)
    (hx : ∀ i, ∀ v ∈ S i, x i v ∈ Icc a (a+u))
    (hy : ∀ v ∈ V, y v ∈ Icc β (β+w))
    (hblock : ∀ i, ∀ v ∈ S i,
      x i v ∈ Icc (a+w^2*(i:ℕ)) (a+w^2*((i:ℕ)+1))) :
    logCurveWeightedBilinearMoment κ W (Finset.univ.sigma S) V
      (fun iv => z iv.1 iv.2) c (fun iv => x iv.1 iv.2) y ≤
      (7/ν)*∑ i, logCurveWeightedBilinearMoment κ W (S i) V (z i) c (x i) y := by
  let R := logCurveIntGridIndex k hk
  let J := Finset.Ico 0 (k:ℤ)
  have hR (i : ℤ) (hi : i ∈ J) : ((R i:Fin k):ℝ) = (i:ℝ) := by
    have hv := logCurveIntGridIndex_val hk hi
    have hn : 0 ≤ i := (Finset.mem_Ico.mp hi).1
    change (((R i:Fin k):ℕ):ℝ) = _
    rw [hv]
    exact_mod_cast Int.toNat_of_nonneg hn
  have h := logCurveWeightedBilinearMoment_localization_closed J
    (fun i => S (R i)) V (fun i => z (R i)) c (fun i => x (R i)) y
    hκ hW hw hν hν₁ hβ ha har hwidth hu hd
    (fun i _ => hx (R i)) hy (fun i hi v hv => by
      simpa only [hR i hi] using hblock (R i) v hv)
  have he (α γ : ℝ) :
      sargosPlanarSum (J.sigma (fun i => S (R i)))
        (fun iv => z (R iv.1) iv.2) (fun iv => x (R iv.1) iv.2)
        (fun iv => logCurve κ (x (R iv.1) iv.2)) α γ =
      sargosPlanarSum (Finset.univ.sigma S) (fun iv => z iv.1 iv.2)
        (fun iv => x iv.1 iv.2) (fun iv => logCurve κ (x iv.1 iv.2)) α γ := by
    simp only [sargosPlanarSum,Finset.sum_sigma]
    exact logCurve_intGrid_sum hk (fun i => ∑ v ∈ S i,
      z i v*fordAdditiveCharacter (x i v*α+logCurve κ (x i v)*γ))
  have hm : logCurveWeightedBilinearMoment κ W (J.sigma (fun i => S (R i))) V
      (fun iv => z (R iv.1) iv.2) c (fun iv => x (R iv.1) iv.2) y =
      logCurveWeightedBilinearMoment κ W (Finset.univ.sigma S) V
        (fun iv => z iv.1 iv.2) c (fun iv => x iv.1 iv.2) y := by
    unfold logCurveWeightedBilinearMoment
    simp_rw [he]
  rw [hm] at h
  have hsum := logCurve_intGrid_sum hk (fun i =>
    logCurveWeightedBilinearMoment κ W (S i) V (z i) c (x i) y)
  change (∑ i ∈ J, logCurveWeightedBilinearMoment κ W (S (R i)) V (z (R i)) c (x (R i)) y) = _ at hsum
  rw [hsum] at h
  exact h

/-- Localization at the linked square scale consumes the smaller primary-grid
bound. The whole-interval separation and all original coefficients are retained. -/
theorem LogCurveBilinearSixBound.localization {k m q : ℕ} {δ ν K : ℝ}
    (hk : 0 < k) (hq : 0 < q) (hδ : 0 < δ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1)
    (hsmall : δ*(k*m) ≤ ν) (hscale : δ*m = (δ*q)^2)
    (hK : LogCurveBilinearSixBound δ m q ν K) :
    LogCurveBilinearSixBound δ (k*m) q ν ((7/ν)*K) := by
  refine ⟨mul_nonneg (by positivity) hK.1,
    fun κ hκ ι τ W hW a b ha haδ hb hbδ hsep S V z c x y hx hy => ?_⟩
  simp only [Nat.cast_mul] at haδ hsep
  let e : Fin k × Fin m ≃ Fin (k*m) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin m => S (e (i,j)))
  let Z := fun i : Fin k => fun jv : (j : Fin m) × ι => z (e (i,jv.1)) jv.2
  let X := fun i : Fin k => fun jv : (j : Fin m) × ι => x (e (i,jv.1)) jv.2
  let U := Finset.univ.sigma V
  let C := fun jv : (j : Fin q) × τ => c jv.1 jv.2
  let Y := fun jv : (j : Fin q) × τ => y jv.1 jv.2
  let ai := fun i : Fin k => a+δ*m*(i:ℕ)
  have heval (i : Fin k) (j : Fin m) :
      ((e (i,j):Fin (k*m)):ℝ) = (j:ℕ)+(m:ℝ)*(i:ℕ) := by
    simp [e,finProdFinEquiv,Nat.cast_add,Nat.cast_mul]
  have hai (i : Fin k) : a ≤ ai i ∧ ai i+δ*m ≤ a+δ*(k*m) := by
    have hi : ((i:ℕ):ℝ)+1 ≤ k := by exact_mod_cast i.isLt
    have hp := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ δ*m)
    have hzero : 0 ≤ δ*m*(i:ℕ) := by positivity
    dsimp only [ai]
    constructor
    · linarith
    · nlinarith only [hp]
  have hfine (i : Fin k) (j : Fin m) (v : ι) (hv : v ∈ S (e (i,j))) :
      x (e (i,j)) v ∈ Icc (ai i+δ*(j:ℕ)) (ai i+δ*((j:ℕ)+1)) := by
    have hf := hx (e (i,j)) v hv
    change x (e (i,j)) v ∈ Icc (a+δ*((e (i,j):Fin (k*m)):ℝ))
      (a+δ*(((e (i,j):Fin (k*m)):ℝ)+1)) at hf
    rw [heval] at hf
    dsimp only [ai]
    constructor <;> nlinarith [hf.1,hf.2]
  have hblock (i : Fin k) (v : (j : Fin m) × ι) (hv : v ∈ T i) :
      X i v ∈ Icc (ai i) (ai i+δ*m) := by
    have hf := hfine i v.1 v.2 (Finset.mem_sigma.mp hv).2
    have hj : ((v.1:ℕ):ℝ)+1 ≤ m := by exact_mod_cast v.1.isLt
    have hp := mul_le_mul_of_nonneg_left hj hδ.le
    have hn : 0 ≤ δ*(v.1:ℕ) := by positivity
    constructor <;> dsimp only [X] <;> nlinarith [hf.1,hf.2]
  have hglobal (i : Fin k) (v : (j : Fin m) × ι) (hv : v ∈ T i) :
      X i v ∈ Icc a (a+δ*(k*m)) :=
    ⟨(hai i).1.trans (hblock i v hv).1,(hblock i v hv).2.trans (hai i).2⟩
  have hsecondary (v : (j : Fin q) × τ) (hv : v ∈ U) :
      Y v ∈ Icc b (b+δ*q) := by
    have hf := hy v.1 v.2 (Finset.mem_sigma.mp hv).2
    have hj : ((v.1:ℕ):ℝ)+1 ≤ q := by exact_mod_cast v.1.isLt
    have hp := mul_le_mul_of_nonneg_left hj hδ.le
    have hn : 0 ≤ δ*(v.1:ℕ) := by positivity
    constructor <;> dsimp only [Y] <;> nlinarith [hf.1,hf.2]
  have hd : 3*ν ≤ |a-b| := by
    rcases hsep with hs | hs
    · have hz : 0 ≤ δ*(k*m) := by positivity
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hz : 0 ≤ δ*q := by positivity
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hwidth : δ^2 ≤ (δ*q)^2 :=
    pow_le_pow_left₀ hδ.le (by nlinarith) 2
  have hloc := logCurveWeightedBilinearMoment_fin_localization hk T U Z C X Y
    hκ hW (by positivity : 0 < δ*q) hν hν₁
    (show b ∈ Icc 0 1 from ⟨hb,by nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg q)]⟩)
    ha haδ hwidth hsmall hd hglobal hsecondary (fun i v hv => by
      have h := hblock i v hv
      dsimp only [ai] at h
      simpa only [← hscale,mul_add,mul_one,mul_assoc,add_assoc] using h)

  let EV := ∑ j, (logCurveWeightedSixNorm κ W (V j) (c j) (y j))^2
  have hpiece (i : Fin k) :
      logCurveWeightedBilinearMoment κ W (T i) U (Z i) C (X i) Y ≤
        K*(∑ j : Fin m,
          (logCurveWeightedSixNorm κ W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2)*EV^2 := by
    have hsep' : ai i+δ*m+3*ν ≤ b ∨ b+δ*q+3*ν ≤ ai i := by
      rcases hsep with hs | hs
      · exact Or.inl (by linarith [(hai i).2])
      · exact Or.inr (by linarith [(hai i).1])
    exact hK.2 κ hκ ι τ W hW (ai i) b (ha.trans (hai i).1) ((hai i).2.trans haδ)
      hb hbδ hsep' (fun j => S (e (i,j))) V (fun j => z (e (i,j))) c
      (fun j => x (e (i,j))) y (hfine i) hy
  have ht :
      logCurveWeightedBilinearMoment κ W (Finset.univ.sigma S) U
        (fun rv => z rv.1 rv.2) C (fun rv => x rv.1 rv.2) Y =
      logCurveWeightedBilinearMoment κ W (Finset.univ.sigma T) U
        (fun iv => Z iv.1 iv.2) C (fun iv => X iv.1 iv.2) Y := by
    unfold logCurveWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with r
    have he :
        sargosPlanarSum (Finset.univ.sigma S) (fun rv => z rv.1 rv.2)
          (fun rv => x rv.1 rv.2) (fun rv => logCurve κ (x rv.1 rv.2)) r.1 r.2 =
        sargosPlanarSum (Finset.univ.sigma T) (fun iv => Z iv.1 iv.2)
          (fun iv => X iv.1 iv.2) (fun iv => logCurve κ (X iv.1 iv.2)) r.1 r.2 := by
      simp only [sargosPlanarSum,Finset.sum_sigma,T,Z,X]
      exact logCurve_finGrid_sum _
    rw [he]
  change logCurveWeightedBilinearMoment κ W (Finset.univ.sigma S) U
    (fun rv => z rv.1 rv.2) C (fun rv => x rv.1 rv.2) Y ≤ _
  rw [ht]
  refine hloc.trans ?_
  have hp := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hpiece i)
  have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 7/ν)
  have he : (∑ i : Fin k, K*(∑ j : Fin m,
      (logCurveWeightedSixNorm κ W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2)*EV^2) =
      K*(∑ r, (logCurveWeightedSixNorm κ W (S r) (z r) (x r))^2)*EV^2 := by
    rw [← Finset.sum_mul,← Finset.mul_sum,logCurve_finGrid_sum]
  rw [he] at hp'
  simpa only [EV,mul_assoc] using hp'

/-- The linked localization/Holder step consumes the genuinely swapped
smaller-grid bound, rather than the original interval conclusion. -/
theorem LogCurveBilinearSixBound.localization_holder {k m q : ℕ} {δ ν K B : ℝ}
    (hk : 0 < k) (hq : 0 < q) (hδ : 0 < δ) (hν : 0 < ν) (hν₁ : ν ≤ 1)
    (hsmall : δ*(k*m) ≤ ν) (hscale : δ*m = (δ*q)^2)
    (hK : LogCurveBilinearSixBound δ q m ν K)
    (hB : LogCurveDecouplingBound q B) :
    LogCurveBilinearSixBound δ (k*m) q ν ((7/ν)*(Real.sqrt K*B^3)) :=
  (hK.holder_swap hq hδ hB).localization hk hq hδ hν hν₁ hsmall hscale

private theorem logCurve_dyadic_width_mul_cells {a n : ℕ} (ha : a ≤ n) :
    (1/(2:ℝ)^n)*(2:ℝ)^(n-a) = 1/(2:ℝ)^a := by
  rw [pow_sub₀ (2:ℝ) (by norm_num) ha]
  field_simp

private theorem logCurve_dyadic_width_sq (b : ℕ) :
    (1/(2:ℝ)^b)^2 = 1/(2:ℝ)^(2*b) := by
  rw [div_pow,one_pow,← pow_mul]
  congr 2
  omega

/-- The actual square-scale recurrence on exact dyadic grids. -/
theorem LogCurveBilinearSixBound.dyadic_step {n a b r : ℕ} {K B : ℝ}
    (ha : a ≤ 2*b) (hb : 2*b ≤ n) (hr : r ≤ a)
    (hK : LogCurveBilinearSixBound (1/(2:ℝ)^n)
      (2^(n-b)) (2^(n-2*b)) (1/(2:ℝ)^r) K)
    (hB : LogCurveDecouplingBound (2^(n-b)) B) :
    LogCurveBilinearSixBound (1/(2:ℝ)^n)
      (2^(n-a)) (2^(n-b)) (1/(2:ℝ)^r)
      ((7/(1/(2:ℝ)^r))*(Real.sqrt K*B^3)) := by
  have hcount : (2:ℕ)^(2*b-a)*2^(n-2*b) = 2^(n-a) := by
    rw [← pow_add]
    congr 1
    omega
  have hsmall : (1/(2:ℝ)^n)*((2:ℕ)^(2*b-a)*(2:ℕ)^(n-2*b)) ≤ 1/(2:ℝ)^r := by
    push_cast
    rw [← pow_add,show (2*b-a)+(n-2*b) = n-a by omega,
      logCurve_dyadic_width_mul_cells (ha.trans hb)]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hr)
  have hscale : (1/(2:ℝ)^n)*(((2:ℕ)^(n-2*b):ℕ):ℝ) =
      ((1/(2:ℝ)^n)*(((2:ℕ)^(n-b):ℕ):ℝ))^2 := by
    push_cast
    rw [logCurve_dyadic_width_mul_cells hb,logCurve_dyadic_width_mul_cells (by omega : b ≤ n),
      logCurve_dyadic_width_sq]
  have hν₁ : 1/(2:ℝ)^r ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^r)).mpr
    simpa only [one_mul] using one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=r)
  have h := hK.localization_holder (k:=2^(2*b-a)) (by positivity) (by positivity)
    (by positivity) (by positivity) hν₁ (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hsmall) hscale hB
  simpa only [hcount] using h


theorem logCurveBilinearSixBound_dyadic_iterate (D : ℕ → ℝ)
    {n r a b t : ℕ} (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (hb : b*2^t ≤ n)
    (hD : ∀ j < n, LogCurveDecouplingBound (2^j) (D j)) :
    LogCurveBilinearSixBound (1/(2:ℝ)^n) (2^(n-a)) (2^(n-b))
      (1/(2:ℝ)^r) (parabolaDyadicBilinearBudget D n r t a b) := by
  induction t generalizing a b with
  | zero =>
    simp only [pow_zero,mul_one] at hb
    exact logCurveBilinearSixBound_of_linear (by positivity) (by positivity)
      (by positivity) (hD (n-a) (by omega)) (hD (n-b) (by omega))
  | succ t ih =>
    have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
    have he : (2*b)*2^t = b*2^(t+1) := by rw [pow_succ]; ring
    have hnext : (2*b)*2^t ≤ n := by rw [he]; exact hb
    have hb₂ : 2*b ≤ n :=
      (show 2*b ≤ (2*b)*2^t by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hpow (Nat.zero_le (2*b))).trans hnext
    have hprev := ih (hra.trans hab) (by omega : b ≤ 2*b) hnext
    have h := hprev.dyadic_step (a:=a) (by omega) hb₂ hra (hD (n-b) (by omega))
    simpa only [parabolaDyadicBilinearBudget] using h

theorem logCurveWeightedSixNorm_bilinear_reduction {ι : Type*}
    (κ : ℝ)
    (J : Finset ℤ) (S : ℤ → Finset ι) (z : ℤ → ι → ℂ) (x : ℤ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W) :
    (logCurveWeightedSixNorm κ W (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2))^6 ≤
      (64*7^6:ℝ)*∑ i ∈ J, (logCurveWeightedSixNorm κ W (S i) (z i) (x i))^6 +
      64*(J.card:ℝ)^5*∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|),
        logCurveWeightedBilinearMoment κ W (S j) (S i) (z j) (z i) (x j) (x i) := by
  classical
  let F := fun i => fun p : ℝ × ℝ =>
    sargosPlanarSum (S i) (z i) (x i) (fun k => logCurve κ (x i k)) p.1 p.2
  let G := fun i j => fun p : ℝ × ℝ => W p*‖F i p‖^2*‖F j p‖^4
  let T := J.sigma S
  let Z := fun ij : (i : ℤ) × ι => z ij.1 ij.2
  let X := fun ij : (i : ℤ) × ι => x ij.1 ij.2
  let H := fun p : ℝ × ℝ => W p*
    ‖sargosPlanarSum T Z X (fun ij => logCurve κ (X ij)) p.1 p.2‖^2*
    ‖sargosPlanarSum T Z X (fun ij => logCurve κ (X ij)) p.1 p.2‖^4
  have hG (i j : ℤ) : Integrable (G i j) := by
    simpa only [G,F,mul_assoc] using
      logCurveMoment_integrable κ (S i) (S j) (z i) (z j) (x i) (x j) hW
  have hH : Integrable H := by
    simpa only [H,mul_assoc] using
      logCurveMoment_integrable κ T T Z Z X X hW
  have hs (p : ℝ × ℝ) :
      sargosPlanarSum T Z X (fun ij => logCurve κ (X ij)) p.1 p.2 = ∑ i ∈ J, F i p := by
    simp only [T,Z,X,F,sargosPlanarSum,Finset.sum_sigma]
  have hpoint (p : ℝ × ℝ) :
      H p ≤ (64*7^6:ℝ)*(∑ i ∈ J, G i i p) +
        64*(J.card:ℝ)^5*(∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), G j i p) := by
    have hp := mul_le_mul_of_nonneg_left
      (parabola_bilinear_reduction_pointwise J (fun i => F i p)) (hW₀ p)
    have he (v : ℂ) : ‖v‖^6 = ‖v‖^2*‖v‖^4 := by ring
    dsimp only [H]
    rw [hs]
    simp_rw [he] at hp
    have hd : W p*((64*7^6:ℝ)*∑ i ∈ J, ‖F i p‖^2*‖F i p‖^4) =
        (64*7^6:ℝ)*∑ i ∈ J, G i i p := by
      rw [← mul_assoc,mul_comm (W p),mul_assoc,Finset.mul_sum]
      simp only [G,mul_assoc]
    have hc : W p*(64*(J.card:ℝ)^5*
        ∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), ‖F j p‖^2*‖F i p‖^4) =
        64*(J.card:ℝ)^5*
          ∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), G j i p := by
      rw [← mul_assoc,mul_comm (W p),mul_assoc]
      simp only [Finset.mul_sum,G,mul_assoc]
    rw [mul_add,hd,hc] at hp
    simpa only [mul_assoc] using hp
  have hdiag : Integrable (fun p => ∑ i ∈ J, G i i p) :=
    integrable_finsetSum J (fun i _ => hG i i)
  have hcross : Integrable (fun p => ∑ i ∈ J,
      ∑ j ∈ J.filter (fun j => 3 < |i-j|), G j i p) :=
    integrable_finsetSum J (fun i _ =>
      integrable_finsetSum _ (fun j _ => hG j i))
  have h := integral_mono hH
    ((hdiag.const_mul (64*7^6:ℝ)).add (hcross.const_mul (64*(J.card:ℝ)^5))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (hdiag.const_mul _) (hcross.const_mul _),
    integral_const_mul,integral_const_mul,
    integral_finsetSum J (fun i _ => hG i i),
    integral_finsetSum J (fun i _ => integrable_finsetSum _ (fun j _ => hG j i))] at h
  simp_rw [integral_finsetSum _ (fun j _ => hG j _)] at h
  simpa only [logCurveWeightedSixNorm_pow_six κ W hW₀ hW,
    logCurveWeightedBilinearMoment,H,T,Z,X,G,F] using h

private theorem logCurve_finGrid_cell {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (i : Fin k) (j : Fin l) :
    ((finProdFinEquiv (i,j) : Fin (k*l)):ℕ)/(k*l:ℝ) =
      (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*((j:ℕ)/(l:ℝ)) ∧
    (((finProdFinEquiv (i,j) : Fin (k*l)):ℕ)+1)/(k*l:ℝ) =
      (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*(((j:ℕ)+1)/(l:ℝ)) := by
  have hk' : (k:ℝ) ≠ 0 := by positivity
  have hl' : (l:ℝ) ≠ 0 := by positivity
  simp only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.cast_add,Nat.cast_mul]
  constructor <;> field_simp <;> ring

private theorem logCurve_sum_nonneg_powers_le {ι : Type*} (J : Finset ι) (E : ι → ℝ)
    (hE : ∀ i ∈ J, 0 ≤ E i) {n : ℕ} (hn : n ≠ 0) :
    ∑ i ∈ J, (E i)^n ≤ (∑ i ∈ J, E i)^n := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [zero_pow hn]
  | @insert a J ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    have hJ : ∀ i ∈ J, 0 ≤ E i := fun i hi => hE i (Finset.mem_insert_of_mem hi)
    calc
      E a^n+(∑ i ∈ J, (E i)^n) ≤ E a^n+(∑ i ∈ J, E i)^n :=
        add_le_add le_rfl (ih hJ)
      _ ≤ _ := pow_add_pow_le (hE a (Finset.mem_insert_self a J))
        (Finset.sum_nonneg hJ) hn

private theorem logCurveWeightedSixNorm_bilinear_budget {ι : Type*}
    (κ : ℝ)
    (J : Finset ℤ) (S : ℤ → Finset ι) (z : ℤ → ι → ℂ) (x : ℤ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W)
    (E : ℤ → ℝ) (A K : ℝ) (hE : ∀ i ∈ J, 0 ≤ E i) (hK : 0 ≤ K)
    (hdiag : ∀ i ∈ J, (logCurveWeightedSixNorm κ W (S i) (z i) (x i))^2 ≤ A^2*E i)
    (hfar : ∀ i ∈ J, ∀ j ∈ J, 3 < |i-j| →
      logCurveWeightedBilinearMoment κ W (S j) (S i) (z j) (z i) (x j) (x i) ≤ K*E j*(E i)^2) :
    (logCurveWeightedSixNorm κ W (J.sigma S)
      (fun iv => z iv.1 iv.2) (fun iv => x iv.1 iv.2))^6 ≤
      ((64*7^6:ℝ)*A^6+64*(J.card:ℝ)^5*K)*(∑ i ∈ J, E i)^3 := by
  have hmain := logCurveWeightedSixNorm_bilinear_reduction κ J S z x W hW₀ hW
  have hds : (∑ i ∈ J, (logCurveWeightedSixNorm κ W (S i) (z i) (x i))^6) ≤
      A^6*(∑ i ∈ J, E i)^3 := by
    calc
      _ ≤ ∑ i ∈ J, A^6*(E i)^3 := by
        apply Finset.sum_le_sum
        intro i hi
        convert pow_le_pow_left₀ (sq_nonneg _) (hdiag i hi) 3 using 1 <;> ring
      _ = A^6*∑ i ∈ J, (E i)^3 := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (logCurve_sum_nonneg_powers_le J E hE (by norm_num : (3:ℕ) ≠ 0)) (by positivity)
  have hc (i : ℤ) (hi : i ∈ J) :
      (∑ j ∈ J.filter (fun j => 3 < |i-j|),
        logCurveWeightedBilinearMoment κ W (S j) (S i) (z j) (z i) (x j) (x i)) ≤
      K*(∑ j ∈ J, E j)*(E i)^2 := by
    calc
      _ ≤ ∑ j ∈ J.filter (fun j => 3 < |i-j|), K*E j*(E i)^2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact hfar i hi j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
      _ ≤ ∑ j ∈ J, K*E j*(E i)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j hj _ => mul_nonneg (mul_nonneg hK (hE j hj)) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul,← Finset.mul_sum]
  have hcs : (∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|),
      logCurveWeightedBilinearMoment κ W (S j) (S i) (z j) (z i) (x j) (x i)) ≤
      K*(∑ i ∈ J, E i)^3 := by
    calc
      _ ≤ ∑ i ∈ J, K*(∑ j ∈ J, E j)*(E i)^2 := Finset.sum_le_sum hc
      _ = (K*(∑ j ∈ J, E j))*∑ i ∈ J, (E i)^2 := (Finset.mul_sum ..).symm
      _ ≤ (K*(∑ j ∈ J, E j))*(∑ i ∈ J, E i)^2 :=
        mul_le_mul_of_nonneg_left
          (logCurve_sum_nonneg_powers_le J E hE (by norm_num : (2:ℕ) ≠ 0))
          (mul_nonneg hK (Finset.sum_nonneg hE))
      _ = _ := by ring
  have hd := mul_le_mul_of_nonneg_left hds (by positivity : (0:ℝ) ≤ 64*7^6)
  have hf := mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ 64*(J.card:ℝ)^5)
  nlinarith only [hmain,hd,hf]

private theorem logCurve_sixth_budget_to_square {L E A K k : ℝ}
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hK : 0 ≤ K) (hk : 1 ≤ k)
    (h : L^6 ≤ ((64*7^6:ℝ)*A^6+64*k^5*K)*E^3) :
    L^2 ≤ (14*A+2*k*K^((6:ℝ)⁻¹))^2*E := by
  let R := K^((6:ℝ)⁻¹)
  have hR : 0 ≤ R := Real.rpow_nonneg hK _
  have hR₆ : R^6 = K := by
    simpa only [R,Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hK (by norm_num : (6:ℕ) ≠ 0)
  have hk₀ : 0 ≤ k := by linarith
  have hkp : k^5 ≤ k^6 := by
    have hp := mul_le_mul_of_nonneg_left hk (pow_nonneg hk₀ 5)
    simpa only [mul_one,← pow_succ] using hp
  have hab := pow_add_pow_le (by positivity : 0 ≤ 14*A)
    (by positivity : 0 ≤ 2*k*R) (by norm_num : (6:ℕ) ≠ 0)
  have hb : (64*7^6:ℝ)*A^6+64*k^5*K ≤ (14*A+2*k*R)^6 := by
    have he : (14*A)^6+(2*k*R)^6 = (64*7^6:ℝ)*A^6+64*k^6*K := by
      rw [mul_pow, mul_pow, mul_pow,hR₆]
      ring
    rw [he] at hab
    have hp := mul_le_mul_of_nonneg_right hkp (mul_nonneg (by norm_num : (0:ℝ) ≤ 64) hK)
    nlinarith only [hab,hp]
  have hc := h.trans (mul_le_mul_of_nonneg_right hb (pow_nonneg hE 3))
  apply (pow_le_pow_iff_left₀ (sq_nonneg L) (by positivity)
    (by norm_num : (3:ℕ) ≠ 0)).mp
  change (L^2)^3 ≤ ((14*A+2*k*R)^2*E)^3
  convert hc using 1 <;> ring

/-- The genuine coarse/fine grid and whole-interval bilinear contracts imply
the linear bound, with an explicit constant and no target-grid assumption. -/
theorem LogCurveDecouplingBound.of_bilinear {k l : ℕ} {A K : ℝ}
    (hk : 0 < k) (hl : 0 < l) (hA : LogCurveDecouplingBound l A)
    (hK : LogCurveBilinearSixBound (1/((k*l:ℕ):ℝ)) l l (1/(k:ℝ)) K) :
    LogCurveDecouplingBound (k*l) (14*A+2*k*K^((6:ℝ)⁻¹)) := by
  have hA₀ := hA.1
  have hK₀ := hK.1
  refine ⟨by positivity,fun κ hκ ι W hW S z x hx => ?_⟩
  let δ : ℝ := 1/((k*l:ℕ):ℝ)
  let e : Fin k × Fin l ≃ Fin (k*l) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => S (e (i,j)))
  let Z := fun i : Fin k => fun jv : (j : Fin l) × ι => z (e (i,jv.1)) jv.2
  let X := fun i : Fin k => fun jv : (j : Fin l) × ι => x (e (i,jv.1)) jv.2
  let E := fun i : Fin k => ∑ j : Fin l,
    (logCurveWeightedSixNorm κ W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2
  let ai := fun i : Fin k => (i:ℕ)/(k:ℝ)
  let R := logCurveIntGridIndex k hk
  let J := Finset.Ico 0 (k:ℤ)
  have hk' : (0:ℝ) < k := by positivity
  have hl' : (0:ℝ) < l := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδl : δ*l = 1/(k:ℝ) := by
    dsimp [δ]
    push_cast
    field_simp
  have hfine (i : Fin k) (j : Fin l) (v : ι) (hv : v ∈ S (e (i,j))) :
      x (e (i,j)) v ∈ Icc (ai i+δ*(j:ℕ)) (ai i+δ*((j:ℕ)+1)) := by
    have h := hx (e (i,j)) v hv
    simp only [Nat.cast_mul] at h
    have hcell := logCurve_finGrid_cell hk hl i j
    change x (e (i,j)) v ∈ Icc
      (((e (i,j):Fin (k*l)):ℝ)/(k*l:ℝ))
      ((((e (i,j):Fin (k*l)):ℝ)+1)/(k*l:ℝ)) at h
    rw [hcell.1,hcell.2] at h
    convert h using 1
    dsimp [ai,δ]
    push_cast
    field_simp
  have hai (i : Fin k) : 0 ≤ ai i := by dsimp [ai]; positivity
  have htop (i : Fin k) : ai i+δ*l ≤ 1 := by
    rw [hδl]
    dsimp only [ai]
    rw [← add_div]
    apply (div_le_iff₀ hk').mpr
    simpa only [one_mul] using
      (show ((i:ℕ):ℝ)+1 ≤ k by exact_mod_cast i.isLt)
  have hlin (i : Fin k) :
      (logCurveWeightedSixNorm κ W (T i) (Z i) (X i))^2 ≤ A^2*E i :=
    logCurve_grid_rescale_bound hl hδ hA hκ (hai i) (htop i) ι W hW
      (fun j => S (e (i,j))) (fun j => z (e (i,j))) (fun j => x (e (i,j))) (hfine i)
  have hR (i : ℤ) (hi : i ∈ J) : ((R i:Fin k):ℝ) = (i:ℝ) := by
    have hv := logCurveIntGridIndex_val hk hi
    have hn : 0 ≤ i := (Finset.mem_Ico.mp hi).1
    change (((R i:Fin k):ℕ):ℝ) = _
    rw [hv]
    exact_mod_cast Int.toNat_of_nonneg hn
  have hfar (i : ℤ) (hi : i ∈ J) (j : ℤ) (hj : j ∈ J) (hij : 3 < |i-j|) :
      logCurveWeightedBilinearMoment κ W (T (R j)) (T (R i))
        (Z (R j)) (Z (R i)) (X (R j)) (X (R i)) ≤ K*E (R j)*(E (R i))^2 := by
    have hsep : ai (R j)+δ*l+3*(1/(k:ℝ)) ≤ ai (R i) ∨
        ai (R i)+δ*l+3*(1/(k:ℝ)) ≤ ai (R j) := by
      dsimp only [ai]
      rw [hδl,hR i hi,hR j hj]
      rcases le_total i j with h | h
      · right
        have hh : i+4 ≤ j := by
          rw [abs_of_nonpos (sub_nonpos.mpr h)] at hij
          omega
        have hh' : (i:ℝ)+4 ≤ j := by exact_mod_cast hh
        convert div_le_div_of_nonneg_right hh' hk'.le using 1
        ring
      · left
        have hh : j+4 ≤ i := by
          rw [abs_of_nonneg (sub_nonneg.mpr h)] at hij
          omega
        have hh' : (j:ℝ)+4 ≤ i := by exact_mod_cast hh
        convert div_le_div_of_nonneg_right hh' hk'.le using 1
        ring
    exact hK.2 κ hκ ι ι W hW (ai (R j)) (ai (R i)) (hai _) (htop _) (hai _) (htop _) hsep
      (fun v => S (e (R j,v))) (fun v => S (e (R i,v)))
      (fun v => z (e (R j,v))) (fun v => z (e (R i,v)))
      (fun v => x (e (R j,v))) (fun v => x (e (R i,v))) (hfine (R j)) (hfine (R i))

  have hE : ∀ i ∈ J, 0 ≤ E (R i) := fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbudget := logCurveWeightedSixNorm_bilinear_budget κ J
    (fun i => T (R i)) (fun i => Z (R i)) (fun i => X (R i)) W hW.1 hW.2.1
    (fun i => E (R i)) A K hE hK.1 (fun i _ => hlin (R i)) hfar
  have hcard : (J.card:ℝ) = k := by simp [J,Int.card_Ico]
  rw [hcard] at hbudget
  have hsq := logCurve_sixth_budget_to_square (Finset.sum_nonneg hE) hA.1 hK.1
    (show (1:ℝ) ≤ k by exact_mod_cast hk) hbudget
  have hsum : (∑ i ∈ J, E (R i)) =
      ∑ r, (logCurveWeightedSixNorm κ W (S r) (z r) (x r))^2 := by
    calc
      _ = ∑ i : Fin k, E i := logCurve_intGrid_sum hk E
      _ = _ := by
        dsimp only [E,e]
        exact (logCurve_finGrid_sum (fun r => (logCurveWeightedSixNorm κ W (S r) (z r) (x r))^2)).symm
  rw [hsum] at hsq
  have htotal :
      logCurveWeightedSixNorm κ W (Finset.univ.sigma S)
        (fun rv => z rv.1 rv.2) (fun rv => x rv.1 rv.2) =
      logCurveWeightedSixNorm κ W (J.sigma (fun i => T (R i)))
        (fun iv => Z (R iv.1) iv.2) (fun iv => X (R iv.1) iv.2) := by
    unfold logCurveWeightedSixNorm
    congr 1
    funext r
    simp only [sargosPlanarSum,Finset.sum_sigma]
    have hs := logCurve_intGrid_sum hk (fun i => ∑ v ∈ T i,
      Z i v*fordAdditiveCharacter (X i v*r.1+logCurve κ (X i v)*r.2))
    rw [hs]
    simp only [T,Z,X,Finset.sum_sigma]
    exact logCurve_finGrid_sum _
  rw [htotal]
  exact hsq

/-- Exact dyadic specialization of the genuine linear/bilinear comparison. -/
theorem LogCurveDecouplingBound.of_bilinear_dyadic {n r : ℕ} {A K : ℝ}
    (hr : r ≤ n) (hA : LogCurveDecouplingBound (2^(n-r)) A)
    (hK : LogCurveBilinearSixBound (1/(2:ℝ)^n)
      (2^(n-r)) (2^(n-r)) (1/(2:ℝ)^r) K) :
    LogCurveDecouplingBound (2^n) (14*A+2*(2:ℝ)^r*K^((6:ℝ)⁻¹)) := by
  have hcount : (2:ℕ)^r*2^(n-r) = 2^n := by
    rw [← pow_add]
    congr 1
    omega
  have hK' : LogCurveBilinearSixBound (1/(((2:ℕ)^r*2^(n-r):ℕ):ℝ))
      (2^(n-r)) (2^(n-r)) (1/((2^r:ℕ):ℝ)) K := by
    simpa only [hcount,Nat.cast_pow,Nat.cast_ofNat] using hK
  have h := LogCurveDecouplingBound.of_bilinear
    (by positivity : 0 < (2:ℕ)^r) (by positivity : 0 < (2:ℕ)^(n-r)) hA hK'
  simpa only [hcount,Nat.cast_pow,Nat.cast_ofNat] using h

/-- The actual iterated linear estimate is obtained from strictly smaller grids.
This finite theorem is not yet the numerical epsilon-loss bound. -/
theorem logCurveDecouplingBound_dyadic_iterate (D : ℕ → ℝ)
    {n r t : ℕ} (hr : 0 < r) (hn : r*2^t ≤ n)
    (hD : ∀ j < n, LogCurveDecouplingBound (2^j) (D j)) :
    LogCurveDecouplingBound (2^n)
      (14*D (n-r)+2*(2:ℝ)^r*
        (parabolaDyadicBilinearBudget D n r t r r)^((6:ℝ)⁻¹)) := by
  have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
  have hrn : r ≤ n :=
    (show r ≤ r*2^t by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpow (Nat.zero_le r)).trans hn
  exact LogCurveDecouplingBound.of_bilinear_dyadic hrn (hD (n-r) (by omega))
    (logCurveBilinearSixBound_dyadic_iterate D hr le_rfl le_rfl hn hD)

/-- Enlarging a proved constant preserves the actual finite-grid estimate. -/
theorem LogCurveDecouplingBound.mono {n : ℕ} {A B : ℝ}
    (hA : LogCurveDecouplingBound n A) (hAB : A ≤ B) :
    LogCurveDecouplingBound n B := by
  refine ⟨hA.1.trans hAB,fun κ hκ ι W hW S z x hx => ?_⟩
  exact (hA.2 κ hκ ι W hW S z x hx).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA.1 hAB 2)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

private theorem logCurve_dyadic_exponential_root {C ε : ℝ} (hC : 0 ≤ C)
    {n r t : ℕ} (ht : 1 ≤ t) (hn : r*2^t ≤ n) :
    (parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t r r)^((6:ℝ)⁻¹) ≤
      2*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3) := by
  have hbudget : 0 ≤
      parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t r r := by
    cases t <;> simp only [parabolaDyadicBilinearBudget] <;> positivity
  have hmajor := parabolaDyadicBilinearBudget_exponential (ε:=ε) (r:=r) hC (a:=r) ht hn
  have hpower :
      (2*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3))^6 =
        64*C^6*(2:ℝ)^(6*ε*n-(3*(t:ℝ)+5)*ε*r+2*r) := by
    rw [mul_pow,mul_pow,←Real.rpow_mul_natCast (by norm_num)]
    norm_num only [show (2:ℝ)^6=64 by norm_num,Nat.cast_ofNat]
    congr 1
    congr 1
    ring
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (by norm_num : (6:ℕ) ≠ 0)).mp
  have hroot := Real.rpow_inv_natCast_pow hbudget (by norm_num : (6:ℕ) ≠ 0)
  simp only [Nat.cast_ofNat] at hroot
  rw [hroot,hpower]
  exact hmajor.trans (by gcongr; norm_num)

private theorem logCurve_dyadic_exponential_iteration {C ε : ℝ} (hC : 0 ≤ C)
    {n r t : ℕ} (ht : 1 ≤ t) (hn : r*2^t ≤ n)
    (hεt : 8 ≤ (3*(t:ℝ)-1)*ε) :
    14*(C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)))+2*(2:ℝ)^r*
      (parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t r r)^((6:ℝ)⁻¹) ≤
        18*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := by
  have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
  have hrn : r ≤ n :=
    (show r ≤ r*2^t by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpow (Nat.zero_le r)).trans hn
  have hroot := logCurve_dyadic_exponential_root (ε:=ε) hC ht hn
  have hexp : ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3+r ≤ ε*((n:ℝ)-r) := by
    have hmul := mul_le_mul_of_nonneg_right hεt (Nat.cast_nonneg r : (0:ℝ) ≤ r)
    nlinarith
  have hterm : 2*(2:ℝ)^r*
      (2*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3)) ≤
        4*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := by
    rw [Nat.cast_sub hrn]
    calc
      _ = 4*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3+r) := by
        rw [Real.rpow_add (by norm_num)
          (ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3) (r:ℝ),
          Real.rpow_natCast]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by positivity)
  have h := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 2*(2:ℝ)^r by positivity)
  linarith








/-- Genuine dyadic finite weighted compact-log-family decoupling with arbitrary positive
epsilon loss. The proof starts from the actual trivial bound and uses strong
induction; no decoupling estimate is an input. -/
theorem exists_logCurveDecouplingBound_dyadic {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ n : ℕ,
      LogCurveDecouplingBound (2^n) (C*(2:ℝ)^(ε*n)) := by
  obtain ⟨s,hs⟩ := exists_nat_gt ((8:ℝ)/ε)
  let t := s+1
  have ht : 1 ≤ t := by omega
  have hεt : 8 ≤ (3*(t:ℝ)-1)*ε := by
    have h := (div_lt_iff₀ hε).mp hs
    dsimp only [t]
    push_cast
    nlinarith
  obtain ⟨r,hr'⟩ := exists_nat_gt ((5:ℝ)/ε)
  have hr0 : (0:ℝ) < r := (div_pos (by norm_num) hε).trans hr'
  have hr : 0 < r := by exact_mod_cast hr0
  have hεr : 5 ≤ ε*r := by
    have h := (div_lt_iff₀ hε).mp hr'
    nlinarith
  have hcontract : (18:ℝ) ≤ (2:ℝ)^(ε*r) := by
    calc
      18 ≤ (2:ℝ)^(5:ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hεr
  let N := r*2^t
  let C : ℝ := (2:ℝ)^N
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : N ≤ n
    · have hactual := logCurveDecouplingBound_dyadic_iterate
        (fun j => C*(2:ℝ)^(ε*j)) hr hn ih
      apply hactual.mono
      have hnum := logCurve_dyadic_exponential_iteration hC.le ht hn hεt
      have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
      have hrn : r ≤ n :=
        (show r ≤ r*2^t by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hpow (Nat.zero_le r)).trans hn
      have he : ε*(n:ℝ)=ε*((n-r:ℕ):ℝ)+ε*r := by
        rw [Nat.cast_sub hrn]; ring
      calc
        _ ≤ 18*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := hnum
        _ ≤ (2:ℝ)^(ε*r)*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := by
          gcongr
        _ = C*(2:ℝ)^(ε*n) := by
          rw [he,Real.rpow_add (by norm_num) (ε*((n-r:ℕ):ℝ)) (ε*r)]
          ring
    · have hnN : n ≤ N := by omega
      have htrivial : LogCurveDecouplingBound (2^n) (Real.sqrt ((2:ℝ)^n)) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using logCurveDecouplingBound_trivial (2^n)
      apply htrivial.mono
      have hpow : (1:ℝ) ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
      calc
        Real.sqrt ((2:ℝ)^n) ≤ (2:ℝ)^n := by
          apply Real.sqrt_le_iff.mpr
          exact ⟨by positivity,by nlinarith⟩
        _ ≤ C := pow_le_pow_right₀ (by norm_num) hnN
        _ ≤ C*(2:ℝ)^(ε*n) := by
          have h := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2)
            (show 0 ≤ ε*(n:ℝ) by positivity)
          nlinarith

/-- The constructed rapid weight majorizes the literal physical box for
the exact log curve, without a comparison to parabolic phases. -/
theorem logCurveBox_le_rapidSixNorm {ι : Type*} (κ : ℝ)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ)
    {R : ℝ} (hR : 0 < R) (r t : ℝ) :
    (∫ p : ℝ × ℝ in Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R),
      ‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖^6) ≤
      (logCurveWeightedSixNorm κ
        (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2) S z x)^6 := by
  let F := fun p : ℝ × ℝ =>
    ‖sargosPlanarSum S z x (fun i => logCurve κ (x i)) p.1 p.2‖^6
  let W := fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2
  let B := Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R)
  have hFc : Continuous F := by unfold F sargosPlanarSum fordAdditiveCharacter; fun_prop
  have hiF : IntegrableOn F B :=
    hFc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hW₀ : ∀ p, 0 ≤ W p := fun p => parabolaRapidWeight_nonneg _ _ _ _ _
  have hiW : Integrable W :=
    (integrable_parabolaRapidKernel hR r).mul_prod (integrable_parabolaRapidKernel hR t)
  have he (v : ℝ) : v^6=v^2*v^4 := by ring
  have hi : Integrable (fun p => W p*F p) := by
    simpa only [F,he,mul_assoc] using logCurveMoment_integrable κ S S z z x x hiW
  have hpoint (p : ℝ × ℝ) (hp : p∈B) : F p ≤ W p*F p := by
    have hα : |p.1-r| ≤ R := abs_le.mpr ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩
    have hγ : |p.2-t| ≤ R := abs_le.mpr ⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (parabolaRapidWeight_one_le hR hα hγ)
        (show 0 ≤ F p by dsimp [F]; positivity)
  have hlocal := setIntegral_mono_on hiF hi.integrableOn
    (measurableSet_Icc.prod measurableSet_Icc) hpoint
  have hwhole := setIntegral_le_integral (s:=B) hi
    (Filter.Eventually.of_forall (fun p => mul_nonneg (hW₀ p)
      (show 0 ≤ F p by dsimp [F]; positivity)))
  have hid := logCurveWeightedSixNorm_pow_six κ W hW₀ hiW S z x
  rw [hid]
  simpa only [F,W,B,he,logCurveWeightedBilinearMoment,mul_assoc] using hlocal.trans hwhole

/-- Physical-box decoupling for the actual logarithmic family. The band
condition is derived for the explicit rapid cutoff, not supplied as a
moment estimate; the constant is uniform in the curve parameter and arrays. -/
theorem exists_logCurveBox_dyadic_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ κ∈Icc (0:ℝ) (1/4), ∀ (n : ℕ) (R r t : ℝ), 0 < R →
      3/(100*R) ≤ ((1/(2:ℝ)^n)/(1+κ))^2 →
      ∀ (ι : Type) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
      (∀ j, ∀ k∈S j, x j k∈Icc
        ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
      (∫ p : ℝ × ℝ in Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R),
        ‖sargosPlanarSum (Finset.univ.sigma S)
          (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2)
          (fun jk => logCurve κ (x jk.1 jk.2)) p.1 p.2‖^6) ≤
        C*(2:ℝ)^(ε*n)*
          (∑ j, (logCurveWeightedSixNorm κ
            (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2)
            (S j) (z j) (x j))^2)^3 := by
  obtain ⟨D,hDpos,hD⟩ := exists_logCurveDecouplingBound_dyadic
    (ε:=ε/6) (by positivity)
  refine ⟨D^6,by positivity,?_⟩
  intro κ hκ n R r t hR hwidth ι S z x hx
  let W := fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2
  have hW : LogCurveWeightBand κ (1/((2^n:ℕ):ℝ)) W := by
    apply ParabolaWeightBand.to_logCurveWeightBand hκ.1
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using
      parabolaRapidWeight_band hR hwidth r t
  have hnorm := (hD n).2 κ hκ ι W hW S z x hx
  have hcube := pow_le_pow_left₀ (sq_nonneg _) hnorm 3
  simp only [mul_pow,←pow_mul] at hcube
  have hcoef : (D*(2:ℝ)^((ε/6)*n))^6 = D^6*(2:ℝ)^(ε*n) := by
    rw [mul_pow,←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    congr 1
    push_cast
    ring
  norm_num only [show (2*3:ℕ)=6 by omega] at hcube
  rw [←mul_pow,hcoef] at hcube
  exact (logCurveBox_le_rapidSixNorm κ (Finset.univ.sigma S)
    (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2) hR r t).trans hcube

private theorem logSix_periodic_unit_shift (f : ℝ → ℝ)
    (hp : Function.Periodic f 1) (a : ℝ) :
    (∫ v : ℝ in Icc (0:ℝ) 1, f (v+a))=∫ v : ℝ in Icc (0:ℝ) 1, f v := by
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_comp_add_right]
  simpa only [zero_add,add_zero,add_comm] using hp.intervalIntegral_add_eq a 0

private theorem logSix_periodic_physical_window (f : ℝ → ℝ)
    (hf : Continuous f) (hp : Function.Periodic f 1) {A : ℝ} (hA : 0 < A) (η : ℝ) :
    (∫ t : ℝ in Icc (-A) A, f (2*t/A+η)) =
      2*A*(∫ u : ℝ in Icc (0:ℝ) 1, f u) := by
  have he (t : ℝ) : 2*t/A=t/(A/2) := by ring
  simp_rw [he]
  rw [integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by linarith : -A ≤ A),
    intervalIntegral.integral_comp_div_add f (by positivity : A/2 ≠ 0)]
  have hleft : (-A)/(A/2)=(-2:ℝ) := by field_simp
  have hright : A/(A/2)=(2:ℝ) := by field_simp
  rw [hleft,hright]
  have hh := hp.intervalIntegral_add_zsmul_eq (4:ℤ) (-2+η)
    (fun a b => hf.intervalIntegrable a b)
  rw [hp.intervalIntegral_add_eq (-2+η) 0] at hh
  norm_num only [zsmul_eq_mul,Int.cast_ofNat,mul_one,zero_add] at hh
  have hend : -2+η+4=2+η := by ring
  rw [hend] at hh
  rw [hh,smul_eq_mul,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ←integral_Icc_eq_integral_Ioc]
  ring

private theorem logSix_integer_character (k : ℤ) :
    fordAdditiveCharacter (k:ℝ)=1 := by
  unfold fordAdditiveCharacter
  have he : 2*Real.pi*Complex.I*((k:ℝ):ℂ)=(k:ℂ)*(2*Real.pi*Complex.I) := by
    push_cast
    ring
  rw [he,Complex.exp_int_mul_two_pi_mul_I]

private def integerQuadraticSix {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (u v : ℝ) : ℝ :=
  ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+(m i:ℝ)^2*v)‖^6

private theorem integerQuadraticSix_continuous {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) :
    Continuous (fun p : ℝ × ℝ => integerQuadraticSix S z m p.1 p.2) := by
  unfold integerQuadraticSix fordAdditiveCharacter
  fun_prop

private theorem integerQuadraticSix_periodic {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) :
    (∀ v, Function.Periodic (fun u => integerQuadraticSix S z m u v) 1) ∧
      (∀ u, Function.Periodic (fun v => integerQuadraticSix S z m u v) 1) := by
  constructor
  · intro v u
    unfold integerQuadraticSix
    apply congrArg (fun w : ℂ => ‖w‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (m i:ℝ)*(u+1)+(m i:ℝ)^2*v =
      ((m i:ℝ)*u+(m i:ℝ)^2*v)+(m i:ℝ) by ring,
      fordAdditiveCharacter_add,logSix_integer_character,mul_one]
  · intro u v
    unfold integerQuadraticSix
    apply congrArg (fun w : ℂ => ‖w‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (m i:ℝ)*u+(m i:ℝ)^2*(v+1) =
      ((m i:ℝ)*u+(m i:ℝ)^2*v)+((m i)^2:ℤ) by push_cast; ring,
      fordAdditiveCharacter_add,logSix_integer_character,mul_one]

/-- Exact shear of the actual Fourier-shifted Taylor polynomial. The
frequency relation is physical, and no quadratic moment is assumed. -/
theorem logarithmic_quadratic_shear {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ) (m : ι → ℤ)
    {A δ : ℝ} (hA : A ≠ 0) (hδ : δ ≠ 0)
    (hm : ∀ i∈S, δ*s i=(m i:ℝ)-A) (α t ξ : ℝ) :
    ‖∑ i∈S, z i*fordAdditiveCharacter
      ((2*A*δ*α+δ*t/A+ξ)*s i+(δ^2*α-δ^2*t/(2*A^2))*(s i)^2)‖^6 =
      ‖∑ i∈S, z i*fordAdditiveCharacter
        ((m i:ℝ)*(2*t/A+ξ/δ)+(m i:ℝ)^2*(α-t/(2*A^2)))‖^6 := by
  let u := 2*t/A+ξ/δ
  let v := α-t/(2*A^2)
  have he (i : ι) (hi : i∈S) :
      (2*A*δ*α+δ*t/A+ξ)*s i+(δ^2*α-δ^2*t/(2*A^2))*(s i)^2 =
        (-v*A^2-u*A)+((m i:ℝ)*u+(m i:ℝ)^2*v) := by
    have hm' : (m i:ℝ)=A+δ*s i := by linarith [hm i hi]
    rw [hm']
    dsimp only [u,v]
    field_simp
    ring
  have hsum :
      (∑ i∈S, z i*fordAdditiveCharacter
        ((2*A*δ*α+δ*t/A+ξ)*s i+(δ^2*α-δ^2*t/(2*A^2))*(s i)^2)) =
      fordAdditiveCharacter (-v*A^2-u*A)*
        (∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+(m i:ℝ)^2*v)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i hi,fordAdditiveCharacter_add]
    ring
  rw [hsum,norm_mul,sargos_character_norm,one_mul]

/-- The exact short-box average is a native integer quadratic mean.
The Fourier shift disappears by periodicity, uniformly in that shift. -/
theorem logarithmic_quadratic_short_box {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ) (m : ι → ℤ)
    {A δ : ℝ} (hA : 0 < A) (hδ : δ ≠ 0)
    (hm : ∀ i∈S, δ*s i=(m i:ℝ)-A) (ξ : ℝ) :
    (∫ t : ℝ in Icc (-A) A, ∫ α : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S, z i*fordAdditiveCharacter
        ((2*A*δ*α+δ*t/A+ξ)*s i+(δ^2*α-δ^2*t/(2*A^2))*(s i)^2)‖^6) =
      2*A*(∫ v : ℝ in Icc (0:ℝ) 1, ∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+(m i:ℝ)^2*v)‖^6) := by
  let P := integerQuadraticSix S z m
  let F := fun u => ∫ v : ℝ in Icc (0:ℝ) 1, P u v
  have hPc : Continuous (fun p : ℝ × ℝ => P p.1 p.2) :=
    integerQuadraticSix_continuous S z m
  have hper := integerQuadraticSix_periodic S z m
  have hFc : Continuous F := by
    have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ:=volume) (f:=P) hPc 0 1
    simpa only [F,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using h
  have hFp : Function.Periodic F 1 := by
    intro u
    apply integral_congr_ae
    filter_upwards with v
    exact hper.1 v u
  simp_rw [logarithmic_quadratic_shear S z s m hA.ne' hδ hm]
  change (∫ t : ℝ in Icc (-A) A, ∫ α : ℝ in Icc (0:ℝ) 1,
    P (2*t/A+ξ/δ) (α-t/(2*A^2)))=_
  have hinner (t : ℝ) : (∫ α : ℝ in Icc (0:ℝ) 1,
      P (2*t/A+ξ/δ) (α-t/(2*A^2)))=F (2*t/A+ξ/δ) := by
    simpa only [F,sub_eq_add_neg] using
      logSix_periodic_unit_shift (P (2*t/A+ξ/δ)) (hper.2 _) (-(t/(2*A^2)))
  simp_rw [hinner]
  rw [logSix_periodic_physical_window F hFc hFp hA (ξ/δ)]
  have hi : Integrable (fun p : ℝ × ℝ => P p.1 p.2)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hPc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hswap := integral_integral_swap (μ:=volume.restrict (Icc (0:ℝ) 1))
    (ν:=volume.restrict (Icc (0:ℝ) 1)) (f:=P) hi
  exact congrArg (fun q : ℝ => 2*A*q) hswap

private theorem logSix_envelope_integrable :
    Integrable (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹) ∧
      (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹) ≤ Real.pi := by
  have hdom (ξ : ℝ) : ((1+|ξ|)^102)⁻¹ ≤ (1+ξ^2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    calc
      1+ξ^2 ≤ (1+|ξ|)^2 := by nlinarith [sq_abs ξ,abs_nonneg ξ]
      _ ≤ (1+|ξ|)^102 := pow_le_pow_right₀ (by linarith [abs_nonneg ξ]) (by norm_num)
  have hc : Continuous (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹) :=
    (by fun_prop : Continuous (fun ξ : ℝ => (1+|ξ|)^102)).inv₀
      (fun ξ => by positivity)
  have hi := integrable_inv_one_add_sq.mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => by
      simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ ((1+|ξ|)^102)⁻¹)] using hdom ξ))
  refine ⟨hi,?_⟩
  have h := integral_mono hi integrable_inv_one_add_sq hdom
  simpa only [integral_univ_inv_one_add_sq] using h

/-- The bounded cubic remainder and exact periodic shear prove a genuine
short-cell logarithmic sixth-moment reduction. All Taylor scales are linked
to the physical height and the actual integer frequencies. -/
theorem exists_logarithmic_short_cell_quadratic :
    ∃ C > (0:ℝ), ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ)
      (s : ι → ℝ) (m : ι → ℤ) (A δ : ℝ), 0 < A → δ ≠ 0 →
      |δ/A| ≤ 1/4 → |δ^3/A^2| ≤ 1 →
      (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
      (∀ i∈S, δ*s i=(m i:ℝ)-A) →
      (∫ t : ℝ in Icc (-A) A, ∫ α : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6) ≤
        C*A*(∫ v : ℝ in Icc (0:ℝ) 1, ∫ u : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+(m i:ℝ)^2*v)‖^6) := by
  obtain ⟨C,hC,htransfer⟩ := exists_logarithmic_physical_sixth_transfer
  refine ⟨2*C*Real.pi,by positivity,?_⟩
  intro ι S z s m A δ hA hδ hscale hcubic hs hm
  let B := Icc (-A) A ×ˢ Icc (0:ℝ) 1
  let P := fun p : ℝ × ℝ =>
    ‖∑ i∈S, z i*fordAdditiveCharacter ((p.2)*(m i:ℝ)^2+p.1*Real.log (m i:ℝ))‖^6
  let F := fun (ξ : ℝ) (p : ℝ × ℝ) =>
    ‖∑ i∈S, z i*fordAdditiveCharacter
      ((2*A*δ*p.2+δ*p.1/A+ξ)*s i+(δ^2*p.2-δ^2*p.1/(2*A^2))*(s i)^2)‖^6
  let V := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  let J := ∫ v : ℝ in Icc (0:ℝ) 1, ∫ u : ℝ in Icc (0:ℝ) 1,
    ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+(m i:ℝ)^2*v)‖^6
  have hPc : Continuous P := by unfold P fordAdditiveCharacter; fun_prop
  have hFc : Continuous (fun q : ℝ × (ℝ × ℝ) => F q.1 q.2) := by
    unfold F fordAdditiveCharacter
    fun_prop
  have hFb (ξ : ℝ) (p : ℝ × ℝ) : ‖F ξ p‖ ≤ (∑ i∈S, ‖z i‖)^6 := by
    rw [Real.norm_of_nonneg (show 0 ≤ F ξ p by dsimp [F]; positivity)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      _ ≤ ∑ i∈S, ‖z i*fordAdditiveCharacter
        ((2*A*δ*p.2+δ*p.1/A+ξ)*s i+(δ^2*p.2-δ^2*p.1/(2*A^2))*(s i)^2)‖ :=
        norm_sum_le _ _
      _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]
  have hiP : IntegrableOn P B :=
    hPc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hiV : Integrable V := logSix_envelope_integrable.1
  have hi1 : IntegrableOn (fun _p : ℝ × ℝ => (1:ℝ)) B :=
    integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_ne_top
  have hiF : Integrable (fun q : ℝ × (ℝ × ℝ) => V q.1*F q.1 q.2)
      (volume.prod (volume.restrict B)) := by
    have h := (hiV.mul_prod hi1).mul_bdd hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => hFb q.1 q.2))
    simpa only [mul_one] using h
  have hpoint (p : ℝ × ℝ) (hp : p∈B) : P p ≤ C*(∫ ξ : ℝ, V ξ*F ξ p) := by
    have ht : |p.1/A| ≤ 1 := by
      rw [abs_div,abs_of_pos hA]
      exact (div_le_one hA).mpr (abs_le.mpr hp.1)
    have ht' : |p.1*δ^3/A^3| ≤ 1 := by
      have he : p.1*δ^3/A^3=(p.1/A)*(δ^3/A^2) := by field_simp
      rw [he,abs_mul]
      simpa only [one_mul] using mul_le_mul ht hcubic (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have h := htransfer S z s hs A δ p.1 p.2 hA hscale ht'
    have he (i : ι) (hi : i∈S) : A+δ*s i=(m i:ℝ) := by linarith [hm i hi]
    have heSum :
        (∑ i∈S, z i*fordAdditiveCharacter
          (p.2*(A+δ*s i)^2+p.1*Real.log (A+δ*s i))) =
        ∑ i∈S, z i*fordAdditiveCharacter
          (p.2*(m i:ℝ)^2+p.1*Real.log (m i:ℝ)) :=
      Finset.sum_congr rfl (fun i hi => by rw [he i hi])
    simpa only [heSum,P,F,V] using h
  have hmain := setIntegral_mono_on hiP
    (hiF.integral_prod_right.const_mul C) (measurableSet_Icc.prod measurableSet_Icc) hpoint
  rw [integral_const_mul] at hmain
  have hswap := integral_integral_swap (μ:=volume) (ν:=volume.restrict B)
    (f:=fun ξ p => V ξ*F ξ p) hiF
  rw [←hswap] at hmain
  have hinner (ξ : ℝ) : (∫ p : ℝ × ℝ in B, F ξ p)=2*A*J := by
    have hFi : IntegrableOn (F ξ) B :=
      (hFc.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
    have hprod : Integrable (F ξ)
        ((volume.restrict (Icc (-A) A)).prod (volume.restrict (Icc (0:ℝ) 1))) := by
      rw [Measure.prod_restrict]
      exact hFi
    have hi := integral_prod (F ξ) hprod
    rw [Measure.prod_restrict,←Measure.volume_eq_prod] at hi
    change (∫ p : ℝ × ℝ in B, F ξ p)=_ at hi
    rw [hi]
    exact logarithmic_quadratic_short_box S z s m hA hδ hm ξ
  simp_rw [integral_const_mul,hinner] at hmain
  rw [integral_mul_const] at hmain
  have hJ : 0 ≤ J := integral_nonneg (fun _ => integral_nonneg (fun _ => by positivity))
  have hbound : C*((∫ ξ : ℝ, V ξ)*(2*A*J)) ≤ (2*C*Real.pi)*A*J := by
    have hv := mul_le_mul_of_nonneg_right logSix_envelope_integrable.2
      (show 0 ≤ 2*C*A*J by positivity)
    dsimp only [V]
    nlinarith only [hv]
  have hprodP : Integrable P
      ((volume.restrict (Icc (-A) A)).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact hiP
  have hleft := integral_prod P hprodP
  rw [Measure.prod_restrict,←Measure.volume_eq_prod] at hleft
  change (∫ p : ℝ × ℝ in B, P p)=_ at hleft
  rw [hleft] at hmain
  exact hmain.trans hbound

/-- The logarithmic short-cell sixth moment now consumes the already
proved native quadratic VMVT, with multiplicity-sensitive coefficient fibers. -/
theorem exists_logarithmic_short_cell_sixth {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
        (m : ι → ℤ) (A δ B : ℝ) (L : ℤ), 0 < A → δ ≠ 0 → 0 ≤ B →
        |δ/A| ≤ 1/4 → |δ^3/A^2| ≤ 1 →
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        (∀ i∈S, δ*s i=(m i:ℝ)-A) →
        (∀ i∈S, L < m i ∧ m i ≤ L+Q) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        (∫ t : ℝ in Icc (-A) A, ∫ α : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6) ≤
          C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨D,hD,hlog⟩ := exists_logarithmic_short_cell_quadratic
  obtain ⟨E,hE,hquad⟩ := exists_bourgain_quadratic_weighted_finite_interval hε
  refine ⟨D*E,by positivity,?_⟩
  intro Q hQ ι S z s m A δ B L hA hδ hB hscale hcubic hs hm hinterval hz
  have h := hlog ι S z s m A δ hA hδ hscale hcubic hs hm
  have hq := hquad Q hQ ι S z m L B hB hinterval hz
  have hh := mul_le_mul_of_nonneg_left hq (mul_nonneg hD.le hA.le)
  exact h.trans (hh.trans_eq (by ring))

/-- Translation in physical height only changes coefficient phases, so
the short-cell bound holds on every time window with the same constant. -/
theorem exists_logarithmic_short_cell_sixth_translated {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
        (m : ι → ℤ) (A δ B t₀ : ℝ) (L : ℤ), 0 < A → δ ≠ 0 → 0 ≤ B →
        |δ/A| ≤ 1/4 → |δ^3/A^2| ≤ 1 →
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        (∀ i∈S, δ*s i=(m i:ℝ)-A) →
        (∀ i∈S, L < m i ∧ m i ≤ L+Q) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        (∫ t : ℝ in Icc (-A) A, ∫ α : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter
            (α*(m i:ℝ)^2+(t+t₀)*Real.log (m i:ℝ))‖^6) ≤
          C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_logarithmic_short_cell_sixth hε
  refine ⟨C,hC,?_⟩
  intro Q hQ ι S z s m A δ B t₀ L hA hδ hB hscale hcubic hs hm hinterval hz
  let z' := fun i => z i*fordAdditiveCharacter (t₀*Real.log (m i:ℝ))
  have hz' (k : ℤ) : (∑ i∈S.filter (fun i => m i=k), ‖z' i‖) ≤ B := by
    simpa only [z',norm_mul,sargos_character_norm,mul_one] using hz k
  have hh := h Q hQ ι S z' s m A δ B L hA hδ hB hscale hcubic hs hm hinterval hz'
  have he (t α : ℝ) :
      (∑ i∈S, z' i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))) =
      ∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+(t+t₀)*Real.log (m i:ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [z']
    rw [mul_assoc,←fordAdditiveCharacter_add]
    congr 2
    ring
  simpa only [he] using hh

/-- A uniform actual moving-window bound controls all Lorentz-weighted
tails. This is averaging of bounded functions, not an assumed moment. -/
theorem logSix_lorentz_of_window {A M : ℝ} (hA : 0 < A)
    (f : ℝ → ℝ) (hf : Continuous f) (hf₀ : ∀ t, 0 ≤ f t)
    (H : ℝ) (hb : ∀ t, ‖f t‖ ≤ H)
    (hwindow : ∀ x, (∫ t : ℝ in Icc (-A) A, f (t+x)) ≤ M) :
    (∫ t : ℝ, (1+(t/A)^2)⁻¹*f t) ≤ (3*Real.pi/2)*M := by
  let I := Icc (-A) A
  let W := fun t : ℝ => (1+(t/A)^2)⁻¹
  have hW : Integrable W := integrable_inv_one_add_sq.comp_div hA.ne'
  have hWf := hW.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hshift (x t : ℝ) (ht : t∈I) : W (x+t) ≤ 3*W x := by
    have ht' : |t/A| ≤ 1 := by
      rw [abs_div,abs_of_pos hA]
      exact (div_le_one hA).mpr (abs_le.mpr ht)
    have ht₂ : (t/A)^2 ≤ 1 := by
      simpa only [one_pow,sq_abs] using pow_le_pow_left₀ (abs_nonneg (t/A)) ht' 2
    dsimp only [W]
    rw [add_div,←one_div,←one_div,mul_one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (x/A+2*(t/A))]
  have hpoint (t : ℝ) (ht : t∈I) :
      (∫ x : ℝ, W x*f x) ≤ 3*(∫ x : ℝ, W x*f (x+t)) := by
    have hiR := hW.mul_bdd
      (hf.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => hb (x+t)))
    calc
      _ = ∫ x : ℝ, W (x+t)*f (x+t) :=
        (integral_add_right_eq_self (μ:=volume) (fun x => W x*f x) t).symm
      _ ≤ ∫ x : ℝ, 3*(W x*f (x+t)) :=
        integral_mono (hWf.comp_add_right t) (hiR.const_mul 3)
          (fun x => (mul_le_mul_of_nonneg_right (hshift x t ht) (hf₀ (x+t))).trans_eq (by ring))
      _ = _ := integral_const_mul 3 _
  have hi1 : IntegrableOn (fun _t : ℝ => (1:ℝ)) I :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hiF : Integrable (fun p : ℝ × ℝ => W p.1*f (p.1+p.2))
      (volume.prod (volume.restrict I)) := by
    have h := (hW.mul_prod hi1).mul_bdd
      (hf.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hb (p.1+p.2)))
    simpa only [mul_one] using h
  have hiConst : IntegrableOn (fun _t : ℝ => ∫ x : ℝ, W x*f x) I :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hmain := setIntegral_mono_on hiConst (hiF.integral_prod_right.const_mul 3)
    measurableSet_Icc hpoint
  rw [setIntegral_const,integral_const_mul] at hmain
  have hmassI : volume.real I=2*A := by
    dsimp only [I]
    rw [Real.volume_real_Icc_of_le (by linarith : -A ≤ A)]
    ring
  rw [hmassI,smul_eq_mul] at hmain
  have hswap := integral_integral_swap (f:=fun x t : ℝ => W x*f (x+t)) hiF
  rw [←hswap] at hmain
  simp_rw [integral_const_mul] at hmain
  have hinner (x : ℝ) : (∫ t : ℝ in I, f (x+t)) ≤ M := by
    simpa only [add_comm,I] using hwindow x
  have hiAvg : Integrable (fun x => W x*(∫ t : ℝ in I, f (x+t))) := by
    simpa only [integral_const_mul] using hiF.integral_prod_left
  have hle := integral_mono hiAvg (hW.mul_const M)
    (fun x => mul_le_mul_of_nonneg_left (hinner x) (by positivity))
  have hmassW : (∫ x : ℝ, W x)=A*Real.pi := by
    have h := Measure.integral_comp_div (fun y : ℝ => (1+y^2)⁻¹) A
    simpa only [W,integral_univ_inv_one_add_sq,abs_of_pos hA,smul_eq_mul] using h
  rw [integral_mul_const,hmassW] at hle
  have hh : 2*A*(∫ x : ℝ, W x*f x) ≤ 3*(A*Real.pi*M) := hmain.trans (by gcongr)
  apply (mul_le_mul_iff_right₀ (show 0 < 2*A by positivity)).mp
  nlinarith only [hh]

/-- All physical time tails of each actual logarithmic short cell are
controlled by translating the proved window estimate. No height cutoff or
large-height Taylor approximation is imposed. -/
theorem exists_logarithmic_short_cell_lorentz {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
        (m : ι → ℤ) (A δ B : ℝ) (L : ℤ), 0 < A → δ ≠ 0 → 0 ≤ B →
        |δ/A| ≤ 1/4 → |δ^3/A^2| ≤ 1 →
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        (∀ i∈S, δ*s i=(m i:ℝ)-A) →
        (∀ i∈S, L < m i ∧ m i ≤ L+Q) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        (∫ t : ℝ, (1+(t/A)^2)⁻¹*(∫ α : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter
            (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6)) ≤
          C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_logarithmic_short_cell_sixth_translated hε
  refine ⟨(3*Real.pi/2)*C,by positivity,?_⟩
  intro Q hQ ι S z s m A δ B L hA hδ hB hscale hcubic hs hm hinterval hz
  let P := fun (t α : ℝ) => ‖∑ i∈S, z i*fordAdditiveCharacter
    (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6
  let f := fun t => ∫ α : ℝ in Icc (0:ℝ) 1, P t α
  have hPc : Continuous (Function.uncurry P) := by
    unfold P Function.uncurry fordAdditiveCharacter
    fun_prop
  have hfc : Continuous f := by
    have hh := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ:=volume) (f:=P) hPc 0 1
    simpa only [f,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using hh
  have hf₀ (t : ℝ) : 0 ≤ f t := integral_nonneg (fun α => by dsimp [P]; positivity)
  have hPb (t α : ℝ) : ‖P t α‖ ≤ (∑ i∈S, ‖z i‖)^6 := by
    rw [Real.norm_of_nonneg (show 0 ≤ P t α by dsimp [P]; positivity)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      _ ≤ ∑ i∈S, ‖z i*fordAdditiveCharacter
        (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]
  have hfb (t : ℝ) : ‖f t‖ ≤ (∑ i∈S, ‖z i‖)^6 := by
    have hh := norm_setIntegral_le_of_norm_le_const_ae
      (μ:=volume) (s:=Icc (0:ℝ) 1) (f:=P t) isCompact_Icc.measure_lt_top
      (Filter.Eventually.of_forall (fun α => hPb t α))
    simpa only [f,Real.volume_real_Icc_of_le (by norm_num : (0:ℝ) ≤ 1),
      sub_zero,mul_one] using hh
  have hwindow (x : ℝ) : (∫ t : ℝ in Icc (-A) A, f (t+x)) ≤
      C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) :=
    h Q hQ ι S z s m A δ B x L hA hδ hB hscale hcubic hs hm hinterval hz
  have hh := logSix_lorentz_of_window hA f hfc hf₀ ((∑ i∈S, ‖z i‖)^6) hfb hwindow
  exact hh.trans_eq (by ring)

private theorem logSix_lorentz_periodic (f : ℝ → ℝ)
    (hf : Continuous f) (hf₀ : ∀ t, 0 ≤ f t)
    (H : ℝ) (hb : ∀ t, ‖f t‖ ≤ H) (hp : Function.Periodic f 1) :
    (∫ t : ℝ, (1+t^2)⁻¹*f t) ≤ 3*Real.pi*(∫ u : ℝ in Icc (0:ℝ) 1, f u) := by
  have hwindow (x : ℝ) : (∫ t : ℝ in Icc (-1:ℝ) 1, f (t+x)) =
      2*(∫ u : ℝ in Icc (0:ℝ) 1, f u) := by
    rw [integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
      intervalIntegral.integral_comp_add_right]
    have hh := hp.intervalIntegral_add_zsmul_eq (2:ℤ) (-1+x)
      (fun a b => hf.intervalIntegrable a b)
    rw [hp.intervalIntegral_add_eq (-1+x) 0] at hh
    norm_num only [zsmul_eq_mul,Int.cast_ofNat,mul_one,zero_add] at hh
    rw [show -1+x+2=1+x by ring] at hh
    rw [hh,intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      ←integral_Icc_eq_integral_Ioc]
  have h := logSix_lorentz_of_window (by norm_num : (0:ℝ) < 1)
    f hf hf₀ H hb (fun x => (hwindow x).le)
  simp only [div_one] at h
  exact h.trans_eq (by ring)

private theorem logSix_lorentz_second_coordinate
    (P : ℝ → ℝ → ℝ) (hPc : Continuous (Function.uncurry P))
    (hP₀ : ∀ t α, 0 ≤ P t α) (H : ℝ) (hPb : ∀ t α, ‖P t α‖ ≤ H)
    (hper : ∀ t, Function.Periodic (P t) 1)
    (W : ℝ → ℝ) (hW : Integrable W) (hW₀ : ∀ t, 0 ≤ W t) :
    (∫ t : ℝ, W t*(∫ α : ℝ, (1+α^2)⁻¹*P t α)) ≤
      3*Real.pi*(∫ t : ℝ, W t*(∫ α : ℝ in Icc (0:ℝ) 1, P t α)) := by
  have hperiod (t : ℝ) :
      (∫ α : ℝ, (1+α^2)⁻¹*P t α) ≤
        3*Real.pi*(∫ α : ℝ in Icc (0:ℝ) 1, P t α) :=
    logSix_lorentz_periodic (P t) (hPc.comp (continuous_const.prodMk continuous_id))
      (hP₀ t) H (hPb t) (hper t)
  have hi1 : IntegrableOn (fun _α : ℝ => (1:ℝ)) (Icc (0:ℝ) 1) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hiC : Integrable (fun p : ℝ × ℝ => W p.1*P p.1 p.2)
      (volume.prod (volume.restrict (Icc (0:ℝ) 1))) := by
    have hi := (hW.mul_prod hi1).mul_bdd hPc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hPb p.1 p.2))
    simpa only [mul_one] using hi
  have hiAvg : Integrable (fun t => W t*(∫ α : ℝ in Icc (0:ℝ) 1, P t α)) := by
    simpa only [integral_const_mul] using hiC.integral_prod_left
  have hmain :
      (∫ t : ℝ, W t*(∫ α : ℝ, (1+α^2)⁻¹*P t α)) ≤
      ∫ t : ℝ, 3*Real.pi*(W t*(∫ α : ℝ in Icc (0:ℝ) 1, P t α)) := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => mul_nonneg
        (hW₀ t)
        (integral_nonneg (fun α => mul_nonneg (by positivity) (hP₀ t α)))))
      (hiAvg.const_mul (3*Real.pi))
    filter_upwards with t
    exact (mul_le_mul_of_nonneg_left (hperiod t)
      (hW₀ t)).trans_eq (by ring)
  rw [integral_const_mul] at hmain
  exact hmain

private theorem logarithmic_product_weight_period_reduction {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) {A : ℝ} (hA : 0 < A) :
    (∫ t : ℝ, (1+(t/A)^2)⁻¹*(∫ α : ℝ, (1+α^2)⁻¹*
      ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6)) ≤
      3*Real.pi*(∫ t : ℝ, (1+(t/A)^2)⁻¹*(∫ α : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6)) := by
  let P := fun (t α : ℝ) => ‖∑ i∈S, z i*fordAdditiveCharacter
    (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6
  have hPc : Continuous (Function.uncurry P) := by
    unfold P Function.uncurry fordAdditiveCharacter
    fun_prop
  have hP₀ (t α : ℝ) : 0 ≤ P t α := by dsimp [P]; positivity
  have hPb (t α : ℝ) : ‖P t α‖ ≤ (∑ i∈S, ‖z i‖)^6 := by
    rw [Real.norm_of_nonneg (hP₀ t α)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      _ ≤ ∑ i∈S, ‖z i*fordAdditiveCharacter
        (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]
  have hper (t : ℝ) : Function.Periodic (P t) 1 := by
    intro α
    unfold P
    apply congrArg (fun v : ℂ => ‖v‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    rw [show (α+1)*(m i:ℝ)^2+t*Real.log (m i:ℝ) =
      (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))+((m i)^2:ℤ) by push_cast; ring,
      fordAdditiveCharacter_add,logSix_integer_character,mul_one]
  exact logSix_lorentz_second_coordinate P hPc hP₀ ((∑ i∈S, ‖z i‖)^6)
    hPb hper (fun t => (1+(t/A)^2)⁻¹)
    (integrable_inv_one_add_sq.comp_div hA.ne') (fun t => by positivity)

/-- The literal two-coordinate Lorentz-weighted physical short-cell moment.
Both time tails and the noncompact square-phase coordinate are accounted for. -/
theorem exists_logarithmic_short_cell_product_weight {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
        (m : ι → ℤ) (A δ B : ℝ) (L : ℤ), 0 < A → δ ≠ 0 → 0 ≤ B →
        |δ/A| ≤ 1/4 → |δ^3/A^2| ≤ 1 →
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        (∀ i∈S, δ*s i=(m i:ℝ)-A) →
        (∀ i∈S, L < m i ∧ m i ≤ L+Q) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        (∫ t : ℝ, (1+(t/A)^2)⁻¹*(∫ α : ℝ, (1+α^2)⁻¹*
          ‖∑ i∈S, z i*fordAdditiveCharacter
            (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6)) ≤
          C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_logarithmic_short_cell_lorentz hε
  refine ⟨3*Real.pi*C,by positivity,?_⟩
  intro Q hQ ι S z s m A δ B L hA hδ hB hscale hcubic hs hm hinterval hz
  have hmain := logarithmic_product_weight_period_reduction S z m hA
  have hsource := h Q hQ ι S z s m A δ B L hA hδ hB hscale hcubic hs hm hinterval hz
  have hh := mul_le_mul_of_nonneg_left hsource (show 0 ≤ 3*Real.pi by positivity)
  exact hmain.trans (hh.trans_eq (by ring))

/-- The exact physical square/log coordinate map sends the compact
Fourier support of a (1 by X) weight into the required log-curve band. -/
theorem logarithmic_physical_band_gap {X δ ξ η : ℝ}
    (hX : 1 ≤ X) (hδ : 4/X ≤ δ^2)
    (hgap : δ^2 ≤ logCurveBandGauge (1/4) ξ η) :
    1/100 ≤ |X^2*ξ/4| ∨ 1/(100*X) ≤ |ξ/8-η/64| := by
  have hX₀ : 0 < X := by linarith
  by_contra h
  push Not at h
  have hξsmall : X^2*|ξ|/4 < (1/100:ℝ) := by
    simpa only [abs_div,abs_mul,abs_of_nonneg (sq_nonneg X),
      abs_of_pos (by norm_num : (0:ℝ) < 4)] using h.1
  have hξ : X*|ξ| < (1/25:ℝ) := by
    have hx := mul_le_mul_of_nonneg_right
      (show X ≤ X^2 by nlinarith) (abs_nonneg ξ)
    nlinarith only [hξsmall,hx]
  have hv : X*|ξ/8-η/64| < (1/100:ℝ) := by
    have hh : |ξ/8-η/64| < (1/100)/X := by
      convert h.2 using 1
      ring
    have hh' := (lt_div_iff₀ hX₀).mp hh
    simpa only [mul_comm] using hh'
  have hη : X*|η| < 1 := by
    have hh : |η| ≤ 8*|ξ|+64*|ξ/8-η/64| := by
      have he : η=8*ξ-64*(ξ/8-η/64) := by ring
      calc
        |η| = |8*ξ-64*(ξ/8-η/64)| := congrArg abs he
        _ ≤ |8*ξ|+|64*(ξ/8-η/64)| := abs_sub _ _
        _ = _ := by norm_num [abs_mul]
    have hh' := mul_le_mul_of_nonneg_left hh hX₀.le
    nlinarith only [hh',hξ,hv]
  have hGauge : logCurveBandGauge (1/4) ξ η ≤ (25/16:ℝ)*(|η|+2*|ξ|) := by
    have hsec : |η-2*(ξ/(1+(1/4:ℝ)))| ≤ |η|+2*|ξ| := by
      have hh := abs_sub η (2*(ξ/(1+(1/4:ℝ))))
      norm_num [abs_mul,abs_div] at hh ⊢
      linarith [abs_nonneg ξ]
    have hmax : max |η| |η-2*(ξ/(1+(1/4:ℝ)))| ≤ |η|+2*|ξ| :=
      max_le (by linarith [abs_nonneg ξ]) hsec
    have hmul := mul_le_mul_of_nonneg_left hmax (by norm_num : (0:ℝ) ≤ 25/16)
    convert hmul using 1
    norm_num only [logCurveBandGauge,parabolaBandGauge]
  have hg := mul_le_mul_of_nonneg_left (hgap.trans hGauge) hX₀.le
  have hd := (div_le_iff₀ hX₀).mp hδ
  nlinarith only [hg,hd,hξ,hη]

private def logarithmicPhysicalCoordinates (X : ℝ) (hX : X ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun p := (X^2*p.1/4+p.2/8,-p.2/64)
  invFun p := ((4*p.1+32*p.2)/X^2,-64*p.2)
  left_inv p := by
    ext <;> dsimp <;> field_simp
    ring
  right_inv p := by
    ext <;> dsimp <;> field_simp
    ring
  map_add' p q := by ext <;> dsimp <;> ring
  map_smul' c p := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def logarithmicPhysicalWeight (X : ℝ) (p : ℝ × ℝ) : ℝ :=
  parabolaRapidKernel 1 0 p.1*parabolaRapidKernel X 0 p.2

theorem logarithmicPhysicalWeight_nonneg (X : ℝ) (p : ℝ × ℝ) :
    0 ≤ logarithmicPhysicalWeight X p :=
  mul_nonneg (parabolaRapidKernel_nonneg _ _ _) (parabolaRapidKernel_nonneg _ _ _)

theorem logarithmicPhysicalWeight_integrable {X : ℝ} (hX : 0 < X) :
    Integrable (logarithmicPhysicalWeight X) :=
  (integrable_parabolaRapidKernel (by norm_num : (0:ℝ) < 1) 0).mul_prod
    (integrable_parabolaRapidKernel hX 0)

private theorem logarithmicPhysicalWeight_fourier_zero {X u v : ℝ}
    (hX : 0 < X) (hgap : 1/100 ≤ |u| ∨ 1/(100*X) ≤ |v|) :
    (∫ p : ℝ × ℝ, (logarithmicPhysicalWeight X p : ℂ)*
      fordAdditiveCharacter (u*p.1+v*p.2))=0 := by
  have hc : Continuous (fun p : ℝ × ℝ => fordAdditiveCharacter (u*p.1+v*p.2)) := by
    unfold fordAdditiveCharacter
    fun_prop
  have hi : Integrable (fun p : ℝ × ℝ => (logarithmicPhysicalWeight X p : ℂ)*
      fordAdditiveCharacter (u*p.1+v*p.2)) :=
    (logarithmicPhysicalWeight_integrable hX).ofReal.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => (sargos_character_norm _).le))
  have hprod := integral_prod _ hi
  rw [←Measure.volume_eq_prod] at hprod
  rw [hprod]
  have he (α t : ℝ) :
      (logarithmicPhysicalWeight X (α,t) : ℂ)*fordAdditiveCharacter (u*α+v*t) =
      ((parabolaRapidKernel 1 0 α : ℂ)*fordAdditiveCharacter (u*α))*
        ((parabolaRapidKernel X 0 t : ℂ)*fordAdditiveCharacter (v*t)) := by
    rw [fordAdditiveCharacter_add]
    dsimp only [logarithmicPhysicalWeight]
    push_cast
    ring
  simp_rw [he,integral_const_mul]
  rw [integral_mul_const]
  rcases hgap with h | h
  · rw [integral_parabolaRapidKernel_character_zero (by norm_num : (0:ℝ) < 1)
      (by simpa only [mul_one] using h),zero_mul]
  · rw [integral_parabolaRapidKernel_character_zero hX h,mul_zero]

/-- An explicit physical (1 by X) rapid weight, transported through the
actual square/log source coordinates, lies in the required compact band. -/
theorem logarithmicPhysicalWeight_band {X δ : ℝ} (hX : 1 ≤ X) (hδ : 4/X ≤ δ^2) :
    LogCurveWeightBand (1/4) δ
      (fun p : ℝ × ℝ => logarithmicPhysicalWeight X ((4*p.1+32*p.2)/X^2,-64*p.2)) := by
  have hX₀ : 0 < X := by linarith
  let e := logarithmicPhysicalCoordinates X hX₀.ne'
  refine ⟨fun p => logarithmicPhysicalWeight_nonneg _ _,
    logCurve_rescaling_integrable e.symm (logarithmicPhysicalWeight_integrable hX₀),?_⟩
  intro ξ η hgap
  obtain ⟨c,hc,hint⟩ := logCurve_rescaling_integral (F:=ℂ) e.symm
  let f := fun p : ℝ × ℝ => (logarithmicPhysicalWeight X p : ℂ)*
    fordAdditiveCharacter (ξ*(e p).1+η*(e p).2)
  have heq :
      (∫ p : ℝ × ℝ,
        (logarithmicPhysicalWeight X ((4*p.1+32*p.2)/X^2,-64*p.2) : ℂ)*
          fordAdditiveCharacter (ξ*p.1+η*p.2)) =
      ∫ p : ℝ × ℝ, f (e.symm p) := by
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [f]
    rw [e.apply_symm_apply]
    rfl
  rw [heq,hint f]
  have he (p : ℝ × ℝ) :
      ξ*(e p).1+η*(e p).2=(X^2*ξ/4)*p.1+(ξ/8-η/64)*p.2 := by
    dsimp [e,logarithmicPhysicalCoordinates]
    ring
  dsimp only [f]
  simp_rw [he]
  rw [logarithmicPhysicalWeight_fourier_zero hX₀
    (logarithmic_physical_band_gap hX hδ hgap),smul_zero]

theorem logarithmicPhysicalWeight_one_le {X : ℝ} (hX : 0 < X)
    {p : ℝ × ℝ} (hα : |p.1| ≤ 1) (ht : |p.2| ≤ X) :
    1 ≤ logarithmicPhysicalWeight X p := by
  exact one_le_mul_of_one_le_of_one_le
    (parabolaRapidKernel_one_le (by norm_num : (0:ℝ) < 1)
      (by simpa only [sub_zero] using hα))
    (parabolaRapidKernel_one_le hX (by simpa only [sub_zero] using ht))

/-- Actual square/log source sums enter the specific log curve at kappa=1/4.
Every frequency keeps its own coefficient and its exact square coordinate. -/
theorem logarithmic_physical_sum_norm {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m x : ι → ℝ)
    {X : ℝ} (hX : 0 < X) (hm : ∀ i∈S, 0 < m i)
    (hx : ∀ i∈S, (m i)^2=X^2*(1+(1/4)*x i)) (α t : ℝ) :
    ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i)^2+t*Real.log (m i))‖ =
      ‖sargosPlanarSum S z x (fun i => logCurve (1/4) (x i))
        (X^2*α/4+t/8) (-t/64)‖ := by
  have he (i : ι) (hi : i∈S) :
      α*(m i)^2+t*Real.log (m i) =
      (α*X^2+t*Real.log X)+
        (x i*(X^2*α/4+t/8)+logCurve (1/4) (x i)*(-t/64)) := by
    have h := logCurve_square_source_phase (κ:=1/4) hX (hm i hi) (hx i hi) α t
    convert h using 1
    ring
  have hsum :
      (∑ i∈S, z i*fordAdditiveCharacter (α*(m i)^2+t*Real.log (m i))) =
      fordAdditiveCharacter (α*X^2+t*Real.log X)*
        sargosPlanarSum S z x (fun i => logCurve (1/4) (x i))
          (X^2*α/4+t/8) (-t/64) := by
    unfold sargosPlanarSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i hi,fordAdditiveCharacter_add]
    ring
  rw [hsum,norm_mul,sargos_character_norm,one_mul]

def logarithmicPhysicalSixMoment {ι : Type*} (X : ℝ)
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, logarithmicPhysicalWeight X p*
    ‖∑ i∈S, z i*fordAdditiveCharacter (p.1*(m i)^2+p.2*Real.log (m i))‖^6

/-- One common positive change-of-variables factor transports the actual
physical moments for the whole sum and every cell. -/
theorem exists_logarithmicPhysicalSixMoment_transport {X : ℝ} (hX : 0 < X) :
    ∃ c > (0:ℝ), ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m x : ι → ℝ),
      (∀ i∈S, 0 < m i) →
      (∀ i∈S, (m i)^2=X^2*(1+(1/4)*x i)) →
      logCurveWeightedBilinearMoment (1/4)
        (fun p : ℝ × ℝ => logarithmicPhysicalWeight X ((4*p.1+32*p.2)/X^2,-64*p.2))
        S S z z x x = c*logarithmicPhysicalSixMoment X S z m := by
  let e := logarithmicPhysicalCoordinates X hX.ne'
  obtain ⟨c,hc,hint⟩ := logCurve_rescaling_integral (F:=ℝ) e.symm
  refine ⟨c,hc,?_⟩
  intro ι S z m x hm hx
  let f := fun p : ℝ × ℝ => logarithmicPhysicalWeight X p*
    ‖sargosPlanarSum S z x (fun i => logCurve (1/4) (x i)) (e p).1 (e p).2‖^6
  have heq :
      logCurveWeightedBilinearMoment (1/4)
        (fun p : ℝ × ℝ => logarithmicPhysicalWeight X ((4*p.1+32*p.2)/X^2,-64*p.2))
        S S z z x x = ∫ p : ℝ × ℝ, f (e.symm p) := by
    unfold logCurveWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [f]
    rw [e.apply_symm_apply]
    change logarithmicPhysicalWeight X ((4*p.1+32*p.2)/X^2,-64*p.2)*
      ‖sargosPlanarSum S z x (fun i => logCurve (1/4) (x i)) p.1 p.2‖^2*
      ‖sargosPlanarSum S z x (fun i => logCurve (1/4) (x i)) p.1 p.2‖^4 =
      logarithmicPhysicalWeight X ((4*p.1+32*p.2)/X^2,-64*p.2)*
      ‖sargosPlanarSum S z x (fun i => logCurve (1/4) (x i)) p.1 p.2‖^6
    ring
  rw [heq,hint f,smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  dsimp only [f,logarithmicPhysicalSixMoment]
  rw [logarithmic_physical_sum_norm S z m x hX hm hx]
  rfl

/-- Genuine decoupling of the original physical square/log sums into
their actual finite cells. Band support and all moment transport factors
are derived, and the sole scale condition is the displayed geometric one. -/
theorem exists_logarithmicPhysicalSixMoment_dyadic {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (X : ℝ), 1 ≤ X →
      4/X ≤ (1/(2:ℝ)^n)^2 →
      ∀ (ι : Type) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (m x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ i∈S j, 0 < m j i) →
        (∀ j, ∀ i∈S j, (m j i)^2=X^2*(1+(1/4)*x j i)) →
        (∀ j, ∀ i∈S j, x j i∈Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        logarithmicPhysicalSixMoment X (Finset.univ.sigma S)
          (fun ji => z ji.1 ji.2) (fun ji => m ji.1 ji.2) ≤
          C*(2:ℝ)^(ε*n)*((2:ℝ)^n)^2*
            ∑ j, logarithmicPhysicalSixMoment X (S j) (z j) (m j) := by
  obtain ⟨D,hD,hdec⟩ := exists_logCurveDecouplingBound_dyadic (ε:=ε/6) (by positivity)
  refine ⟨D^6,by positivity,?_⟩
  intro n X hX hwidth ι S z m x hm hx hgrid
  have hX₀ : 0 < X := by linarith
  let W := fun p : ℝ × ℝ => logarithmicPhysicalWeight X
    ((4*p.1+32*p.2)/X^2,-64*p.2)
  have hW : LogCurveWeightBand (1/4) (1/((2^n:ℕ):ℝ)) W := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using logarithmicPhysicalWeight_band hX hwidth
  obtain ⟨c,hc,htransport⟩ := exists_logarithmicPhysicalSixMoment_transport hX₀
  have hcell (j : Fin (2^n)) :
      (logCurveWeightedSixNorm (1/4) W (S j) (z j) (x j))^6 =
      c*logarithmicPhysicalSixMoment X (S j) (z j) (m j) := by
    rw [logCurveWeightedSixNorm_pow_six (1/4) W hW.1 hW.2.1]
    exact htransport ι (S j) (z j) (m j) (x j) (hm j) (hx j)
  have hwhole :
      (logCurveWeightedSixNorm (1/4) W (Finset.univ.sigma S)
        (fun ji => z ji.1 ji.2) (fun ji => x ji.1 ji.2))^6 =
      c*logarithmicPhysicalSixMoment X (Finset.univ.sigma S)
        (fun ji => z ji.1 ji.2) (fun ji => m ji.1 ji.2) := by
    rw [logCurveWeightedSixNorm_pow_six (1/4) W hW.1 hW.2.1]
    exact htransport (Sigma fun _ : Fin (2^n) => ι) (Finset.univ.sigma S)
      (fun ji => z ji.1 ji.2) (fun ji => m ji.1 ji.2) (fun ji => x ji.1 ji.2)
      (fun ji hji => hm ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
      (fun ji hji => hx ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
  have hnorm := (hdec n).2 (1/4) (by norm_num) ι W hW S z x hgrid
  have hcube := pow_le_pow_left₀ (sq_nonneg _) hnorm 3
  simp only [mul_pow,←pow_mul] at hcube
  have hcoef : (D*(2:ℝ)^((ε/6)*n))^6=D^6*(2:ℝ)^(ε*n) := by
    rw [mul_pow,←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    congr 1
    push_cast
    ring
  norm_num only [show (2*3:ℕ)=6 by omega] at hcube
  rw [←mul_pow,hcoef] at hcube
  have hholder := pow_sum_le_card_mul_sum_pow (s:=Finset.univ)
    (f:=fun j => (logCurveWeightedSixNorm (1/4) W (S j) (z j) (x j))^2)
    (fun _ _ => sq_nonneg _) 2
  norm_num only [show (2+1:ℕ)=3 by omega,←pow_mul,
    show (2*3:ℕ)=6 by omega,Finset.card_univ,Fintype.card_fin,
    Nat.cast_pow,Nat.cast_ofNat] at hholder
  simp_rw [hcell] at hholder
  rw [←Finset.mul_sum] at hholder
  have hmain := hcube.trans (mul_le_mul_of_nonneg_left hholder
    (show 0 ≤ D^6*(2:ℝ)^(ε*n) by positivity))
  rw [hwhole] at hmain
  apply (mul_le_mul_iff_right₀ hc).mp
  convert hmain using 1
  ring

/-- The explicit rapid physical weight is dominated by the product weight
already handled by the short-cell theorem, uniformly over larger centers. -/
theorem exists_logarithmicPhysicalWeight_le_lorentz :
    ∃ C > (0:ℝ), ∀ (X A : ℝ), 0 < X → X ≤ A → ∀ p : ℝ × ℝ,
      logarithmicPhysicalWeight X p ≤ C*(1+p.1^2)⁻¹*(1+(p.2/A)^2)⁻¹ := by
  obtain ⟨D,hD,hdec⟩ := parabolaRapidKernel_decay 2
  have hkernel (R y : ℝ) :
      parabolaRapidKernel R 0 y ≤ D*(1+(y/R)^2)⁻¹ := by
    have h := hdec R 0 y
    simp only [sub_zero] at h
    have hs : 1+(y/R)^2 ≤ (1+|y/R|)^2 := by
      nlinarith [sq_abs (y/R),abs_nonneg (y/R)]
    have hp := (mul_le_mul_of_nonneg_right hs (parabolaRapidKernel_nonneg _ _ _)).trans h
    apply (le_div_iff₀ (by positivity : 0 < 1+(y/R)^2)).mpr
    simpa only [mul_comm] using hp
  refine ⟨D^2,by positivity,?_⟩
  intro X A hX hXA p
  have hA : 0 < A := hX.trans_le hXA
  have hα : parabolaRapidKernel 1 0 p.1 ≤ D*(1+p.1^2)⁻¹ := by
    simpa only [div_one] using hkernel 1 p.1
  have hratio : |p.2/A| ≤ |p.2/X| := by
    rw [abs_div,abs_div,abs_of_pos hA,abs_of_pos hX]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hX hXA
  have hs : (p.2/A)^2 ≤ (p.2/X)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hratio 2
  have ht : parabolaRapidKernel X 0 p.2 ≤ D*(1+(p.2/A)^2)⁻¹ :=
    (hkernel X p.2).trans (mul_le_mul_of_nonneg_left
      (inv_anti₀ (by positivity) (by linarith : 1+(p.2/A)^2 ≤ 1+(p.2/X)^2)) hD.le)
  have hp := mul_le_mul hα ht (parabolaRapidKernel_nonneg _ _ _) (by positivity)
  exact hp.trans_eq (by ring)

/-- The actual rapid-weighted physical short cell is bounded using the
native quadratic mean value estimate. Neither its moment nor its Fourier
support is supplied as a hypothesis. -/
theorem exists_logarithmicPhysicalSixMoment_short_cell {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
        (m : ι → ℤ) (X A δ B : ℝ) (L : ℤ),
        0 < X → X ≤ A → δ ≠ 0 → 0 ≤ B →
        |δ/A| ≤ 1/4 → |δ^3/A^2| ≤ 1 →
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        (∀ i∈S, δ*s i=(m i:ℝ)-A) →
        (∀ i∈S, L < m i ∧ m i ≤ L+Q) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        logarithmicPhysicalSixMoment X S z (fun i => (m i:ℝ)) ≤
          C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨D,hD,hweight⟩ := exists_logarithmicPhysicalWeight_le_lorentz
  obtain ⟨C,hC,hcell⟩ := exists_logarithmic_short_cell_product_weight hε
  refine ⟨D*C,by positivity,?_⟩
  intro Q hQ ι S z s m X A δ B L hX hXA hδ hB hscale hcubic hs hm hinterval hz
  have hA : 0 < A := hX.trans_le hXA
  let P := fun p : ℝ × ℝ => ‖∑ i∈S, z i*fordAdditiveCharacter
    (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ))‖^6
  have hPc : Continuous P := by unfold P fordAdditiveCharacter; fun_prop
  have hP₀ (p : ℝ × ℝ) : 0 ≤ P p := by dsimp [P]; positivity
  have hPb (p : ℝ × ℝ) : ‖P p‖ ≤ (∑ i∈S, ‖z i‖)^6 := by
    rw [Real.norm_of_nonneg (hP₀ p)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      _ ≤ ∑ i∈S, ‖z i*fordAdditiveCharacter
        (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]
  have hiL : Integrable (fun p : ℝ × ℝ => (1+p.1^2)⁻¹*(1+(p.2/A)^2)⁻¹*P p) :=
    (integrable_inv_one_add_sq.mul_prod
      (integrable_inv_one_add_sq.comp_div hA.ne')).mul_bdd hPc.aestronglyMeasurable
        (Filter.Eventually.of_forall hPb)
  have hiR : Integrable (fun p : ℝ × ℝ => logarithmicPhysicalWeight X p*P p) :=
    (logarithmicPhysicalWeight_integrable hX).mul_bdd hPc.aestronglyMeasurable
      (Filter.Eventually.of_forall hPb)
  have hmain : logarithmicPhysicalSixMoment X S z (fun i => (m i:ℝ)) ≤
      ∫ p : ℝ × ℝ, D*((1+p.1^2)⁻¹*(1+(p.2/A)^2)⁻¹*P p) := by
    apply integral_mono hiR (hiL.const_mul D)
    intro p
    exact (mul_le_mul_of_nonneg_right (hweight X A hX hXA p) (hP₀ p)).trans_eq (by ring)
  rw [integral_const_mul] at hmain
  have hprod := integral_prod_symm _ hiL
  rw [←Measure.volume_eq_prod] at hprod
  have hinter : (∫ p : ℝ × ℝ, (1+p.1^2)⁻¹*(1+(p.2/A)^2)⁻¹*P p) =
      ∫ t : ℝ, (1+(t/A)^2)⁻¹*(∫ α : ℝ, (1+α^2)⁻¹*P (α,t)) := by
    rw [hprod]
    apply integral_congr_ae
    filter_upwards with t
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with α
    ring
  rw [hinter] at hmain
  have hsource := hcell Q hQ ι S z s m A δ B L hA hδ hB hscale hcubic hs hm hinterval hz
  exact hmain.trans ((mul_le_mul_of_nonneg_left hsource hD.le).trans_eq (by ring))

private theorem logarithmic_grid_center {X K j : ℝ}
    (hX : 0 < X) (hK : 0 < K) (hj : 0 ≤ j) (hjK : j ≤ K) :
    let A := Real.sqrt (X^2*(1+j/(4*K)))
    X ≤ A ∧ A ≤ 2*X ∧ A^2=X^2*(1+j/(4*K)) := by
  dsimp
  have hu : 0 ≤ j/(4*K) := by positivity
  have hu₁ : j/(4*K) ≤ 1/4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*K)).mpr
    linarith
  have hsq := Real.sq_sqrt (show 0 ≤ X^2*(1+j/(4*K)) by positivity)
  have h₀ := Real.sqrt_nonneg (X^2*(1+j/(4*K)))
  have hl := mul_nonneg (sq_nonneg X) hu
  have hh := mul_le_mul_of_nonneg_left hu₁ (sq_nonneg X)
  exact ⟨by nlinarith,by nlinarith,hsq⟩

private theorem logarithmic_grid_radius {X K A : ℝ}
    (hX : 0 < X) (hK : 1 ≤ K) (hXA : X ≤ A) (hscale : X ≤ 16*K^2) :
    let δ := X/(8*K)
    0 < δ ∧ |δ/A| ≤ 1/4 ∧ |δ^3/A^2| ≤ 1 := by
  dsimp
  have hK₀ : 0 < K := by linarith
  have hA : 0 < A := hX.trans_le hXA
  have hδ : 0 < X/(8*K) := by positivity
  have hδle : X/(8*K) ≤ X/8 := by
    apply (div_le_iff₀ (by positivity : 0 < 8*K)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hK hX.le]
  refine ⟨hδ,?_,?_⟩
  · rw [abs_of_pos (div_pos hδ hA)]
    apply (div_le_iff₀ hA).mpr
    linarith
  · rw [abs_of_pos (by positivity : 0 < (X/(8*K))^3/A^2)]
    have hden : X^2 ≤ A^2 := by nlinarith
    have hcmp := div_le_div_of_nonneg_left (show 0 ≤ (X/(8*K))^3 by positivity)
      (sq_pos_of_pos hX) hden
    have he : (X/(8*K))^3/X^2=X/(512*K^3) := by field_simp; ring
    rw [he] at hcmp
    apply hcmp.trans
    apply (div_le_iff₀ (by positivity : 0 < 512*K^3)).mpr
    have hpow : K^2 ≤ K^3 := by nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hK)]
    nlinarith [sq_nonneg K]

private theorem logarithmic_grid_cell_range {X K j A m x : ℝ}
    (hX : 0 < X) (hK : 0 < K) (hXA : X ≤ A)
    (hA : A^2=X^2*(1+j/(4*K))) (hm : 0 < m)
    (hmx : m^2=X^2*(1+x/4)) (hx : x∈Icc (j/K) ((j+1)/K)) :
    A ≤ m ∧ m ≤ A+X/(8*K) := by
  have hxlo := (div_le_iff₀ hK).mp hx.1
  have hxhi := (le_div_iff₀ hK).mp hx.2
  have hdiff : m^2-A^2=X^2*(x-j/K)/4 := by
    rw [hmx,hA]
    field_simp
    ring
  have hlo : 0 ≤ m^2-A^2 := by
    rw [hdiff]
    exact div_nonneg (mul_nonneg (sq_nonneg X) (sub_nonneg.mpr hx.1)) (by norm_num)
  have hAm : A ≤ m := by nlinarith
  have hgap : m^2-A^2 ≤ X^2/(4*K) := by
    rw [hdiff]
    have h := mul_le_mul_of_nonneg_left
      (show x-j/K ≤ 1/K by apply (le_div_iff₀ hK).mpr; field_simp at hxlo ⊢; nlinarith)
      (sq_nonneg X)
    have hh := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 4)
    convert hh using 1
    field_simp
  have hfac := mul_nonneg (sub_nonneg.mpr hAm)
    (show 0 ≤ m+A-2*X by linarith)
  have he : 2*X*(X/(8*K))=X^2/(4*K) := by ring
  have hh : 2*X*(m-A) ≤ 2*X*(X/(8*K)) := by nlinarith
  have hbound := (mul_le_mul_iff_right₀ (show 0 < 2*X by positivity)).mp hh
  exact ⟨hAm,by linarith⟩

private theorem logarithmic_grid_integer_interval {X K A : ℝ}
    (hK : 1 ≤ K) (hscale : 4*K^2 ≤ X) :
    let Q := Nat.ceil (X/(8*K))+2
    let L := Int.floor A-1
    1 ≤ Q ∧ (Q:ℝ) ≤ X/K ∧
      ∀ m : ℤ, A ≤ (m:ℝ) → (m:ℝ) ≤ A+X/(8*K) → L < m ∧ m ≤ L+Q := by
  dsimp
  have hK₀ : 0 < K := by linarith
  have hX : 0 < X := by nlinarith
  have hδ : 0 ≤ X/(8*K) := by positivity
  have hceil := Nat.ceil_lt_add_one hδ
  have hfloor := Int.floor_le A
  have hfloor' := Int.lt_floor_add_one A
  have hceil' := Nat.le_ceil (X/(8*K))
  refine ⟨by omega,?_,?_⟩
  · push_cast
    have hratio : 4 ≤ X/K := by
      apply (le_div_iff₀ hK₀).mpr
      nlinarith
    have he : X/(8*K)=(X/K)/8 := by ring
    rw [he] at hceil ⊢
    linarith
  · intro m hmlo hmhi
    constructor
    · have hh : ((Int.floor A-1:ℤ):ℝ) < m := by push_cast; linarith
      exact_mod_cast hh
    · have hh : (m:ℝ) ≤ ((Int.floor A-1:ℤ):ℝ)+(Nat.ceil (X/(8*K))+2:ℕ) := by
        push_cast
        linarith
      exact_mod_cast hh

/-- An actual square-coordinate grid cell satisfies every analytic
short-cell hypothesis. The center, radius and integer interval are
constructed from its physical scale, not supplied independently. -/
theorem exists_logarithmicPhysicalSixMoment_grid_cell {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (X K j : ℝ), 1 ≤ K → 4*K^2 ≤ X → X ≤ 16*K^2 →
      0 ≤ j → j ≤ K → ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ)
        (m : ι → ℤ) (x : ι → ℝ) (B : ℝ), 0 ≤ B →
        (∀ i∈S, 0 < (m i:ℝ)) →
        (∀ i∈S, (m i:ℝ)^2=X^2*(1+(1/4)*x i)) →
        (∀ i∈S, x i∈Icc (j/K) ((j+1)/K)) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        logarithmicPhysicalSixMoment X S z (fun i => (m i:ℝ)) ≤
          C*X*B^6*(X/K)^((3:ℝ)+ε) := by
  obtain ⟨C,hC,hcell⟩ := exists_logarithmicPhysicalSixMoment_short_cell hε
  refine ⟨2*C,by positivity,?_⟩
  intro X K j hK hl hu hj hjK ι S z m x B hB hm hx hgrid hz
  have hK₀ : 0 < K := by linarith
  have hX : 0 < X := by nlinarith
  let A := Real.sqrt (X^2*(1+j/(4*K)))
  let δ := X/(8*K)
  let Q := Nat.ceil δ+2
  let L := Int.floor A-1
  obtain ⟨hXA,hAX,hAsq⟩ := logarithmic_grid_center hX hK₀ hj hjK
  change X ≤ A at hXA
  change A ≤ 2*X at hAX
  obtain ⟨hδ,hδA,hcubic⟩ := logarithmic_grid_radius hX hK hXA hu
  change 0 < δ at hδ
  obtain ⟨hQ,hQbound,hinterval⟩ := logarithmic_grid_integer_interval (A:=A) hK hl
  change 1 ≤ Q at hQ
  change (Q:ℝ) ≤ X/K at hQbound
  have hrange (i : ι) (hi : i∈S) : A ≤ (m i:ℝ) ∧ (m i:ℝ) ≤ A+δ := by
    exact logarithmic_grid_cell_range hX hK₀ hXA hAsq (hm i hi)
      (by convert hx i hi using 1; ring) (hgrid i hi)
  have hs (i : ι) (hi : i∈S) : ((m i:ℝ)-A)/δ∈Icc (-1:ℝ) 1 := by
    have hh := hrange i hi
    constructor
    · apply (le_div_iff₀ hδ).mpr
      linarith
    · apply (div_le_iff₀ hδ).mpr
      linarith
  have hmul (i : ι) (_hi : i∈S) : δ*(((m i:ℝ)-A)/δ)=(m i:ℝ)-A := by
    field_simp
  have hI (i : ι) (hi : i∈S) : L < m i ∧ m i ≤ L+Q :=
    hinterval (m i) (hrange i hi).1 (hrange i hi).2
  have hh := hcell Q hQ ι S z (fun i => ((m i:ℝ)-A)/δ) m X A δ B L
    hX hXA hδ.ne' hB hδA hcubic hs hmul hI hz
  have hp : (Q:ℝ)^((3:ℝ)+ε) ≤ (X/K)^((3:ℝ)+ε) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hQbound (by positivity)
  calc
    _ ≤ C*A*B^6*(Q:ℝ)^((3:ℝ)+ε) := hh
    _ ≤ C*(2*X)*B^6*(X/K)^((3:ℝ)+ε) := by gcongr
    _ = _ := by ring

private theorem logarithmic_grid_scale_identity {X : ℝ} (hX : 0 < X)
    (n : ℕ) (ε : ℝ) :
    (2:ℝ)^(ε*n)*((2:ℝ)^n)^3*X*(X/(2:ℝ)^n)^((3:ℝ)+ε) = X^((4:ℝ)+ε) := by
  have hK : 0 < (2:ℝ)^n := by positivity
  have he : (2:ℝ)^(ε*n)=((2:ℝ)^n)^ε := by
    rw [mul_comm,Real.rpow_natCast_mul (by norm_num)]
  rw [he]
  generalize (2:ℝ)^n = K at hK ⊢
  rw [Real.div_rpow hX.le hK.le,Real.rpow_add hX,
    Real.rpow_add hK,Real.rpow_add hX]
  norm_num only [Real.rpow_natCast,Real.rpow_ofNat]
  have hr : K^ε ≠ 0 := (Real.rpow_pos_of_pos hK ε).ne'
  field_simp

/-- Physical grid assembly with every cell estimate discharged. This is
the rapid-weighted logarithmic sixth moment for the actual integer arrays,
not a theorem conditional on a local moment bound. -/
theorem exists_logarithmicPhysicalSixMoment_grid {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (X : ℝ),
      4*((2:ℝ)^n)^2 ≤ X → X ≤ 16*((2:ℝ)^n)^2 →
      ∀ (ι : Type) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (m : Fin (2^n) → ι → ℤ)
        (x : Fin (2^n) → ι → ℝ) (B : ℝ), 0 ≤ B →
        (∀ j, ∀ i∈S j, 0 < (m j i:ℝ)) →
        (∀ j, ∀ i∈S j, (m j i:ℝ)^2=X^2*(1+(1/4)*x j i)) →
        (∀ j, ∀ i∈S j, x j i∈Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        (∀ j, ∀ k : ℤ, (∑ i∈(S j).filter (fun i => m j i=k), ‖z j i‖) ≤ B) →
        logarithmicPhysicalSixMoment X (Finset.univ.sigma S)
          (fun ji => z ji.1 ji.2) (fun ji => (m ji.1 ji.2:ℝ)) ≤
          C*B^6*X^((4:ℝ)+ε) := by
  obtain ⟨D,hD,hdec⟩ := exists_logarithmicPhysicalSixMoment_dyadic hε
  obtain ⟨C,hC,hcell⟩ := exists_logarithmicPhysicalSixMoment_grid_cell hε
  refine ⟨D*C,by positivity,?_⟩
  intro n X hl hu ι S z m x B hB hm hx hgrid hz
  have hK : 1 ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
  have hX : 1 ≤ X := by nlinarith
  have hX₀ : 0 < X := by linarith
  have hwidth : 4/X ≤ (1/(2:ℝ)^n)^2 := by
    rw [div_pow,one_pow]
    apply (div_le_div_iff₀ hX₀ (by positivity)).mpr
    simpa only [one_mul] using hl
  have hmain := hdec n X hX hwidth ι S z (fun j i => (m j i:ℝ)) x hm hx hgrid
  have hcells (j : Fin (2^n)) :
      logarithmicPhysicalSixMoment X (S j) (z j) (fun i => (m j i:ℝ)) ≤
        C*X*B^6*(X/(2:ℝ)^n)^((3:ℝ)+ε) := by
    apply hcell X ((2:ℝ)^n) (j:ℕ) hK hl hu (Nat.cast_nonneg _) ?_
      ι (S j) (z j) (m j) (x j) B hB (hm j) (hx j) ?_ (hz j)
    · exact_mod_cast j.isLt.le
    · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hgrid j
  have hsum := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hcells j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_pow,Nat.cast_ofNat] at hsum
  have hh := hmain.trans (mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ D*(2:ℝ)^(ε*n)*((2:ℝ)^n)^2 by positivity))
  have he : D*(2:ℝ)^(ε*n)*((2:ℝ)^n)^2*
      ((2:ℝ)^n*(C*X*B^6*(X/(2:ℝ)^n)^((3:ℝ)+ε))) =
      (D*C)*B^6*X^((4:ℝ)+ε) := by
    calc
      _ = (D*C)*B^6*((2:ℝ)^(ε*n)*((2:ℝ)^n)^3*X*
        (X/(2:ℝ)^n)^((3:ℝ)+ε)) := by ring
      _ = _ := by rw [logarithmic_grid_scale_identity hX₀]
  exact hh.trans_eq he

-- Reuse of the existing Bourgain closed-endpoint finite-grid argument.
private def logarithmicClosedGridCell (n : ℕ) (x : ℝ) : Fin (2^n) :=
  ⟨min ⌊((2^n:ℕ):ℝ)*x⌋₊ (2^n-1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (by positivity) (by decide))⟩

private theorem logarithmicClosedGridCell_mem (n : ℕ) {x : ℝ}
    (hx : x∈Icc (0:ℝ) 1) :
    x∈Icc (((logarithmicClosedGridCell n x:ℕ):ℝ)/((2^n:ℕ):ℝ))
      ((((logarithmicClosedGridCell n x:ℕ):ℝ)+1)/((2^n:ℕ):ℝ)) := by
  let M := 2^n
  have hM : 0<M := by dsimp [M]; positivity
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hlo := Nat.floor_le (mul_nonneg hMr.le hx.1)
  have hmin : ((min ⌊(M:ℝ)*x⌋₊ (M-1):ℕ):ℝ)≤⌊(M:ℝ)*x⌋₊ := by
    exact_mod_cast min_le_left ⌊(M:ℝ)*x⌋₊ (M-1)
  change x∈Icc (((min ⌊(M:ℝ)*x⌋₊ (M-1):ℕ):ℝ)/M)
    ((((min ⌊(M:ℝ)*x⌋₊ (M-1):ℕ):ℝ)+1)/M)
  constructor
  · apply (div_le_iff₀ hMr).mpr
    nlinarith [hmin.trans hlo]
  · apply (le_div_iff₀ hMr).mpr
    by_cases hc : ⌊(M:ℝ)*x⌋₊≤M-1
    · rw [min_eq_left hc]
      have hh := Nat.lt_floor_add_one ((M:ℝ)*x)
      linarith
    · rw [min_eq_right (le_of_not_ge hc)]
      have hm : M-1+1=M := Nat.sub_add_cancel hM
      have hm' : ((M-1:ℕ):ℝ)+1=M := by exact_mod_cast hm
      rw [hm']
      nlinarith [hx.2]

/-- A physical positive-frequency block enters the proved logarithmic
decoupling chain through its exact square coordinate. The grid scale and
partition are constructed, including closed endpoints and coefficient fibers. -/
theorem exists_logarithmicPhysicalSixMoment_block {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (X : ℝ), 4 ≤ X →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (B : ℝ), 0 ≤ B →
        (∀ i∈S, 0 < (m i:ℝ)) →
        (∀ i∈S, (m i:ℝ)^2∈Icc (X^2) (5*X^2/4)) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        logarithmicPhysicalSixMoment X S z (fun i => (m i:ℝ)) ≤ C*B^6*X^((4:ℝ)+ε) := by
  classical
  obtain ⟨C,hC,hgrid⟩ := exists_logarithmicPhysicalSixMoment_grid hε
  refine ⟨C,hC,?_⟩
  intro X hX ι S z m B hB hm hblock hz
  have hX₀ : 0 < X := by linarith
  obtain ⟨n,hnlo,hnhi⟩ := exists_nat_pow_near (show (1:ℝ) ≤ X/4 by linarith)
    (by norm_num : (1:ℝ) < 4)
  have hpow : (4:ℝ)^n=((2:ℝ)^n)^2 := by
    rw [←pow_mul,pow_mul']
    norm_num
  have hl : 4*((2:ℝ)^n)^2 ≤ X := by rw [hpow] at hnlo; linarith
  have hu : X ≤ 16*((2:ℝ)^n)^2 := by rw [pow_succ,hpow] at hnhi; linarith
  let x := fun i => 4*((m i:ℝ)^2/X^2-1)
  let g := fun i => logarithmicClosedGridCell n (x i)
  let U := fun j => S.filter (fun i => g i=j)
  have hx (i : ι) (hi : i∈S) : x i∈Icc (0:ℝ) 1 := by
    have hh := hblock i hi
    have hlo : 1 ≤ (m i:ℝ)^2/X^2 := (le_div_iff₀ (sq_pos_of_pos hX₀)).mpr (by simpa using hh.1)
    have hhi : (m i:ℝ)^2/X^2 ≤ 5/4 :=
      (div_le_iff₀ (sq_pos_of_pos hX₀)).mpr (by linarith only [hh.2])
    dsimp only [x]
    constructor <;> linarith
  have hsq (i : ι) (_hi : i∈S) : (m i:ℝ)^2=X^2*(1+(1/4)*x i) := by
    dsimp only [x]
    field_simp
    ring
  have hcell (j : Fin (2^n)) (i : ι) (hi : i∈U j) :
      x i∈Icc ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ)) := by
    obtain ⟨hi,hgi⟩ := Finset.mem_filter.mp hi
    have hh := logarithmicClosedGridCell_mem n (hx i hi)
    change x i∈Icc ((g i:ℕ)/((2^n:ℕ):ℝ)) (((g i:ℕ)+1)/((2^n:ℕ):ℝ)) at hh
    rwa [hgi] at hh
  have hfiber (j : Fin (2^n)) (k : ℤ) :
      (∑ i∈(U j).filter (fun i => m i=k), ‖z i‖) ≤ B := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)) (hz k)
    intro i hi
    obtain ⟨hi,hmk⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,hmk⟩
  have hh := hgrid n X hl hu ι U (fun _ => z) (fun _ => m) (fun _ => x) B hB
    (fun _ i hi => hm i (Finset.mem_filter.mp hi).1)
    (fun _ i hi => hsq i (Finset.mem_filter.mp hi).1) hcell hfiber
  have heq : logarithmicPhysicalSixMoment X (Finset.univ.sigma U)
      (fun ji => z ji.2) (fun ji => (m ji.2:ℝ)) =
      logarithmicPhysicalSixMoment X S z (fun i => (m i:ℝ)) := by
    unfold logarithmicPhysicalSixMoment
    apply integral_congr_ae
    filter_upwards with p
    congr 2
    rw [Finset.sum_sigma]
    apply congrArg norm
    exact Finset.sum_fiberwise_of_maps_to (fun i (_hi : i∈S) => Finset.mem_univ (g i))
      (fun i => z i*fordAdditiveCharacter (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ)))
  rwa [heq] at hh

theorem logarithmicPhysical_box_le {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℝ) {X : ℝ} (hX : 0 < X) :
    (∫ t : ℝ in Icc (-X) X, ∫ α : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i)^2+t*Real.log (m i))‖^6) ≤
      logarithmicPhysicalSixMoment X S z m := by
  let P := fun p : ℝ × ℝ => ‖∑ i∈S, z i*fordAdditiveCharacter
    (p.1*(m i)^2+p.2*Real.log (m i))‖^6
  let B := Icc (0:ℝ) 1 ×ˢ Icc (-X) X
  have hPc : Continuous P := by unfold P fordAdditiveCharacter; fun_prop
  have hP₀ (p : ℝ × ℝ) : 0 ≤ P p := by dsimp [P]; positivity
  have hPb (p : ℝ × ℝ) : ‖P p‖ ≤ (∑ i∈S, ‖z i‖)^6 := by
    rw [Real.norm_of_nonneg (hP₀ p)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    calc
      _ ≤ ∑ i∈S, ‖z i*fordAdditiveCharacter
        (p.1*(m i)^2+p.2*Real.log (m i))‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]
  have hiP : IntegrableOn P B :=
    hPc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hiW : Integrable (fun p : ℝ × ℝ => logarithmicPhysicalWeight X p*P p) :=
    (logarithmicPhysicalWeight_integrable hX).mul_bdd hPc.aestronglyMeasurable
      (Filter.Eventually.of_forall hPb)
  have hpoint (p : ℝ × ℝ) (hp : p∈B) : P p ≤ logarithmicPhysicalWeight X p*P p := by
    have hα : |p.1| ≤ 1 := abs_le.mpr ⟨by linarith [hp.1.1],hp.1.2⟩
    have ht : |p.2| ≤ X := abs_le.mpr hp.2
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (logarithmicPhysicalWeight_one_le hX hα ht) (hP₀ p)
  have hlocal := setIntegral_mono_on hiP hiW.integrableOn
    (measurableSet_Icc.prod measurableSet_Icc) hpoint
  have hwhole := setIntegral_le_integral (s:=B) hiW
    (Filter.Eventually.of_forall (fun p => mul_nonneg
      (logarithmicPhysicalWeight_nonneg X p) (hP₀ p)))
  have hiProd : Integrable P
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (Icc (-X) X))) := by
    rwa [Measure.prod_restrict,←Measure.volume_eq_prod]
  have hprod := integral_prod_symm P hiProd
  rw [Measure.prod_restrict,←Measure.volume_eq_prod] at hprod
  change (∫ p in B, P p)=_ at hprod
  rw [hprod] at hlocal
  exact hlocal.trans hwhole

/-- Literal translated time windows for an original integer frequency
block. Time modulation preserves all coefficient-fiber norms. -/
theorem exists_logarithmic_block_sixth_translated {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (X : ℝ), 4 ≤ X →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (B t₀ : ℝ), 0 ≤ B →
        (∀ i∈S, 0 < (m i:ℝ)) →
        (∀ i∈S, (m i:ℝ)^2∈Icc (X^2) (5*X^2/4)) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        (∫ t : ℝ in Icc (-X) X, ∫ α : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter
            (α*(m i:ℝ)^2+(t+t₀)*Real.log (m i:ℝ))‖^6) ≤ C*B^6*X^((4:ℝ)+ε) := by
  obtain ⟨C,hC,hblock⟩ := exists_logarithmicPhysicalSixMoment_block hε
  refine ⟨C,hC,?_⟩
  intro X hX ι S z m B t₀ hB hm hrange hz
  let c := fun i => z i*fordAdditiveCharacter (t₀*Real.log (m i:ℝ))
  have hcn (i : ι) : ‖c i‖=‖z i‖ := by
    simp only [c,norm_mul,sargos_character_norm,mul_one]
  have hcz (k : ℤ) : (∑ i∈S.filter (fun i => m i=k), ‖c i‖) ≤ B := by
    simpa only [hcn] using hz k
  have hmain := (logarithmicPhysical_box_le S c (fun i => (m i:ℝ))
    (by linarith : 0 < X)).trans (hblock X hX ι S c m B hB hm hrange hcz)
  have he (α t : ℝ) :
      (∑ i∈S, c i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))) =
      ∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+(t+t₀)*Real.log (m i:ℝ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [c]
    rw [mul_assoc,←fordAdditiveCharacter_add]
    congr 2
    ring
  simpa only [he] using hmain

private theorem logSix_long_window {A T M : ℝ} (hA : 0 < A) (hT : 0 ≤ T)
    (f : ℝ → ℝ) (hf : Continuous f) (hf₀ : ∀ t, 0 ≤ f t)
    (hwindow : ∀ x, (∫ t : ℝ in Icc (-A) A, f (t+x)) ≤ M) :
    (∫ t : ℝ in Icc (-T) T, f t) ≤ (T/A+1)*M := by
  let q := Nat.ceil (T/A)
  let a := fun k : ℕ => -T+2*A*k
  have hM : 0 ≤ M := (integral_nonneg (fun t => hf₀ (t+0))).trans (hwindow 0)
  have hceil : T/A ≤ (q:ℝ) := Nat.le_ceil _
  have hTq : T ≤ A*q := (div_le_iff₀ hA).mp hceil |>.trans_eq (by ring)
  have hcover : Icc (-T) T ⊆ Icc (a 0) (a q) := by
    intro t ht
    dsimp only [a]
    norm_num only [Nat.cast_zero,mul_zero,add_zero]
    exact ⟨ht.1,by linarith [ht.2]⟩
  have hmono := setIntegral_mono_set
    (hf.continuousOn.integrableOn_compact (μ:=volume) (K:=Icc (a 0) (a q)) isCompact_Icc)
    (Filter.Eventually.of_forall hf₀) (Filter.Eventually.of_forall hcover)
  have hcell (k : ℕ) : (∫ t : ℝ in a k..a (k+1), f t) ≤ M := by
    let c := -T+2*A*k+A
    have hh := hwindow c
    rw [integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le (by linarith : -A ≤ A),
      intervalIntegral.integral_comp_add_right] at hh
    have ha : -A+c=a k := by dsimp [a,c]; ring
    have hb : A+c=a (k+1) := by dsimp [a,c]; push_cast; ring
    rwa [ha,hb] at hh
  have hsum := Finset.sum_le_sum (fun k (_hk : k∈Finset.range q) => hcell k)
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ => hf.intervalIntegrable (a k) (a (k+1)))] at hsum
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  have ha : a 0 ≤ a q := by
    dsimp only [a]
    norm_num only [Nat.cast_zero,mul_zero,add_zero]
    linarith [mul_nonneg (show 0 ≤ 2*A by positivity) (Nat.cast_nonneg q)]
  rw [intervalIntegral.integral_of_le ha,←integral_Icc_eq_integral_Ioc] at hsum
  have hq : (q:ℝ) ≤ T/A+1 := (Nat.ceil_lt_add_one (div_nonneg hT hA.le)).le
  exact (hmono.trans hsum).trans (mul_le_mul_of_nonneg_right hq hM)

/-- Arbitrary physical time lengths for an original logarithmic frequency
block, with the sharp linear time factor. Adjacent translated windows,
not a supplied long-interval moment, give the estimate. -/
theorem exists_logarithmic_block_sixth {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (X T : ℝ), 4 ≤ X → 0 ≤ T →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (B : ℝ), 0 ≤ B →
        (∀ i∈S, 0 < (m i:ℝ)) →
        (∀ i∈S, (m i:ℝ)^2∈Icc (X^2) (5*X^2/4)) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        (∫ t : ℝ in Icc (-T) T, ∫ α : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter
            (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6) ≤ C*B^6*(T+X)*X^((3:ℝ)+ε) := by
  obtain ⟨C,hC,hblock⟩ := exists_logarithmic_block_sixth_translated hε
  refine ⟨C,hC,?_⟩
  intro X T hX hT ι S z m B hB hm hrange hz
  have hX₀ : 0 < X := by linarith
  let P := fun (t α : ℝ) => ‖∑ i∈S, z i*fordAdditiveCharacter
    (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6
  let f := fun t => ∫ α : ℝ in Icc (0:ℝ) 1, P t α
  have hPc : Continuous (Function.uncurry P) := by
    unfold P Function.uncurry fordAdditiveCharacter
    fun_prop
  have hfc : Continuous f := by
    have hh := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ:=volume) (f:=P) hPc 0 1
    simpa only [f,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)] using hh
  have hwindow (x : ℝ) : (∫ t : ℝ in Icc (-X) X, f (t+x)) ≤ C*B^6*X^((4:ℝ)+ε) :=
    hblock X hX ι S z m B x hB hm hrange hz
  have hh := logSix_long_window hX₀ hT f hfc
    (fun t => integral_nonneg (fun α => by dsimp [P]; positivity)) hwindow
  have he : (T/X+1)*(C*B^6*X^((4:ℝ)+ε))=C*B^6*(T+X)*X^((3:ℝ)+ε) := by
    rw [show (4:ℝ)+ε=((3:ℝ)+ε)+1 by ring,Real.rpow_add_one hX₀.ne']
    field_simp
  exact hh.trans_eq he

def logarithmicSixMoment {ι : Type*} (T : ℝ)
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) : ℝ :=
  ∫ t : ℝ in Icc (-T) T, ∫ α : ℝ in Icc (0:ℝ) 1,
    ‖∑ i∈S, z i*fordAdditiveCharacter (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6

private theorem logarithmicSixMoment_eq_prod {ι : Type*} (T : ℝ)
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) :
    logarithmicSixMoment T S z m =
      ∫ p : ℝ × ℝ in Icc (0:ℝ) 1 ×ˢ Icc (-T) T,
        ‖∑ i∈S, z i*fordAdditiveCharacter (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ))‖^6 := by
  let P := fun p : ℝ × ℝ => ‖∑ i∈S, z i*fordAdditiveCharacter
    (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ))‖^6
  have hP : Continuous P := by unfold P fordAdditiveCharacter; fun_prop
  have hi := hP.continuousOn.integrableOn_compact (μ:=volume)
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (-T) T))
  rw [IntegrableOn,Measure.volume_eq_prod,←Measure.prod_restrict] at hi
  have hh := integral_prod_symm P hi
  rw [Measure.prod_restrict,←Measure.volume_eq_prod] at hh
  exact hh.symm

private theorem logarithmicSixMoment_fiberwise {ι : Type*} {K : ℕ}
    (T : ℝ) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (g : ι → Fin K) :
    logarithmicSixMoment T S z m ≤
      (K:ℝ)^5*∑ j, logarithmicSixMoment T (S.filter (fun i => g i=j)) z m := by
  classical
  let R := Icc (0:ℝ) 1 ×ˢ Icc (-T) T
  let A := fun (j : Fin K) (p : ℝ × ℝ) => ∑ i∈S.filter (fun i => g i=j),
    z i*fordAdditiveCharacter (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ))
  let F := fun p : ℝ × ℝ => ‖∑ i∈S, z i*fordAdditiveCharacter
    (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ))‖^6
  have hAc (j : Fin K) : Continuous (fun p => ‖A j p‖^6) := by
    unfold A fordAdditiveCharacter
    fun_prop
  have hFc : Continuous F := by unfold F fordAdditiveCharacter; fun_prop
  have hiA (j : Fin K) : IntegrableOn (fun p => ‖A j p‖^6) R :=
    (hAc j).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hiSum : IntegrableOn (fun p => (K:ℝ)^5*∑ j, ‖A j p‖^6) R :=
    (integrable_finsetSum _ (fun j _ => hiA j)).const_mul _
  have hpoint (p : ℝ × ℝ) : F p ≤ (K:ℝ)^5*∑ j, ‖A j p‖^6 := by
    have he : (∑ j, A j p)=∑ i∈S, z i*fordAdditiveCharacter
        (p.1*(m i:ℝ)^2+p.2*Real.log (m i:ℝ)) :=
      Finset.sum_fiberwise_of_maps_to (fun i (_hi : i∈S) => Finset.mem_univ (g i)) _
    have hn := pow_le_pow_left₀ (norm_nonneg (∑ j, A j p))
      (norm_sum_le Finset.univ (fun j => A j p)) 6
    have hh := pow_sum_le_card_mul_sum_pow (s:=Finset.univ)
      (f:=fun j => ‖A j p‖) (fun _ _ => norm_nonneg _) 5
    simp only [show (5+1:ℕ)=6 by omega,Finset.card_univ,Fintype.card_fin] at hh
    simpa only [he,F] using hn.trans hh
  have hmain := setIntegral_mono_on
    (hFc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    hiSum (measurableSet_Icc.prod measurableSet_Icc) (fun p _ => hpoint p)
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => hiA j)] at hmain
  simp only [logarithmicSixMoment_eq_prod]
  exact hmain

/-- A full dyadic frequency shell follows by the existing closed-endpoint
partition into sixteen genuine logarithmic blocks. -/
theorem exists_logarithmic_dyadic_sixth {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (X T : ℝ), 4 ≤ X → 0 ≤ T →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (B : ℝ), 0 ≤ B →
        (∀ i∈S, (m i:ℝ)∈Icc X (2*X)) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        logarithmicSixMoment T S z m ≤ C*B^6*(T+X)*X^((3:ℝ)+ε) := by
  classical
  obtain ⟨C,hC,hblock⟩ := exists_logarithmic_block_sixth hε
  refine ⟨16^6*C*(2:ℝ)^((4:ℝ)+ε),by positivity,?_⟩
  intro X T hX hT ι S z m B hB hm hz
  have hX₀ : 0 < X := by linarith
  let x := fun i => (m i:ℝ)/X-1
  let g := fun i => logarithmicClosedGridCell 4 (x i)
  let U := fun j => S.filter (fun i => g i=j)
  let A := fun j : Fin (2^4) => X*(1+(j:ℕ)/16)
  have hA (j : Fin (2^4)) : X ≤ A j ∧ A j ≤ 2*X := by
    have hj : (0:ℝ) ≤ (j:ℕ) := Nat.cast_nonneg _
    have hj' : ((j:ℕ):ℝ) ≤ 16 := by exact_mod_cast (show (j:ℕ) ≤ 16 by omega)
    have hlo := mul_nonneg hX₀.le hj
    have hhi := mul_le_mul_of_nonneg_left hj' hX₀.le
    dsimp only [A]
    constructor <;> nlinarith
  have hx (i : ι) (hi : i∈S) : x i∈Icc (0:ℝ) 1 := by
    have hh := hm i hi
    have hlo : 1 ≤ (m i:ℝ)/X := (le_div_iff₀ hX₀).mpr (by simpa only [one_mul] using hh.1)
    have hhi : (m i:ℝ)/X ≤ 2 := (div_le_iff₀ hX₀).mpr hh.2
    dsimp only [x]
    constructor <;> linarith
  have hxeq (i : ι) : (m i:ℝ)=X*(1+x i) := by dsimp [x]; field_simp; ring
  have hrange (j : Fin (2^4)) (i : ι) (hi : i∈U j) :
      A j ≤ (m i:ℝ) ∧ (m i:ℝ) ≤ (17/16)*A j := by
    obtain ⟨hi,hgi⟩ := Finset.mem_filter.mp hi
    have hh := logarithmicClosedGridCell_mem 4 (hx i hi)
    change x i∈Icc ((g i:ℕ)/((2^4:ℕ):ℝ)) (((g i:ℕ)+1)/((2^4:ℕ):ℝ)) at hh
    rw [hgi] at hh
    norm_num only [Nat.reducePow,Nat.cast_ofNat] at hh
    have hlo := mul_le_mul_of_nonneg_left hh.1 hX₀.le
    have hhi := mul_le_mul_of_nonneg_left hh.2 hX₀.le
    have hcenter := (hA j).1
    rw [hxeq i]
    dsimp only [A] at hcenter ⊢
    constructor <;> nlinarith
  have hfiber (j : Fin (2^4)) (k : ℤ) :
      (∑ i∈(U j).filter (fun i => m i=k), ‖z i‖) ≤ B := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)) (hz k)
    intro i hi
    obtain ⟨hi,hk⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,hk⟩
  have hcell (j : Fin (2^4)) : logarithmicSixMoment T (U j) z m ≤
      C*(2:ℝ)^((4:ℝ)+ε)*B^6*(T+X)*X^((3:ℝ)+ε) := by
    have hAj : 4 ≤ A j := hX.trans (hA j).1
    have hmj (i : ι) (hi : i∈U j) : 0 < (m i:ℝ) := by
      have hh := (hrange j i hi).1
      linarith
    have hsq (i : ι) (hi : i∈U j) :
        (m i:ℝ)^2∈Icc ((A j)^2) (5*(A j)^2/4) := by
      have hh := hrange j i hi
      have hpos := hmj i hi
      constructor
      · nlinarith
      · have hprod := mul_nonneg (sub_nonneg.mpr hh.2)
          (show 0 ≤ (17/16)*A j+(m i:ℝ) by positivity)
        nlinarith [sq_nonneg (A j)]
    have hh := hblock (A j) T hAj hT ι (U j) z m B hB hmj hsq (hfiber j)
    have hmono : C*B^6*(T+A j)*(A j)^((3:ℝ)+ε) ≤
        C*B^6*(2*(T+X))*(2*X)^((3:ℝ)+ε) := by gcongr <;> linarith [(hA j).2]
    apply hh.trans (hmono.trans_eq ?_)
    rw [Real.mul_rpow (by norm_num) hX₀.le,
      show (4:ℝ)+ε=((3:ℝ)+ε)+1 by ring,Real.rpow_add_one (by norm_num : (2:ℝ) ≠ 0)]
    ring
  have hsum := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hcell j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hh := (logarithmicSixMoment_fiberwise T S z m g).trans
    (mul_le_mul_of_nonneg_left hsum (by positivity))
  norm_num only [Nat.reducePow,Nat.cast_ofNat] at hh
  exact hh.trans_eq (by ring)

private theorem logarithmicSixMoment_small {ι : Type*} {T B : ℝ}
    (hT : 0 ≤ T) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ)
    (hm : ∀ i∈S, 1 ≤ m i ∧ m i ≤ 4)
    (hz : ∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) :
    logarithmicSixMoment T S z m ≤ 2*T*(4*B)^6 := by
  classical
  have hmass : (∑ i∈S, ‖z i‖) ≤ 4*B := by
    have he := Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_Icc.mpr (hm i hi)) (fun i => ‖z i‖)
    rw [←he]
    apply (Finset.sum_le_sum (fun k (_hk : k∈Finset.Icc (1:ℤ) 4) => hz k)).trans_eq
    norm_num [show Int.toNat (4:ℤ)=4 by decide]
  let P := fun (t α : ℝ) => ‖∑ i∈S, z i*fordAdditiveCharacter
    (α*(m i:ℝ)^2+t*Real.log (m i:ℝ))‖^6
  have hP₀ (t α : ℝ) : 0 ≤ P t α := by dsimp [P]; positivity
  have hb (t α : ℝ) : ‖P t α‖ ≤ (4*B)^6 := by
    rw [Real.norm_of_nonneg (hP₀ t α)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have hh := norm_sum_le S (fun i => z i*fordAdditiveCharacter
      (α*(m i:ℝ)^2+t*Real.log (m i:ℝ)))
    simp only [norm_mul,sargos_character_norm,mul_one] at hh
    exact hh.trans hmass
  have hinner (t : ℝ) : (∫ α : ℝ in Icc (0:ℝ) 1, P t α) ≤ (4*B)^6 := by
    have hh := norm_setIntegral_le_of_norm_le_const_ae
      (μ:=volume) (s:=Icc (0:ℝ) 1) (f:=P t) isCompact_Icc.measure_lt_top
      (Filter.Eventually.of_forall (hb t))
    rw [Real.norm_of_nonneg (integral_nonneg (hP₀ t))] at hh
    simpa only [Real.volume_real_Icc_of_le (by norm_num : (0:ℝ) ≤ 1),sub_zero,mul_one] using hh
  have hmain : (∫ t : ℝ in Icc (-T) T, ∫ α : ℝ in Icc (0:ℝ) 1, P t α) ≤
      ∫ _t : ℝ in Icc (-T) T, (4*B)^6 := by
    have hc : IntegrableOn (fun _t : ℝ => (4*B)^6) (Icc (-T) T) :=
      integrableOn_const isCompact_Icc.measure_ne_top
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => integral_nonneg (hP₀ t))) hc
    exact Filter.Eventually.of_forall hinner
  have he : (∫ _t : ℝ in Icc (-T) T, (4*B)^6)=2*T*(4*B)^6 := by
    rw [setIntegral_const,smul_eq_mul,Real.volume_real_Icc_of_le (by linarith : -T ≤ T)]
    ring
  exact hmain.trans_eq he

/-- Full positive integer frequency range, before absorbing the explicit
sixth power of the dyadic shell count. The low frequencies are included. -/
theorem exists_logarithmic_sixth_log_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (B : ℝ), 0 ≤ B →
        (∀ i∈S, 1 ≤ m i ∧ m i ≤ N) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        logarithmicSixMoment T S z m ≤
          C*((Nat.log 2 N+1:ℕ):ℝ)^6*B^6*(T+N)*(N:ℝ)^((3:ℝ)+ε) := by
  classical
  obtain ⟨D,hD,hdyadic⟩ := exists_logarithmic_dyadic_sixth hε
  let C := max D (2*4^6)
  have hC : 0 < C := hD.trans_le (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro N hN T hT ι S z m B hB hm hz
  let K := Nat.log 2 N+1
  let p := fun i => (m i).toNat
  let g := fun i => (⟨min (Nat.log 2 (p i)) (Nat.log 2 N),
    (min_le_right _ _).trans_lt (Nat.lt_succ_self _)⟩ : Fin K)
  let U := fun j => S.filter (fun i => g i=j)
  have hp (i : ι) (hi : i∈S) : 1 ≤ p i ∧ p i ≤ N := by
    have hh := hm i hi
    dsimp only [p]
    omega
  have hpInt (i : ι) (hi : i∈S) : (p i:ℤ)=m i :=
    Int.toNat_of_nonneg (by have := (hm i hi).1; omega)
  have hlabel (j : Fin K) (i : ι) (hi : i∈U j) : Nat.log 2 (p i)=(j:ℕ) := by
    obtain ⟨hi,hgi⟩ := Finset.mem_filter.mp hi
    have hg := congrArg (fun j : Fin K => (j:ℕ)) hgi
    dsimp only [g] at hg
    rwa [min_eq_left (Nat.log_mono_right (hp i hi).2)] at hg
  have hfiber (j : Fin K) (k : ℤ) :
      (∑ i∈(U j).filter (fun i => m i=k), ‖z i‖) ≤ B := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)) (hz k)
    intro i hi
    obtain ⟨hi,hk⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,hk⟩
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hpowN : 1 ≤ (N:ℝ)^((3:ℝ)+ε) := Real.one_le_rpow hN₁ (by positivity)
  have hcell (j : Fin K) : logarithmicSixMoment T (U j) z m ≤
      C*B^6*(T+N)*(N:ℝ)^((3:ℝ)+ε) := by
    by_cases hj : 2 ≤ (j:ℕ)
    · have hX : (4:ℝ) ≤ (2:ℝ)^(j:ℕ) := by
        simpa only [show (2:ℝ)^2=4 by norm_num] using
          pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj
      have hjN : (j:ℕ) ≤ Nat.log 2 N := by have := j.isLt; dsimp [K] at this; omega
      have hXN : (2:ℝ)^(j:ℕ) ≤ N := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) hjN).trans
          (Nat.pow_log_le_self 2 (by omega : N ≠ 0))
      have hrange (i : ι) (hi : i∈U j) : (m i:ℝ)∈Icc ((2:ℝ)^(j:ℕ)) (2*(2:ℝ)^(j:ℕ)) := by
        have his := (Finset.mem_filter.mp hi).1
        have hlo := Nat.pow_log_le_self 2 (by have := (hp i his).1; omega : p i ≠ 0)
        have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (p i)
        rw [hlabel j i hi] at hlo hhi
        rw [pow_succ] at hhi
        have hpr : (p i:ℝ)=(m i:ℝ) := by exact_mod_cast hpInt i his
        constructor
        · have hh : (2:ℝ)^(j:ℕ) ≤ (p i:ℝ) := by exact_mod_cast hlo
          rwa [hpr] at hh
        · have hh : (p i:ℝ) ≤ 2*(2:ℝ)^(j:ℕ) := by exact_mod_cast (show p i ≤ 2*2^(j:ℕ) by omega)
          rwa [hpr] at hh
      have hh := hdyadic ((2:ℝ)^(j:ℕ)) T hX hT ι (U j) z m B hB hrange (hfiber j)
      apply hh.trans
      gcongr
      exact le_max_left _ _
    · have hrange (i : ι) (hi : i∈U j) : 1 ≤ m i ∧ m i ≤ 4 := by
        have his := (Finset.mem_filter.mp hi).1
        have hhi := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (p i)
        rw [hlabel j i hi] at hhi
        have hpow : 2^((j:ℕ)+1) ≤ (4:ℕ) := by
          simpa only [show (2:ℕ)^2=4 by norm_num] using
            Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ)) (show (j:ℕ)+1 ≤ 2 by omega)
        have he := hpInt i his
        exact ⟨(hm i his).1,by omega⟩
      have hh := logarithmicSixMoment_small hT (U j) z m hrange (hfiber j)
      have hcoeff : 2*4^6 ≤ C := le_max_right _ _
      calc
        _ ≤ 2*T*(4*B)^6 := hh
        _ = (2*4^6)*B^6*T := by ring
        _ ≤ C*B^6*T := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoeff (by positivity)) hT
        _ ≤ C*B^6*(T+N) := mul_le_mul_of_nonneg_left
          (by linarith only [hN₁] : T ≤ T+N) (by positivity)
        _ ≤ C*B^6*(T+N)*(N:ℝ)^((3:ℝ)+ε) :=
          le_mul_of_one_le_right (show 0 ≤ C*B^6*(T+(N:ℝ)) by positivity) hpowN
  have hsum := Finset.sum_le_sum (fun j (_hj : j∈Finset.univ) => hcell j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hh := (logarithmicSixMoment_fiberwise T S z m g).trans
    (mul_le_mul_of_nonneg_left hsum (by positivity))
  exact hh.trans_eq (by dsimp only [K]; ring)

private theorem logSix_shell_count {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η) :
    (((Nat.log 2 N+1:ℕ):ℝ))^6 ≤ (2*(1+6/η))^6*(N:ℝ)^η := by
  have hN₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN₀ : (0:ℝ) < N := zero_lt_one.trans_le hN₁
  have hp : (2:ℝ)^(Nat.log 2 N) ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  have hl := Real.log_le_log (pow_pos (by norm_num : (0:ℝ) < 2) _) hp
  rw [Real.log_pow] at hl
  have hlogtwo : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hmul := mul_le_mul_of_nonneg_left hlogtwo (Nat.cast_nonneg (Nat.log 2 N))
  have hcount : ((Nat.log 2 N+1:ℕ):ℝ) ≤ 2*(1+Real.log N) := by
    push_cast
    nlinarith only [hl,hmul]
  have hbudget := one_add_log_le_rpow_budget hN₁ (show 0 < η/6 by positivity)
  have he : 1/(η/6)=6/η := by field_simp
  rw [he] at hbudget
  have hpoint := hcount.trans (mul_le_mul_of_nonneg_left hbudget (by norm_num : (0:ℝ) ≤ 2))
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (Nat.log 2 N+1)) hpoint 6
  have hexp : ((N:ℝ)^(η/6))^6=(N:ℝ)^η := by
    rw [←Real.rpow_mul_natCast hN₀.le]
    congr 1
    norm_num
  simpa only [mul_pow,hexp,mul_assoc] using hs

/-- The full logarithmic sixth moment, with all positive integer
frequencies, arbitrary nonnegative time length and coefficient multiplicities.
The analytic bound is derived from the actual logarithmic phase. -/
theorem exists_logarithmic_sixth {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (B : ℝ), 0 ≤ B →
        (∀ i∈S, 1 ≤ m i ∧ m i ≤ N) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖) ≤ B) →
        logarithmicSixMoment T S z m ≤ C*B^6*(T+N)*(N:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨D,hD,hbound⟩ := exists_logarithmic_sixth_log_loss (ε:=ε/2) (by positivity)
  let E := (2*(1+6/(ε/2)))^6
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨D*E,by positivity,?_⟩
  intro N hN T hT ι S z m B hB hm hz
  have hN₀ : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcount := logSix_shell_count hN (show 0 < ε/2 by positivity)
  change (((Nat.log 2 N+1:ℕ):ℝ))^6 ≤ E*(N:ℝ)^(ε/2) at hcount
  have hh := hbound N hN T hT ι S z m B hB hm hz
  have hmain : D*((Nat.log 2 N+1:ℕ):ℝ)^6*B^6*(T+N)*(N:ℝ)^((3:ℝ)+ε/2) ≤
      D*(E*(N:ℝ)^(ε/2))*B^6*(T+N)*(N:ℝ)^((3:ℝ)+ε/2) := by gcongr
  apply hh.trans (hmain.trans_eq ?_)
  calc
    _ = (D*E)*B^6*(T+N)*((N:ℝ)^(ε/2)*(N:ℝ)^((3:ℝ)+ε/2)) := by ring
    _ = _ := by
      rw [←Real.rpow_add hN₀]
      congr 2
      ring

/-- The literal unweighted natural-number sum, including its first and
last frequencies, in the normalized additive-character convention. -/
theorem exists_logarithmic_sixth_unweighted {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      (∫ t : ℝ in Icc (-T) T, ∫ α : ℝ in Icc (0:ℝ) 1,
        ‖∑ n∈Finset.Icc 1 N,
          fordAdditiveCharacter (α*(n:ℝ)^2+t*Real.log (n:ℝ))‖^6) ≤
        C*(T+N)*(N:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_logarithmic_sixth hε
  refine ⟨C,hC,?_⟩
  intro N hN T hT
  have hm (n : ℕ) (hn : n∈Finset.Icc 1 N) : (1:ℤ) ≤ n ∧ (n:ℤ) ≤ N := by
    exact_mod_cast Finset.mem_Icc.mp hn
  have hz (k : ℤ) :
      (∑ _n∈(Finset.Icc 1 N).filter (fun n : ℕ => (n:ℤ)=k), ‖(1:ℂ)‖) ≤ (1:ℝ) := by
    simp only [norm_one,Finset.sum_const,nsmul_eq_mul,mul_one]
    have hc : ((Finset.Icc 1 N).filter (fun n : ℕ => (n:ℤ)=k)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have he := (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
      exact_mod_cast he
    exact_mod_cast hc
  have hh := h N hN T hT ℕ (Finset.Icc 1 N) (fun _ => 1) (fun n => (n:ℤ)) 1
    (by norm_num) hm hz
  simpa only [logarithmicSixMoment,Int.cast_natCast,one_mul,one_pow,mul_one] using hh

end TaoTrudgianYang2025.LogarithmicSixth

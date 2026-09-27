import TaoTrudgianYang2025.BetaCanonicalLegendre
import TaoTrudgianYang2025.BetaCanonicalTaylorLegendre
import TaoTrudgianYang2025.ExponentPairShiftUniformity
import TaoTrudgianYang2025.SargosWithinDerivativeCalculus
import TaoTrudgianYang2025.ExponentPairAllHeights
import TaoTrudgianYang2025.SargosDoubleLargeSieve
import TaoTrudgianYang2025.SargosQuarticPoisson
import TaoTrudgianYang2025.PositiveSlopeCharts

noncomputable section
open Set Expdb Filter GafniTao
open scoped Topology ContDiff
open scoped BigOperators
namespace TaoTrudgianYang2025.DisplacementDualPrototype

/-- The actual normalized negative first derivative retains the complete
closed-interval model contract, including both endpoints. -/
theorem negative_first_derivative_model
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hF : IsApproximateModelPhaseFunction F σ (P+1) δ) :
    IsApproximateModelPhaseFunction
      (fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u)
      (σ+1) P (δ/σ) := by
  refine ⟨contDiffOn_const.mul
    (sargos_contDiffOn_iteratedDerivWithin hF.1 uniqueDiffOn_phaseInterval 1),?_⟩
  intro p hp u
  have hu : 0 < (u:ℝ) := lt_of_lt_of_le zero_lt_one u.property.1
  have hw (τ : ℝ) (n : ℕ) :
      iteratedDerivWithin n (modelPhase τ) phaseInterval u =
        iteratedDeriv n (modelPhase τ) u :=
    iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval
      (Real.contDiffAt_rpow_const_of_ne hu.ne') u.property
  have hm : -σ⁻¹*iteratedDerivWithin (p+1) (modelPhase σ) phaseInterval u =
      iteratedDerivWithin p (modelPhase (σ+1)) phaseInterval u := by
    rw [hw,hw,modelPhase_iteratedDeriv_succ_parameter σ hu]
    field_simp
  have he : modelPhaseErrorAt
      (fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u) (σ+1) p u =
      -σ⁻¹*modelPhaseErrorAt F σ (p+1) u := by
    rw [modelPhaseErrorAt,iteratedDerivWithin_const_mul_field,
      sargos_iteratedDerivWithin_comp_order,← hm,← mul_sub]
    rfl
  rw [he,norm_mul,Real.norm_eq_abs,abs_neg,
    abs_of_pos (inv_pos.mpr hσ)]
  have h := mul_le_mul_of_nonneg_left (hF.2 (p+1) (by omega) u)
    (inv_nonneg.mpr hσ.le)
  simpa only [div_eq_mul_inv,mul_comm] using h

/-- Reuse of the completed Legendre and shift APIs, with both actual retained
slope windows and all uniform tolerances. This is not the D-process bound. -/
theorem double_dual_shift_uniformity
    {σ a b c d : ℝ} (hσ : 0 < σ)
    (ha : (2:ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1) (hba : b < 2*a)
    (hc : (2:ℝ)^(-(σ⁻¹+1)) < c) (hcd : c ≤ d) (hd : d < 1) (hdc : d < 2*c) :
    ∃ A B : ℝ, 0 < A ∧ A < a ∧ b < 2*A ∧ 0 < B ∧ B < c ∧ d < 2*B ∧
      ∃ χ ψ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        (∀ v∈Icc a b, χ v=1) ∧ (∀ w∈Icc c d, ψ w=1) ∧
        ∀ (Q : ℕ) (ε : ℝ), 0 < ε →
        ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
          ∃ P : ℕ, 1 ≤ P ∧ ∀ (F : ℝ → ℝ) (η : ℝ),
            IsApproximateModelPhaseFunction F σ P δ → 0 < η → η ≤ η₀ →
            let L := canonicalLegendrePhase χ F σ A a
            let J := aProcessShiftPhase L σ⁻¹ η
            let G := canonicalLegendrePhase ψ J (σ⁻¹+1) B c
            Icc a b ⊆ modelPhaseSlopeRange F ∧
            Icc c d ⊆ modelPhaseSlopeRange J ∧
            IsApproximateModelPhaseFunction G (σ⁻¹+1)⁻¹ Q ε ∧
            (∀ v∈Icc a b, v/A∈Ioo (1:ℝ) 2 ∧
              L (v/A)=A^(σ⁻¹-1)*(modelPhaseLegendreDual F v-modelPhaseLegendreDual F a)+
                referenceModelPrimitive σ⁻¹ (a/A)) ∧
            (∀ w∈Icc c d, w/B∈Ioo (1:ℝ) 2 ∧
              G (w/B)=B^((σ⁻¹+1)⁻¹-1)*
                (modelPhaseLegendreDual J w-modelPhaseLegendreDual J c)+
                referenceModelPrimitive (σ⁻¹+1)⁻¹ (c/B)) := by
  have hs : 0 < σ⁻¹ := inv_pos.mpr hσ
  obtain ⟨A,hA,hAa,hbA,χ,hχ,hχc,hχone,hfirst⟩ :=
    modelPhaseLegendreDual_canonical_extension hσ ha hab hb hba
  obtain ⟨B,hB,hBc,hdB,ψ,hψ,hψc,hψone,hsecond⟩ :=
    modelPhaseLegendreDual_canonical_extension (show 0 < σ⁻¹+1 by linarith) hc hcd hd hdc
  refine ⟨A,B,hA,hAa,hbA,hB,hBc,hdB,χ,ψ,hχ,hχc,hψ,hψc,hχone,hψone,?_⟩
  intro Q ε hε
  obtain ⟨δ₂,hδ₂,_hδ₂small,hsecondModel⟩ := hsecond Q ε hε
  let Q₂ := legendreFiniteInputOrder (Q+1)
  obtain ⟨δ₁,η₀,hδ₁,hη₀,hηhalf,hshift⟩ :=
    aProcessShiftPhase_uniform_model hs Q₂ hδ₂
  obtain ⟨δ,hδ,_hδsmall,hfirstModel⟩ := hfirst (Q₂+1) δ₁ hδ₁
  let P := max 1 (legendreFiniteInputOrder ((Q₂+1)+1))
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,P,le_max_left _ _,?_⟩
  intro F η hF hη hηle L J G
  have hsource := approximateModelPhase_mono hF (le_max_right _ _) le_rfl
  obtain ⟨hwindow₁,hL,hLvalues⟩ := hfirstModel F hsource
  have hJ := hshift L η hL hη hηle
  obtain ⟨hwindow₂,hG,hGvalues⟩ := hsecondModel J hJ
  exact ⟨hwindow₁,hwindow₂,hG,hLvalues,hGvalues⟩

/-- The stationary phase of the actual difference of inverse slopes is
exactly the negative double Legendre phase; the displacement is derived. -/
theorem inverse_slope_shift_stationary_identity
    {σ δ k u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hu : u∈modelPhaseSlopeRange F) (huk : u+k∈modelPhaseSlopeRange F) :
    let c := modelPhaseInverseSlope F
    let K := fun v => modelPhaseLegendreDual F v-modelPhaseLegendreDual F (v+k)
    let d := c u-c (u+k)
    HasDerivAt K d u ∧
      2*(F (c (u+k))-F (c u)-k*c (u+k)) = -2*(d*u-K u) := by
  intro c K d
  have hleft := modelPhaseLegendreDual_hasDerivAt hσ hδ hF hu
  have hright := (modelPhaseLegendreDual_hasDerivAt hσ hδ hF huk).comp u
    ((hasDerivAt_id u).add_const k)
  refine ⟨?_,?_⟩
  · simpa only [mul_one] using hleft.sub hright
  · dsimp only [c,K,d,modelPhaseLegendreDual]
    ring

/-- Exact parameter returned by the reused B-A-B model construction when
the incoming phase is the normalized negative first derivative. -/
theorem derivative_double_dual_parameter {σ : ℝ} (hσ : 0 < σ) :
    ((σ+1)⁻¹+1)⁻¹=(σ+1)/(σ+2) := by
  have h1 : σ+1 ≠ 0 := by positivity
  have h2 : σ+2 ≠ 0 := by positivity
  field_simp
  ring

/-- On a retained open window the canonical phase has the actual inverse
slope as its derivative, with the exact physical scaling factor. -/
theorem canonical_legendre_hasDerivAt
    {σ δ A a b v : ℝ} {F χ : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (ha : 0 < a) (hv : v ∈ Ioo a b)
    (hwindow : Icc a b ⊆ modelPhaseSlopeRange F)
    (hχ : ∀ z∈Icc a b, χ z=1) :
    HasDerivAt (canonicalLegendrePhase χ F σ A a)
      (A^(σ⁻¹-1)*modelPhaseInverseSlope F v*A) (v/A) := by
  have he : canonicalLegendrePhase χ F σ A a =ᶠ[𝓝 (v/A)]
      fun x => A^(σ⁻¹-1)*(modelPhaseLegendreDual F (A*x)-modelPhaseLegendreDual F a)+
        referenceModelPrimitive σ⁻¹ (a/A) := by
    have hc : ContinuousAt (fun x:ℝ => A*x) (v/A) := by fun_prop
    have hn : Ioo a b ∈ 𝓝 (A*(v/A)) := by
      rw [mul_div_cancel₀ _ hA.ne']
      exact isOpen_Ioo.mem_nhds hv
    filter_upwards [hc.preimage_mem_nhds hn] with x hx
    have hz : 0 < A*x := ha.trans hx.1
    have hh := canonicalLegendrePhase_agrees (F:=F) (σ:=σ) hA ha hz
      (hχ (A*x) ⟨hx.1.le,hx.2.le⟩)
    simpa only [mul_div_cancel_left₀ _ hA.ne'] using hh
  have hd₀ : HasDerivAt (modelPhaseLegendreDual F) (modelPhaseInverseSlope F v)
      (A*(v/A)) := by
    simpa only [mul_div_cancel₀ _ hA.ne'] using
      modelPhaseLegendreDual_hasDerivAt hσ hδ hF (hwindow ⟨hv.1.le,hv.2.le⟩)
  have hd := hd₀.comp (v/A) ((hasDerivAt_id (v/A)).const_mul A)
  simp only [mul_one] at hd
  convert (((hd.sub_const (modelPhaseLegendreDual F a)).const_mul
    (A^(σ⁻¹-1))).add_const (referenceModelPrimitive σ⁻¹ (a/A))).congr_of_eventuallyEq
      he using 1
  ring

/-- The compressed shift of the actual first dual retains both its literal
value and its displacement derivative; no independent curve is supplied. -/
theorem canonical_shift_displacement
    {σ δ A a b η y : ℝ} {F χ : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (ha : 0 < a)
    (hwindow : Icc a b ⊆ modelPhaseSlopeRange F)
    (hχ : ∀ z∈Icc a b, χ z=1)
    (hu : A*aProcessShiftPoint η 0 y ∈ Ioo a b)
    (huk : A*aProcessShiftPoint η 1 y ∈ Ioo a b) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let H := modelPhaseLegendreDual F
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalLegendrePhase χ F σ A a) σ⁻¹ η
    J y=s*(H u-H (u+k)) ∧ HasDerivAt J (s*A*(1-η)*d) y := by
  intro u k H d s J
  have hcoords : A*aProcessShiftPoint η 1 y = u+k := by
    dsimp [u,k,aProcessShiftPoint]
    ring
  have hval (t:ℝ) (ht:A*aProcessShiftPoint η t y∈Ioo a b) :=
    canonicalLegendrePhase_agrees (F:=F) (σ:=σ) hA ha (ha.trans ht.1)
      (hχ _ ⟨ht.1.le,ht.2.le⟩)
  constructor
  · have h0 := hval 0 hu
    have h1 := hval 1 huk
    simp only [mul_div_cancel_left₀ _ hA.ne'] at h0 h1
    dsimp only [J,aProcessShiftPhase]
    rw [h0,h1,hcoords]
    dsimp [s,u,H]
    ring
  · have hd (t:ℝ) (ht:A*aProcessShiftPoint η t y∈Ioo a b) :
        HasDerivAt (fun x => canonicalLegendrePhase χ F σ A a (aProcessShiftPoint η t x))
          (A^(σ⁻¹-1)*modelPhaseInverseSlope F (A*aProcessShiftPoint η t y)*A*(1-η)) y := by
      have hh := canonical_legendre_hasDerivAt hσ hδ hF hA ha ht hwindow hχ
      rw [mul_div_cancel_left₀ _ hA.ne'] at hh
      convert hh.comp y
        (((hasDerivAt_id y).const_mul (1-η)).add_const ((1+t)*η)) using 1
      simp
    have h0 := hd 0 hu
    have h1 := hd 1 huk
    have hj := (h0.sub h1).div_const (σ⁻¹*η)
    rw [hcoords] at hj
    convert hj using 1
    dsimp [J,aProcessShiftPhase,aProcessShiftPoint,s,d,u]
    ring

/-- Exact retained double-dual value for the actual displacement resonance.
The compression contributes the explicit linear term, which is not dropped. -/
theorem canonical_double_dual_resonance
    {σ δ δJ A B a b c η y : ℝ} {F χ ψ : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hδJ : δJ ≤ min (modelPhaseCurvatureLower (σ⁻¹+1)) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hc : 0 < c)
    (hwindow : Icc a b ⊆ modelPhaseSlopeRange F)
    (hχ : ∀ z∈Icc a b, χ z=1) (hy : y∈Ioo (1:ℝ) 2)
    (hu : A*aProcessShiftPoint η 0 y ∈ Ioo a b)
    (huk : A*aProcessShiftPoint η 1 y ∈ Ioo a b) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalLegendrePhase χ F σ A a) σ⁻¹ η
    let w := s*A*(1-η)*d
    let R := 2*(F (modelPhaseInverseSlope F (u+k))-F (modelPhaseInverseSlope F u)-
      k*modelPhaseInverseSlope F (u+k))
    IsApproximateModelPhaseFunction J (σ⁻¹+1) 1 δJ → 0 < w → ψ w=1 →
    canonicalLegendrePhase ψ J (σ⁻¹+1) B c (w/B) =
      B^((σ⁻¹+1)⁻¹-1)*(-s/2*R-s*k*d-modelPhaseLegendreDual J c)+
        referenceModelPrimitive (σ⁻¹+1)⁻¹ (c/B) := by
  intro u k d s J w R hJ hw hψ
  have hcoords : A*aProcessShiftPoint η 1 y=u+k := by
    dsimp [u,k,aProcessShiftPoint]
    ring
  obtain ⟨hval,hderiv⟩ := canonical_shift_displacement hσ hδ hF hA ha
    hwindow hχ hu huk
  change J y=s*(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k)) at hval
  change HasDerivAt J w y at hderiv
  have hinv : modelPhaseInverseSlope J w=y := by
    rw [← hderiv.deriv]
    exact modelPhaseInverseSlope_deriv (by positivity) hδJ hJ hy
  have hR := (inverse_slope_shift_stationary_identity hσ hδ hF
    (hwindow ⟨hu.1.le,hu.2.le⟩)
    (show u+k∈modelPhaseSlopeRange F by
      rw [← hcoords]
      exact hwindow ⟨huk.1.le,huk.2.le⟩)).2
  change R = -2*(d*u-(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k))) at hR
  have hdual : modelPhaseLegendreDual J w = -s/2*R-s*k*d := by
    rw [modelPhaseLegendreDual,hinv,hval,hR]
    dsimp [w,u,k,aProcessShiftPoint]
    ring
  rw [canonicalLegendrePhase_agrees hB hc hw hψ,hdual]

/-- An analytic exponent pair applies to the double dual computed from the
original model, with all constants chosen before the phase and physical scales.
The separate chart identity above is still needed for the resonance sum. -/
theorem source_double_dual_exponent_pair_bound
    {σ a b c d k l ε : ℝ} (hσ : 0 < σ) (hpair : ExponentPair k l) (hε : 0 < ε)
    (ha : (2:ℝ)^(-(σ+1)) < a) (hab : a ≤ b) (hb : b < 1) (hba : b < 2*a)
    (hc : (2:ℝ)^(-((σ+1)⁻¹+1)) < c) (hcd : c ≤ d) (hd : d < 1) (hdc : d < 2*c) :
    ∃ A B : ℝ, 0 < A ∧ A < a ∧ b < 2*A ∧ 0 < B ∧ B < c ∧ d < 2*B ∧
      ∃ χ ψ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        (∀ v∈Icc a b, χ v=1) ∧ (∀ w∈Icc c d, ψ w=1) ∧
        ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
          ∃ P : ℕ, 1 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
            ∀ (F : ℝ → ℝ) (η T N : ℝ) (m n : ℕ),
              IsApproximateModelPhaseFunction F σ P δ → 0 < η → η ≤ η₀ →
              0 < T → 1 ≤ N → N ≤ (m:ℝ) → (n:ℝ) ≤ 2*N →
              let F₁ := fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u
              let L := canonicalLegendrePhase χ F₁ (σ+1) A a
              let J := aProcessShiftPhase L (σ+1)⁻¹ η
              let G := canonicalLegendrePhase ψ J ((σ+1)⁻¹+1) B c
              Icc a b ⊆ modelPhaseSlopeRange F₁ ∧
              Icc c d ⊆ modelPhaseSlopeRange J ∧
              ‖exponentialSumAt G T N m n‖ ≤
                C*((T/N)^(k+ε)*N^(l+ε)+N/T) := by
  have hs : 0 < σ+1 := by positivity
  have ht : 0 < ((σ+1)⁻¹+1)⁻¹ := by positivity
  obtain ⟨A,B,hA,hAa,hbA,hB,hBc,hdB,χ,ψ,hχ,hχc,hψ,hψc,hχone,hψone,hmodels⟩ :=
    double_dual_shift_uniformity hs ha hab hb hba hc hcd hd hdc
  obtain ⟨δG,hδG,Q,_hQ,C,hC,hbound⟩ := hpair.allPositiveHeight_bound ht hε
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,P,hP,hall⟩ := hmodels Q δG hδG
  refine ⟨A,B,hA,hAa,hbA,hB,hBc,hdB,χ,ψ,hχ,hχc,hψ,hψc,hχone,hψone,
    σ*δ,η₀,mul_pos hσ hδ,hη₀,hηhalf,P+1,by omega,C,hC,?_⟩
  intro F η T N m n hF hη hηle hT hN hm hn F₁ L J G
  have hF₁ := negative_first_derivative_model hσ hF
  rw [mul_div_cancel_left₀ _ hσ.ne'] at hF₁
  obtain ⟨hwindow₁,hwindow₂,hG,_hLvalues,_hGvalues⟩ := hall F₁ η hF₁ hη hηle
  exact ⟨hwindow₁,hwindow₂,hbound T N G m n hT hN hm hn hG⟩

/-- The dual length, height and integer-displacement argument are tied to
the original physical scales; none is an independently supplied certificate. -/
theorem double_dual_physical_scales
    {P V A B τ θ η : ℝ} (hP : 0 < P) (hV : 0 < V)
    (hA : 0 < A) (hB : 0 < B) (hτ : 0 < τ) (hη : 0 < η) (hηone : η < 1) :
    let s := A^(τ-1)/(τ*η)
    let M := B*P/(s*A*(1-η))
    let H := 2*V/(s*B^(θ-1))
    let K := V*A*η/P
    0 < M ∧ 0 < H ∧ 0 < K ∧
      H/M=(2*V/P)*A*(1-η)*B^(-θ) ∧
      M=(B*τ/(A^(τ+1)*(1-η)))*(P^2/V)*K ∧
      ∀ d:ℝ, (s*A*(1-η)*(d/P))/B=d/M ∧
        2*V*(A*η)*(d/P)=2*K*d := by
  intro s M H K
  have hs : 0 < s := by dsimp [s]; positivity
  have h1 : 0 < 1-η := by linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hE : B^(θ-1)*B=B^θ := by
    calc
      _ = B^(θ-1)*B^(1:ℝ) := by rw [Real.rpow_one]
      _ = B^((θ-1)+1) := (Real.rpow_add hB _ _).symm
      _ = _ := by congr 1; ring
  have hAexp : A^(τ-1)*A^2=A^(τ+1) := by
    calc
      _ = A^(τ-1)*A^(2:ℝ) := by rw [Real.rpow_two]
      _ = A^((τ-1)+2) := (Real.rpow_add hA _ _).symm
      _ = _ := by congr 1; ring
  refine ⟨hM,hH,hK,?_,?_,?_⟩
  · rw [Real.rpow_neg hB.le]
    dsimp [H,M]
    field_simp
    nlinarith only [hE]
  · rw [← hAexp]
    dsimp [M,K,s]
    field_simp
  · intro d
    dsimp [M,K]
    constructor <;> field_simp

/-- Reuse the moving Taylor extension twice. Source tolerance and shift cap
are independent of both shrinking endpoint buffers and both actual anchors.
Unlike the fixed-window construction, no reference-slope interior assumption
is imposed on a retained value. This is model uniformity, not a D estimate. -/
theorem moving_double_dual_uniformity
    {σ A B : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hA₂ : A ≤ 2)
    (hB : 0 < B) (hB₂ : B ≤ 2) (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ P Q₁ : ℕ, 1 ≤ P ∧
        ∀ (F : ℝ → ℝ) (η w h : ℝ),
          IsApproximateModelPhaseFunction F σ P δ →
          0 < η → η ≤ η₀ → w ∈ modelPhaseSlopeRange F →
          0 < h → h ≤ 1 →
          modelPhaseClosedSlope F 2+4*h < modelPhaseClosedSlope F 1 →
          let L := canonicalTaylorLegendrePhase F σ A Q₁ w h
          let J := aProcessShiftPhase L σ⁻¹ η
          ∀ (v g : ℝ), v ∈ modelPhaseSlopeRange J → 0 < g → g ≤ 1 →
            modelPhaseClosedSlope J 2+4*g < modelPhaseClosedSlope J 1 →
            IsApproximateModelPhaseFunction
              (canonicalTaylorLegendrePhase J (σ⁻¹+1) B Q v g)
              (σ⁻¹+1)⁻¹ Q ε := by
  have hs : 0 < σ⁻¹ := inv_pos.mpr hσ
  obtain ⟨δ₂,hδ₂,_hsmall₂,_hpos₂,hsecond⟩ :=
    canonicalTaylorLegendrePhase_uniformity (show 0 < σ⁻¹+1 by positivity)
      hB hB₂ Q hε
  let Q₂ := legendreFiniteInputOrder (Q+2)
  obtain ⟨δ₁,η₀,hδ₁,hη₀,hηhalf,hshift⟩ :=
    aProcessShiftPhase_uniform_model hs Q₂ hδ₂
  obtain ⟨δ,hδ,_hsmall,_hpos,hfirst⟩ :=
    canonicalTaylorLegendrePhase_uniformity hσ hA hA₂ (Q₂+1) hδ₁
  let P := max 1 (legendreFiniteInputOrder ((Q₂+1)+2))
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,P,Q₂+1,le_max_left _ _,?_⟩
  intro F η w h hF hη hηle hw hh hh₁ hgap L J v g hv hg hg₁ hgap₂
  have hsource := approximateModelPhase_mono hF (le_max_right _ _) le_rfl
  have hL := hfirst F hsource w hw h hh hh₁ hgap
  have hJ := hshift L η hL hη hηle
  exact hsecond J hJ v hv g hg hg₁ hgap₂

/-- A finite family of actual interior slope values admits one positive
Taylor buffer. It can shrink with the family; the preceding analytic
uniformity does not depend on this choice. -/
theorem finite_slope_values_retained
    {ι : Type*} (S : Finset ι) {lo hi : ℝ} (hlohi : lo < hi)
    (v : ι → ℝ) (hv : ∀ i∈S, v i ∈ Ioo lo hi) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ lo+4*h < hi ∧
      ∀ i∈S, v i ∈ Icc (lo+2*h) (hi-2*h) := by
  classical
  let t := S.image (fun i => min (v i-lo) (hi-v i))
  let b := min 1 (hi-lo)
  have hb : 0 < b := lt_min zero_lt_one (sub_pos.mpr hlohi)
  let m := (insert b t).min' (Finset.insert_nonempty b t)
  have hm : 0 < m := by
    have hx : m ∈ insert b t := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]
      exact hb
    · obtain ⟨i,hiS,he⟩ := Finset.mem_image.mp hx
      rw [← he]
      exact lt_min (sub_pos.mpr (hv i hiS).1) (sub_pos.mpr (hv i hiS).2)
  have hmb : m ≤ b := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hm₁ : m ≤ 1 := hmb.trans (min_le_left _ _)
  have hmspan : m ≤ hi-lo := hmb.trans (min_le_right _ _)
  refine ⟨m/8,by positivity,by linarith,by linarith,?_⟩
  intro i hiS
  have hmi : m ≤ min (v i-lo) (hi-v i) :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,hiS,rfl⟩))
  have hl := hmi.trans (min_le_left _ _)
  have hr := hmi.trans (min_le_right _ _)
  constructor <;> linarith

/-- All values in a finite family from the actual open slope image can be
realized by one closed model phase, even arbitrarily near its moving endpoints.
The tolerance precedes the original phase and the finite family. -/
theorem finite_actual_legendre_realization
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hA₂ : A ≤ 2)
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 1 ≤ P ∧
      ∀ F : ℝ → ℝ, IsApproximateModelPhaseFunction F σ P δ →
        ∀ (ι : Type*) (S : Finset ι) (v : ι → ℝ),
          (∀ i∈S, v i ∈ modelPhaseSlopeRange F) →
          ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
            IsApproximateModelPhaseFunction
              (canonicalTaylorLegendrePhase F σ A Q (deriv F (3/2)) h) σ⁻¹ Q ε ∧
            ∀ i∈S,
              canonicalTaylorLegendrePhase F σ A Q (deriv F (3/2)) h (v i/A) =
                A^(σ⁻¹-1)*(modelPhaseLegendreDual F (v i)-
                  modelPhaseLegendreDual F (deriv F (3/2)))+
                  referenceModelPrimitive σ⁻¹ (deriv F (3/2)/A) := by
  obtain ⟨δ,hδ,hsmall,hpos,hmodel⟩ :=
    canonicalTaylorLegendrePhase_uniformity hσ hA hA₂ Q hε
  let P := max 1 (legendreFiniteInputOrder (Q+2))
  refine ⟨δ,hδ,P,le_max_left _ _,?_⟩
  intro F hF ι S v hv
  have hF₁ := approximateModelPhase_mono hF (le_max_left _ _) le_rfl
  have hFQ := approximateModelPhase_mono hF (le_max_right _ _) le_rfl
  have hwin := modelPhaseSlopeRange_eq_endpoint_Ioo hσ hsmall hF₁
  have hw : deriv F (3/2) ∈ modelPhaseSlopeRange F :=
    ⟨3/2,by norm_num,rfl⟩
  have hwi := hw
  rw [hwin] at hwi
  have hlo : 0 < modelPhaseClosedSlope F 2 :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < (2:ℝ)^(-σ)/2)
      (modelPhaseClosedSlope_positive_window hσ hpos hF
        (u:=2) (by norm_num [phaseInterval])).1
  obtain ⟨h,hh,hh₁,hgap,hvalues⟩ := finite_slope_values_retained S
    (lt_trans hwi.1 hwi.2) v (fun i hi => by simpa only [hwin] using hv i hi)
  refine ⟨h,hh,hh₁,hmodel F hFQ _ hw h hh hh₁ hgap,?_⟩
  intro i hi
  have hvi := hv i hi
  rw [hwin] at hvi
  exact canonicalTaylorLegendrePhase_agrees Q hA (hlo.trans hwi.1)
    (hlo.trans hvi.1) hh (hvalues i hi)

/-- The compression term disappears from the actual integer-frequency
character only after its physical coefficient and displacement have both
been identified as integers. The anchor phase remains explicit. -/
theorem canonical_double_dual_physical_character
    {σ δ δJ A B a b c η y P V : ℝ} {F χ ψ : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hδJ : δJ ≤ min (modelPhaseCurvatureLower (σ⁻¹+1)) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hc : 0 < c)
    (hP : 0 < P) (hV : 0 < V) (hη : 0 < η) (hηone : η < 1)
    (hwindow : Icc a b ⊆ modelPhaseSlopeRange F)
    (hχ : ∀ z∈Icc a b, χ z=1) (hy : y∈Ioo (1:ℝ) 2)
    (hu : A*aProcessShiftPoint η 0 y ∈ Ioo a b)
    (huk : A*aProcessShiftPoint η 1 y ∈ Ioo a b)
    (K n r : ℤ) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalLegendrePhase χ F σ A a) σ⁻¹ η
    let w := s*A*(1-η)*d
    let θ := (σ⁻¹+1)⁻¹
    let G := canonicalLegendrePhase ψ J (σ⁻¹+1) B c
    let M := B*P/(s*A*(1-η))
    let H := 2*V/(s*B^(θ-1))
    let C := -2*V/s*modelPhaseLegendreDual J c+H*referenceModelPrimitive θ (c/B)
    let R := 2*(F (modelPhaseInverseSlope F (u+k))-F (modelPhaseInverseSlope F u)-
      k*modelPhaseInverseSlope F (u+k))
    IsApproximateModelPhaseFunction J (σ⁻¹+1) 1 δJ → 0 < w → ψ w=1 →
      V*k/P=(K:ℝ) → P*d=(n:ℝ) →
      fordAdditiveCharacter ((r:ℝ)*V*R) =
        fordAdditiveCharacter ((r:ℝ)*C)*
          star (fordAdditiveCharacter ((r:ℝ)*H*G ((n:ℝ)/M))) := by
  intro u k d s J w θ G M H C R hJ hw hψ hK hn
  have hs : 0 < s := by dsimp [s]; positivity
  have hz : 0 < B^(θ-1) := Real.rpow_pos_of_pos hB _
  have hG := canonical_double_dual_resonance hσ hδ hδJ hF hA hB ha hc
    hwindow hχ hy hu huk hJ hw hψ
  change G (w/B)=B^(θ-1)*(-s/2*R-s*k*d-modelPhaseLegendreDual J c)+
    referenceModelPrimitive θ (c/B) at hG
  have hd : d=(n:ℝ)/P := by apply (eq_div_iff hP.ne').mpr; nlinarith only [hn]
  have hscales := double_dual_physical_scales (θ:=θ) hP hV hA hB
    (inv_pos.mpr hσ) hη hηone
  have harg := (hscales.2.2.2.2.2 (n:ℝ)).1
  change (s*A*(1-η)*((n:ℝ)/P))/B=(n:ℝ)/M at harg
  have hwarg : w/B=(n:ℝ)/M := by dsimp only [w]; rw [hd]; exact harg
  rw [hwarg] at hG
  have hR : V*R=C-H*G ((n:ℝ)/M)-2*(K:ℝ)*(n:ℝ) := by
    rw [hG,← hK,← hn]
    dsimp only [H,C]
    field_simp
    ring
  have he : (r:ℝ)*V*R =
      ((r:ℝ)*C+-((r:ℝ)*H*G ((n:ℝ)/M)))+((-2*r*K*n:ℤ):ℝ) := by
    push_cast
    rw [mul_assoc, hR]
    ring
  have hint (z : ℤ) : fordAdditiveCharacter (z:ℝ)=1 := by
    unfold fordAdditiveCharacter
    have hz' : 2*Real.pi*Complex.I*((z:ℝ):ℂ) =
        (z:ℂ)*(2*Real.pi*Complex.I) := by push_cast; ring
    rw [hz',Complex.exp_int_mul_two_pi_mul_I]
  rw [he,fordAdditiveCharacter_add,hint,mul_one,
    fordAdditiveCharacter_add,← conj_fordAdditiveCharacter]
  rfl

/-- The moving Taylor extension has the derivative of the literal dual at
every strictly retained slope value. Its buffer may depend on the finite
physical family; no fixed reference-slope window is used. -/
theorem moving_legendre_hasDerivAt
    {σ δ A a v h : ℝ} {F : ℝ → ℝ} (Q : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (ha : 0 < a) (hv : 0 < v) (hh : 0 < h)
    (hret : v ∈ Ioo (modelPhaseClosedSlope F 2+2*h)
      (modelPhaseClosedSlope F 1-2*h)) :
    HasDerivAt (canonicalTaylorLegendrePhase F σ A Q a h)
      (A^(σ⁻¹-1)*modelPhaseInverseSlope F v*A) (v/A) := by
  have hvwin : v ∈ modelPhaseSlopeRange F := by
    rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    constructor <;> linarith [hret.1,hret.2]
  have he : canonicalTaylorLegendrePhase F σ A Q a h =ᶠ[𝓝 (v/A)]
      fun x => A^(σ⁻¹-1)*(modelPhaseLegendreDual F (A*x)-modelPhaseLegendreDual F a)+
        referenceModelPrimitive σ⁻¹ (a/A) := by
    have hc : ContinuousAt (fun x:ℝ => A*x) (v/A) := by fun_prop
    have hn : Ioo (max 0 (modelPhaseClosedSlope F 2+2*h))
        (modelPhaseClosedSlope F 1-2*h) ∈ 𝓝 (A*(v/A)) := by
      rw [mul_div_cancel₀ _ hA.ne']
      exact isOpen_Ioo.mem_nhds ⟨max_lt hv hret.1,hret.2⟩
    filter_upwards [hc.preimage_mem_nhds hn] with x hx
    have hpos : 0 < A*x := lt_of_le_of_lt (le_max_left _ _) hx.1
    have hlow := lt_of_le_of_lt (le_max_right _ _) hx.1
    have hval := canonicalTaylorLegendrePhase_agrees (σ:=σ) Q hA ha hpos hh
      ⟨hlow.le,hx.2.le⟩
    simpa only [mul_div_cancel_left₀ _ hA.ne'] using hval
  have hd₀ : HasDerivAt (modelPhaseLegendreDual F) (modelPhaseInverseSlope F v)
      (A*(v/A)) := by
    simpa only [mul_div_cancel₀ _ hA.ne'] using
      modelPhaseLegendreDual_hasDerivAt hσ hδ hF hvwin
  have hd := hd₀.comp (v/A) ((hasDerivAt_id (v/A)).const_mul A)
  simp only [mul_one] at hd
  convert (((hd.sub_const (modelPhaseLegendreDual F a)).const_mul
    (A^(σ⁻¹-1))).add_const (referenceModelPrimitive σ⁻¹ (a/A))).congr_of_eventuallyEq
      he using 1
  ring

/-- Literal values and displacement derivative for the actual shifted moving
dual. In particular, changing the Taylor buffer introduces no phase error. -/
theorem moving_shift_displacement
    {σ δ A a h η y : ℝ} {F : ℝ → ℝ} (Q : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (ha : 0 < a) (hh : 0 < h)
    (hu : 0 < A*aProcessShiftPoint η 0 y)
    (huk : 0 < A*aProcessShiftPoint η 1 y)
    (hret₀ : A*aProcessShiftPoint η 0 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h))
    (hret₁ : A*aProcessShiftPoint η 1 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalTaylorLegendrePhase F σ A Q a h) σ⁻¹ η
    J y=s*(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k)) ∧
      HasDerivAt J (s*A*(1-η)*d) y := by
  intro u k d s J
  have hcoords : A*aProcessShiftPoint η 1 y = u+k := by
    dsimp [u,k,aProcessShiftPoint]
    ring
  have h0 := canonicalTaylorLegendrePhase_agrees (σ:=σ) Q hA ha hu hh
    ⟨hret₀.1.le,hret₀.2.le⟩
  have h1 := canonicalTaylorLegendrePhase_agrees (σ:=σ) Q hA ha huk hh
    ⟨hret₁.1.le,hret₁.2.le⟩
  simp only [mul_div_cancel_left₀ _ hA.ne'] at h0 h1
  constructor
  · dsimp only [J,aProcessShiftPhase]
    rw [h0,h1,hcoords]
    dsimp [s,u]
    ring
  · have hd (t:ℝ) (ht:0 < A*aProcessShiftPoint η t y)
        (hr:A*aProcessShiftPoint η t y ∈
          Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
        HasDerivAt
          (fun x => canonicalTaylorLegendrePhase F σ A Q a h (aProcessShiftPoint η t x))
          (A^(σ⁻¹-1)*modelPhaseInverseSlope F (A*aProcessShiftPoint η t y)*A*(1-η)) y := by
      have hv := moving_legendre_hasDerivAt Q hσ hδ hF hA ha ht hh hr
      rw [mul_div_cancel_left₀ _ hA.ne'] at hv
      convert hv.comp y
        (((hasDerivAt_id y).const_mul (1-η)).add_const ((1+t)*η)) using 1
      simp
    have hj := ((hd 0 hu hret₀).sub (hd 1 huk hret₁)).div_const (σ⁻¹*η)
    rw [hcoords] at hj
    convert hj using 1
    dsimp [J,aProcessShiftPhase,aProcessShiftPoint,s,d,u]
    ring

/-- The exact double-dual resonance formula survives both moving Taylor
extensions. Both buffers are explicit and no fixed reference chart occurs. -/
theorem moving_double_dual_resonance
    {σ δ δJ A B a c h g η y : ℝ} {F : ℝ → ℝ} (Q₁ Q₂ : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hδJ : δJ ≤ min (modelPhaseCurvatureLower (σ⁻¹+1)) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hc : 0 < c)
    (hh : 0 < h) (hg : 0 < g) (hy : y ∈ Ioo (1:ℝ) 2)
    (hu : 0 < A*aProcessShiftPoint η 0 y)
    (huk : 0 < A*aProcessShiftPoint η 1 y)
    (hret₀ : A*aProcessShiftPoint η 0 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h))
    (hret₁ : A*aProcessShiftPoint η 1 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalTaylorLegendrePhase F σ A Q₁ a h) σ⁻¹ η
    let w := s*A*(1-η)*d
    let R := 2*(F (modelPhaseInverseSlope F (u+k))-F (modelPhaseInverseSlope F u)-
      k*modelPhaseInverseSlope F (u+k))
    IsApproximateModelPhaseFunction J (σ⁻¹+1) 1 δJ → 0 < w →
      w ∈ Icc (modelPhaseClosedSlope J 2+2*g) (modelPhaseClosedSlope J 1-2*g) →
      canonicalTaylorLegendrePhase J (σ⁻¹+1) B Q₂ c g (w/B) =
        B^((σ⁻¹+1)⁻¹-1)*(-s/2*R-s*k*d-modelPhaseLegendreDual J c)+
          referenceModelPrimitive (σ⁻¹+1)⁻¹ (c/B) := by
  intro u k d s J w R hJ hw hwret
  have hcoords : A*aProcessShiftPoint η 1 y=u+k := by
    dsimp [u,k,aProcessShiftPoint]
    ring
  obtain ⟨hval,hderiv⟩ := moving_shift_displacement Q₁ hσ hδ hF hA ha hh
    hu huk hret₀ hret₁
  change J y=s*(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k)) at hval
  change HasDerivAt J w y at hderiv
  have hinv : modelPhaseInverseSlope J w=y := by
    rw [← hderiv.deriv]
    exact modelPhaseInverseSlope_deriv (by positivity) hδJ hJ hy
  have huwin : u ∈ modelPhaseSlopeRange F := by
    rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    constructor <;> linarith [hret₀.1,hret₀.2]
  have hukwin : u+k ∈ modelPhaseSlopeRange F := by
    rw [← hcoords,modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    constructor <;> linarith [hret₁.1,hret₁.2]
  have hR := (inverse_slope_shift_stationary_identity hσ hδ hF huwin hukwin).2
  change R = -2*(d*u-(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k))) at hR
  have hdual : modelPhaseLegendreDual J w = -s/2*R-s*k*d := by
    rw [modelPhaseLegendreDual,hinv,hval,hR]
    dsimp [w,u,k,aProcessShiftPoint]
    ring
  rw [canonicalTaylorLegendrePhase_agrees Q₂ hB hc hw hg hwret,hdual]

/-- One pair of moving buffers realizes an entire finite family of actual
displacement resonances by a single closed double-dual model. Constants and
orders precede the phase, the shift and the finite family. This proves the
model/value bridge, not a sharp source-count estimate. -/
theorem finite_moving_double_dual_realization
    {σ A B : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hA₂ : A ≤ 2)
    (hB : 0 < B) (hB₂ : B ≤ 2) (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ P Q₁ : ℕ, 1 ≤ P ∧
        ∀ (F : ℝ → ℝ) (η : ℝ), IsApproximateModelPhaseFunction F σ P δ →
          0 < η → η ≤ η₀ → ∀ (ι : Type*) (S : Finset ι) (y : ι → ℝ),
          (∀ i∈S, y i ∈ Ioo (1:ℝ) 2) →
          (∀ i∈S, A*aProcessShiftPoint η 0 (y i) ∈ modelPhaseSlopeRange F) →
          (∀ i∈S, A*aProcessShiftPoint η 1 (y i) ∈ modelPhaseSlopeRange F) →
          let u := fun i => A*aProcessShiftPoint η 0 (y i)
          let k := A*η
          let d := fun i => modelPhaseInverseSlope F (u i)-modelPhaseInverseSlope F (u i+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let R := fun i => 2*(F (modelPhaseInverseSlope F (u i+k))-
            F (modelPhaseInverseSlope F (u i))-k*modelPhaseInverseSlope F (u i+k))
          ∃ h g : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < g ∧ g ≤ 1 ∧
            let L := canonicalTaylorLegendrePhase F σ A Q₁ (deriv F (3/2)) h
            let J := aProcessShiftPhase L σ⁻¹ η
            let c := deriv J (3/2)
            let G := canonicalTaylorLegendrePhase J (σ⁻¹+1) B Q c g
            IsApproximateModelPhaseFunction G (σ⁻¹+1)⁻¹ Q ε ∧
              ∀ i∈S, G (s*A*(1-η)*d i/B) =
                B^((σ⁻¹+1)⁻¹-1)*(-s/2*R i-s*k*d i-modelPhaseLegendreDual J c)+
                  referenceModelPrimitive (σ⁻¹+1)⁻¹ (c/B) := by
  classical
  have hτ : 0 < σ⁻¹+1 := by positivity
  obtain ⟨δ₂,hδ₂,hsmall₂,hpos₂,hsecond⟩ :=
    canonicalTaylorLegendrePhase_uniformity hτ hB hB₂ Q hε
  let QJ := max 1 (legendreFiniteInputOrder (Q+2))
  obtain ⟨δ₁,η₀,hδ₁,hη₀,hηhalf,hshift⟩ :=
    aProcessShiftPhase_uniform_model (inv_pos.mpr hσ) QJ hδ₂
  obtain ⟨δ,hδ,hsmall,hpos,hfirst⟩ :=
    canonicalTaylorLegendrePhase_uniformity hσ hA hA₂ (QJ+1) hδ₁
  let P := max 1 (legendreFiniteInputOrder ((QJ+1)+2))
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,P,QJ+1,le_max_left _ _,?_⟩
  intro F η hF hη hηle ι S y hy hu huk u k d s R
  have hF₁ := approximateModelPhase_mono hF (le_max_left _ _) le_rfl
  have hFQ := approximateModelPhase_mono hF (le_max_right _ _) le_rfl
  have hwin := modelPhaseSlopeRange_eq_endpoint_Ioo hσ hsmall hF₁
  have hpositive {v:ℝ} (hv:v∈modelPhaseSlopeRange F) : 0 < v :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < (2:ℝ)^(-σ)/2)
      (modelPhaseSlopeRange_positive_window hσ hpos hF hv).1
  have ha : deriv F (3/2) ∈ modelPhaseSlopeRange F := ⟨3/2,by norm_num,rfl⟩
  have hai := ha
  rw [hwin] at hai
  let U := S.image u ∪ S.image (fun i => A*aProcessShiftPoint η 1 (y i))
  have hU : ∀ v∈U, v ∈ Ioo (modelPhaseClosedSlope F 2) (modelPhaseClosedSlope F 1) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      simpa only [hwin] using hu i hi
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      simpa only [hwin] using huk i hi
  obtain ⟨b,hb,hb₁,hgap,hvalues⟩ := finite_slope_values_retained U
    (lt_trans hai.1 hai.2) id hU
  have hh : 0 < b/2 := by positivity
  have hh₁ : b/2 ≤ 1 := by linarith
  have hhgap : modelPhaseClosedSlope F 2+4*(b/2) < modelPhaseClosedSlope F 1 := by
    linarith
  have hret₀ (i:ι) (hi:i∈S) : A*aProcessShiftPoint η 0 (y i) ∈
      Ioo (modelPhaseClosedSlope F 2+2*(b/2)) (modelPhaseClosedSlope F 1-2*(b/2)) := by
    have hv := hvalues (u i) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    change modelPhaseClosedSlope F 2+2*b ≤ u i ∧ u i ≤ modelPhaseClosedSlope F 1-2*b at hv
    change modelPhaseClosedSlope F 2+2*(b/2) < u i ∧ u i < modelPhaseClosedSlope F 1-2*(b/2)
    constructor <;> linarith [hv.1,hv.2]
  have hret₁ (i:ι) (hi:i∈S) : A*aProcessShiftPoint η 1 (y i) ∈
      Ioo (modelPhaseClosedSlope F 2+2*(b/2)) (modelPhaseClosedSlope F 1-2*(b/2)) := by
    have hv := hvalues _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    change modelPhaseClosedSlope F 2+2*b ≤ A*aProcessShiftPoint η 1 (y i) ∧
      A*aProcessShiftPoint η 1 (y i) ≤ modelPhaseClosedSlope F 1-2*b at hv
    constructor <;> linarith [hv.1,hv.2]
  let L := canonicalTaylorLegendrePhase F σ A (QJ+1) (deriv F (3/2)) (b/2)
  let J := aProcessShiftPhase L σ⁻¹ η
  have hL := hfirst F hFQ _ ha (b/2) hh hh₁ hhgap
  have hJ := hshift L η hL hη hηle
  have hJ₁ := approximateModelPhase_mono hJ (le_max_left _ _) le_rfl
  have hJQ := approximateModelPhase_mono hJ (le_max_right _ _) le_rfl
  let w := fun i => s*A*(1-η)*d i
  have hw (i:ι) (hi:i∈S) : w i ∈ modelPhaseSlopeRange J := by
    have hd := (moving_shift_displacement (QJ+1) hσ hsmall hF₁ hA
      (hpositive ha) hh (hpositive (hu i hi)) (hpositive (huk i hi))
      (hret₀ i hi) (hret₁ i hi)).2
    exact ⟨y i,hy i hi,hd.deriv⟩
  let c := deriv J (3/2)
  have hc : c ∈ modelPhaseSlopeRange J := ⟨3/2,by norm_num,rfl⟩
  have hwinJ := modelPhaseSlopeRange_eq_endpoint_Ioo hτ hsmall₂ hJ₁
  change modelPhaseSlopeRange J = Ioo (modelPhaseClosedSlope J 2)
    (modelPhaseClosedSlope J 1) at hwinJ
  have hci := hc
  rw [hwinJ] at hci
  have hpositiveJ {v:ℝ} (hv:v∈modelPhaseSlopeRange J) : 0 < v :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < (2:ℝ)^(-(σ⁻¹+1))/2)
      (modelPhaseSlopeRange_positive_window hτ hpos₂ hJ hv).1
  obtain ⟨g,hg,hg₁,hgapJ,hvaluesJ⟩ := finite_slope_values_retained S
    (lt_trans hci.1 hci.2) w (fun i hi => by simpa only [hwinJ] using hw i hi)
  refine ⟨b/2,g,hh,hh₁,hg,hg₁,?_,?_⟩
  · exact hsecond J hJQ c hc g hg hg₁ hgapJ
  · intro i hi
    exact moving_double_dual_resonance (QJ+1) Q hσ hsmall hsmall₂ hF₁
      hA hB (hpositive ha) (hpositiveJ hc) hh hg (hy i hi)
      (hpositive (hu i hi)) (hpositive (huk i hi)) (hret₀ i hi) (hret₁ i hi)
      hJ₁ (hpositiveJ (hw i hi)) (hvaluesJ i hi)

/-- A genuine exponent-pair bound for the physical resonance sum, not for
an independently supplied dual phase. Both moving buffers and the actual
closed model are constructed from the original phase and finite interval.
The remaining chart-selection and source-count estimates are not assumed. -/
theorem actual_displacement_interval_exponent_pair_bound
    {σ A B k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2) (hB : 0 < B) (hB₂ : B ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V : ℝ) (a b : ℕ) (K : ℤ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V →
          (∀ n∈Finset.Icc a b, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let θ := (σ⁻¹+1)⁻¹
          let M := B*P/(s*A*(1-η))
          let H := 2*V/(s*B^(θ-1))
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          1 ≤ M → M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M → V*k/P=(K:ℝ) →
          (∀ n∈Finset.Icc a b, P*d n=(n:ℝ)) →
          ∀ r : ℤ, r ≠ 0 →
            ‖∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*V*R n)‖ ≤
              C*(((|(r:ℝ)| * H)/M)^(k₀+ε)*M^(l₀+ε)+M/(|(r:ℝ)| * H)) := by
  have hθ : 0 < (σ⁻¹+1)⁻¹ := by positivity
  obtain ⟨δG,hδG,QG,_hQG,C,hC,hbound⟩ := hpair.allPositiveHeight_bound hθ hε
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,Q,Q₁,hQ,hrealize⟩ :=
    finite_moving_double_dual_realization hσ hA hA₂ hB hB₂ QG hδG
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,?_⟩
  intro F η P V a b K y hF hη hηle hP hV hy hu huk u k d s θ M H R
    hM ha hb hK hn
  obtain ⟨h,g,_hh,_hh₁,_hg,_hg₁,hG,hvalues⟩ :=
    hrealize F η hF hη hηle ℕ (Finset.Icc a b) y hy hu huk
  let J := aProcessShiftPhase
    (canonicalTaylorLegendrePhase F σ A Q₁ (deriv F (3/2)) h) σ⁻¹ η
  let c := deriv J (3/2)
  let G := canonicalTaylorLegendrePhase J (σ⁻¹+1) B QG c g
  let C₀ := -2*V/s*modelPhaseLegendreDual J c+H*referenceModelPrimitive θ (c/B)
  have hs : 0 < s := by dsimp [s]; positivity
  have hz : 0 < B^(θ-1) := Real.rpow_pos_of_pos hB _
  have hH : 0 < H := by dsimp [H]; positivity
  have hηone : η < 1 := by linarith
  have hscales := double_dual_physical_scales (θ:=θ) hP hV hA hB
    (inv_pos.mpr hσ) hη hηone
  have hphase (n:ℕ) (hni:n∈Finset.Icc a b) :
      V*R n=C₀-H*G ((n:ℝ)/M)-2*(K:ℝ)*(n:ℝ) := by
    have hd : d n=(n:ℝ)/P := by
      apply (eq_div_iff hP.ne').mpr
      nlinarith only [hn n hni]
    have hv := hvalues n hni
    change G (s*A*(1-η)*d n/B)=
      B^(θ-1)*(-s/2*R n-s*k*d n-modelPhaseLegendreDual J c)+
        referenceModelPrimitive θ (c/B) at hv
    have harg := (hscales.2.2.2.2.2 (n:ℝ)).1
    change s*A*(1-η)*((n:ℝ)/P)/B=(n:ℝ)/M at harg
    rw [hd,harg] at hv
    rw [hv,← hK]
    dsimp only [H,C₀]
    field_simp
    ring
  have hint (z:ℤ) : fordAdditiveCharacter (z:ℝ)=1 := by
    unfold fordAdditiveCharacter
    have he : 2*Real.pi*Complex.I*((z:ℝ):ℂ) =
        (z:ℂ)*(2*Real.pi*Complex.I) := by push_cast; ring
    rw [he,Complex.exp_int_mul_two_pi_mul_I]
  intro r hr
  have hchar (n:ℕ) (hni:n∈Finset.Icc a b) :
      fordAdditiveCharacter ((r:ℝ)*V*R n) =
        fordAdditiveCharacter ((r:ℝ)*C₀)*
          star (fordAdditiveCharacter ((r:ℝ)*H*G ((n:ℝ)/M))) := by
    have he : (r:ℝ)*V*R n =
        ((r:ℝ)*C₀+-((r:ℝ)*H*G ((n:ℝ)/M)))+
          ((-2*r*K*(n:ℤ):ℤ):ℝ) := by
      push_cast
      rw [mul_assoc,hphase n hni]
      ring
    rw [he,fordAdditiveCharacter_add,hint,mul_one,
      fordAdditiveCharacter_add,← conj_fordAdditiveCharacter]
    rfl
  have hsum : (∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*V*R n)) =
      fordAdditiveCharacter ((r:ℝ)*C₀)*star (exponentialSumAt G ((r:ℝ)*H) M a b) := by
    rw [exponentialSumAt,star_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hni
    simp only [hchar n hni,sargos_ford_character_eq_fourier,oscillatory]
  rw [hsum,norm_mul,sargos_character_norm,one_mul,norm_star]
  have hnormheight : ‖exponentialSumAt G ((r:ℝ)*H) M a b‖ =
      ‖exponentialSumAt G (|(r:ℝ)| * H) M a b‖ := by
    by_cases hrpos : 0 ≤ (r:ℝ)
    · rw [abs_of_nonneg hrpos]
    · have hrneg : (r:ℝ) < 0 := lt_of_not_ge hrpos
      have he : exponentialSumAt G ((r:ℝ)*H) M a b =
          star (exponentialSumAt G (|(r:ℝ)| * H) M a b) := by
        simp only [exponentialSumAt,star_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        simp only [oscillatory,←sargos_ford_character_eq_fourier,abs_of_neg hrneg]
        have harg : (r:ℝ)*H*G ((n:ℝ)/M) = -(-(r:ℝ)*H*G ((n:ℝ)/M)) := by ring
        rw [harg,←conj_fordAdditiveCharacter]
        rfl
      rw [he,norm_star]
  rw [hnormheight]
  exact hbound (|(r:ℝ)| * H) M G a b
    (mul_pos (abs_pos.mpr (Int.cast_ne_zero.mpr hr)) hH)
    hM ha hb hG

/-- Reuse the existing finite positive-slope grid for compressed shifts.
The original point and its shifted partner are represented exactly, with
uniform interior room even on a grid-cell boundary. -/
theorem positive_slope_chart_compressed_coordinate
    {d v k : ℝ} (hd : 0 < d) (hv : v ∈ Icc (4*d) 2)
    (hk : 0 ≤ k) (hkd : k ≤ d) :
    let j := positiveSlopeChartIndex d v
    let A := positiveSlopeChartScale d j
    let η := k/A
    let y := (v/A-η)/(1-η)
    j ∈ positiveSlopeChartIndices d ∧ 0 < A ∧ A ≤ 3/2 ∧
      0 ≤ η ∧ η ≤ 1/3 ∧ y ∈ Ioo (1:ℝ) 2 ∧
        A*aProcessShiftPoint η 0 y=v ∧ A*aProcessShiftPoint η 1 y=v+k := by
  intro j A η y
  have hj : j ∈ positiveSlopeChartIndices d := positiveSlopeChartIndex_mem hd hv
  obtain ⟨hA,hA₂⟩ := positiveSlopeChartScale_bounds hd hj
  have hj₄ : (4:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hjd := mul_le_mul_of_nonneg_right hj₄ hd.le
  have hAd : 3*d ≤ A := by dsimp [A,positiveSlopeChartScale]; nlinarith only [hjd]
  have hη : 0 ≤ η := div_nonneg hk hA.le
  have hη₁ : η ≤ 1/3 := by
    apply (div_le_iff₀ hA).mpr
    linarith only [hkd,hAd]
  have hden : 0 < 1-η := by linarith
  have hvpos : 0 ≤ v := (by positivity : (0:ℝ) ≤ 4*d).trans hv.1
  have hcell := (positiveSlopeChartIndex_eq_iff hd hvpos j).mp (show _=j from rfl)
  have hcoord := positiveSlopeChart_coordinate hd (Finset.mem_Icc.mp hj).1 hcell
  have hupper : v+k < 2*A := by
    dsimp [A,positiveSlopeChartScale]
    nlinarith only [hcell.2,hkd,hjd]
  have hy : y ∈ Ioo (1:ℝ) 2 := by
    constructor
    · apply (one_lt_div hden).mpr
      linarith only [hcoord.1]
    · apply (div_lt_iff₀ hden).mpr
      have hdiv : v/A+η < 2 := by
        dsimp only [η]
        rw [← add_div]
        exact (div_lt_iff₀ hA).mpr hupper
      linarith only [hdiv]
  have hzero : A*aProcessShiftPoint η 0 y=v := by
    dsimp only [aProcessShiftPoint,y]
    field_simp [show A ≠ 0 from hA.ne',hden.ne']
    ring
  refine ⟨hj,hA,hA₂,hη,hη₁,hy,hzero,?_⟩
  have hkA : A*η=k := mul_div_cancel₀ k (show A ≠ 0 from hA.ne')
  calc
    A*aProcessShiftPoint η 1 y=A*aProcessShiftPoint η 0 y+A*η := by
      dsimp [aProcessShiftPoint]
      ring
    _ = v+k := by rw [hzero,hkA]

/-- A diagnostic for the unmodified Robert--Sargos reduction, even if its
sample-pair count were reduced to its unavoidable diagonal. With lengths
N^h, N^q, N^r and fourth derivative N^(-d), these are four of the surviving
losses in the eighth power. Rebalancing them cannot improve 1/13.
This is not an obstruction to the desired D theorem or to a sharper sieve. -/
theorem robertSargos_relaxed_loss_floor {d h q r t : ℝ}
    (hH : t ≤ 4*h) (hQR : t ≤ 2*q+2*r)
    (hHQ : t ≤ d-h-q) (hRH : t ≤ d-r-2*h) :
    13*t ≤ 8*d := by
  linarith only [hH,hQR,hHQ,hRH]

/-- At alpha=2/5, the desired D(Bourgain) saving strictly exceeds the
best saving allowed by the four unchanged relaxed RS losses. -/
theorem robertSargos_relaxed_losses_do_not_close_d_bourgain :
    ¬ ∃ h q r : ℝ,
      (190:ℝ)/199 ≤ 4*h ∧ 190/199 ≤ 2*q+2*r ∧
        190/199 ≤ 3/2-h-q ∧ 190/199 ≤ 3/2-r-2*h := by
  rintro ⟨h,q,r,hH,hQR,hHQ,hRH⟩
  have hn := robertSargos_relaxed_loss_floor hH hQR hHQ hRH
  norm_num at hn

#print axioms robertSargos_relaxed_loss_floor
#print axioms moving_legendre_hasDerivAt
#print axioms moving_shift_displacement
#print axioms moving_double_dual_resonance
#print axioms finite_moving_double_dual_realization
#print axioms actual_displacement_interval_exponent_pair_bound
#print axioms positive_slope_chart_compressed_coordinate
#print axioms finite_actual_legendre_realization
#print axioms canonical_double_dual_physical_character
#print axioms robertSargos_relaxed_losses_do_not_close_d_bourgain
#print axioms moving_double_dual_uniformity
#print axioms finite_slope_values_retained
#print axioms inverse_slope_shift_stationary_identity
#print axioms negative_first_derivative_model
#print axioms derivative_double_dual_parameter
#print axioms double_dual_shift_uniformity
#print axioms canonical_legendre_hasDerivAt
#print axioms canonical_shift_displacement
#print axioms canonical_double_dual_resonance
#print axioms source_double_dual_exponent_pair_bound
#print axioms double_dual_physical_scales

-- Smallest chart, exact cell boundary, and the largest permitted physical shift.
example :
    let A := positiveSlopeChartScale (1/4) (positiveSlopeChartIndex (1/4) 1)
    let η := (1/4)/A
    let y := (1/A-η)/(1-η)
    A=3/4 ∧ η=1/3 ∧ y=3/2 ∧ A*aProcessShiftPoint η 0 y=1 ∧
      A*aProcessShiftPoint η 1 y=5/4 := by
  norm_num [positiveSlopeChartScale,positiveSlopeChartIndex,aProcessShiftPoint]

-- The closed upper endpoint of the existing slope grid is not discarded.
example :
    let A := positiveSlopeChartScale (1/4) (positiveSlopeChartIndex (1/4) 2)
    let η := (1/4)/A
    let y := (2/A-η)/(1-η)
    A=3/2 ∧ η=1/6 ∧ y=7/5 ∧ A*aProcessShiftPoint η 0 y=2 ∧
      A*aProcessShiftPoint η 1 y=9/4 := by
  norm_num [positiveSlopeChartScale,positiveSlopeChartIndex,aProcessShiftPoint]

-- Zero shift is valid for chart geometry only; the analytic consumer requires positivity.
example :
    let A := positiveSlopeChartScale (1/4) (positiveSlopeChartIndex (1/4) 1)
    A*aProcessShiftPoint 0 0 (4/3)=1 ∧ A*aProcessShiftPoint 0 1 (4/3)=1 := by
  norm_num [positiveSlopeChartScale,positiveSlopeChartIndex,aProcessShiftPoint]
end TaoTrudgianYang2025.DisplacementDualPrototype

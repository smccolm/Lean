import TaoTrudgianYang2025.BetaCanonicalLegendre
import TaoTrudgianYang2025.ExponentPairShiftUniformity
import TaoTrudgianYang2025.SargosWithinDerivativeCalculus

noncomputable section
open Set Expdb Filter
open scoped Topology ContDiff
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

#print axioms inverse_slope_shift_stationary_identity
#print axioms negative_first_derivative_model
#print axioms derivative_double_dual_parameter
#print axioms double_dual_shift_uniformity
#print axioms canonical_legendre_hasDerivAt
#print axioms canonical_shift_displacement
#print axioms canonical_double_dual_resonance
end TaoTrudgianYang2025.DisplacementDualPrototype

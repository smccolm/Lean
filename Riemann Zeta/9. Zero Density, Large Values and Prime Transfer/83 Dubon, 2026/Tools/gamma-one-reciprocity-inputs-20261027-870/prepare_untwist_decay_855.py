from pathlib import Path
import json
s=Path(__file__).parent
p=s/'gamma-one-reciprocity-reuse-848/S_ModularCurve_exists_invariant_untwist_of_multiplier_eq_exp_periodOf.lean.txt'
t=p.read_text(encoding='utf-8')
start=t.index('  set M : ℂ → ℝ :=')
end=t.index('\nprivate def Good',start)
tail=t[start:end].replace('    have h5 := (h1.mul h4).congr_of_eventuallyEq (hΦσ_eq u hu0)','    have h5 : HasFDerivAt Φσ _ u := h1.mul h4')
body=r"""import SourceMeromorphicCuspUntwist
import SourceCuspDerivativeDecay

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> vanishing real derivative of the invariant untwist
at every translated cusp. Native analytic action replaces Mobius formulas;
the primary norm estimate is retained with its actual cusp-form primitive.
Adapted from the pinned Apache-2.0 scope-848 untwisting source. -/
namespace Dubon2026.SourcePeriodUntwist
noncomputable section
open UpperHalfPlane Filter Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

theorem analyticAt_translate (G : ℂ → ℂ) (σ : SL(2, ℤ)) {u : ℂ} (hu : 0 < u.im)
    (hG : AnalyticAt ℂ G ((σ • ofComplex u : ℍ) : ℂ)) :
    AnalyticAt ℂ (fun v : ℂ => G ((σ • ofComplex v : ℍ) : ℂ)) u := by
  have hd1 : (σ : GL (Fin 2) ℝ).val.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  have hd : 0 < (σ : GL (Fin 2) ℝ).val.det := by rw [hd1]; exact one_pos
  have hs : AnalyticAt ℂ (fun v : ℂ => ((σ • ofComplex v : ℍ) : ℂ)) u := by
    simpa [ofComplex_apply_of_im_pos hu] using (ofComplex u).analyticAt_smul hd
  exact AnalyticAt.comp (f := fun v : ℂ => ((σ • ofComplex v : ℍ) : ℂ)) hG hs

theorem analyticAt_reg_translate (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (σ : SL(2, ℤ)) {L : ℂ} (hL0 : L ≠ 0)
    (hL : Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℂ, A < u.im →
      AnalyticAt ℂ (fun v : ℂ => reg F ((σ • ofComplex v : ℍ) : ℂ)) u := by
  obtain ⟨A, hA0, hA⟩ := reg_near_cusp F hF σ hL0 hL one_pos
  refine ⟨A, hA0, fun u hu => ?_⟩
  have hu0 : 0 < u.im := lt_of_le_of_lt hA0 hu
  have ho : meromorphicOrderAt (F ∘ ofComplex) ((σ • ofComplex u : ℍ) : ℂ) = 0 := by
    simpa only [ofComplex_apply_of_im_pos hu0] using (hA (⟨u, hu0⟩ : ℍ) hu).1
  exact analyticAt_translate (reg F) σ hu0 (analyticAt_reg_of_order_zero F hF _ ho)

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]

theorem Φ_decay (F : ℍ → ℂ) (k : CuspForm (Γ.map (mapGL ℝ)) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (σ : SL(2, ℤ)) {L : ℂ} (hL0 : L ≠ 0)
    (hL : Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    Tendsto (fun τ : ℍ =>
      fderiv ℝ (fun u : ℂ => Φ F k ((σ • ofComplex u : ℍ) : ℂ)) (τ : ℂ))
      atImInfty (𝓝 0) := by
  obtain ⟨L₂, hL₂⟩ := Ek_exists_cusp_limit k σ
  set Fσ : ℂ → ℂ := fun u => reg F ((σ • ofComplex u : ℍ) : ℂ) with hFσ
  set Eσ : ℂ → ℂ := fun u => Ek k ((σ • ofComplex u : ℍ) : ℂ) with hEσ
  have hFσ_lim : Tendsto Fσ (comap Complex.im atTop) (𝓝 L) :=
    (tendsto_reg_cusp F hF σ hL0 hL).comp tendsto_comap_im_ofComplex
  have hEσ_lim : Tendsto Eσ (comap Complex.im atTop) (𝓝 L₂) :=
    hL₂.comp tendsto_comap_im_ofComplex
  obtain ⟨A, hA0, hA⟩ := analyticAt_reg_translate F hF σ hL0 hL
  have hEσ_an : ∀ u : ℂ, 0 < u.im → AnalyticAt ℂ Eσ u := fun u hu =>
    analyticAt_translate (Ek k) σ hu (analyticAt_Ek k (σ • ofComplex u).im_pos)
  have hdF : Tendsto (deriv Fσ) (comap Complex.im atTop) (𝓝 0) :=
    tendsto_deriv_zero (fun u hu => (hA u hu).differentiableAt) hFσ_lim
  have hdE : Tendsto (deriv Eσ) (comap Complex.im atTop) (𝓝 0) :=
    tendsto_deriv_zero (A := 0) (fun u hu => (hEσ_an u hu).differentiableAt) hEσ_lim
  set Φσ : ℂ → ℂ := fun u => Φ F k ((σ • ofComplex u : ℍ) : ℂ) with hΦσ
"""
with (s/'SourceMeromorphicUntwistDecay.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(body+tail+'\nend\nend Dubon2026.SourcePeriodUntwist\n')
route=json.loads((s/'gamma-one-cusp-derivative-route-854.json').read_text(encoding='utf-8'))
route['shorterRoute']='Use native analyticAt_smul and the proved nonzero normalized cusp limit. The actual primitive has an existing cusp limit. Apply eventual-holomorphy derivative decay to these exact two functions and the primary operator-norm estimate to their real exponential product. No separate Mobius analytic, order or inverse-coordinate library is constructed.'
with (s/'gamma-one-untwist-decay-route-855.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2);f.write('\n')
print('Prepared real derivative decay of actual invariant untwist.')

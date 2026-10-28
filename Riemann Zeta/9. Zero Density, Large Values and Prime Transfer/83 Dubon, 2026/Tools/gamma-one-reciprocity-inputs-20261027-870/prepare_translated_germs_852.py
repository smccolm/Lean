from pathlib import Path
import json
s=Path(__file__).parent
primary=s/'gamma-one-reciprocity-reuse-848/S_ModularCurve_exists_invariant_untwist_of_multiplier_eq_exp_periodOf.lean.txt'
t=primary.read_text(encoding='utf-8')
start=t.index('private theorem meromorphicOrderAt_eq_zero_of_near')
stop=t.index('\ninclude hcusp in',start)
near=t[start:stop].replace('private theorem','theorem')
body=r"""import SourceMeromorphicPeriodUntwist

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> nonzero limits of normalized untwisting at cusps.
Use native upper-half-plane analytic action and local normalization.
The local order-zero bound is adapted from the pinned Apache-2.0
scope-848 untwisting primary; no custom Mobius infrastructure is needed. -/
namespace Dubon2026.SourcePeriodUntwist
noncomputable section
open UpperHalfPlane Filter Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

theorem order_translate (F : ℍ → ℂ) (σ : SL(2, ℤ)) (τ : ℍ) :
    meromorphicOrderAt (fun z => F (σ • ofComplex z)) (τ : ℂ) =
      meromorphicOrderAt (F ∘ ofComplex) ((σ • τ : ℍ) : ℂ) := by
  have hd1 : (σ : GL (Fin 2) ℝ).val.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  have hd : 0 < (σ : GL (Fin 2) ℝ).val.det := by rw [hd1]; exact one_pos
  simpa using meromorphicOrderAt_comp_smul (f := F) (τ := τ) hd

theorem meromorphicAt_translate (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (σ : SL(2, ℤ)) (τ : ℍ) :
    MeromorphicAt (fun z => F (σ • ofComplex z)) (τ : ℂ) := by
  have hd1 : (σ : GL (Fin 2) ℝ).val.det = 1 := Matrix.SpecialLinearGroup.det_coe _
  have hd : 0 < (σ : GL (Fin 2) ℝ).val.det := by rw [hd1]; exact one_pos
  have ha := τ.analyticAt_smul hd
  have hm : MeromorphicAt (F ∘ ofComplex)
      ((fun z : ℂ => (((σ : GL (Fin 2) ℝ) • ofComplex z : ℍ) : ℂ)) (τ : ℂ)) := by
    simpa only [ofComplex_apply] using hF ((σ : GL (Fin 2) ℝ) • τ)
  simpa only [Function.comp_apply, ofComplex_apply] using hm.comp_analyticAt ha

theorem reg_eq_nhdsNE (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ)) (τ : ℍ) :
    (fun w : ℍ => reg F w) =ᶠ[𝓝[≠] τ] F := by
  have hm : MeromorphicOn (F ∘ ofComplex) upperHalfPlaneSet := fun z hz => hF ⟨z, hz⟩
  apply SourceFunctionField.ModularRatios.eventually_nhdsNE_coe_iff.mp
  filter_upwards [hm.toMeromorphicNFOn_eq_self_on_nhdsNE τ.im_pos,
    eventually_nhdsWithin_of_eventually_nhds
      (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z he him
  simpa only [Function.comp_apply, ofComplex_apply_of_im_pos him] using he

theorem analyticAt_reg_of_order_zero (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ)) (τ : ℍ)
    (ho : meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) = 0) :
    AnalyticAt ℂ (reg F) (τ : ℂ) := by
  have hm : MeromorphicOn (F ∘ ofComplex) upperHalfPlaneSet := fun z hz => hF ⟨z, hz⟩
  apply (meromorphicNFOn_toMeromorphicNFOn (F ∘ ofComplex) upperHalfPlaneSet
    τ.im_pos).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hm τ.im_pos, ho]

"""
with (s/'SourceMeromorphicTranslatedGerms.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(body+near+'\nend\nend Dubon2026.SourcePeriodUntwist\n')
route=json.loads((s/'gamma-one-meromorphic-untwist-route-851.json').read_text(encoding='utf-8'))
route['shorterRoute']='Translate actual germs with native UpperHalfPlane analyticAt_smul and meromorphicOrderAt_comp_smul. Preserve native normalization on upper-half-plane punctured neighborhoods. Use the primary local order-zero bound directly; cusp estimates can then be transferred through the native action homeomorphism, without inverse-Mobius-coordinate constructions.'
with (s/'gamma-one-translated-germs-route-852.json').open('x',encoding='utf-8') as f:json.dump(route,f,indent=2);f.write('\n')
print('Prepared actual translated meromorphic germs and local order-zero bound.')

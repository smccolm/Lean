from pathlib import Path
import re
p=Path(r'E:\Lean\.tmp\dubon83')
f=p/'SourceSmoothOrbitIntegralChangeVariables.lean'
d=p/'smooth-orbit-integral-change-variables-warning-910a';d.mkdir();(d/f.name).write_bytes(f.read_bytes())
t=f.read_text(encoding='utf-8').replace('UHP := fun z hz =>','UHP := fun _ hz =>')
t=t.replace("    have := det_coe' γ\n    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this","    simp [Matrix.GeneralLinearGroup.val_det_apply]")
t=t.replace('include hF hFU hg hh hhs hhU in','include hF hg hh hhs hhU in')
t=t.replace('include hF hFs hFU hg hh hhU in','include hF hFs hFU hg hh in')
f.write_text(t,encoding='utf-8',newline='\n')
src=p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_ModularCurve_tendsto_integral_mul_smoothedFundamental_mul_finsum_translate.lean.txt'
s=src.read_text(encoding='utf-8')
h=(p/'SourceSmoothOrbitIntegralGeometry.lean').read_text(encoding='utf-8')
header=h[h.index('/-!'):h.index('theorem sm_image')]
header+='open SourceSmoothedFundamental (smoothedFundamental)\n\n'
sig=s[s.index('theorem main'):s.index('  classical',s.index('theorem main'))]
sig=sig.replace('theorem main','theorem compact_translate_eventually_eq')
sig=sig.replace('    (h : ℝ → ℂ → ℂ) (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental Γ T z : ℂ)) :', '    :')
sig=sig.replace('h T z','(smoothedFundamental Γ T z : ℂ)')
sig=sig.replace('    Tendsto (fun T : ℝ => ∫ z : ℂ,','    ∀ᶠ T : ℝ in atTop, (∫ z : ℂ,')
sig=sig.replace(')) atTop\n      (𝓝 (∫ z : ℂ, g (ofComplex z) * F z)) := by', ')) = ∫ z : ℂ, g (ofComplex z) * F z := by')
# Capture the finite exact unfolding and real orbit-sum conversion only.
body=s[s.index('  classical',s.index('theorem main')):s.index('  have hH01')]
body=body.replace('  classical\n','  classical\n  let h : ℝ → ℂ → ℂ := fun T z => (smoothedFundamental Γ T z : ℂ)\n  have hh : ∀ T z, h T z = (smoothedFundamental Γ T z : ℂ) := fun _ _ => rfl\n',1)
body=body.replace('ModularCurve.smoothedFundamental','smoothedFundamental')
body=body.replace('ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one','SourceSmoothedFundamental.smooth_partition')
body=body.replace('integrable_term F hF hFU g hg','integrable_term F hF g hg')
body=body.replace('integrable_term\' F hF hFs hFU g hg (h T) (hhc T) (hhU T)', 'integrable_term\' F hF hFs hFU g hg (h T) (hhc T)')
body=body.replace('integral_term Γ F hF hFU g hg hgw (h T) (hhc T) (hhU T)', 'integral_term Γ F hFU g hgw (h T) (hhU T)')
tail='''  obtain ⟨B, hB⟩ := hFs.bddAbove_image
    (Complex.continuous_im.continuousOn.max
      (Complex.continuous_im.continuousOn.inv₀ fun z hz => (hFU hz).ne'))
  filter_upwards [eventually_ge_atTop B] with T hT
  rw [hE2 T]
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    by_cases hw : w ∈ tsupport F
    · have hwt : max (ofComplex w).im (ofComplex w).im⁻¹ ≤ T := by
        have hb := hB (mem_image_of_mem (fun z : ℂ => max z.im z.im⁻¹) hw)
        simpa only [← UpperHalfPlane.coe_im, coe_ofComplex (hFU hw)] using hb.trans hT
      rw [hHreal, (hS T).2.2.2.2.2.2.1 _ hwt]
      simp
    · simp [image_eq_zero_of_notMem_tsupport hw]

'''
sig=sig.replace(chr(0x1d54c),'UHP')
limit=s[s.index('theorem main'):s.index('  classical',s.index('theorem main'))]
limit=limit.replace('theorem main','theorem compact_translate_limit')
limit=limit.replace('    (h : ℝ → ℂ → ℂ) (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental Γ T z : ℂ)) :','    :')
limit=limit.replace('h T z','(smoothedFundamental Γ T z : ℂ)').replace(chr(0x1d54c),'UHP')
limit+='''  obtain ⟨hi, he⟩ := compact_translate_eventually_eq Γ F hF hFs hFU g hg hgw
  exact ⟨hi, tendsto_const_nhds.congr' he.symm⟩
'''
out='import SourceSmoothOrbitIntegralChangeVariables\nimport SourceModularSmoothedFundamental\n\n'+header+sig+body+tail+limit+'\nend\nend Dubon2026.SourceSmoothOrbitIntegral\n'
with (p/'SourceSmoothCompactTranslateIntegral.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(out)
print('Prepared exact-eventual compact unfolding and its source limit; repaired warning causes in change of variables.')

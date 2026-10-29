from pathlib import Path
s=Path(__file__).parent
a=s/'SourceGammaOneIntegralRatioResidue1466c.lean'
t=a.read_text(encoding='utf-8')
pos=t.index('theorem intFormRatiosC_subset_residueImage')
helper='''private theorem residue_fraction_mem (u v : LaurentSeries A)
    (hv : ϖ A v ≠ 0)
    (hz : ι A u / ι A v ∈ functionFieldOver Γ L) :
    ϖ A u / ϖ A v ∈ residueImage A Γ := by
  have hiv0 : ι A v ≠ 0 := fun h =>
    (ϖ_ne_zero_ne_zero hv) ((ι_eq_zero_iff A v).mp h)
  let z : functionFieldOver Γ L := ⟨ι A u / ι A v, hz⟩
  have hzv : (z : LaurentSeries L) * ι A v = ι A u := div_mul_cancel₀ _ hiv0
  have hzint : z ∈ coefficientGaussRing Γ A := ⟨u, v, hv, hzv⟩
  have hr := resHom_mem_residueImage A Γ ⟨z, hzint⟩
  have he := resHom_eq A Γ hv hzv
  exact he ▸ hr

'''
t=t[:pos]+helper+t[pos:]
start=t.index('  have hiv0 :',t.index('theorem intFormRatiosC_subset_residueImage'))
end=t.index('\ntheorem qExpFunctionFieldC_le_residueImage',start)
t=t[:start]+'''  have hiv0 : ι A v ≠ 0 := fun h =>
    (ϖ_ne_zero_ne_zero hv) ((ι_eq_zero_iff A v).mp h)
  have hgL : intSeriesC L pg ≠ 0 := hiv ▸ hiv0
  have hz : ι A u / ι A v ∈ functionFieldOver Γ L := by
    rw [hiu, hiv, functionFieldOver_eq_qExpFunctionFieldC]
    exact div_mem_qExpFunctionFieldC f g hf hg hgL
  have hr := residue_fraction_mem A Γ u v hv hz
  rw [hru, hrv] at hr
  exact hr
'''+t[end:]
a.rename(a.with_suffix('.lean.txt'))
with (s/'SourceGammaOneIntegralRatioResidue1466d.lean').open('x',encoding='utf-8') as h:h.write(t)

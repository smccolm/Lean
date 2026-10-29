from pathlib import Path
s=Path(__file__).parent
a=s/'SourceGammaOneIntegralRatioResidue1466d.lean'
t=a.read_text(encoding='utf-8').replace('have he := resHom_eq A Γ hv hzv','have he := resHom_eq A Γ (f := ⟨z, hzint⟩) (x := u) (y := v) hv hzv')
a.rename(a.with_suffix('.lean.txt'))
with (s/'SourceGammaOneIntegralRatioResidue1466e.lean').open('x',encoding='utf-8') as h:h.write(t)

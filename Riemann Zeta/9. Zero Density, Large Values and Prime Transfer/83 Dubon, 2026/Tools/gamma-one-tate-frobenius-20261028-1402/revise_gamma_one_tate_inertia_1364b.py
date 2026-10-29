from pathlib import Path
p=Path(__file__).parent
rows=[('SourceGammaOneInertiaPlaceReduction1364a','SourceGammaOneInertiaPlaceReduction1364b'),('SourceGammaOneInertiaPicard1365a','SourceGammaOneInertiaPicard1365b'),('SourceGammaOneTateInertia1366a','SourceGammaOneTateInertia1366b')]
for old,new in rows:
 f=p/(old+'.lean');s=f.read_text(encoding='utf-8')
 for a,b in rows:s=s.replace('import '+a+'\n','import '+b+'\n')
 if old==rows[0][0]:
  a='  rw [hplace, decompositionResiduePlace_eq_self_of_inertia A Δ d hd]\n'
  assert a in s;s=s.replace(a,'  exact (hplace d P).trans (decompositionResiduePlace_eq_self_of_inertia A Δ d hd _)\n')
 t=p/(new+'.lean');assert not t.exists();t.write_text(s,encoding='utf-8')
 assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
s=(p/'build_gamma_one_tate_inertia_1364.ps1').read_text(encoding='utf-8')
for a,b in rows:s=s.replace(a,b)
f=p/'build_gamma_one_tate_inertia_1364b.ps1';assert not f.exists();f.write_text(s,encoding='utf-8')

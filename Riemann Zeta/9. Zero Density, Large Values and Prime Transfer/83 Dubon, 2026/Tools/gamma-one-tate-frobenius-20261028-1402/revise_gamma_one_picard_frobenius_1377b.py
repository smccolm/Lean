from pathlib import Path
p=Path(__file__).parent
rows=[('SourceGammaOneNormDiamondOrientation1377a','SourceGammaOneNormDiamondOrientation1377b'),('SourceGammaOneHeckeTorsionPicard1378a','SourceGammaOneHeckeTorsionPicard1378b'),('SourceGammaOnePicardFrobeniusRelation1379b','SourceGammaOnePicardFrobeniusRelation1379c')]
for a,b in rows:
 f=p/(a+'.lean');s=f.read_text(encoding='utf-8')
 for old,new in rows:s=s.replace('import '+old+'\n','import '+new+'\n')
 if a==rows[0][0]:
  s=s.replace('  ext f\n','  apply AlgEquiv.ext\n  intro f\n')
  s=s.replace('theorem norm_diamond_inverse_label','omit [NeZero M] in\ntheorem norm_diamond_inverse_label')
 t=p/(b+'.lean');assert not t.exists();t.write_text(s,encoding='utf-8')
 assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@("+','.join("'"+b+"'" for a,b in rows)+")")
t=p/'build_gamma_one_picard_frobenius_1377b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')

from pathlib import Path
p=Path(__file__).parent
rows=[('SourceGammaOneHeckePicardDescent1381a','SourceGammaOneHeckePicardDescent1381b'),('SourceGammaOneHeckeTorsionPicard1378d','SourceGammaOneHeckeTorsionPicard1378e'),('SourceGammaOnePicardFrobeniusRelation1379e','SourceGammaOnePicardFrobeniusRelation1379f'),('SourceGammaOneTateFrobeniusRelation1380b','SourceGammaOneTateFrobeniusRelation1380c')]
for old,new in rows:
 f=p/(old+'.lean');s=f.read_text(encoding='utf-8')
 for a,b in rows:s=s.replace('import '+a+'\n','import '+b+'\n')
 if old==rows[0][0]:
  s='import SourceGammaOneGenusSpecialization\n'+s
  s=s.replace('open SourceCurve CongruenceSubgroup ConstantField\n','open SourceCurve CongruenceSubgroup ConstantField\nattribute [local instance] specializationResidueAlgebra\n')
 t=p/(new+'.lean');assert not t.exists();t.write_text(s,encoding='utf-8')
 assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
s=(p/'build_gamma_one_picard_descent_1381.ps1').read_text(encoding='utf-8')
for a,b in rows:s=s.replace(a,b)
t=p/'build_gamma_one_picard_descent_1381b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')

from pathlib import Path
s=Path(__file__).parent
for name,old,new,repls in [
 ('SourceGammaOneGaloisDiamondPolynomial','1436b','1436c',{'SourceGammaOneTwistedGaloisHecke1404b':'SourceGammaOneTwistedGaloisHecke','SourceAbsoluteCyclotomicLocal1405a':'SourceAbsoluteCyclotomicLocal'}),
 ('SourceGammaOneDiamondQuotientPolynomial','1439d','1439e',{'SourceGammaOneGaloisDiamondPolynomial1436b':'SourceGammaOneGaloisDiamondPolynomial1436c'}),
 ('SourceGammaOneDiamondQuotientHecke','1440d','1440e',{'SourceGammaOneDiamondQuotientPolynomial1439d':'SourceGammaOneDiamondQuotientPolynomial1439e'})]:
 f=s/(name+old+'.lean');c=f.read_text(encoding='utf-8')
 for a,b in repls.items():c=c.replace('import '+a+'\n','import '+b+'\n')
 t=s/(name+new+'.lean');assert not t.exists();t.write_text(c,encoding='utf-8')
 t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
runner=(s/'build_gamma_one_diamond_polynomial_1433.ps1').read_text(encoding='utf-8')
a=runner.index('$names=@(');b=runner.index('\nforeach',a)
runner=runner[:a]+"$names=@('SourceGammaOneGaloisDiamondPolynomial1436c','SourceGammaOneDiamondQuotientPolynomial1439e','SourceGammaOneDiamondQuotientHecke1440e')"+runner[b:]
t=s/'build_gamma_one_quotient_consumers_1440e.ps1';assert not t.exists();t.write_text(runner,encoding='utf-8')
print('Aligned shared scratch imports; all mathematical bodies and comments unchanged.')

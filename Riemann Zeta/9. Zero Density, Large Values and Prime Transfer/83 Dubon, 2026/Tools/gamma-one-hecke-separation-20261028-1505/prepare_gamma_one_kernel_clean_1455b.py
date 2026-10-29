from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientWordKernel1455a.lean'
assert f.with_suffix('.exit').read_text().strip()=='0'
log=f.with_suffix('.log').read_text(encoding='utf-16')
assert 'error:' not in log and 'warning:' not in log
c=f.read_text(encoding='utf-8');assert c.count('set_option diagnostics true in\n')==1
c=c.replace('set_option diagnostics true in\n','')
t=s/'SourceGammaOneDiamondQuotientWordKernel1455b.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
a=f.with_suffix('.lean.txt');assert not a.exists();f.rename(a)
c=(s/'SourceGammaOneDiamondQuotientCharacter1452a.lean.txt').read_text(encoding='utf-8')
c=c.replace('import SourceGammaOneDiamondQuotientWords1451d','import SourceGammaOneDiamondQuotientWordKernel1455b')
a=c.index('private local instance : AddCommGroup\n');b=c.index('theorem binaryDiamondQuotient_original_character',a)
c=c[:a]+c[b:]
t=s/'SourceGammaOneDiamondQuotientCharacter1452b.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
print('Kernel consumer completed with diagnostics enabled; prepare identical proof without diagnostic output and its character consumer.')

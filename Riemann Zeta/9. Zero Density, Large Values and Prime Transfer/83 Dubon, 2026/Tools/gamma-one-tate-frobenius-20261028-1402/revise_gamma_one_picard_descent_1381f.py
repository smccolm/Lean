from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneHeckePicardDescent1381e.lean';s=f.read_text(encoding='utf-8')
assert 'q.map_nsmul Z p' in s
s=s.replace('q.map_nsmul Z p','q.map_nsmul p Z')
t=p/'SourceGammaOneHeckePicardDescent1381f.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
target=f.with_suffix('.lean.txt');assert not target.exists();f.rename(target)
s=(p/'build_gamma_one_picard_descent_1381e.ps1').read_text(encoding='utf-8').replace('1381e','1381f')
t=p/'build_gamma_one_picard_descent_1381f.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')

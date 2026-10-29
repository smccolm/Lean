from pathlib import Path
p=Path(__file__).parent
s=(p/'build_gamma_one_picard_descent_1381f.ps1').read_text(encoding='utf-8').replace('SourceGammaOneHeckePicardDescent1381f','SourceGammaOneParabolicGaloisFrobenius1410a')
t=p/'build_gamma_one_parabolic_frobenius_1410.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')

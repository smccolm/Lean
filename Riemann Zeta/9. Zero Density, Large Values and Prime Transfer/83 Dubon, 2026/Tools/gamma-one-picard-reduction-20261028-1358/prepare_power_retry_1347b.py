from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOneKummerPowerLifting1347a.lean'
t=p.read_text(encoding='utf-8').replace('  have hidentity := gammaOne_kummer_genus_sub_one M hf hdvd E','  have hidentity : (genusFF Qbar E : ℤ) - 1 =\n      (q : ℤ) * ((genusFF Qbar FF : ℤ) - 1) := gammaOne_kummer_genus_sub_one M hf hdvd E')
(s/'SourceGammaOneKummerPowerLifting1347b.lean').write_text(t,encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
p=s/'SourceGammaOnePicardPrimeKernel1345a.lean'
p.write_text(p.read_text(encoding='utf-8').replace('import SourceGammaOneKummerPowerLifting1347a','import SourceGammaOneKummerPowerLifting1347b'),encoding='utf-8')
p=s/'build_gamma_one_kummer_consumers_1347.ps1'
(s/'build_gamma_one_kummer_consumers_1347b.ps1').write_text(p.read_text(encoding='utf-8-sig').replace('SourceGammaOneKummerPowerLifting1347a','SourceGammaOneKummerPowerLifting1347b'),encoding='utf-8-sig')

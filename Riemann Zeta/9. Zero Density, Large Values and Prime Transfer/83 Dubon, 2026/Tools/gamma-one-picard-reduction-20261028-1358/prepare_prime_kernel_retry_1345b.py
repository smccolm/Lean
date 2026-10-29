from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOnePicardPrimeKernel1345a.lean'
t=p.read_text(encoding='utf-8').replace('  haveI := residueImage_isCurveOver A Δ hT','  letI hcurve : IsCurveOver kk Fb := residueImage_isCurveOver A Δ hT').replace(' := IsCurveOver.finiteResidue',' :=\n    fun v => @IsCurveOver.finiteResidue kk Fb inferInstance inferInstance\n      (specializationResidueAlgebra A Δ) hcurve v')
(s/'SourceGammaOnePicardPrimeKernel1345b.lean').write_text(t,encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
p=s/'SourceGammaOnePicardTorsion1346a.lean'
p.write_text(p.read_text(encoding='utf-8').replace('SourceGammaOnePicardPrimeKernel1345a','SourceGammaOnePicardPrimeKernel1345b'),encoding='utf-8')
p=s/'build_gamma_one_kummer_consumers_1347.ps1'
t=p.read_text(encoding='utf-8-sig').replace("'SourceGammaOneKummerPowerLifting1347a',",'').replace('SourceGammaOnePicardPrimeKernel1345a','SourceGammaOnePicardPrimeKernel1345b')
(s/'build_gamma_one_picard_consumers_1345b.ps1').write_text(t,encoding='utf-8-sig')

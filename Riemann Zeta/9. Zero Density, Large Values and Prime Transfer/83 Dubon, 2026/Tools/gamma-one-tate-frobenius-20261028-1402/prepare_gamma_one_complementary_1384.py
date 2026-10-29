from pathlib import Path
p=Path(__file__).parent
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceTateDualDiamondQuadratic1383a','SourceHomogeneousComplementaryHecke1384a')")
t=p/'build_gamma_one_complementary_1384.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')

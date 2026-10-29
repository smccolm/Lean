from pathlib import Path
p=Path(__file__).parent
def out(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
f=p/'SourceGammaOneDecompositionCharts1361a.lean'
s=f.read_text(encoding='utf-8')
old='''  rw [nonunit_decompositionResiduePlace_iff, map_sub,
    decompositionResidueAut_constants, ← hr, ← IsLocalRing.ResidueField.residue_smul]
'''
new='''  rw [nonunit_decompositionResiduePlace_iff, map_sub, ← hr]
  erw [decompositionResidueAut_constants A Γ d⁻¹,
    ← IsLocalRing.ResidueField.residue_smul]
'''
assert old in s
out('SourceGammaOneDecompositionCharts1361b.lean',s.replace(old,new))
assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
f=p/'SourceGammaOneSpecializationEquivariance1363a.lean'
out('SourceGammaOneSpecializationEquivariance1363b.lean',f.read_text(encoding='utf-8').replace('SourceGammaOneDecompositionCharts1361a','SourceGammaOneDecompositionCharts1361b'))
assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
out('build_gamma_one_chart_transport_1361b.ps1',(p/'build_gamma_one_chart_transport_1361.ps1').read_text(encoding='utf-8').replace('SourceGammaOneDecompositionCharts1361a','SourceGammaOneDecompositionCharts1361b').replace('SourceGammaOneSpecializationEquivariance1363a','SourceGammaOneSpecializationEquivariance1363b'))

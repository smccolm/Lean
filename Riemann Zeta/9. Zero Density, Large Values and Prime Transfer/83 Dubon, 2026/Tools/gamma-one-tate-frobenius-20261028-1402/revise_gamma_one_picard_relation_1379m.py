from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOnePicardFrobeniusRelation1379k.lean';s=f.read_text(encoding='utf-8')
s='import SourceTorsionReductionDiamond1389a\n'+s
a=s.index('  let F :=');b=s.index('\nend\n',a)
s=s[:a]+'''  have hT : ModularGroup.T ∈ Γ := by simp [Gamma1_mem, ModularGroup.T]
  exact sourceTorsionReduction_diamond_quadratic R.pic0Map
    (heckePicard Qbar M p) (gamma1ArithmeticPicardRep Qbar M d.val)
    (arithmeticDiamondPicard M g⁻¹).toAddMonoidHom
    (decompositionResiduePicard A Γ hT d) (decompositionResiduePicard A Γ hT d⁻¹) p x
    (hhecke R hR _ m hm0 (Pic0.mem_torsion_iff.mp hFx)) (he d)
    (decompositionResiduePicard_inverse A Γ hT d)
    (fun y => (arithmeticDiamondPicard_galois M g⁻¹ d.val y).symm)
'''+s[b:]
t=p/'SourceGammaOnePicardFrobeniusRelation1379m.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
for old in ['SourceGammaOnePicardFrobeniusRelation1379k','SourceGammaOnePicardFrobeniusRelation1379l']:
    f=p/(old+'.lean');t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
f=p/'SourceGammaOneTateFrobeniusRelation1380h.lean';s=f.read_text(encoding='utf-8').replace('1379k','1379m')
t=p/'SourceGammaOneTateFrobeniusRelation1380i.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceTorsionReductionDiamond1389a','SourceGammaOnePicardFrobeniusRelation1379m','SourceGammaOneTateFrobeniusRelation1380i')")
t=p/'build_gamma_one_picard_relation_1379m.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')

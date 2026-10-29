from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneHeckeTorsionPicard1378b.lean';s=f.read_text(encoding='utf-8')
a=s.index('  change Pic0.mk (R.degZeroMap')
b=s.index('  apply congrArg Pic0.mk',a)
s=s[:a]+'''  have hT : ModularGroup.T ∈ Γ := by simp [Gamma1_mem, ModularGroup.T]
  let E := fieldDegZeroEquiv (arithmeticDiamondAut M g)
    (functionFieldOver_residue_bijective Γ hT)
    (functionFieldOver_residue_bijective Γ hT) D
  have hdiamond : arithmeticDiamondPicard M g⁻¹ (Pic0.mk D) = Pic0.mk E :=
    arithmeticDiamondPicard_inverse_lift_mk M g D
  rw [hdiamond]
  change Pic0.mk (R.degZeroMap ⟨heckeDivisor Qbar M p D.val,
    heckeDivisor_mem_degZero Qbar M p D.property⟩) =
    Pic0.mk (decompositionResidueDegZero A Γ hT d (R.degZeroMap E)) +
      p • Pic0.mk (decompositionResidueDegZero A Γ hT d⁻¹ (R.degZeroMap D))
  rw [← map_nsmul, ← map_add]
'''+s[b:]
t=p/'SourceGammaOneHeckeTorsionPicard1378c.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
f=p/'SourceGammaOnePicardFrobeniusRelation1379c.lean'
s=f.read_text(encoding='utf-8').replace('SourceGammaOneHeckeTorsionPicard1378b','SourceGammaOneHeckeTorsionPicard1378c')
t=p/'SourceGammaOnePicardFrobeniusRelation1379d.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceGammaOneHeckeTorsionPicard1378c','SourceGammaOnePicardFrobeniusRelation1379d')")
t=p/'build_gamma_one_picard_descent_1378c.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')

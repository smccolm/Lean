from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOnePicardFrobeniusRelation1379j.lean';s=f.read_text(encoding='utf-8')
a=s.index('  erw [map_add');b=s.index('\nend\n',a)
s=s[:a]+'''  let F := gamma1ArithmeticPicardRep Qbar M d.val
  let D := arithmeticDiamondPicard M g⁻¹
  have hT : ModularGroup.T ∈ Γ := by simp [Gamma1_mem, ModularGroup.T]
  let C := decompositionResiduePicard A Γ hT d
  let Ci := decompositionResiduePicard A Γ hT d⁻¹
  have hfirst : C (R.pic0Map (D (F x))) = R.pic0Map (F (F (D x))) :=
    (congrArg (fun z => C (R.pic0Map z))
      (arithmeticDiamondPicard_galois M g⁻¹ d.val x).symm).trans (he d (F (D x))).symm
  have hsecond : Ci (R.pic0Map (F x)) = R.pic0Map x :=
    (congrArg Ci (he d x)).trans
      (decompositionResiduePicard_inverse A Γ hT d (R.pic0Map x))
  have hmap : R.pic0Map (F (F (D x)) + p • x) =
      R.pic0Map (F (F (D x))) + p • R.pic0Map x :=
    (R.pic0Map.map_add _ _).trans
      (congrArg (fun z => R.pic0Map (F (F (D x))) + z) (R.pic0Map.map_nsmul p x))
  exact (hhecke R hR _ m hm0 (Pic0.mem_torsion_iff.mp hFx)).trans
    ((congrArg₂ (· + ·) hfirst (congrArg (fun z => p • z) hsecond)).trans hmap.symm)
'''+s[b:]
t=p/'SourceGammaOnePicardFrobeniusRelation1379k.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
target=f.with_suffix('.lean.txt');assert not target.exists();f.rename(target)
f=p/'SourceGammaOneTateFrobeniusRelation1380g.lean';s=f.read_text(encoding='utf-8').replace('1379j','1379k')
t=p/'SourceGammaOneTateFrobeniusRelation1380h.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
target=f.with_suffix('.lean.txt');assert not target.exists();f.rename(target)
s=(p/'build_gamma_one_frobenius_field_1379j.ps1').read_text(encoding='utf-8').replace('1379j','1379k').replace('1380g','1380h')
t=p/'build_gamma_one_picard_relation_1379k.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')

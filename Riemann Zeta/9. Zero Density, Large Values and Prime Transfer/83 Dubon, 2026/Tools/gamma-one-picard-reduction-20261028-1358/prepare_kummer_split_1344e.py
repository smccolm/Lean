from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOneKummerPowerLifting1344d.lean'
t=p.read_text(encoding='utf-8')
t=t.replace('gammaOne_exists_power_of_residue_power_of_degree_genus_eq','gammaOne_kummer_residue_genus_inequality_of_degree_eq').replace('    (hgen : genusFF kk Fb = genusFF Qbar FF)\n','')
t=t.replace('    (f : coefficientGaussRing Δ A)\n','    (f : coefficientGaussRing Δ A) (hf : ∀ g : FF, g ^ q ≠ (f : FF))\n')
start=t.index('    {w : Fb}')
end=t.index('  letI : NeZero q',start)
t=t[:start]+'''    {w : Fb} (hw0 : w ≠ 0) (hw : w ^ q = residueToImage A Δ f)
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E] [IsScalarTower Qbar FF E]
    [IsSplittingField FF E (X ^ q - C (f : FF))] :
    q * genusFF kk Fb ≤ genusFF Qbar E := by
  classical
  haveI := valuation_residue_isAlgClosed A
'''+t[end:]
start=t.index('  rw [hgen] at hineq')
end=t.index('\nend\n',start)
t=t[:start]+'  exact hineq\n'+t[end:]
t=t.replace('import SourceGammaOneKummerGenus1336a','import SourceGammaOneKummerDegree1335a')
a=t.index('/-!');b=t.index('namespace',a)
t=t[:a]+'''/-! DUB-17/18 -> original Gamma1 Picard torsion injectivity -> Kummer
power lifting. The actual unramified prime Kummer cover has q distinct
regular reductions to the original residue image. Coordinate-degree
preservation and the proved separating residue j supply every input to
the joint genus inequality. Genus equality is not needed for this step. -/
'''+t[b:]
(s/'SourceGammaOneKummerResidueGenus1344e.lean').write_text(t,encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))

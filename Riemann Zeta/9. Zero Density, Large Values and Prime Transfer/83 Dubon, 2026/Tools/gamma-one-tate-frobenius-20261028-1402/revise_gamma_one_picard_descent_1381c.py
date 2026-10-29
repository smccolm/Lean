from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneHeckePicardDescent1381b.lean';s=f.read_text(encoding='utf-8')
a=s.index('  rw [hdiamond]');b=s.index('\nend\n',a)
s=s[:a]+'''  have hzero : R.degZeroMap ⟨heckeDivisor Qbar M p D.val,
      heckeDivisor_mem_degZero Qbar M p D.property⟩ =
      decompositionResidueDegZero A Γ hT d (R.degZeroMap E) +
        p • decompositionResidueDegZero A Γ hT d⁻¹ (R.degZeroMap D) := by
    apply Subtype.ext
    change R.divMap (heckeDivisor Qbar M p D.val) =
      decompositionResidueDivisorEquiv A Γ d
        (R.divMap (fieldDivisorEquiv (arithmeticDiamondAut M g) D.val)) +
      p • decompositionResidueDivisorEquiv A Γ d⁻¹ (R.divMap D.val)
    rw [← decompositionResidueDivisorEquiv_symm]
    exact hdiv
  have hclass := congrArg (Pic0.mk (K := kk) (F := Fb)) hzero
  rw [map_add, map_nsmul] at hclass
  change R.pic0Map (heckePicard Qbar M p (Pic0.mk D)) =
    decompositionResiduePicard A Γ hT d (R.pic0Map (Pic0.mk E)) +
      p • decompositionResiduePicard A Γ hT d⁻¹ (R.pic0Map (Pic0.mk D)) at hclass
  exact hclass.trans (congrArg (fun z =>
    decompositionResiduePicard A Γ hT d (R.pic0Map z) +
      p • decompositionResiduePicard A Γ hT d⁻¹ (R.pic0Map (Pic0.mk D))) hdiamond.symm)
'''+s[b:]
t=p/'SourceGammaOneHeckePicardDescent1381c.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
s=(p/'build_gamma_one_inertia_1359.ps1').read_text(encoding='utf-8')
s=s.replace("@('SourceGammaOneArithmeticCharts1359a','SourceGammaOneSpecializationCharts1360a')","@('SourceGammaOneHeckePicardDescent1381c')")
t=p/'build_gamma_one_picard_descent_1381c.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
s='''$ErrorActionPreference='Stop'
$taskScratch='E:\\Lean\\.tmp\\dubon83'
$env:ELAN_HOME='C:\\Users\\Naraphim\\.elan'
$env:LEAN_PATH=$taskScratch
Set-Location -LiteralPath 'E:\\Lean\\Riemann Zeta\\9. Zero Density, Large Values and Prime Transfer\\83 Dubon, 2026\\Extension'
$taskLog=Join-Path $taskScratch 'SourceGammaOneHeckePicardDescent1381b-diagnostics'
if(Test-Path -LiteralPath "$taskLog.log"){throw 'Diagnostic evidence already exists'}
& 'C:\\Users\\Naraphim\\.elan\\bin\\lake.exe' env lean -DautoImplicit=false -Ddiagnostics=true (Join-Path $taskScratch 'SourceGammaOneHeckePicardDescent1381b.lean') *> "$taskLog.log"
$taskCode=$LASTEXITCODE
$taskCode | Set-Content -LiteralPath "$taskLog.exit"
Get-Content -LiteralPath "$taskLog.log" -Tail 45
exit $taskCode
'''
t=p/'diagnose_gamma_one_picard_descent_1381b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')

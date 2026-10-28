from pathlib import Path
import json,re,ast,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
cfg=json.loads((p/'source-gamma-one-smooth-divisor-908-compile-config.json').read_text(encoding='utf-8'))
cfg['compileEvidence']['SourceModularSmoothProjectiveRepresentatives']='SourceModularSmoothProjectiveRepresentatives908b'
mods=cfg['modules'];ths=cfg['theorems'];defs=cfg['constructions'];queries=cfg['queries']
required=queries+[
'Dubon2026.SourceComplexReciprocity.Dipole.exists_localModel_pair',
'Dubon2026.SourceSmoothedUnfolding.projection_ker_card',
'Dubon2026.SourceSmoothedFundamental.finite_moving',
'Dubon2026.SourceFunctionField.CellGeometry.analyticAt_dslope',
'Dubon2026.SourceFunctionField.GammaOne.exists_degree_zero_reciprocity_data',
'Dubon2026.SourceFunctionField.GammaOne.two_mul_ramification_eq_stabilizer_card',
'Dubon2026.SourceFunctionField.GammaOne.analyticPlace_smul_plusMinus',
'Dubon2026.SourceFunctionField.StabilizerCharacter.finite_stabilizer',
'MulAction.stabilizerEquivStabilizer','MonoidHom.fiberEquivKerOfSurjective',
'Nat.card_prod','Equiv.sigmaFiberEquiv']
cfg.update(proofEdges=required,separatelyAxiomChecked=[],separateReason='Every retained declaration is consumed by the actual original-divisor comparison theorem. Three incidental helpers outside the VALUE closure were deferred before audit.')
for m in mods:
 f=p/(m+'.lean');ev=cfg['compileEvidence'][m]
 assert (p/(ev+'.exit')).read_text().strip()=='0' and (p/(ev+'.log')).stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
output('source-gamma-one-smooth-divisor-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceComplexDipoleAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
 b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE COMPLEX DIPOLE','SOURCE GAMMA ONE SMOOTH DIVISOR').replace('Complex Dipole','Gamma One Smooth Divisor')
output('SourceGammaOneSmoothDivisorAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceComplexDipoleDependencyAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',cfg['roots']),('localModules',cfg['scratchImportClosure']),('required',required)]:
 b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE SMOOTH DIVISOR DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the actual original-divisor consumer. Compact dipoles, actual projective fibers, original ramification and degree zero are consumed. V invariance, exact local orders, cusp normalization and logarithmic derivative are constructed. Smooth integral, winding reciprocity, original principal-divisor converse and full all-weight chain remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneSmoothDivisorDependencyAudit1.lean',imports+b)
t=(p/'SourceComplexDipoleScratchOwnership893.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def inspectOwnership'):]
b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
output('SourceGammaOneSmoothDivisorScratchOwnership909.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
paths=[p/'smooth-projective-orbit-route-898.json',p/'smooth-local-model-route-892.json',p/'gamma-one-local-model-construction-reuse-889/S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.lean.txt',p/'source-complex-dipole-1-scratch-receipt.json',p/'source-gamma-one-smooth-divisor-probe-907.json',p/'SourceGammaOneSmoothDivisorValueProbe907.log']
route=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> full all-weight arithmetic association -> original Gamma1 Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> actual smooth invariant comparison V',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in paths],shorterRoute='Use actual projective subgroup and native fiber/kernel equivalences with the already proved kernel of order two, replacing the source positive-matrix representative and duplicated two-fiber infrastructure. Reuse existing analytic dslope, finite stabilizers, proper discontinuity and compact dipoles. Defer three unused lemmas identified by the VALUE probe.',assumptionsToDischarge=['Construct V from the actual degree-zero original analytic divisor at every nonzero Gamma1 level','Derive exact integer local orders from original ramification and projective stabilizer counts','Prove subgroup invariance and value one high in every translated cusp','Construct compact coefficient functions with exact pi times endpoint integral','Derive the actual almost-everywhere logarithmic derivative as the stabilizer-normalized translate sum'],remaining='The smooth comparison V is C1 with prescribed integer local models, not the meromorphic realization required by the principal-divisor converse. Its smoothed integral and the filled quotient winding/period identity must still be assembled into analytic reciprocity, then the original principal-divisor converse and all-weight arithmetic chain. 16/20; DUB-17--20 OPEN.')
output('source-gamma-one-smooth-divisor-audit-route-909.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_complex_dipole_893.py').read_text(encoding='utf-8')
for a,b in [('source-complex-dipole-1','source-gamma-one-smooth-divisor-1'),('SourceComplexDipole','SourceGammaOneSmoothDivisor'),('SOURCE COMPLEX DIPOLE','SOURCE GAMMA ONE SMOOTH DIVISOR'),('source-complex-dipole-audit-route-893.json','source-gamma-one-smooth-divisor-audit-route-909.json'),('(4, 36, 41)',str((len(mods),len(queries),len(required)))),('all 41 required',f'all {len(required)} required'),('requiredProofValueEdges=41',f'requiredProofValueEdges={len(required)}'),('modules=4, queries=36',f'modules={len(mods)}, queries={len(queries)}'),('proofEdges=41',f'proofEdges={len(required)}'),('== 4',f'== {len(mods)}'),('linterScopes=4',f'linterScopes={len(mods)}')]:
 assert a in t,a
 t=t.replace(a,b)
ast.parse(t);output('record_source_gamma_one_smooth_divisor_909.py',t)
ps="$ErrorActionPreference='Stop'\n$env:ELAN_HOME='C:\\Users\\Naraphim\\.elan'\n$env:LEAN_PATH='E:\\Lean\\.tmp\\dubon83'\nSet-Location -LiteralPath 'E:\\Lean\\Riemann Zeta\\9. Zero Density, Large Values and Prime Transfer\\83 Dubon, 2026\\Extension'\n"
ps+="$names=@('SourceGammaOneSmoothDivisorAudit1','SourceGammaOneSmoothDivisorDependencyAudit1','SourceGammaOneSmoothDivisorScratchOwnership909')\n"
ps+=r"""foreach($n in $names){
 $base="E:\Lean\.tmp\dubon83\$n"
 if(Test-Path -LiteralPath "$base.log"){throw "Evidence exists: $n"}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false "$base.lean" *> "$base.log"
 $rc=$LASTEXITCODE
 $rc | Out-File -LiteralPath "$base.exit" -Encoding ascii
 if($rc -ne 0 -or (Select-String -LiteralPath "$base.log" -Pattern 'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]')){
  Get-Content -LiteralPath "$base.log" -Encoding Unicode -Tail 40;exit 1
 }
 Write-Output "PASS $n"
}
python 'E:\Lean\.tmp\dubon83\record_source_gamma_one_smooth_divisor_909.py'
exit $LASTEXITCODE
"""
output('audit_smooth_divisor_909.ps1',ps)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(queries),required=len(required))))

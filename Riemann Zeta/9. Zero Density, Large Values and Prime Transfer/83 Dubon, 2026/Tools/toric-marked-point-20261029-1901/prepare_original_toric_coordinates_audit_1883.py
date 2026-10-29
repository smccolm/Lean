from pathlib import Path
from datetime import datetime, timezone
import ast,hashlib,json,re
p=Path(__file__).parent
repo=Path(r'E:\Lean\Riemann Zeta')
src=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=['SourceTateIntegralCoefficients1873a','SourceTateIntegralCurve1874a','SourceTateEisensteinInvariants1875b','SourceGammaOneToricOriginalRatios1876a','SourceGammaOneToricOriginalCoordinates1877a','SourceGammaOneToricOriginalCoordinateValues1878b','SourceIntegralDiamondScalarRatioAction1879a','SourceGammaOneToricRatioDiamond1880a','SourceGammaOneToricCoordinateDiamond1881b','SourceGammaOneOriginalToricCoordinates1882a']
mapping={v:re.sub(r'\d+[a-z]$','',v) for v in versions}
modules=list(mapping.values());base='Dubon2026.SourceFunctionField.';tc=base+'GammaOne.ToricCoordinates.';tf=base+'GammaOne.ToricFourier.'
theorems=[];constructions=[];queries=[];files=[]
def output(name,text):
 f=p/name;assert not f.exists(),f
 if name.endswith('.py'):ast.parse(text)
 f.write_text(text,encoding='utf-8')
for i,(v,m) in enumerate(mapping.items()):
 f=p/(v+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert not (src/(m+'.lean')).exists()
 t=f.read_text(encoding='utf-8')
 pref=base if i<3 else base+'IntegralDiamond.' if i==6 else tc
 for kind,name in re.findall(r'(?m)^(?:@\[[^]]*\] )?(theorem|lemma|def|abbrev|instance)\s+(\S+)',t):
  full=pref+name;queries.append(full)
  (theorems if kind in ('theorem','lemma') else constructions).append(full)
 c=re.sub(r'(?m)^import (\S+)$',lambda x:'import '+mapping.get(x[1],x[1]),t)
 assert re.sub(r'(?m)^import .*\n','',c)==re.sub(r'(?m)^import .*\n','',t)
 output(m+'.lean',c)
 files.append(dict(version=v,module=m,sourcePath=str(f),originalSha256=sha(f),canonicalSha256=sha(p/(m+'.lean')),mathematicalBodyIdentical=True))
assert len(queries)==len(set(queries))
roots=[tc+'exists_originalToricCoordinates',base+'instIsElliptic_tateLaurent']
edges=roots+[tc+n for n in ['w₁','w₂','β','δ','f6','isIntegralQExp_f6','isIntegralQExp_E6Γ','isIntegralQExp_E4Γ','f6_slash','intSeriesC_eisenstein4_ne_zero','intSeriesC_eisenstein6_ne_zero','intSeriesC_eisenstein4','intSeriesC_eisenstein6','natCast_laurent_ne_zero','coe_w₁','coe_w₂','reducedFieldActionOver_β_inv','reducedFieldActionOver_δ_inv','reducedFieldActionOver_β','reducedFieldActionOver_δ','reducedFieldActionOver_w₁','reducedFieldActionOver_w₂','gamma0Unit','coe_inv_gamma0Unit','sum_reindex']]
edges += [base+n for n in ['tateB','twelve_mul_tateB','tateA6','tatePowerSeries','tateLaurent','laurentOfInt','coeff_one_tateA4','coeff_one_tateA6','c4_tatePowerSeries','c6_tatePowerSeries','c4_tateLaurent','c6_tateLaurent','GammaOne.div_mem_qExpFunctionFieldC']]
edges += [tf+n for n in ['B','D','isIntegralQExp_B','isIntegralQExp_D','B_slash','D_slash','weightTwo_series','weightFour_series','fourier_inversion']]
edges += [base+'IntegralDiamond.'+n for n in ['reducedFieldActionOver_integral_ratio','reducedFieldPull_eq','reducedDiamond_eq','reducedFieldActionOver_coeff']]
edges += [base+'GammaOne.divisionForm','Dubon2026.SourceFricke.qExpansion_wpNormZ_coeff','Dubon2026.SourceFricke.qExpansion_E6_eq_map_eisenstein6','MonoidHom.toHomUnits']
assert len(edges)==len(set(edges))
cfg=dict(modules=modules,theorems=theorems,constructions=constructions,queries=queries,roots=roots,proofEdges=edges,compileEvidence={m:m+'-1883' for m in modules},separatelyAxiomChecked=[])
output('source-original-toric-coordinates-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
output('original-toric-coordinates-versions-1883.json',json.dumps(files,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
array=lambda ns:'#['+', '.join('`'+n for n in ns)+']'
def replace_array(t,n,ns):
 t,c=re.subn(r'(?m)^  let '+n+r' : Array Name := #\[.*$', '  let '+n+' : Array Name := '+array(ns),t);assert c==1,n;return t
for old,new in [('SourceIntegralToricFormsAudit2','SourceOriginalToricCoordinatesAudit1'),('SourceIntegralToricFormsDependencyAudit2','SourceOriginalToricCoordinatesDependencyAudit1'),('SourceIntegralToricFormsScratchOwnership1872','SourceOriginalToricCoordinatesScratchOwnership1883')]:
 t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
 t=t.replace('IntegralToricForms','OriginalToricCoordinates').replace('Integral toric forms','Original toric coordinates').replace('SOURCE INTEGRAL TORIC FORMS','SOURCE ORIGINAL TORIC COORDINATES')
 if 'Dependency' in old:
  for n,ns in [('roots',roots),('localModules',modules+json.loads((p/'source-integral-toric-forms-2-audit-config.json').read_text())['modules']),('required',edges)]:t=replace_array(t,n,ns)
  a=t.index('  logInfo m!');b=t.index('\n\n#eval',a)
  t=t[:a]+'  logInfo m!"SOURCE ORIGINAL TORIC COORDINATES DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the literal original-field toric coordinates and Tate ellipticity. Integral modular ratios, exact Laurent values and the actual diamond action are consumed. Exact-order points, finite elliptic fibers and reverse genus remain open; DUB17--20 OPEN."'+t[b:]
 elif 'Ownership' in old:t=replace_array(t,'mods',modules)
 else:
  t=t[:t.index('\n#lint')]
  for n,ns in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=replace_array(t,n,ns)
  t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
 output(new+'.lean',imports+t)
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB17 Theorem2.6 / DUB18 Cor8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight association -> Gamma1 genus preservation -> reverse genus -> finite elliptic residue fibers -> actual Gamma1 marked-point chart -> original-field toric coordinates and literal Tate curve.',reuseChecked=[],shorterRoute='Reuse the accepted integral B,D forms, original same-weight-ratio membership and actual prime-field/scalar-extended diamond action. Mathlib Gamma0Map.toHomUnits and finite sum reindexing supply the exact index action without constructing a second Gamma0 character. Native Eisenstein series identify the literal Tate c4 and c6. Full nonarchimedean uniformization and general non-toric slots are deferred while the native complex period uniformization/division-polynomial/good-reduction route is assessed.',assumptionsToDischarge=['Literal integral Tate a6 coefficients, c4=E4 and c6=-E6, with ellipticity in every coefficient characteristic proved from the discriminant leading coefficient.', 'Both toric invariant functions are constructed as actual same-weight integral modular-form ratios in the original Gamma1 field.', 'Their exact Laurent-series values follow from the proved integer Fourier reconstruction.', 'The original residue diamond action is proved on those field elements; no ratio-action or compatibility certificate is assumed.'],remaining='The exact-order toric point, marked-point/original-field correspondence, finite elliptic fiber bounds and reverse genus remain required. Acceptance16/20;DUB17--20 OPEN.',boundary='Scratch audit only. No point, finite-fiber bound or completed gate is claimed.',rootPinsChanged=False,proofLimitsChanged=False)
for n in ['SourceGammaOneDivisionForms','SourceGammaOneFunctionField','SourceIntegralDiamondScalarNormalizedAction','SourceIntegerJEulerNormalization','SourceEllipticPeriodUniformization','SourceEllipticVariableAddEquiv','SourceEllipticTorsionDivisionRoot','SourceEllipticTorsionReductionCoordinates']:
 f=src/(n+'.lean');route['reuseChecked'].append(dict(path=str(f),sha256=sha(f)))
for f in [repo/'.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean',repo/'.lake/packages/mathlib/Mathlib/Algebra/Group/Units/Hom.lean']:
 route['reuseChecked'].append(dict(path=str(f),sha256=sha(f)))
route['externalReferences']=[dict(path=str(f),sha256=sha(f),built=False,imported=False) for f in [p/'anthropic-tate-formal-1860b/Def_ModularCurve_TateFormal.lean.txt',p/'anthropic-gamma-one-toric-inputs-1848/S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq.lean.txt']]
output('source-original-toric-coordinates-audit-route-1883.json',json.dumps(route,indent=2)+'\n')
t=(p/'build_integral_toric_forms_canonical_1872.ps1').read_text(encoding='utf-8')
t=re.sub(r'(?m)^\$names=@\(.*$', '$names=@('+','.join("'"+m+"'" for m in modules)+')',t)
t=t.replace('1872','1883').replace('integral_toric_forms','original_toric_coordinates')
output('build_original_toric_coordinates_canonical_1883.ps1',t)
t=(p/'audit_integral_toric_forms_1872.ps1').read_text(encoding='utf-8')
t=t.replace('SourceIntegralToricFormsAudit2','SourceOriginalToricCoordinatesAudit1').replace('SourceIntegralToricFormsDependencyAudit2','SourceOriginalToricCoordinatesDependencyAudit1').replace('SourceIntegralToricFormsScratchOwnership1872','SourceOriginalToricCoordinatesScratchOwnership1883').replace('record_integral_toric_forms_1872','record_original_toric_coordinates_1883')
output('audit_original_toric_coordinates_1883.ps1',t)
t=(p/'record_integral_toric_forms_1872.py').read_text(encoding='utf-8')
for a,b in {'source-integral-toric-forms-2':'source-original-toric-coordinates-1','source-integral-toric-forms-audit-route-1872':'source-original-toric-coordinates-audit-route-1883','SourceIntegralToricFormsAudit2':'SourceOriginalToricCoordinatesAudit1','SourceIntegralToricFormsDependencyAudit2':'SourceOriginalToricCoordinatesDependencyAudit1','SourceIntegralToricFormsScratchOwnership1872':'SourceOriginalToricCoordinatesScratchOwnership1883','SOURCE INTEGRAL TORIC FORMS':'SOURCE ORIGINAL TORIC COORDINATES','(15, 93, 57)':str((len(modules),len(queries),len(edges))),'== 15':'== 10','linterScopes=15':'linterScopes=10','all 57 required':'all '+str(len(edges))+' required','requiredProofValueEdges=57':'requiredProofValueEdges='+str(len(edges)),'modules=15, queries=93':'modules=10, queries='+str(len(queries)),'proofEdges=57':'proofEdges='+str(len(edges))}.items():t=t.replace(a,b)
output('record_original_toric_coordinates_1883.py',t)
print(json.dumps(dict(modules=len(modules),queries=len(queries),theorems=len(theorems),constructions=len(constructions),edges=len(edges))))

from pathlib import Path
import re,json
s=Path(__file__).parent
versions={
'SourcePeakedDiscriminantSeries':'1610b','SourcePeakedSeriesOperations':'1611b',
'SourcePeakedShiftedCoefficients':'1615b','SourcePeakedShiftedSeries':'1613d',
'SourcePeakedWidthOneIdentification':'1617b','SourcePeakedIntegralQExpansion':'1618b',
'SourcePeakedTranslatedIntegralExpansion':'1620a','SourcePeakedScaledOrders':'1621a',
'SourcePeakedOrderGapDecay':'1622a','SourceActualPeakedAuxiliary':'1623a'}
mods=[m+v for m,v in versions.items()];ths=[];defs=[]
for m in mods:
 f=s/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S));ns=re.search(r'^namespace (\S+)',c,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^(?:theorem|lemma)\s+([\w.\x27]+)',c,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:noncomputable )?def\s+([\w.\x27]+)',c,re.M)]
assert len(set(ths+defs))==len(ths+defs)
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.'
roots=[ns+'exists_gamma1_peaked_auxiliary_form_twelve_dvd']
edges=ths+defs+[
'Dubon2026.SourceFunctionField.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit',
'Dubon2026.hasSum_pow_dvd_reindex',
'Dubon2026.SourceFricke.qParam_one_eq_pow',
'Dubon2026.SourceFricke.gammaOne_one_mem_strictPeriods',
'Dubon2026.SourceFricke.qExpansion_coeff_width',
'Dubon2026.SourceFunctionField.GammaOne.CuspAuxiliary.natCast_mem_strictPeriods_conj',
'ModularFormClass.qExpansion_coeff_unique',
ns+'exists_peaked_exponent_on_actual_cusps',
ns+'Form.exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow',
ns+'Form.uFun_smul',ns+'Form.ord_eq',ns+'Form.thetaFun_slash_apply',
ns+'FiniteExpansion.hasSum_productSeries',ns+'FiniteExpansion.integral_productSeries',
ns+'FiniteExpansion.integral_level_inverse_productSeries_zero',
ns+'FiniteExpansion.productSeries_zero_ne_zero']
cfg=dict(modules=mods,theorems=ths,constructions=defs,roots=roots,proofEdges=edges)
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
def write(n,t):
 f=s/n;assert not f.exists();f.write_text(t,encoding='utf-8')
write('actual-peaked-auxiliary-versions-1624.json',json.dumps(versions,indent=2)+'\n')
write('actual-peaked-auxiliary-preflight-config-1624.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceIntegralTraceAudit1','SourceActualPeakedAuxiliaryPreflight1624'),('SourceIntegralTraceDependencyAudit1','SourceActualPeakedAuxiliaryValuePreflight1624')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if a=='SourceIntegralTraceAudit1':
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 else:
  for k,v in [('roots',roots),('localModules',mods),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the actual even-weight Gamma1 peaked auxiliary, including proved exponent scaling, discriminant power choice, exact integral coefficients and leading inverse, weight/order gap and separated cusp decay. The auxiliary existence premise is discharged; its trace application, reduced field action and degree/genus preservation remain open'+c[end:]
 c=c.replace('INTEGRAL TRACE','ACTUAL PEAKED AUXILIARY PREFLIGHT').replace('Frobenius Normalization','Siegel expansion')
 write(b+'.lean',c)
 c=(s/'audit_peaked_exponent_preflight_1552.ps1').read_text(encoding='utf-8').replace('SourcePeakedExponentPreflight1552',b)
 write('audit_'+b+'_1624.ps1',c)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),edges=len(edges))))

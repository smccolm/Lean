from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneHeckeMixedLaurentReduction','SourceGammaOneHeckeIntegralDiamondReduction']
ev=dict(zip(mods,['1322a','1323c'],strict=True))
ths=[];defs=[]
for m in mods:
 assert (p/(m+ev[m]+'.exit')).read_text().strip()=='0'
 assert (p/(m+ev[m]+'.log')).stat().st_size==0
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
 defs += [ns+x for x in re.findall(r'^def\s+([\w.\x27]+)',code,re.M)]
cn='Dubon2026.SourceFunctionField.GammaOne.'
previous=json.loads((p/'source-gamma-one-diamond-norm-2-audit-config.json').read_text(encoding='utf-8'))
roots=[cn+'exists_gammaOne_hecke_norm_integral_reduction_of_diamond']
edges=ths+defs+[cn+'exists_gammaOne_hecke_norm_beta_product',
 'Dubon2026.SourceFunctionField.primeRootValuationUnit_coe',
 'Dubon2026.SourceFunctionField.primeRootValuationUnit_residue',
 'Dubon2026.SourceFunctionField.qExpand_heckeLaurentUnexpand',
 'Dubon2026.SourceFunctionField.pow_char_eq_coeffMap_frobenius_qExpand',
 'Dubon2026.SourceFunctionField.qExpand_injective']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,
 proofEdges=edges,localModules=previous['localModules']+mods,separatelyAxiomChecked=[],
 compileEvidence={m:m+ev[m] for m in mods})
assert (len(ths),len(defs),len(edges))==(3,1,10)
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-diamond-reduction-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneHeckeDegree';new='SourceGammaOneDiamondReduction'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1297','ScratchOwnership1325')]:
 s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
 s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
 if a=='Audit1':
  s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1':
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
  s=s[:start]+' occur in the proof value closure of the actual original Gamma1 integral Hecke norm reduction with explicit integral representatives of the original input and its actual diamond image. The norm-product, embedding census, reverse-map identity and diamond label are derived; producing the diamond integral representative from input integrality alone, genus preservation and original Picard specialization remain unresolved'+s[end:]
 else:
  s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('GAMMA ONE HECKE DEGREE','GAMMA ONE DIAMOND REDUCTION')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in ['SourceOriginalHeckeNormReduction',
 'SourceHeckeLaurentNormExtraction','SourceHeckeLaurentProductReduction','SourceHeckePrimeRootReduction',
 'SourceLaurentFrobenius','SourceLaurentCoefficientReindex']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 Tate Frobenius -> Hecke norm reduction -> the two-input Laurent product and exact arithmetic diamond norm.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='Reuse the existing primitive-root valuation unit, characteristic-p twist collapse, Laurent Frobenius and coefficient unexpansion. The necessary adaptation has exactly two integral Laurent inputs: the actual diamond image and the original function. The already proved actual beta norm product discharges the product hypothesis. No new valuation or norm infrastructure is introduced; integral preservation by the diamond is not assumed silently.',
 assumptionsToDischarge=['Given integral Laurent representatives of an original function and its actual arithmetic diamond image, the genuine Hecke norm has an integral representative with the exact coefficient-Frobenius-times-q-Frobenius residue. The norm product, complete embeddings, reverse-map identity and diamond label are no longer premises.'],
 remaining='An integral representative of the actual diamond image remains an explicit narrower input. It must be constructed from input integrality alone before claiming unconditional integral norm reduction. Residue degree equality, genus preservation, original-to-residue place/Picard specialization and torsion injectivity remain, hence original Tate Frobenius/inertia, arithmetic realization, all-weight association, automorphy and higher continuation remain. 16/20; DUB17--20 OPEN.',
 externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
routefile='source-gamma-one-diamond-reduction-audit-route-1325.json'
write(routefile,json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_hecke_degree_1297.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-hecke-degree-audit-route-1297',routefile[:-5]),
 ('source-gamma-one-hecke-degree-1',stem),(old,new),('ScratchOwnership1297','ScratchOwnership1325'),
 ('GAMMA ONE HECKE DEGREE','GAMMA ONE DIAMOND REDUCTION')]:s=s.replace(a,b)
s=s.replace('(4, 14, 22)','(2, 4, 10)').replace('== 4','== 2')
s=s.replace('linterScopes=4','linterScopes=2').replace('modules=4','modules=2')
s=s.replace('queries=14','queries=4').replace('all 22 required','all 10 required')
s=s.replace('requiredProofValueEdges=22','requiredProofValueEdges=10').replace('proofEdges=22','proofEdges=10')
ast.parse(s);write('record_gamma_one_diamond_reduction_1325.py',s)
s=(p/'audit_gamma_one_hecke_degree_1297.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1297','ScratchOwnership1325'),
 ('record_gamma_one_hecke_degree_1297','record_gamma_one_diamond_reduction_1325')]:s=s.replace(a,b)
write('audit_gamma_one_diamond_reduction_1325.ps1',s)
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),proofEdges=len(edges))))

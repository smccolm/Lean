from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneGaussCriterion','SourceGammaOneGaussValuation',
 'SourceGammaOneGaussResidueHom','SourceGammaOneGaussResidueKernel',
 'SourceGammaOneGaussConstants','SourceGammaOneGaussResidueImage',
 'SourceGammaOneRegularProlongation','SourceGammaOneResidueJCoordinate',
 'SourceReductionResidueCoordinateFinite','SourceGammaOneResidueCoordinateFinite']
attempts=['1268b','1269b','1270b','1271a','1272a','1273b','1274a','1275a','1276b','1277b']
ev={m:m+a for m,a in zip(mods,attempts)}
ths=[];defs=[]
for m in mods:
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0'
 assert (p/(ev[m]+'.log')).stat().st_size==0
 raw=(p/(m+'.lean')).read_text(encoding='utf-8')
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',raw,flags=re.S))
 ns=re.findall(r'^namespace ([\w.]+)',code,re.M)
 assert len(ns)==1
 ths += [ns[0]+'.'+x for x in re.findall(r"^theorem\s+([\w.']+)",code,re.M)]
 defs += [ns[0]+'.'+x for x in re.findall(r"^def\s+([\w.']+)",code,re.M)]
gn='Dubon2026.SourceFunctionField.GammaOne.'
cn=gn+'CoefficientReduction.'
rn='Dubon2026.SourceCurve.RegularProlongation.'
edges=[gn+x for x in ['qExpFunctionField_exists_primitive_fraction',
 'qExpFunctionField_isInt_or_inv','coefficientGaussRing',
 'functionFieldOver_eq_qExpFunctionFieldC','finiteDimensional_jCoordinateOver']]
edges += [cn+x for x in ['resHom','resHom_eq_zero_iff','algebraMap_mem_gaussRing_iff',
 'exists_smul_mem_gaussRing','residueEmbedding','residueImage','residueToImage',
 'regularProlongation','resHom_jCoordinateOver','transcendental_residueJCoordinate',
 'finite_residueCoordinate_and_degree_le','gammaOne_finite_residueCoordinate_and_degree_le']]
edges += [rn+x for x in ['residue_coordinate_rank_le','residue_coordinate_finite_and_finrank_le',
 'linearIndependent_adjoinField']]
edges += ['Dubon2026.SourceFunctionField.GaussReduction.exists_primitive_form',
 'Dubon2026.SourceFunctionField.transcendental_jqModC','rank_le']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,
 roots=[cn+'gammaOne_finite_residueCoordinate_and_degree_le'],proofEdges=edges,
 localModules=mods,separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-reduction-2'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceDiamondTransfer';new='SourceGammaOneReduction'
for a,b in [('Audit1','Audit2'),('DependencyAudit1','DependencyAudit2'),('ScratchOwnership1262','ScratchOwnership1278b')]:
 s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
 s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
 if a=='Audit1':
  s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1':
  for k,v in [('roots',cfg['roots']),('localModules',mods),('required',edges)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
  s=s[:start]+' occur in the proof value closure of the original Gamma1 residue finite-coordinate endpoint, through native primitive fractions, the literal coefficient valuation, exact residue kernel, constructed regular prolongation, transcendental reduced j and native coordinate independence lifting. Degree equality, genus preservation, original geometric Frobenius and inertia remain unresolved'+s[end:]
 else:
  s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('DIAMOND TRANSFER','GAMMA ONE REDUCTION')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in [
 'SourceGammaOneFunctionField','SourceGammaOneScalarExtension','SourceGammaOneFunctionFieldFinite',
 'SourceModularPrimitiveScaling','SourceModularGaussFractions','SourceModularGaussResidueHom',
 'SourceModularGaussResidueKernel','SourceModularGaussValuationRing','SourceReductionFrame',
 'SourceOriginalPicardFrobeniusQuadratic','SourceOriginalFrobeniusPicardReduction',
 'SourceOriginalHeckeTorsionReduction']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original finite Gamma1 arithmetic realization -> original geometric Tate Frobenius/inertia -> original good reduction and prime-to-residue Picard torsion specialization -> literal coefficient prolongation and finite residue coordinate.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='Reuse native finite integer coefficient spans, primitive scaling, fraction operations and coordinate-field independence lifting. Restrict the fraction valuation to the original scalar-extended Gamma1 function field. Construct its actual residue field image in Laurent series and prove its exact kernel and constant action, without assuming an identification with a separately defined characteristic-p modular function field. The literal original j-coordinate reduces to the native integral j-series. Its transcendence and the existing original finite-degree theorem give finite residue degree by the native independence lift; no separate valuation-extension theorem or new scheme/cohomology framework is needed.',
 assumptionsToDischarge=[
 'Every original q-expansion ratio has a primitive scaled integral fraction; the literal IsInt predicate on the original scalar-extended field is a valuation subring.',
 'The actual coefficient reduction is well defined with maximal-ideal kernel, correct restriction to constants and nonzero constant rescaling. Its actual Laurent residue image receives a surjective residue map, constructing the full native RegularProlongation without caller assumptions.',
 'The original j-coordinate reduces to the literal residue j-series, proved transcendental. The original finite-coordinate theorem and native independence lift prove finite residue degree and the upper bound by the original degree, including the actual Gamma1 levels.'],
 remaining='This is the original coefficient valuation and regular prolongation with finite residue coordinate and degree upper bound, not degree equality, genus preservation, place compatibility, good reduction or torsion injectivity. Original Hecke/diamond reduction, geometric Frobenius and inertia, parabolic character realization, exceptional-prime exclusion, coefficient-field realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher continuation remain. 16/20; DUB17--20 OPEN.',
 preservedFailures='Superseded successful bodies and failed elaborations are preserved as inert sources and original logs. Fixes concern exact native namespace, intermediate-field construction and dependent coordinate rewriting; no statement weakening, limit increase or diagnostic suppression.',
 externalBuild=False,externalImport=False,rootPinsChanged=False)
write('source-gamma-one-reduction-audit-route-1278b.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_diamond_transfer_1262.py').read_text(encoding='utf-8')
for a,b in [('source-diamond-transfer-audit-route-1262','source-gamma-one-reduction-audit-route-1278b'),
 ('source-diamond-transfer-1',stem),(old,new),('ScratchOwnership1262','ScratchOwnership1278b'),
 ('DIAMOND TRANSFER','GAMMA ONE REDUCTION')]:s=s.replace(a,b)
s=s.replace('(9, 14, 20)',str((len(mods),len(ths+defs),len(edges))))
s=s.replace('== 9','== 10').replace('linterScopes=9','linterScopes=10').replace('modules=9','modules=10')
s=s.replace('all 20 required',f'all {len(edges)} required').replace('requiredProofValueEdges=20',f'requiredProofValueEdges={len(edges)}')
s=s.replace('proofEdges=20',f'proofEdges={len(edges)}').replace('queries=14',f'queries={len(ths+defs)}')
s=s.replace('SourceGammaOneReductionAudit1','SourceGammaOneReductionAudit2').replace('SourceGammaOneReductionDependencyAudit1','SourceGammaOneReductionDependencyAudit2')
ast.parse(s);write('record_gamma_one_reduction_1278b.py',s)
s=(p/'audit_diamond_transfer_1262.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1262','ScratchOwnership1278b'),('record_diamond_transfer_1262','record_gamma_one_reduction_1278b')]:s=s.replace(a,b)
s=s.replace('SourceGammaOneReductionAudit1','SourceGammaOneReductionAudit2').replace('SourceGammaOneReductionDependencyAudit1','SourceGammaOneReductionDependencyAudit2')
write('audit_gamma_one_reduction_1278b.ps1',s)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))

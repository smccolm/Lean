from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneResiduePlaces','SourceGammaOneResiduePlaceOrders','SourceGammaOneResidueFrobeniusPlaces']
ev=dict(zip(mods,['1288a','1289a','1290a'],strict=True))
cn='Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.'
ths=[];defs=[]
for m in mods:
 assert (p/(m+ev[m]+'.exit')).read_text().strip()=='0'
 assert (p/(m+ev[m]+'.log')).stat().st_size==0
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ths += [cn+x for x in re.findall(r"^theorem\s+([\w.']+)",code,re.M)]
 defs += [cn+x for x in re.findall(r"^def\s+([\w.']+)",code,re.M)]
roots=[cn+x for x in ['decompositionResiduePlaceEquiv',
 'decompositionResiduePlace_ord_action','decompositionResiduePlace_eq_self_of_inertia',
 'geometricFrobenius_place_order']]
edges=[x for x in ths+defs if not x.endswith('.mem_decompositionResiduePlace_iff')]+[
 cn+'decompositionResidueAut',cn+'decompositionResidueAut_eq_one_of_inertia',
 cn+'geometricFrobenius','Dubon2026.SourceCurve.Place.eq_ord_of_addHom_of_nonneg_iff',
 'Dubon2026.SourceCurve.Place.ord_zpow']
prev=json.loads((p/'source-gamma-one-residue-frobenius-1-audit-config.json').read_text(encoding='utf-8'))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,
 proofEdges=edges,localModules=prev['localModules']+mods,separatelyAxiomChecked=[],
 compileEvidence={m:m+ev[m] for m in mods})
assert(len(ths),len(defs),len(edges))==(10,4,18)
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-residue-places-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneResidueCompatibility';new='SourceGammaOneResiduePlaces'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),
 ('ScratchOwnership1285','ScratchOwnership1291')]:
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
  s=s[:start]+' occur in the proof value closures of the actual Gamma1 residue decomposition permutation, inertia identity and geometric Frobenius place restriction with normalized order multiplied by p. Norm reduction, degree and genus preservation, Picard specialization and the geometric Tate quadratic remain unresolved'+s[end:]
 else:
  s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('GAMMA ONE RESIDUE COMPATIBILITY','GAMMA ONE RESIDUE PLACES')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in [
 'SourceCurvePlaceTransport','SourceResidueCoefficientPlaces',
 'SourceResidueCoefficientPlaceOrders','SourceResidueGeometricFrobeniusPlaces']]
reuse += [p/'source-gamma-one-residue-compatibility-1-scratch-receipt.json',
 p/'source-gamma-one-residue-frobenius-1-scratch-receipt.json']
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 Picard/Tate Frobenius and inertia -> equivariant specialization on places -> actual decomposition and geometric Frobenius on residue places.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='Reuse the existing normalized discrete-order uniqueness and the native coefficient-place construction, specialized to the already constructed actual Gamma1 residue image. Literal valuation-ring transport proves discreteness. The actual coefficient automorphism supplies the inverse permutation and inertia identity. Comap along geometric Frobenius equals that coefficient place, so discreteness and the exact order multiplier p follow directly without adding a separate degree argument or generic scheme framework.',
 assumptionsToDischarge=[
 'The actual decomposition action permutes all genuine places of the original Gamma1 residue field and preserves normalized orders with the precise inverse convention.',
 'Original arithmetic inertia fixes the actual residue places.',
 'For an actual decomposition element with pth-power action on residue constants, restriction along the original geometric Frobenius is exactly that decomposition permutation, with normalized orders multiplied by p.'],
 remaining='The arithmetic Frobenius constant-action premise is explicit. The original norm identity, degree equality, genus preservation, original-to-residue place/Picard specialization and prime-to-residue torsion injectivity remain. Actions on residue places alone do not prove inertia or the Frobenius quadratic on the original Picard Tate module. Parabolic character realization, exceptional primes, coefficient-field realization, original all-weight characteristic-zero association, automorphy and literal higher continuation remain. 16/20; DUB17--20 OPEN.',
 externalBuild=False,externalImport=False,rootPinsChanged=False)
routefile='source-gamma-one-residue-places-audit-route-1291.json'
write(routefile,json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_residue_compatibility_1285.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-residue-compatibility-audit-route-1285',routefile[:-5]),
 ('source-gamma-one-residue-compatibility-1',stem),(old,new),
 ('ScratchOwnership1285','ScratchOwnership1291'),
 ('GAMMA ONE RESIDUE COMPATIBILITY','GAMMA ONE RESIDUE PLACES')]:s=s.replace(a,b)
s=s.replace('(6, 28, 39)','(3, 14, 18)').replace('== 6','== 3')
s=s.replace('linterScopes=6','linterScopes=3').replace('modules=6','modules=3')
s=s.replace('all 39 required','all 18 required').replace('requiredProofValueEdges=39','requiredProofValueEdges=18')
s=s.replace('proofEdges=39','proofEdges=18').replace('queries=28','queries=14')
ast.parse(s);write('record_gamma_one_residue_places_1291.py',s)
s=(p/'audit_gamma_one_residue_compatibility_1285.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1285','ScratchOwnership1291'),
 ('record_gamma_one_residue_compatibility_1285','record_gamma_one_residue_places_1291')]:s=s.replace(a,b)
write('audit_gamma_one_residue_places_1291.ps1',s)
print(json.dumps(dict(modules=3,queries=14,edges=18)))

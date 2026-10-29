from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib
s=Path(__file__).parent
versions={'SourceReducedBaseCoordinateMap':'1702b','SourceReducedBaseDegreeLower':'1703b',
 'SourceIntegralDiamondIndexLower':'1704b','SourceReducedCoordinateIndependence':'1707a',
 'SourceReducedCoordinateMapIndependence':'1708a','SourceReducedFieldCoefficientMap':'1710b',
 'SourceReducedCoordinateDegreeTransport':'1711a','SourceReducedResidueDegreeTransport':'1712b',
 'SourceGammaOneDegreePreservation':'1713a'}
mods=[m+v for m,v in versions.items()];ths=[]
for m in mods:
 f=s/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',c,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^(?:theorem|lemma)\s+([\w.\x27]+)',c,re.M)]
ns='Dubon2026.SourceFunctionField.'
roots=[ns+'IntegralDiamond.'+n for n in ['gammaOne_degree_and_residueField_away_level','signed_index_le_residue_ratio_degree']]
prior=json.loads((s/'reduced-diamond-kernel-preflight-config-1705.json').read_text(encoding='utf-8'))
edges=ths+prior['proofEdges']+[ns+n for n in ['residue_j_minpoly_natDegree_eq_psi',
 'finiteDimensional_coeff_field','residue_j_substitution_isIntegral','linearIndependent_coeffMap_algebraMap',
 'GammaOne.CoefficientReduction.gammaOne_degree_and_residueField_of_integral_ratio_index',
 'GammaOne.CoefficientReduction.finite_residueCoordinate_and_degree_le',
 'GammaOne.CoefficientReduction.qExpFunctionFieldC_le_residueImage']]
edges+=['Dubon2026.SourceLevelProjective.gamma0_index','minpoly.degree_le_of_ne_zero','Module.rank_lt_aleph0_iff']
edges=list(dict.fromkeys(edges))
cfg=dict(modules=mods,theorems=ths,constructions=[],roots=roots,proofEdges=edges,localModules=mods+prior['localModules'])
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
write('gamma-one-degree-versions-1715.json',json.dumps(versions,indent=2)+'\n')
write('gamma-one-degree-preflight-config-1715.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceReducedDiamondKernelPreflight1705','SourceGammaOneDegreePreflight1715'),('SourceReducedDiamondKernelValuePreflight1705','SourceGammaOneDegreeValuePreflight1715')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if 'Value' not in a:
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',[])]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 else:
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of original Gamma1 coordinate degree preservation and equality of the actual residue image with the original integral-ratio field, at every coefficient prime away from the level. No signed-index, finiteness, coefficient-independence or degree-preservation premise remains. Genus preservation, all-weight association, automorphy and higher continuation remain open'+c[end:]
 c=c.replace('REDUCED DIAMOND KERNEL PREFLIGHT','GAMMA ONE DEGREE PREFLIGHT')
 write(b+'.lean',c)
 c=(s/('audit_'+a+'_1705.ps1')).read_text(encoding='utf-8').replace(a,b)
 write('audit_'+b+'_1715.ps1',c)
c=(s/'audit_reduced_diamond_kernel_preflight_1705.ps1').read_text(encoding='utf-8').replace('1705','1715').replace('ReducedDiamondKernel','GammaOneDegree')
write('audit_gamma_one_degree_preflight_1715.ps1',c)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
native=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
files=[native/n for n in ['SourceLaurentScalarIndependence.lean','SourceLaurentDegreeTransportIndependence.lean',
 'SourceModularCoefficientFieldFinite.lean','SourceResidueAllLevelDegree.lean',
 'SourceGammaOneResidueRatioDegree.lean','SourceGammaOneIntegralRatioDegreeAssembly.lean']]
files+=[s/'anthropic-reduced-degree-transport-1706/manifest.json']
review=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB17 Thm2.6 / DUB18 Cor8.2 -> higher continuation -> automorphy -> original all-weight association -> actual homogeneous Gamma1 Hecke-character realization -> original degree/genus preservation -> signed-index lower bound and finite-degree transport.',
 checked=[dict(path=str(f),sha256=sha(f)) for f in files],
 selectedRoute='Map the actual j-substitution minimal polynomial to the algebraic closure and use the already proved exact degree there. Only a lower bound on the full base degree is needed. Native finite divisor generation supplies finiteness. Actual Artin degree and base fixation give the signed-index bound from positive coordinate degree. Native coefficient independence plus finite denominator clearing transfers positive degree and the bound between the original prime and residue fields; no base-change equality, new spanning theorem or infinite-dimensional transport is needed. Native upper-degree assembly then proves degree preservation and actual residue-field equality.',
 discharged=['full modular base lower degree','finite prime-field coordinate degree','signed total index lower bound','coordinate degree preservation','residue image equals original integral-ratio field'],
 endpointAssumptions=['nonzero level N','prime ell not dividing N','actual valuation subring A of a characteristic-zero coefficient field','residue field of characteristic ell'],
 remaining='Original genus preservation and all remaining DUB17--20 requirements. Acceptance16/20. Mathematical endpoint compiles; preflight and canonical verification pending.',
 proofOptionsChanged=False,externalImport=False,externalBuild=False)
write('gamma-one-degree-reuse-review-1714.json',json.dumps(review,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),theorems=len(ths),edges=len(edges))))

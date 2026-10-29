from pathlib import Path
import json,re
s=Path(__file__).parent
versions={'SourceGammaOneResidueGenusUpper':'1717b'}
mods=[m+v for m,v in versions.items()]
for m in mods:
 f=s/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
ths=['Dubon2026.SourceFunctionField.IntegralDiamond.gammaOne_residue_genus_le_away_level']
prior=json.loads((s/'gamma-one-degree-preflight-config-1715.json').read_text(encoding='utf-8'))
edges=ths+prior['proofEdges']+['Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly.genus_inequality_of_separating_residue_coordinate',
 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.isSeparable_residueCoordinate',
 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.regularProlongation_jCoordinateOver']
cfg=dict(modules=mods,theorems=ths,constructions=[],roots=ths,proofEdges=edges,localModules=mods+prior['localModules'])
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
write('gamma-one-genus-upper-versions-1720.json',json.dumps(versions,indent=2)+'\n')
write('gamma-one-genus-upper-preflight-config-1720.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceGammaOneDegreePreflight1715','SourceGammaOneGenusUpperPreflight1720'),('SourceGammaOneDegreeValuePreflight1715','SourceGammaOneGenusUpperValuePreflight1720')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if 'Value' not in a:
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',[])]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 else:
  for k,v in [('roots',ths),('localModules',cfg['localModules']),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the actual original Gamma1 residue genus upper bound. The original degree-preservation theorem and native separating coordinate discharge every hypothesis of the single-prolongation genus inequality. Reverse genus comparison, all-weight association, automorphy and higher continuation remain open'+c[end:]
 c=c.replace('GAMMA ONE DEGREE PREFLIGHT','GAMMA ONE GENUS UPPER PREFLIGHT')
 write(b+'.lean',c)
 c=(s/('audit_'+a+'_1715.ps1')).read_text(encoding='utf-8').replace(a,b)
 write('audit_'+b+'_1720.ps1',c)
c=(s/'audit_gamma_one_degree_preflight_1715.ps1').read_text(encoding='utf-8').replace('1715','1720').replace('GammaOneDegree','GammaOneGenusUpper')
write('audit_gamma_one_genus_upper_preflight_1720.ps1',c)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),edges=len(edges))))

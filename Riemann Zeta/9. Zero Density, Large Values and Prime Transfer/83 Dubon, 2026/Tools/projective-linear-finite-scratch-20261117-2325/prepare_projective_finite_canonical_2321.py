from pathlib import Path
import json, hashlib, re
s = Path(__file__).parent
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
c = json.loads((s / 'source-projective-linear-audit-config-2313.json').read_text())
pairs = [
 ('SourceResidualFiniteAmbient2316d','SourceResidualFiniteAmbient'),
 ('SourceResidualFiniteDescent2317a','SourceResidualFiniteDescent'),
 ('SourceResidualFiniteBounds2318b','SourceResidualFiniteBounds'),
 ('SourceResidualFiniteLinearAlternatives2319a','SourceResidualFiniteLinearAlternatives'),
 ('SourceGammaOneFiniteProjectiveLinearResidual2320a','SourceGammaOneFiniteProjectiveLinearResidual')]
for version, module in pairs:
 source=s/(version+'.lean')
 assert (s/(version+'.exit')).read_text().strip()=='0'
 assert (s/(version+'.log')).stat().st_size==0
 t=source.read_text('utf-8')
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|set_option|nolint)\b',t)
 for old,new in pairs:t=re.sub(r'(?m)^import '+re.escape(old)+r'$', 'import '+new,t)
 out=s/(module+'.lean');assert not out.exists();out.write_text(t,encoding='utf-8')
 strip=lambda text:re.sub(r'(?m)^import .+\n','',text)
 assert strip(t)==strip(source.read_text('utf-8'))
 c['files'].append(dict(version=version,module=module,sourceSha256=sha(source),canonicalSha256=sha(out),mathematicalBodyIdentical=True))
 c['modules'].append(module)
 ns=re.search(r'(?m)^namespace (\S+)',t).group(1)
 for kind,name in re.findall(r'(?m)^(theorem|def) (\S+)',t):
  q=ns+'.'+name;assert q not in c['queries'];c['queries'].append(q)
  c['theorems' if kind=='theorem' else 'constructions'].append(q)
c['roots']=['Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.exists_gammaOne_original_finite_projective_linear_residual']
c['proofEdges'] += ['Dubon2026.SourceDickson.'+n for n in [
 'exists_finite_intermediateField_containing','exists_residual_finite_matrix_ambient',
 'exists_matrix_over_intermediateField','exists_residual_finite_descent',
 'scalar_factor_descends','subgroup_map_conjugate','linear_subfield_bounds_descend',
 'finite_linear_subfield_bounds_of_bounds']]+c['roots']
c['scope']='Original-form projective classification, actual linear subfield bounds and their descent into a finite coefficient extension; scratch only.'
c['routeAssessment'] += ' The finite coefficient-image comparison now places both embeddings and the conjugating matrix in one finite intermediate field and descends both linear bounds. Arithmetic small-image exclusion and the connection to the required original local deformation conditions remain open.'
c['precedingScratchReceipt']=str(s/'source-projective-linear-1-scratch-receipt.json')
c['precedingScratchReceiptSha256']=sha(s/'source-projective-linear-1-scratch-receipt.json')
out=s/'source-projective-finite-audit-config-2321.json';assert not out.exists();out.write_text(json.dumps(c,indent=2)+'\n',encoding='utf-8')
mods=[n for _,n in pairs]
arr=lambda xs:'#['+', '.join('`'+n for n in xs)+']'
t=(s/'SourceProjectiveLinearDeclarations2311.lean').read_text('utf-8').replace('import SourceGammaOneProjectiveLinearResidual','import SourceGammaOneFiniteProjectiveLinearResidual')
t=re.sub(r'let mods : Array Name := #\[.*\]','let mods : Array Name := '+arr(mods),t)
(s/'SourceProjectiveFiniteDeclarations2321.lean').write_text(t,encoding='utf-8')
t=(s/'SourceProjectiveLinearAudit2.lean').read_text('utf-8').replace('import SourceGammaOneProjectiveLinearResidual','import SourceGammaOneFiniteProjectiveLinearResidual')
t=re.sub(r'^#print axioms .+\n','',t,flags=re.M)
t=t.replace('open Lean\n','open Lean\n\n'+'\n'.join('#print axioms '+q for q in c['queries'][425:])+'\n',1)
t=re.sub(r'let modules : Array Name := #\[.*\]','let modules : Array Name := '+arr(mods),t)
t=re.sub(r'^#lint in .+\n','',t,flags=re.M)
t+='\n'.join('#lint in '+m for m in mods)+'\n'
t=t.replace('SOURCE PROJECTIVE LINEAR AXIOM AUDIT PASS','SOURCE PROJECTIVE FINITE AXIOM AUDIT PASS')
t=t.replace('explicit matrix conjugacy and small-image-or-linear-subfield bounds.','explicit matrix conjugacy and small-image-or-linear-subfield bounds over an actual finite coefficient extension.')
(s/'SourceProjectiveFiniteAudit1.lean').write_text(t,encoding='utf-8')
t=(s/'SourceProjectiveLinearDependencyAudit2.lean').read_text('utf-8').replace('import SourceGammaOneProjectiveLinearResidual','import SourceGammaOneFiniteProjectiveLinearResidual')
for key,values in [('roots',c['roots']),('localModules',c['modules']),('required',c['proofEdges'])]:
 t=re.sub('let '+key+r' : Array Name := #\[.*\]','let '+key+' : Array Name := '+arr(values),t)
t=t.replace('SOURCE PROJECTIVE LINEAR VALUE AUDIT PASS','SOURCE PROJECTIVE FINITE VALUE AUDIT PASS')
t=t.replace('native perfect-SL2 lifting are consumed.','native perfect-SL2 lifting and actual finite-coefficient descent are consumed.')
(s/'SourceProjectiveFiniteDependencyAudit1.lean').write_text(t,encoding='utf-8')
print(json.dumps(dict(modules=len(c['modules']),public=len(c['queries']),theorems=len(c['theorems']),constructions=len(c['constructions']),requiredProofEdges=len(c['proofEdges']),newAuditScopes=5)))

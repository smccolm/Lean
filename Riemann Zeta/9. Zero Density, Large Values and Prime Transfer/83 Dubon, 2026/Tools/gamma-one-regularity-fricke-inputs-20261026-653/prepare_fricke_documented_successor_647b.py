from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceFrickePeriodHomothety','SourceFrickeModularLattice','SourceFrickeTorsionTransformation','SourceFrickeFunctionTransformation']
docs={'smulPeriodPair':'The actual period pair scaled by a nonzero complex number.','smulLatticeEquiv':'Multiplication by the scaling factor identifies the two actual period lattices.','periodPairOfTau':'The actual period lattice with generators tau and one.','denomZ':'The lower-row denominator of the original integral modular matrix.','numZ':'The upper-row numerator of the original integral modular matrix.','frickeTorsionPt':'The representative of the specified torsion point in the actual period torus.','vecMulSL':'The original right row-vector action on torsion indices modulo the level.','frickeF':'The normalized Fricke function built from the actual Weierstrass value and modular forms.','vecMulSLEquiv':'The invertible original modular action on all torsion indices.','FrickeIdx':'The nonzero torsion indices used by the Fricke family.','frickeIdxPerm':'The original modular action restricted to nonzero torsion indices.'}
changes=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 for a in mods:s=s.replace('import '+a+'\n','import '+a+'V2\n')
 for n,doc in docs.items():
  s=re.sub(r'(?m)^((?:def|abbrev) '+re.escape(n)+r'\b)',lambda mm:'/-'+'- '+doc+' -/\n'+mm[1],s)
 s=s.replace('scoped instance (N :','/-- The finite nonzero torsion-index family at a positive level. -/\nscoped instance (N :')
 s=s.replace('Adapted from the fixed Apache-2.0 FLT source archived in reuse scope646;','Adapted from anthropics/fermats-last-theorem, commit\n6e837e75355538c7f80bab5b956861e86c4eacc2, under Apache License 2.0.\nThe exact source and license are retained in the project research archives;')
 g=p/(m+'V2.lean');assert not g.exists();g.write_text(s,encoding='utf-8')
 # Apart from import ownership and comments, every declaration and proof is unchanged.
 strip=lambda t:re.sub(r'\s+','',re.sub(r'(?m)^import .*\n','',re.sub(r'/\-.*?\-/','',t,flags=re.S)))
 assert strip(s)==strip(f.read_text(encoding='utf-8'))
 changes.append(dict(predecessor=str(f),predecessorSha256=hashlib.sha256(f.read_bytes()).hexdigest().upper(),successor=str(g),successorSha256=hashlib.sha256(g.read_bytes()).hexdigest().upper(),mathematicalBodiesIdentical=True))
out=p/'fricke-transformation-documented-successor-647b.json';assert not out.exists()
out.write_text(json.dumps(dict(reason='First exhaustive axiom audit passed but the 16-linter stage rejected twelve missing documentation strings. Preserve every predecessor source and failed audit; fresh V2 modules add only documentation and qualify successor imports. No proof, hypothesis or limit is changed.',files=changes,failedAudit='SourceFrickeTransformationAudit4.log'),indent=2)+'\n',encoding='utf-8')
s=(p/'prepare_fricke_transformation_audit_647.py').read_text(encoding='utf-8')
for m in mods:s=s.replace("'"+m+"'","'"+m+"V2'")
s=s.replace('source-fricke-transformation-4-audit-config','source-fricke-transformation-4b-audit-config').replace('SourceFrickeTransformationAudit4.lean','SourceFrickeTransformationAudit4b.lean').replace('SourceFrickeTransformationDependencyAudit4.lean','SourceFrickeTransformationDependencyAudit4b.lean')
s=s.replace("roots=[ns+n", "defs.append('Dubon2026.SourceFricke.instFintypeFrickeIdxOfNeZeroNat')\nseparate=['Dubon2026.SourceFricke.instFintypeFrickeIdxOfNeZeroNat']\nroots=[ns+n")
s=s.replace('required=ths+defs+extra','required=[n for n in ths+defs if n not in separate]+extra').replace('separatelyAxiomChecked=[]','separatelyAxiomChecked=separate')
f=p/'prepare_fricke_transformation_audit_647b.py';assert not f.exists();f.write_text(s,encoding='utf-8')
print('Prepared documented successors; failed audit and original modules preserved.')

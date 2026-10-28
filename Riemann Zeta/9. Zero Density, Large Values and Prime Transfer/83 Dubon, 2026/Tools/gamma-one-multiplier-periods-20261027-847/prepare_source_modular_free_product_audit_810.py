from pathlib import Path
import json,re,hashlib,ast
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceModularIrrationalAction','SourceModularPingPongSets','SourceModularFreeProductInjection','SourceModularProjectiveKernel','SourceModularFreeProduct']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 code=re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S);stack=[]
 for l in code.splitlines():
  if l.startswith('namespace '):stack.append(l[10:].strip())
  elif l.startswith('end '):stack.pop()
  else:
   hit=re.match(r'^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(theorem|def|abbrev)\s+([\w.]+)',l)
   if hit:(ths if hit[1]=='theorem' else defs).append('.'.join(stack+[hit[2]]))
queries=ths+defs
required=queries+['SpecialLinearGroup.SL2Z_generators','Matrix.SpecialLinearGroup.mem_center_iff','Monoid.CoprodI.lift_injective_of_ping_pong']
assert (len(mods),len(ths),len(defs),len(required))==(5,48,15,66)
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,proofEdges=required,roots=queries,separatelyAxiomChecked=[],scratchImportClosure=mods,separateReason='Actual generator-preserving projective modular free-product equivalence. Cusp-period correction and integral parabolic-character lifting remain.')
output('source-modular-free-product-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE MODULAR FREE PRODUCT').replace('Gamma One Exact Ramification','Modular Free Product')
output('SourceModularFreeProductAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8-sig');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',queries),('localModules',mods),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE MODULAR FREE PRODUCT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual projective modular free-product equivalence, its specified generator images, irrational Mobius action and native ping-pong, modular generation and scalar-center theorems. Only declaration values are traversed. Cusp-period correction, integral character lifting, analytic reciprocity and full arithmetic association remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceModularFreeProductDependencyAudit1.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=p/'gamma-one-integral-lift-presentation-route-805.json';old=json.loads(route.read_text(encoding='utf-8'))
rd=dict(chain=old['chain'],assumptionsToDischarge='The actual group SL2(Z)/center is explicitly isomorphic to C2 * C3, with the two standard generators mapping to S and S*T. The Mobius action, nonvanishing denominators, irrationality preservation, signed ping-pong domains, injectivity, generation and exact central kernel are derived. No group-presentation premise remains for the planned integral parabolic-character lift.',remaining='Promote and run assembled verification. Cusp-period correction and integral parabolic-character lifting, unitary exponential lifting, analytic reciprocity, original Gamma1 Picard/H1 and all-weight arithmetic association remain. 16/20; DUB-17--20 OPEN.',reuseChecked=old['reuseChecked']+[dict(path=str(route),sha256=sha(route))],shorterRoute=old['shorterRoute'])
output('source-modular-free-product-audit-route-810.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_closed_chain_periods_804.py').read_text(encoding='utf-8-sig')
for a,b in [('source-gamma-one-closed-chain-periods-1','source-modular-free-product-1'),('SourceGammaOneClosedChainPeriods','SourceModularFreeProduct'),('SOURCE GAMMA ONE CLOSED CHAIN PERIODS','SOURCE MODULAR FREE PRODUCT'),('gamma-one-closed-chain-audit-route-804.json','source-modular-free-product-audit-route-810.json'),('(5, 20, 24)','(5, 63, 66)'),('all 24 required','all 66 required'),('requiredProofValueEdges=24','requiredProofValueEdges=66'),('modules=5, queries=20','modules=5, queries=63'),('proofEdges=24','proofEdges=66')]:
 assert a in s,a
 s=s.replace(a,b)
ast.parse(s);output('record_source_modular_free_product_810.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8-sig').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceModularFreeProductScratchOwnership810.lean',s)
print(json.dumps(dict(modules=5,queries=63,edges=66)))

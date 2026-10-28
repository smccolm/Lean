from pathlib import Path
from datetime import datetime, timezone
import json, re, hashlib

p = Path(__file__).parent
names = [('SourceGammaOneFiniteOrderDischarge','1133b'), ('SourceGammaOneBinaryPeriodCharacters','1134a'), ('SourceGammaOneCoefficientHeckeCharacters','1135a'), ('SourceGammaOneBinaryParabolicH1','1136b'), ('SourceGammaOneBinaryTateH1','1137b'), ('SourceGammaOneBinaryTateHecke','1138b')]
mods = [n for n,a in names]
ths, defs = [], []
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
for n,a in names:
    t = (p/(n+'.lean')).read_text(encoding='utf-8')
    ns = re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
    ths += [ns+x for x in re.findall(r'^theorem (\w+)',t,re.M)]
    defs += [ns+x for x in re.findall(r'^(?:def|abbrev) (\w+)',t,re.M)]
    assert (p/(n+a+'.exit')).read_text().strip() == '0'
    assert (p/(n+a+'.log')).stat().st_size == 0
ns = 'Dubon2026.SourceFunctionField.GammaOne.'
roots = [ns+x for x in ['binaryTateH1Equiv_word','binaryTateH1Equiv','binaryTateH1Equiv_hom_apply','binaryParabolicH1_hecke_mem','originalGammaOne_finiteOrder_character_zero']]
separate = [ns+'binaryPeriodCharacterEquiv_apply']
edges = [x for x in ths+defs if x not in separate]
edges += ['Dubon2026.binaryHomogeneousMonomialBasis','Dubon2026.sourceGammaOnePrimeOperators','Dubon2026.sourceHeckeWord_intertwine_addHom','Dubon2026.SourceFiniteOrder.offDiag_eq_zero_or_natAbs_trace_le_one']
edges += [ns+x for x in ['arithmeticPeriodInclusion_isBaseChange','arithmeticPeriodInclusion_hecke','finiteLatticeCharacterEquiv','periodLatticeHecke_latticePeriod']]
prior = json.loads((p/'source-gamma-one-finite-tate-h1-1b-audit-config.json').read_text())
cfg = dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(mods+prior['localModules'])),separatelyAxiomChecked=separate,compileEvidence={n:n+a for n,a in names})
def write(n,t):
    f=p/n
    assert not f.exists(), f
    f.write_text(t,encoding='utf-8')
stem = 'source-gamma-one-binary-tate-h1-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+n for n in mods)+'\nimport Mathlib.Tactic\n'
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneFiniteTateH1'
new='SourceGammaOneBinaryTateH1'
for suffix,newSuffix in [('Audit1','Audit1'),('DependencyAudit1b','DependencyAudit1'),('ScratchOwnership1132','ScratchOwnership1139')]:
    t=(p/(old+suffix+'.lean')).read_text(encoding='utf-8')
    t=imports+t[t.index('\nopen Lean'):]
    if suffix=='Audit1':
        t=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),t,count=1)
        for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
            t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
        t=re.sub(r'#lint in [^\n]+\n','',t).rstrip()+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
    elif suffix=='DependencyAudit1b':
        for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
            t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
        t=t.replace('actual arithmetic finite Tate dual/native H1 equivalence and Hecke transpose VALUE closures. Parabolic and finite-order vanishing define the explicit H1 target. Full/parabolic passage, homogeneous coefficients, diamond and Galois realization remain','actual original homogeneous-coefficient arithmetic Tate dual/parabolic H1 equivalence and original whole-word Hecke VALUE closures. Actual levels discharge finite-order vanishing. Full/parabolic passage, diamonds and Galois realization remain')
    else:
        t=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),t)
    t=t.replace('GAMMA ONE FINITE TATE H1','GAMMA ONE BINARY TATE H1').replace('Gamma One Finite Tate H1','Gamma One Binary Tate H1')
    write(new+newSuffix+'.lean',t)
routes=['source-gamma-one-finite-order-reuse-1133.json','source-gamma-one-binary-period-reuse-1134.json','source-gamma-one-finite-tate-h1-1b-scratch-receipt.json']
reuse=[dict(path=str(p/f),sha256=sha(p/f)) for f in routes]
for f in routes[:2]:
    reuse+=json.loads((p/f).read_text())['reuseChecked']
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of the original finite Gamma1 homogeneous-coefficient Hecke character -> full/parabolic and arithmetic Tate dual comparison -> original homogeneous coefficients and every original Hecke word.',reuseChecked=reuse,
shorterRoute='The existing finite-order integral trace bound and literal Gamma1 congruences discharge finite-order vanishing at the actual Q*(p^(n+1))^2 levels. The already proved original homogeneous monomial basis reduces lattice-factor existence to the existing scalar equivalence. Native IsBaseChange lifts the original coefficient-valued dual directly to the actual arithmetic Tate module. The exact native coefficient Hecke formula and actual Picard Hecke period inclusion identify independently defined arithmetic dual operators, then the existing integral-word intertwining theorem proves all original words. No new group torsion-freeness theory, polynomial basis, tensor basis or scalar replacement is introduced.',
assumptionsToDischarge=['Parabolic vanishing already implies finite-order vanishing at the original levels for p>3.','The original homogeneous-coefficient parabolic H1 at Q*(p^(n+1))^2 is equivalent to the original integral-period lattice dual.','The actual arithmetic Picard Tate module dual with the original homogeneous coefficient module is equivalent to this literal native parabolic H1.','The actual arithmetic Picard Hecke dual followed by the original homogeneous matrix action intertwines sourceGammaOnePrimeOperators and every integral free-algebra word.'],
remaining='The original constructed character acts on full H1; its passage to the parabolic space is not yet proved. Diamonds, coefficient-field/Frobenius/inertia realization, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. A finite-character comparison is not a characteristic-zero lift. DUB-17--20 OPEN; 16/20; all twenty acceptance gates unchanged.',
preservedFailures='1133a generic-matrix trace rewrite, 1136a field-notation line break, 1137a explicit-map base-change extensionality, 1138a polynomial extensionality depth. Failed source and diagnostics preserved before repair. No mathematical statement or proof limit changed.')
write('source-gamma-one-binary-tate-h1-audit-route-1139.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_finite_tate_h1_1132b.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-finite-tate-h1-1b',stem),('source-gamma-one-finite-tate-h1-audit-route-1132b','source-gamma-one-binary-tate-h1-audit-route-1139'),(old,new),('ScratchOwnership1132','ScratchOwnership1139'),('DependencyAudit1b','DependencyAudit1'),('GAMMA ONE FINITE TATE H1','GAMMA ONE BINARY TATE H1')]:
    t=t.replace(a,b)
t=t.replace('(7, 32, 38)',str((len(mods),len(ths+defs),len(edges))))
t=t.replace('all 38 required',f'all {len(edges)} required').replace('requiredProofValueEdges=38',f'requiredProofValueEdges={len(edges)}').replace('proofEdges=38',f'proofEdges={len(edges)}').replace('queries=32',f'queries={len(ths+defs)}')
t=t.replace('== 7',f'== {len(mods)}').replace('linterScopes=7',f'linterScopes={len(mods)}').replace('modules=7',f'modules={len(mods)}')
write('record_source_gamma_one_binary_tate_h1_1139.py',t)
t=(p/'audit_gamma_one_finite_tate_h1_1132b.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1132','ScratchOwnership1139'),('DependencyAudit1b','DependencyAudit1'),('record_source_gamma_one_finite_tate_h1_1132b','record_source_gamma_one_binary_tate_h1_1139')]:
    t=t.replace(a,b)
t=t.replace("$names=@('","$names=@('"+new+"Audit1','",1)
write('audit_gamma_one_binary_tate_h1_1139.ps1',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))

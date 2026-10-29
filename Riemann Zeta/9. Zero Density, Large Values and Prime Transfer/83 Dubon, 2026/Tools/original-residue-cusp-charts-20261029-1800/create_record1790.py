from pathlib import Path
import ast,hashlib,json,re
D=Path('E:/Lean/.tmp/dubon83')
rows=json.loads((D/'determinant-ordinary-metadata-entries.json').read_text(encoding='utf8'))
assert len(rows)==4
mods=[dict(scope=r[0],name=r[1],mathematics=r[7],boundary=r[10],status='D-only UNCOMPILED; no proof claim.',draftSha256=hashlib.sha256((D/(r[1]+'.lean')).read_bytes()).hexdigest()) for r in rows]
route=dict(date='2026-10-10',status='Four D-only UNCOMPILED drafts1787-1790; metadata and static review ready; no proof claim.',modules=mods,expectedScope=[1790,1157,7378],source='https://pub.math.leidenuniv.nl/~smitbde/papers/bu-fermat-1995-desmit-lenstra.pdf',sourceSection='6.1-6.2',arithmeticAssembly=mods[-1].copy(),scopeLimit='The literal simultaneous determinant and ordinary quotient classifies the genuine original arithmetic classes. Residual absolute irreducibility, residue characteristic, determinant compatibility and true residual ordinarity remain explicit. Finite-flat, p-adic Hodge conditions, full Selmer, modular association and patching remain open.',next='First compile and verify ordinary quotient1778-1786, then compile and verify these four combined-condition drafts. Source gates17-20 remain open.')
(D/'actual-arithmetic-determinant-ordinary-route-20261010.json').write_text(json.dumps(route,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
t=(D/'record1786combined.py').read_text(encoding='utf8')
t=t.replace('batches = list(range(1778, 1787))','batches = list(range(1787, 1791))')
t=re.sub(r'^keys = .+$','keys = '+repr(['actual'+r[1]+'Implementation20261010' for r in rows]),t,flags=re.M)
t=t.replace("checks[0][1] == '7369'","checks[0][1] == '7378'").replace("'paper1786-console.log'","'paper1790-console.log'")
t=t.replace("len(c['productionModules']) == 1786","len(c['productionModules']) == 1790").replace('len(modules) == len(set(modules)) == 9','len(modules) == len(set(modules)) == 4').replace('assembled 1786-module','assembled 1790-module')
t=t.replace('The current verified scope has 1777 production modules, 1144 exact consumers, 7,347 explicit audit registrations','The current verified scope has 1786 production modules, 1153 exact consumers, 7,369 explicit audit registrations')
t=t.replace("f'The current verified scope has 1786 production modules, 1153 exact consumers, 7,369 explicit audit registrations","f'The current verified scope has 1790 production modules, 1157 exact consumers, 7,378 explicit audit registrations")
t=t.replace('scope:1786 production modules;1153 exact consumers;7369 explicit registrations','scope:1790 production modules;1157 exact consumers;7378 explicit registrations').replace('assembled actual arithmetic ordinary unframed quotient classification','assembled actual arithmetic fixed-determinant ordinary unframed quotient classification').replace('assembled scope1786','assembled scope1790')
t=t.replace('### Actual arithmetic ordinary unframed quotient classification','### Actual arithmetic fixed-determinant ordinary unframed quotient classification').replace('Nine production increments','Four production increments').replace('scope 1786: 1153 exact consumers, 7,369 explicit registrations','scope 1790: 1157 exact consumers, 7,378 explicit registrations').replace('all nine increments','all four increments')
a=t.index('The actual residual inertia-invariant module');b=t.index('The foundation verifier observed',a)
body='''The combined condition is the conjunction of the actual original whole determinant predicate and the genuine ordinary invariant rank-one direct-summand predicate. Their coefficient criterion is annihilation of the literal sum of the original determinant and ordinary ideals. Both conditions concern the same original matrices and the same coefficient map.

Original residual determinant compatibility and actual residual ordinarity place that sum in the true coefficient maximal ideal. This derives locality, Noetherianity, the own maximal-adic quotient topology and completeness. The quotient coefficient fiber then classifies exactly the original classes satisfying both conditions, with the original matrix evaluation formula.

The arithmetic consumer starts from the actual rational arithmetic group, original residual representation and actual inertia at the specified height-one prime. The constructed trace universal ring supplies the whole original classification, and the actual residual invariant module supplies the nonidentity inertia element. The universal classification, chosen element and combined quotient ring properties are all derived. Residual absolute irreducibility, residue characteristic, determinant compatibility and genuine residual ordinarity remain explicit arithmetic inputs.

[de Smit–Lenstra, Sections6.1-6.2](https://pub.math.leidenuniv.nl/~smitbde/papers/bu-fermat-1995-desmit-lenstra.pdf) supplies the source context for imposing these genuine conditions on original deformation classes. Finite-flat and p-adic Hodge local conditions, full Selmer theory, modular Galois association, patching, higher symmetric automorphy/continuation, unconditional Deligne, non-CM Sato-Tate and the final modular application remain open. DUB-01-16 remain accepted; DUB-17-20 remain OPEN.

'''
t=t[:a]+body+t[b:]
t=t.replace('Tools/actual-arithmetic-ordinary-quotient-route-20261010.json','Tools/actual-arithmetic-determinant-ordinary-route-20261010.json').replace('Combined1786 verification recorded','Combined1790 verification recorded')
ast.parse(t);(D/'record1790combined.py').write_text(t,encoding='utf8')
t=(D/'finalize1786.py').read_text(encoding='utf8').replace('1786','1790').replace('1153','1157').replace('7369','7378')
t=t.replace('All nine modules1778-1790','All four modules1787-1790').replace('All nine promoted','All four promoted').replace('actual-arithmetic-ordinary-quotient-route','actual-arithmetic-determinant-ordinary-route').replace('futureOrdinaryQuotientDrafts','futureDeterminantOrdinaryDrafts')
t=re.sub(r"^v\['semanticBoundary'\]=.+$", "v['semanticBoundary']="+repr(route['scopeLimit']),t,flags=re.M)
t=re.sub(r"^v\['scopeLimit'\]=.+$", "v['scopeLimit']="+repr(route['scopeLimit']),t,flags=re.M)
t=re.sub(r"^v\['next'\]=.+$", "v['next']="+repr('Construct the remaining finite-flat and p-adic Hodge local conditions, full Selmer comparison, modular association and patching with actual source objects.'),t,flags=re.M)
t=re.sub(r"^s\['futureArithmeticOrdinaryAssembly'\].+\n",'',t,flags=re.M)
ast.parse(t);(D/'finalize1790.py').write_text(t,encoding='utf8')
print('Combined1790 receipt and finalizer READY NOT EXECUTED; four drafts1787-1790 remain UNCOMPILED.')

from pathlib import Path
import ast,json,re
D=Path('E:/Lean/.tmp/dubon83')
rows=json.loads((D/'ordinary-quotient-metadata-entries.json').read_text(encoding='utf8'))+[json.loads((D/'arithmetic-ordinary-metadata-entry.json').read_text(encoding='utf8'))]
assert len(rows)==9
drafts=json.loads((D/'ordinary-quotient-next-drafts-20261010.json').read_text(encoding='utf8'))
assembly=json.loads((D/'arithmetic-ordinary-assembly-draft-20261010.json').read_text(encoding='utf8'))
mods=[]
for row in rows:
 review=json.loads((D/f'primary-review{row[0]}.json').read_text(encoding='utf8'))
 import hashlib
 mods.append(dict(scope=row[0],name=row[1],mathematics=row[7],boundary=row[10],status='D-only UNCOMPILED; no proof claim.',draftSha256=hashlib.sha256((D/(row[1]+'.lean')).read_bytes()).hexdigest()))
route=dict(date='2026-10-10',status='Nine D-only UNCOMPILED drafts1778-1786; metadata and static review ready; no proof claim.',modules=mods,expectedScope=[1786,1153,7369],source='https://pub.math.leidenuniv.nl/~smitbde/papers/bu-fermat-1995-desmit-lenstra.pdf',sourceSection='6.2',arithmeticAssembly=assembly,scopeLimit='Ordinary invariant direct-summand geometry, coefficient ideal and original arithmetic class classification. Actual residual absolute irreducibility, residue characteristic and residual ordinarity remain explicit. Finite-flat and p-adic Hodge conditions, Selmer theory, modular association and patching remain open.',next='First verify the ordinary relation criterion1765-1777; then compile and verify these nine drafts including the actual arithmetic consumer. Source gates17-20 remain open.')
(D/'actual-arithmetic-ordinary-quotient-route-20261010.json').write_text(json.dumps(route,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
t=(D/'record1777combined.py').read_text(encoding='utf8')
t=t.replace('batches = list(range(1765, 1778))','batches = list(range(1778, 1787))')
t=re.sub(r'^keys = .+$','keys = '+repr(['actual'+r[1]+'Implementation20261010' for r in rows]),t,flags=re.M)
t=t.replace("checks[0][1] == '7347'","checks[0][1] == '7369'")
t=t.replace("'paper1777-console.log'","'paper1786-console.log'")
t=t.replace("len(c['productionModules']) == 1777","len(c['productionModules']) == 1786")
t=t.replace('len(modules) == len(set(modules)) == 13','len(modules) == len(set(modules)) == 9')
t=t.replace('assembled 1777-module','assembled 1786-module')
t=t.replace('The current verified scope has 1764 production modules, 1131 exact consumers, 7,318 explicit audit registrations','The current verified scope has 1777 production modules, 1144 exact consumers, 7,347 explicit audit registrations')
t=t.replace("f'The current verified scope has 1777 production modules, 1144 exact consumers, 7,347 explicit audit registrations","f'The current verified scope has 1786 production modules, 1153 exact consumers, 7,369 explicit audit registrations")
t=t.replace('scope:1777 production modules;1144 exact consumers;7347 explicit registrations','scope:1786 production modules;1153 exact consumers;7369 explicit registrations')
t=t.replace('assembled actual ordinary invariant direct-summand criterion','assembled actual arithmetic ordinary unframed quotient classification')
t=t.replace('assembled scope1777','assembled scope1786')
t=t.replace('### Actual ordinary invariant direct-summand criterion','### Actual arithmetic ordinary unframed quotient classification')
t=t.replace('Thirteen production increments','Nine production increments').replace('scope 1777: 1144 exact consumers, 7,347 explicit registrations','scope 1786: 1153 exact consumers, 7,369 explicit registrations').replace('all thirteen increments','all nine increments')
a=t.index('The new public criterion compares');b=t.index('The foundation verifier observed',a)
body='''The actual residual inertia-invariant module supplies an original nonidentity inertia element by a dimension argument. The ordinary ideal is the span of all entries of the actual operators formed from that same element and original representation. Its precise coefficient-change law identifies ideal annihilation with the genuine invariant module being free of rank one and a direct summand. Actual basis change preserves this condition, so it descends to the existing original unframed classes.

Residual ordinary data places the literal ideal in the true maximal ideal. Quotient locality, Noetherianity, own maximal-adic topology and completeness are derived. The original residue-preserving coefficient fiber then identifies quotient coefficient maps with the actual ordinary classes, with an exact evaluation formula for the same original universal matrices.

The arithmetic consumer uses the actual rational arithmetic Galois group, the genuine inertia subgroup at the original height-one prime and the constructed arithmetic trace universal ring. It derives the whole class bijection from the existing arithmetic theorem and derives the ordinary quotient structure from the residual invariant module. The nontrivial inertia element, whole universal classification and quotient ring properties are not extra public assumptions. Original residual absolute irreducibility, residue characteristic and actual residual ordinarity remain explicit arithmetic inputs.

[de Smit–Lenstra, Section6.2](https://pub.math.leidenuniv.nl/~smitbde/papers/bu-fermat-1995-desmit-lenstra.pdf) provides the source context. This is the genuine ordinary condition for the specified original arithmetic residual representation. Finite-flat and p-adic Hodge local conditions, full Selmer theory, modular Galois association, patching, higher symmetric automorphy/continuation, unconditional Deligne, non-CM Sato-Tate and the final modular application remain open. DUB-01-16 remain accepted; DUB-17-20 remain OPEN.

'''
t=t[:a]+body+t[b:]
t=t.replace('Tools/actual-ordinary-invariant-line-route-20261010.json','Tools/actual-arithmetic-ordinary-quotient-route-20261010.json')
t=t.replace('Combined1777 verification recorded','Combined1786 verification recorded')
ast.parse(t);(D/'record1786combined.py').write_text(t,encoding='utf8')
t=(D/'finalize1777.py').read_text(encoding='utf8')
t=t.replace('1777','1786').replace('1144','1153').replace('7347','7369')
t=t.replace('All thirteen modules1765-1786','All nine modules1778-1786').replace('All thirteen promoted','All nine promoted')
t=t.replace('actual-ordinary-invariant-line-route','actual-arithmetic-ordinary-quotient-route').replace('futureOrdinaryInvariantDrafts','futureOrdinaryQuotientDrafts')
t=re.sub(r"^v\['semanticBoundary'\]=.+$", "v['semanticBoundary']="+repr(route['scopeLimit']),t,flags=re.M)
t=re.sub(r"^v\['scopeLimit'\]=.+$", "v['scopeLimit']="+repr(route['scopeLimit']),t,flags=re.M)
t=re.sub(r"^v\['next'\]=.+$", "v['next']="+repr('Construct the remaining finite-flat and p-adic Hodge local conditions, full Selmer comparison, modular association and patching. Ordinary/determinant combinations must consume the actual coefficient ideals and class conditions.'),t,flags=re.M)
t=t.replace('route_verified=v',"v['arithmeticAssembly']['status']='Full assembled verification PASS, actual exits0 consumed and zero diagnostics.'\nroute_verified=v")
t=t.replace("s['futureOrdinaryQuotientDrafts']['status']=", "s['futureArithmeticOrdinaryAssembly']['status']='Promoted and fully verified through1786; combined receipt EXECUTED.'\ns['futureOrdinaryQuotientDrafts']['status']=")
ast.parse(t);(D/'finalize1786.py').write_text(t,encoding='utf8')
print('Combined1786 receipt and finalizer READY NOT EXECUTED; all nine drafts1778-1786 remain UNCOMPILED.')

from pathlib import Path
import ast,hashlib,json,re
D=Path('E:/Lean/.tmp/dubon83')
rows=json.loads((D/'hopf-points-metadata-entries.json').read_text(encoding='utf8'))+json.loads((D/'point-closure-metadata-entries.json').read_text(encoding='utf8'))
assert len(rows)==6
mods=[dict(scope=r[0],name=r[1],mathematics=r[7],boundary=r[10],status='D-only UNCOMPILED; no proof claim.',draftSha256=hashlib.sha256((D/(r[1]+'.lean')).read_bytes()).hexdigest()) for r in rows]
boundary='Actual Hopf point groups, coefficient actions, finite-free point bounds and coordinate vanishing-ideal properties only. Comultiplication descent, a Hopf quotient, Galois-stable generic-fiber comparison, products/subquotients as finite-flat group schemes, original arithmetic realization and the finite-flat deformation quotient remain open. No modular source gate closes.'
route=dict(date='2026-10-10',status='Six D-only UNCOMPILED drafts1791-1796; metadata ready; no proof claim.',modules=mods,expectedScope=[1796,1163,7399],source='https://pub.math.leidenuniv.nl/~smitbde/papers/bu-fermat-1995-desmit-lenstra.pdf',sourceSection='6.3',scopeLimit=boundary,next='First compile and fully verify the arithmetic fixed-determinant ordinary quotient through1790, then compile these six genuine Hopf-point and coordinate-closure steps.')
(D/'actual-hopf-points-coordinate-closure-route-20261010.json').write_text(json.dumps(route,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
mapping={'1790':'1796','1786':'1790','1157':'1163','1153':'1157','7378':'7399','7369':'7378','7,378':'7,399','7,369':'7,378'}
def convert(t):
 pins=[]
 def stash(m):pins.append(m[0]);return f'__PIN_{len(pins)-1}__'
 t=re.sub(r'\b[a-f0-9]{40,64}\b',stash,t)
 t=re.sub('|'.join(map(re.escape,sorted(mapping,key=len,reverse=True))),lambda m:mapping[m[0]],t)
 for i,p in enumerate(pins):t=t.replace(f'__PIN_{i}__',p)
 return t.replace('actual-arithmetic-determinant-ordinary-route','actual-hopf-points-coordinate-closure-route')
t=convert((D/'record1790combined.py').read_text(encoding='utf8'))
t=t.replace('batches = list(range(1787, 1791))','batches = list(range(1791, 1797))')
t=re.sub(r'^keys = .+$','keys = '+repr(['actual'+r[1]+'Implementation20261010' for r in rows]),t,flags=re.M)
t=t.replace('len(modules) == len(set(modules)) == 4','len(modules) == len(set(modules)) == 6')
t=t.replace('actual arithmetic fixed-determinant ordinary unframed quotient classification','actual Hopf points and coordinate-closure construction')
t=t.replace('Actual arithmetic fixed-determinant ordinary unframed quotient classification','Actual Hopf points and coordinate-closure construction')
t=t.replace('Four production increments','Six production increments').replace('all four increments','all six increments')
a=t.index('The combined condition is the conjunction');b=t.index('The foundation verifier observed',a)
body='''The same original commutative Hopf algebra supplies its actual algebra-valued point group. The antipode law proves the inverse under existing convolution, and genuine coefficient automorphisms act on the original coordinate values. Existing finite-free algebra-hom results give finiteness and the coordinate-rank bound for the real field-valued points.

The actual simultaneous evaluation kernel defines the point vanishing ideal. Its quotient embeds into the product of actual point-value rings. Original subgroup inversion and the identity give antipode and counit stability. Over a principal ideal domain and a faithful field algebra, this injection derives torsion-freeness; finite generation then derives finite freeness of the coordinate quotient.

These are coordinate prerequisites for [de Smit–Lenstra, Section6.3](https://pub.math.leidenuniv.nl/~smitbde/papers/bu-fermat-1995-desmit-lenstra.pdf). Comultiplication descent, a Hopf quotient, actual Galois-stable geometric-point comparison, closure under finite-flat group-scheme products/subquotients and an original finite-flat deformation quotient remain unproved. In particular, finite freeness of the coordinate quotient does not alone identify its geometric points with the original subgroup. [Conrad, Definition1.1.1](https://math.stanford.edu/~conrad/papers/ramdef.pdf) requires genuine generic-fiber realization at every finite maximal-ideal quotient; these helpers do not supply that conclusion.

Full Selmer theory, modular Galois association, patching, higher symmetric automorphy/continuation, unconditional Deligne, non-CM Sato-Tate and the final modular application remain open. DUB-01-16 remain accepted; DUB-17-20 remain OPEN.

'''
t=t[:a]+body+t[b:];ast.parse(t);(D/'record1796combined.py').write_text(t,encoding='utf8')
t=convert((D/'finalize1790.py').read_text(encoding='utf8'))
t=t.replace('All four modules1787-1796','All six modules1791-1796')
t=re.sub(r"^v\['semanticBoundary'\]=.+$","v['semanticBoundary']="+repr(boundary),t,flags=re.M)
t=re.sub(r"^v\['scopeLimit'\]=.+$","v['scopeLimit']="+repr(boundary),t,flags=re.M)
t=re.sub(r"^v\['next'\]=.+$","v['next']="+repr('Prove actual comultiplication descent and the Galois-stable geometric-point identification, preserving all source generic-fiber and finite-quotient requirements.'),t,flags=re.M)
t=re.sub(r"^v\['arithmeticAssembly'\].+\n",'',t,flags=re.M)
t=t.replace("s['futureDeterminantOrdinaryDrafts']['status']='All four promoted and fully verified through1796; combined receipt EXECUTED.'","s['futureFiniteFlatPointDrafts']['status']='Three point modules promoted and fully verified through1796; combined receipt EXECUTED.'\ns['futureFiniteFlatClosureDrafts']['status']='Three coordinate-closure modules promoted and fully verified through1796; combined receipt EXECUTED.'")
ast.parse(t);(D/'finalize1796.py').write_text(t,encoding='utf8')
for n in ['record1796combined.py','finalize1796.py']:
 assert 'actual-arithmetic-determinant-ordinary-route' not in (D/n).read_text(encoding='utf8')
print('Combined1796 record/finalizer READY NOT EXECUTED; six uncompiled drafts, expected1796/1163/7399.')

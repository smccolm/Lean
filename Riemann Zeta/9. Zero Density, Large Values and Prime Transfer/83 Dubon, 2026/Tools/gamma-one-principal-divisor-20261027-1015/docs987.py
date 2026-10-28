from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
d=Path('E:/Lean/.tmp/dubon83')
modules=json.loads((d/'modules987.json').read_text(encoding='utf8'))
math='Eight further production modules prove that literal substitution by the universal matrix has polynomial coefficients in the original matrix entries. The actual coefficient functionals separate the original finite-dimensional homogeneous space, so every linear functional of every matrix orbit is one such polynomial. Consequently every actual coefficient of the degree-2m determinant twist det^-m is a polynomial divided by det(g)^m. The original finite raising basis, its distinct weights and its nonzero lowering coefficients prove irreducibility under the original three infinitesimals. Actual norm derivatives of original group curves then carry every genuine group-invariant subspace into that Lie action; finite dimensionality supplies closedness, so the genuine determinant-twisted GL2 representation is irreducible. The original nonzero vector X0^(2m) spans a line preserved by every actual upper-triangular matrix, and the original diagonal torus acts on it by u^m v^(-m). Its integral highest weight (m,-m) is dominant, and its rho-shifted entries (m+1,-m) have positive difference 2m+1. The source even-weight range supplies m. A single public theorem combines actual algebraic coefficients, original group irreducibility, the genuine highest vector and regular shifted weight with equality of the entire full GL2 central character on every original real K-finite cusp vector and every vector of this actual finite model.'
remaining='The actual finite algebraic model and its regular infinitesimal-character comparison on the original real K-finite component are proved. Source-level identification of the full adelic automorphic representation, including its irreducibility, still requires proofs. All higher symmetric continuations, unconditional Deligne, non-CM Sato–Tate and the final modular application remain open. DUB-01–16 remain accepted; DUB-17–20 remain OPEN.'
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Original irreducible algebraic model and regular character: '+math+' Four exact consumers expand registered scope to 987 production modules, 414 exact consumers and 4,479 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
section='### Original irreducible algebraic model and regular character — 8 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'
for n in modules:section+=f'- [{n}](Extension/Dubon2026/{n}.lean).\n'
(d/'status987.txt').write_text(status+'\n',encoding='utf8');(d/'section987.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t
 pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8')
old='  KC --> A';assert old in t
t=t.replace(old,'''  KC --> RA["Proved actual irreducible algebraic determinant twist, highest weight and regular full character comparison"]
  RA --> A''',1)
t=t.replace('OPEN DUB-17: regular-algebraic representation identification','OPEN DUB-17: full source automorphic representation identification',1)
f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'))
j['adelicIrreducibleAlgebraicModelImplementation20261008']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 987 production modules, 414 exact consumers and 4479 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8')
 old='Algebraicity and regular-highest-weight identification of the actual finite model, and full source-level automorphic identification, remain open.'
 assert old in t
 new='The actual finite determinant twist is now proved algebraic and irreducible, with the original highest weight and regular shifted character agreeing with the original real K-finite cusp component (focused compilation passed; expanded verification pending). Full source-level automorphic identification and full adelic irreducibility remain open.'
 t=t.replace(old,new,1);q.write_text(t,encoding='utf8')
print('All fifteen status documents, active architecture, source mappings, research metadata and both overviews synchronized to the precise 987-module pending scope.')

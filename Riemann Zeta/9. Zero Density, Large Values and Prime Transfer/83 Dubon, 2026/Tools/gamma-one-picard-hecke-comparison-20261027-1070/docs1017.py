from pathlib import Path
import json
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
d=Path('E:/Lean/.tmp/dubon83')
math='Twenty-one further production modules construct the actual finite-level orthogonal projector in the original full adelic Hilbert space. Compactness and an original open stabilizer make each algebraic level orbit finite, so this projector preserves the actual finite-adelic algebraic span. Its fixed-level part is therefore dense in the full lowest-weight fixed-level space. Each literal finite-adelic translate is proved to restrict to its original rational slash function with the exact determinant-root factor root^(2-k) required by the pinned slash convention. Finite combinations are holomorphic and vanish at every arithmetic cusp. Faithfulness of the original Hilbert embedding transfers level invariance to the original adelic functions; rational diagonal invariance then proves every original Gamma0 slash equation. This constructs genuine cusp forms at the original level. Proved strong approximation, scalar normalization and rational sign correction identify each such original adelic function everywhere with the full canonical lift of its unique reconstructed classical cusp form, including the negative real component. The actual real restriction is consequently faithful on the fixed-level algebraic core. The already proved finite dimensionality of the genuine classical cusp space makes this actual core finite dimensional and hence closed in the original Hilbert norm. Combining closedness with the proved density identifies the entire lowest-weight fixed-level Hilbert space with its original finite-adelic algebraic core. Every such completed Hilbert vector thus comes from a unique genuine original-level classical cusp lift. No classical reconstruction, finite-dimensionality or full adelic irreducibility premise is assumed.'
remaining='Fixed-level classical reconstruction of the full original lowest-weight Hilbert space is proved. The actual finite-adelic Hecke compatibility and newspace-preservation bridge needed for primitive multiplicity one remain open. Source-level identification of the full adelic automorphic representation, including its irreducibility, still requires proofs. All higher symmetric continuations, unconditional Deligne, non-CM Sato–Tate and the final modular application remain open. DUB-01–16 remain accepted; DUB-17–20 remain OPEN.'
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status='Original full fixed-level classical reconstruction: '+math+' Six exact consumers expand registered scope to 1017 production modules, 424 exact consumers and 4,566 explicit audit registrations. '+pending+' '+remaining+' Earlier milestone paragraphs retain their historical scope.'
modules=json.loads((d/'modules1017.json').read_text(encoding='utf8'))
section='### Original full fixed-level classical reconstruction — 8 October 2026\n\n'+math+'\n\n'+remaining+'\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in modules)
(d/'status1017.txt').write_text(status+'\n',encoding='utf8');(d/'section1017.txt').write_text(section,encoding='utf8')
s=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
for name in s['statusDocuments']:
 f=p/name;t=f.read_text(encoding='utf8');assert status not in t
 pos=t.index('\n');f.write_text(t[:pos+1]+'\n'+status+'\n\n'+t[pos+1:],encoding='utf8')
for name in ['Dubon Checklist.md','Dubon Crosswalk.md','Dubon Research Agenda.md','Dubon Source Contract.md']:
 with (p/name).open('a',encoding='utf8') as out:out.write('\n'+section)
f=p/'Dubon Architecture.md';t=f.read_text(encoding='utf8');old='  FW --> A';assert old in t
t=t.replace(old,'''  FW --> LP["Proved actual compact level projector preserves the finite-adelic algebraic core"]
  LP --> CD["Proved fixed-level core density and original rational slash reconstruction"]
  CD --> FC["Proved full lowest-weight fixed-level Hilbert vectors are unique original-level classical cusp lifts"]
  FC --> HB["OPEN DUB-17: actual finite-adelic Hecke compatibility and newspace preservation"]
  HB --> A''',1);f.write_text(t,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'))
j['adelicFixedLowestClassicalImplementation20261008']={'status':'Focused production compilation passed; expanded verification pending. DUB-17 remains OPEN.','mathematics':section,'productionModules':modules,'validation':'Registered 1017 production modules, 424 exact consumers and 4566 explicit audit declarations; expanded verification pending.','sourceGate':'DUB-17','remaining':remaining}
f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
for q in [p.parent/'README.md',p.parents[1]/'README.md']:
 t=q.read_text(encoding='utf8');old='The fixed-level classical reconstruction and multiplicity-one bridge, full source-level automorphic identification and full adelic irreducibility remain open.';assert old in t
 new='The entire original lowest-weight fixed-level Hilbert space is now reconstructed as genuine original-level classical cusp lifts, using the actual level projector, rational slash normalization, full adelic function equality and finite-dimensional closedness (focused compilation passed; expanded verification pending). Actual finite-adelic Hecke compatibility and newspace preservation for multiplicity one, full source-level automorphic identification and full adelic irreducibility remain open.'
 q.write_text(t.replace(old,new,1),encoding='utf8')
print('Synchronized all 15 status documents, architecture, source mappings, metadata and both overviews to 1017-module pending scope.')

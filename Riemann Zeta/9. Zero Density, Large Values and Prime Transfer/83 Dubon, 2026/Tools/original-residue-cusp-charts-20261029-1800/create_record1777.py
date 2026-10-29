from pathlib import Path
import ast,json,re
D=Path('E:/Lean/.tmp/dubon83')
rows=json.loads((D/'ordinary-line-metadata-entries.json').read_text(encoding='utf8'))
assert len(rows)==13
t=(D/'record1764combined.py').read_text(encoding='utf8')
t=t.replace('batches = list(range(1757, 1765))','batches = list(range(1765, 1778))')
t=re.sub(r'^keys = .+$','keys = '+repr(['actual'+r[1]+'Implementation20261010' for r in rows]),t,flags=re.M)
t=t.replace("checks[0][1] == '7318'","checks[0][1] == '7347'")
t=t.replace("'paper1764-console.log'","'paper1777-console.log'")
t=t.replace("len(c['productionModules']) == 1764","len(c['productionModules']) == 1777")
t=t.replace('len(modules) == len(set(modules)) == 8','len(modules) == len(set(modules)) == 13')
t=t.replace('assembled 1764-module','assembled 1777-module')
t=t.replace('The current verified scope has 1756 production modules, 1123 exact consumers, 7,296 explicit audit registrations','The current verified scope has 1764 production modules, 1131 exact consumers, 7,318 explicit audit registrations')
t=t.replace("f'The current verified scope has 1764 production modules, 1131 exact consumers, 7,318 explicit audit registrations","f'The current verified scope has 1777 production modules, 1144 exact consumers, 7,347 explicit audit registrations")
t=t.replace('scope:1764 production modules;1131 exact consumers;7318 explicit registrations','scope:1777 production modules;1144 exact consumers;7347 explicit registrations')
t=t.replace('assembled actual original arithmetic determinant and inertia unframed quotient construction','assembled actual ordinary invariant direct-summand criterion')
t=t.replace('assembled scope1764','assembled scope1777')
t=t.replace('### Actual original arithmetic unframed determinant and inertia quotient','### Actual ordinary invariant direct-summand criterion')
t=t.replace('Eight production increments','Thirteen production increments').replace('scope 1764: 1131 exact consumers, 7,318 explicit registrations','scope 1777: 1144 exact consumers, 7,347 explicit registrations').replace('all eight increments','all thirteen increments')
a=t.index('Apply the actual original strict-conjugacy identity');b=t.index('The foundation verifier observed',a)
body='''The new public criterion compares the literal operators `(rho(g)-1)(rho(g0)-det(rho(g0))*1)` with the entire invariant submodule of the same original two-dimensional representation. It proves that all these operators vanish if and only if that submodule is free of rank one and is a direct summand of the original two-dimensional local coefficient module. The original residue map is local and the chosen original element has nonidentity residual matrix.

In the forward direction the determinant-complement operator is nonzero in the genuine residue, so one of its actual columns is a primitive invariant vector. An explicit invertible basis extending that vector and residual unit reflection identify the entire invariant submodule. A linear equivalence and projection construct its rank-one structure and complementary submodule. In the converse direction, the original direct-sum projection and rank-one equivalence produce a primitive invariant vector. The resulting invariant-line basis shows that the determinant-complement operator maps into that same line, so every original ordinary relation vanishes.

The existing `matrixStandardRepresentation` column-action definition was generalized from fields to commutative rings and arbitrary type universes; its matrix formula and map-one/map-multiplication proof remain unchanged. All original field Schur results retain their assumptions and are checked in the complete package and audit. The existing file's exact hash is included below. No duplicate column representation or resource-limit increase was introduced.

[de Smit–Lenstra, Section6.2](https://pub.math.leidenuniv.nl/~smitbde/papers/bu-fermat-1995-desmit-lenstra.pdf) supplies the source ordinary criterion. The present result proves its local matrix algebra for the original representation. Specializing to actual arithmetic inertia, deriving the nontrivial element from the original residual ordinary data, constructing the literal ordinary coefficient quotient and its original class classification remain separate obligations.

Exceptional finite-flat and p-adic Hodge local conditions, full Selmer theory, modular Galois association, patching, higher symmetric automorphy/continuation, unconditional Deligne, non-CM Sato-Tate and the final modular application remain open. DUB-01-16 remain accepted; DUB-17-20 remain OPEN.

'''
t=t[:a]+body+t[b:]
t=t.replace('Tools/actual-unframed-condition-route-20261010.json','Tools/actual-ordinary-invariant-line-route-20261010.json')
t=t.replace("'Extension/Dubon2026.lean', 'Extension/lakefile.toml'","'Extension/Dubon2026/MatrixAdjointSchur.lean',\n             'Extension/Dubon2026.lean', 'Extension/lakefile.toml'")
t=t.replace('Combined1764 verification recorded','Combined1777 verification recorded')
ast.parse(t)
assert 'c5ea00351c28e24afc9f0f84379aa41082b1188f' in t
assert '9dd7c9f61aeb2704832c897475a76d471f855150ff6cde03e08cee141a090114' in t
(D/'record1777combined.py').write_text(t,encoding='utf8')
t=(D/'finalize1764.py').read_text(encoding='utf8')
t=t.replace('1764','1777').replace('1131','1144').replace('7318','7347')
t=t.replace('All eight modules1757-1777','All thirteen modules1765-1777').replace('All eight promoted','All thirteen promoted')
t=t.replace('actual-unframed-condition-route','actual-ordinary-invariant-line-route').replace('futureUnframedConditionDrafts','futureOrdinaryInvariantDrafts')
t=re.sub(r"^v\['semanticBoundary'\]=.+$", "v['semanticBoundary']="+repr('Verified exact equivalence between the actual ordinary matrix relations and the genuine full invariant submodule being free of rank one and a direct summand. The original representation, local residue map and nonidentity residual element remain explicit. Arithmetic inertia specialization, deriving the residual element, literal ordinary quotient and class classification, finite-flat and p-adic Hodge conditions, full Selmer comparison, modular association and patching remain open.'),t,flags=re.M)
ast.parse(t)
(D/'finalize1777.py').write_text(t,encoding='utf8')
print('Combined1777 receipt and finalizer READY NOT EXECUTED; modules1765-1777 remain UNCOMPILED drafts.')

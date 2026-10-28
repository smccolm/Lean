from pathlib import Path
import json,re
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
d=Path('E:/Lean/.tmp/dubon83')
r=Path('E:/Lean/Riemann Zeta')
mods=json.loads((d/'modules877.json').read_text())
title='Actual complex matrix Lie action and central enveloping Casimir'
math='Six further production modules construct the actual complex Lie algebra of traceless two-by-two matrices with its original half-diagonal and elementary basis. The proved original Hilbert commutators extend to a genuine complex Lie algebra homomorphism on the actual smooth subspace. For every original smooth real matrix curve through the identity, its literal matrix-entry tangent acts by precisely its original Hilbert norm derivative. Generation induction in the genuine universal enveloping algebra proves that the normalized quadratic element is in its full algebraic center. The original Lie action lifts to an actual algebra homomorphism, and that central element maps exactly to the original successive Hilbert Casimir operator. The original smooth generator and every actual enveloping-algebra translate have the precise eigenvalue k/2 times (1-k/2). No central character, irreducibility or symmetric continuation is assumed to obtain these identities.'
remaining='The source’s regular-algebraic and irreducible automorphic representation identification, and higher symmetric continuations, remain open. Unconditional Deligne, non-CM Sato–Tate and the final modular application remain open. DUB-01–16 remain accepted; DUB-17–20 remain OPEN.'
pending='Focused production compilation passed; source-consumer compilation, expanded audit, all sixteen linters and sequential foundation/paper verification are pending.'
status=f'{title}: {math} Three exact consumers expand registered scope to 877 production modules, 377 exact consumers and 4,121 explicit audit registrations. {pending} {remaining} Earlier milestone paragraphs retain their historical scope.\n'
section=f'### {title} — 8 October 2026\n\n{math} {remaining}\n\n'+''.join(f'- [{n}](Extension/Dubon2026/{n}.lean).\n' for n in mods)+'\nExact consumers: `actual_adelic_matrix_Lie_action_source`, `actual_adelic_enveloping_casimir_source` and `actual_adelic_enveloping_casimir_orbit_source`.\n'
(d/'status877.txt').write_text(status,encoding='utf8');(d/'section877.txt').write_text(section,encoding='utf8')
c=json.loads((p/'Tools/scaffold.json').read_text(encoding='utf8'))
for n in c['statusDocuments']:
 f=p/n;s=f.read_text(encoding='utf8');a=s.index('\n');s=s[:a+1]+'\n'+status+'\n'+s[a+1:];f.write_text(s,encoding='utf8')
for n in ['Dubon Crosswalk.md','Dubon Reproduction Manifest.md']:
 f=p/n;s=f.read_text(encoding='utf8');f.write_text(s+'\n'+section,encoding='utf8')
f=p/'Dubon Architecture.md';s=f.read_text(encoding='utf8');a='  C --> A["OPEN DUB-17: central enveloping-algebra and regular-algebraic identification"]';assert s.count(a)==1
s=s.replace(a,'  C --> E["Proved actual complex Lie action and central enveloping Casimir image"]\n  E --> A["OPEN DUB-17: regular-algebraic representation identification"]');f.write_text(s,encoding='utf8')
a="Identification with the source's central universal-enveloping-algebra element and regular-algebraic representation, irreducibility and higher symmetric continuations remain open."
b='The original infinitesimals now define a genuine action of actual traceless complex matrices, agreeing with every original smooth real-curve derivative. The actual central element in the full universal enveloping algebra maps exactly to the original Hilbert Casimir and has the proved original generator eigenvalue. The source’s regular-algebraic and irreducible automorphic representation identification, and higher symmetric continuations, remain open.'
for f in [r/'README.md',p.parent/'README.md']:
 s=f.read_text(encoding='utf8');assert s.count(a)==1;s=s.replace(a,b);f.write_text(s,encoding='utf8')
f=p/'Tools/modular_research_20261006.json';j=json.loads(f.read_text(encoding='utf8'));j['adelicEnvelopingCasimirImplementation20261008']={'date':'2026-10-08','status':'Focused production and exact source-consumer compilation passed with zero diagnostics; expanded audit, sixteen linters and sequential verification pending. DUB-17 remains OPEN.','modules':mods,'mathematics':section,'remaining':remaining,'validation':'877 production modules; 377 exact consumers; 4121 explicit registrations. Full verification pending.'};f.write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
s=(d/'record871.py').read_text(encoding='utf8').replace('871','877').replace('374','377').replace('4094','4121').replace('4,094','4,121').replace('adelicSl2BracketsImplementation20261008','adelicEnvelopingCasimirImplementation20261008').replace('Actual full sl2 brackets and original quadratic operator commutation',title).replace('actual full sl2 brackets and original quadratic operator commutation','actual complex matrix Lie action and central enveloping Casimir')
s=s.replace('The current verified scope has 857 production modules, 371 exact consumers, 4,044 explicit audit registrations and 7,146 exhaustive theorem dependency checks.','The current verified scope has 871 production modules, 374 exact consumers, 4,094 explicit audit registrations and 7,220 exhaustive theorem dependency checks.')
good=next(x['rev'] for x in json.loads((r/'lake-manifest.json').read_text())['packages'] if x['name']=='mathlib')
s=re.sub(r'Mathlib `[0-9a-f]{40}`','Mathlib `'+good+'`',s)
(d/'record877.py').write_text(s,encoding='utf8')
print('Synchronized the new central enveloping-algebra scope; DUB-17–20 remain open.')

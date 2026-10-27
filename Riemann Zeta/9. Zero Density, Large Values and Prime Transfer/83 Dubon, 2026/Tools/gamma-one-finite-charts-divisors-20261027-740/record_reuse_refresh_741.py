from pathlib import Path
import datetime, hashlib, json

p = Path(__file__).parent
a = p / 'reuse-head-refresh-741'
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
heads = json.loads((a / 'manifest.json').read_text(encoding='utf-8'))
chain = ('DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation '
    '-> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic '
    'realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> actual '
    'Picard/H1, full/parabolic, transpose and diamond comparison -> differential and period geometry.')
findings = [
    dict(source='leanprover-community/mathlib4', decision='No new required input in the inspected modular-form changes.',
         evidence='The complete current tree was compared with the previous tree. All four changed modular-form files were retrieved at both revisions and their complete diffs read. Discriminant, LevelOne/DimensionFormula, QExpansion and RamanujanFormula only change nonzero API names to ne_zero API names in these diffs.'),
    dict(source='openai/math', decision='No inspected result discharges the original Gamma1 field-to-period comparison or the non-CM arithmetic continuation requirement.',
         evidence='The new CM Hodge formalization is catalogued, but a theorem about CM abelian varieties is not the required non-CM all-weight modular association. Complete NumberTheory, AlgebraicGeometry, ArithmeticGeometry and RepresentationTheory path inventories were inspected, along with the catalogue and selected full primary proof files. The inspected smooth-scheme chart constructions require actual smooth complex schemes and their algebraic coordinate machinery. They do not construct the needed Gamma1 model or compare its places with the existing integral-ratio function field. The bivariate convergent-series file assumes convergence and proves differentiated-series identities; it does not construct a normalized place embedding.'),
    dict(source='teal-sea/zeta-lab', decision='No reduction of the open modular acceptance gates from the inspected update.',
         evidence='The new work concerns a Davenport-Heilbronn function, a linear combination of two character L-functions. The original named statement also admits a trivial zero; the source explicitly distinguishes the stronger strip results. The numerical strip assembly was not downloaded, built or audited here. Neither version provides the required modular symmetric-power continuation. Existing fixed-character Dubon gates are already closed.'),
    dict(source='anthropics/fermats-last-theorem', decision='Retain the precise period alternative as a candidate; its prerequisites are not yet locally discharged.',
         evidence='The live head is unchanged. Scope736 and scope739 inspect the actual principal-divisor converse, meromorphic realization, real-period dimension bound, multiplier normalization and reciprocity dependencies. Reusing local all-modular-ratio membership avoids rebuilding the external field framework. Specializing meromorphic pole clearing to a finite analytic divisor may avoid the general compact-pole enumeration. Real-period surjectivity, Abel-Petersson reciprocity and order-zero control at all j-pole places still require proof.'),
    dict(source='ImperialCollegeLondon/FLT; dozenalist/ModularFormsMod; dozenalist/LeanModularForms',
         decision='Heads unchanged; previous exact source-contract assessments remain applicable.',
         evidence='Live GitHub default-branch commit responses are preserved with retrieval timestamps and SHA-256 hashes.')]
coverage = [
    'Seven live repository heads checked at 2026-10-27 09:40:44--47 UTC; three changed.',
    'GitHub compare file lists cap at 300. The OpenAI root recursive tree is truncated, and so is the previous root tree. Visible delta entries are not evidence that a file was newly added or absent previously.',
    'Fresh targeted recursive subtrees for NumberTheory (29617 entries), AlgebraicGeometry (25062), ArithmeticGeometry (631) and RepresentationTheory (3390) are complete and untruncated. This is not a complete content search of every external file.',
    'Full selected primary files and the four Mathlib modular-form diffs were read; file-path matches and repository catalogues alone are not counted as proved reusable theorems.',
    'Broad web queries: Lean formalization symmetric power automorphy GitHub 2026; Lean Eichler Shimura GitHub; Lean modular curves Picard formalization. These did not identify an additional verified matching proof. Search absence is not a universal nonexistence claim.',
    'No external dependency closure was compiled or axiom-audited. No new external import or root-pin change. OpenAI uses Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; local Lean 4.30 and mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f remain unchanged. OpenAI source license is Apache-2.0.'
]
assessment = dict(recordedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    chain=chain, repositories=heads['repositories'], findings=findings, coverage=coverage,
    routeDecision='Promote the already audited exact finite charts and divisor-moving results common to the required Picard/period comparison. Before further global geometry expansion, continue comparing the concrete cusp route and the pinned modular-period alternative. Defer unrelated zero-free, Hodge, broad scheme and bivariate-series infrastructure.',
    actualProgress='Scope738 discharges the finite prescribed-order and divisor-moving obligations using existing local closed residues, separator indicators, curve principal divisors and actual finite-place exhaustion. Every degree-zero divisor class now has a finite analytic representative with coefficient sum zero. Its scratch receipt passes; production integration remains pending.',
    boundary='16/20; DUB-17--20 OPEN. Every original source quantifier, all-weight arithmetic obligation and acceptance gate remains unchanged. Finite characters, complex semisimplicity, Witt coefficients and universal deformation rings are not characteristic-zero lifts.',
    relatedAssessments=[dict(path=str(p / f), sha256=sha(p / f)) for f in [
        'gamma-one-global-period-route-reuse-736/route-assessment.json',
        'gamma-one-period-alternative-reuse-739/route-assessment.json',
        'source-gamma-one-divisor-moving-1-scratch-receipt.json']],
    evidence=[dict(path=f.name, sha256=sha(f)) for f in sorted(a.iterdir()) if f.is_file()],
    rootPinsChanged=False, externalImport=False, externalClosureBuilt=False, acceptanceGatesClosed=0)
with (a / 'assessment.json').open('x', encoding='utf-8') as f:
    json.dump(assessment, f, indent=2); f.write('\n')
archive = 'Tools/gamma-one-finite-charts-divisors-20261027-740'
report = '''# Dubon Lean reuse refresh: 27 October 2026

Seven repository heads were checked live at **09:40 UTC on 27 October 2026**. Mathlib, OpenAI/math and zeta-lab changed since the previous search. The inspected updates do not yet close a remaining Dubon gate. The useful period alternative from the pinned FLT source remains under assessment, with its missing assumptions identified explicitly.

The source dependency is **DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of the original finite Gamma1 Hecke characters -> Picard/H1, full/parabolic, transpose and diamond comparison -> actual differential and period geometry**. The original homogeneous coefficient action must be retained throughout.

| Repository and inspected revision | Finding for the remaining work |
| --- | --- |
'''
short = {
    'anthropics/fermats-last-theorem':'Unchanged. Selected genuine Gamma1 and modular-period arguments remain useful; the finite-character-to-characteristic-zero gap remains.',
    'ImperialCollegeLondon/FLT':'Unchanged. Previous exact-contract assessment retained.',
    'dozenalist/ModularFormsMod':'Unchanged. Previous residual/all-weight reuse remains available.',
    'dozenalist/LeanModularForms':'Unchanged. Native modular-form reuse remains available.',
    'leanprover-community/mathlib4':'Four changed modular-form files inspected in full diff: API renamings only, with no new theorem for the missing period or arithmetic comparison.',
    'openai/math':'New CM Hodge formalization and scheme-chart infrastructure inspected at the catalogue/signature level, with selected chart proofs read fully. No verified replacement for the actual Gamma1 model/period bridge or non-CM arithmetic association.',
    'teal-sea/zeta-lab':'New Davenport-Heilbronn strip-zero work concerns a different function and does not supply modular symmetric-power continuation.'}
for row in heads['repositories']:
    report += f"| [{row['repository']} `{row['head'][:12]}`]({row['url']}) | {short[row['repository']]} |\n"
report += '''
The four Mathlib files are `Discriminant`, `LevelOne/DimensionFormula`, `QExpansion` and `RamanujanFormula`. Their complete before/after diffs are preserved. The inspected OpenAI `ComplexPoint/AnalyticMap` and `ClosedImmersion/NormalCoordinates` proofs already require smooth complex schemes and algebraic coordinates. Using them here would first require the missing identification with the actual integral-ratio function field. The inspected convergent-series result assumes convergence; it supplies no missing place embedding. These are deferred because the necessary connection to the Dubon dependency chain has not been shortened.

The most promising alternate argument is the pinned FLT principal-divisor converse: finite analytic divisors and nonzero cusp limits can avoid an explicit cusp atlas in that final step. Existing local modular-ratio membership supplies its field inclusion. A finite-divisor specialization may also avoid repeating the general compact-pole enumeration. However, the complete comparison still needs real-period surjectivity, Abel-Petersson reciprocity, and order-zero control at every remaining j-pole place. The local Gamma0 dimension bound cannot be substituted for the required Gamma1/principal-level bound. This is a candidate route, not a verified shortcut to a closed gate.

The shared divisor-moving obligation has now been proved and audited in scratch: arbitrary orders can be prescribed at finitely many actual places; subtracting the resulting principal divisor moves every divisor class to a finite analytic divisor. For a degree-zero class, its analytic coefficients sum to zero. This reuses local separator indicators, closed residues, principal-divisor geometry and finite-place exhaustion. It removes the finite-support reduction from both candidate period routes. Its production verification is recorded separately in the assembled proof record.

Coverage is bounded and explicit. GitHub truncated the full OpenAI tree, so complete Number Theory, Algebraic Geometry, Arithmetic Geometry and Representation Theory subtrees were fetched separately. A path inventory is not a proof audit. Broad web searches also checked symmetric-power automorphy, Eichler-Shimura and modular-curve Picard formalizations. No external closure was compiled or audited locally, and absence from these searches is not a claim of universal absence. OpenAI's Lean 4.34.1 and Mathlib pin differ from the local Lean 4.30 environment; the local pins remain unchanged.

The [frozen assessment](ARCHIVE/reuse-head-refresh-741/assessment.json), [head manifest](ARCHIVE/reuse-head-refresh-741/manifest.json), [scope-736 route assessment](ARCHIVE/gamma-one-global-period-route-reuse-736/route-assessment.json) and [scope-739 dependency assessment](ARCHIVE/gamma-one-period-alternative-reuse-739/route-assessment.json) preserve exact revisions, source URLs, hashes, coverage and outstanding assumptions. Selected source files are research snapshots with `.txt` extensions, outside Lean import closures. Earlier dated search reports remain unchanged.

**16/20; DUB-17--20 remain OPEN.** All twenty acceptance conditions and the full all-weight arithmetic goal are unchanged. Finite characters, complex semisimplicity, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. Current verification status belongs to the [reproduction manifest](Dubon%20Reproduction%20Manifest.md), not to this dated research snapshot.
'''.replace('ARCHIVE', archive)
with (a / 'Dubon Reuse Refresh 2026-10-27.md').open('x', encoding='utf-8') as f:
    f.write(report)
print(json.dumps(dict(assessmentSha256=sha(a / 'assessment.json'), reportSha256=sha(a / 'Dubon Reuse Refresh 2026-10-27.md'), productionMutation=False)))

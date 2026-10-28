import datetime
import hashlib
import json
from pathlib import Path

root = Path(__file__).parent
heads = json.loads((root.parent / 'public-head-followup-20261018-live.json').read_text())
tau = json.loads((root / 'source-manifest.json').read_text())
flt = json.loads((root / 'flt-source-manifest.json').read_text())
oai = json.loads((root / 'openai-math/receipt.json').read_text())
oai_sources = json.loads((root / 'openai-math/class-field-manifest.json').read_text())
assessment = {
    'checkedUTC': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'request': 'Fresh search for existing Lean proofs that can substantially shorten the full active Dubon formalization.',
    'target': 'DUB-17: primitive_satoTate_of_higher_continuation_alone, frozen source lines 1616-1687; reverse H1 localization -> exact dual Selmer -> arithmetic patching -> higher symmetric-power continuation. Separate modular association, purity and automorphy remain required. DUB-18: genuine modular-form Theorem 2.6 and level-one Corollary 8.2. DUB-19-20: full semantic and verification gates.',
    'acceptance': '16/20; DUB-17-20 remain open. This research closes no acceptance gate.',
    'publicHeads': [{k: h[k] for k in ['repository', 'sha', 'date', 'url']} for h in heads['heads']],
    'additionalRepository': {k: oai[k] for k in ['repository', 'sha', 'date', 'url']},
    'sourceReceipts': {'tauCeti': tau, 'imperialFLT': flt, 'openaiClassField': oai_sources},
    'compatibility': {
        'native': 'Lean 4.30.0; frozen Mathlib/PNT+ pins unchanged',
        'tauCeti': 'Lean 4.36.0-rc1', 'imperialFLT': 'Lean 4.35.0-rc3',
        'openaiMath': 'Lean 4.34.1; ClassFieldTheory dependency pinned to 2eb22d6485af45f29c5219de6c49f196a61c4f49',
        'decision': 'No wholesale dependency replacement or toolchain migration. Any selected proof would require a faithful local port and its complete dependency audit.'},
    'findings': [
        {'candidate': 'TauCeti SelmerStructure', 'inspection': 'Full selected source body',
         'result': 'Defines localization, Selmer groups and their membership characterization. Does not prove the reverse H1 localization or exact dual Selmer theorem needed here.',
         'reuseDecision': 'Do not replace the existing native Selmer objects with another definition.'},
        {'candidate': 'TauCeti ClassFormation and Brauer/SumFormula', 'inspection': 'Selected public statements and proofs; ClassFormation body and SumFormula main proof bodies',
         'result': 'ClassFormation supplies zero-sum/kernel and refinement reductions conditional on universal Kummer norm-index and prime-layer generator inputs. SumFormula assumes Hasse injectivity over finite extensions or idele-class H1 vanishing.',
         'reuseDecision': 'Native constructed full-order class and zero-total relation criterion already supply the relevant class-field edge. These reductions do not identify the actual Dubon Cartier cup total or remove the remaining reverse-localization obligation.'},
        {'candidate': 'TauCeti PrescribedInvariant', 'inspection': 'Declaration index, generator/refinement statements and their proofs, and decomposition-character/cyclic-layer statements and proofs',
         'result': 'Constructs absolute H2 prescribed totals, generator classes after refinement, and a same-layer cyclic generator given a surjective decomposition map. The last surjectivity is an explicit hypothesis; it does not automatically discharge every prime-layer input in ClassFormation.',
         'reuseDecision': 'Useful reference, but importing this new object stack would duplicate native original-field generator and norm-root proofs.'},
        {'candidate': 'TauCeti LiftingObstruction and CorestrictionLocalization', 'inspection': 'Selected source bodies and exact public signatures',
         'result': 'Proves idele H2 kernel/range relations, cyclic-layer surjectivity and Mackey localization. The latter explicitly stops before identifying subgroup double cosets with actual extension-field places.',
         'reuseDecision': 'No replacement for the required original-completion/prime normalization comparison. Reuse native original maps and constructed relation criterion.'},
        {'candidate': 'TauCeti IdeleLocalization and Cup/Duality/Basic', 'inspection': 'Headers, declaration indexes and selected statements only; not full proof-body or import-closure audit',
         'result': 'Actual idele localization and finite support; generic duality pairings and conditional bijectivity transport.',
         'reuseDecision': 'Retain as bounded candidates, not certified replacements for global arithmetic duality.'},
        {'candidate': 'Anthropic FLT', 'inspection': 'Live head and primary proof-route document, against earlier cached source review',
         'result': 'Head unchanged from the previous review. Its documented modularity lifting is for the weight-two, semistable and level-conditioned 3/5 route; that is not all higher symmetric powers of every non-CM modular form.',
         'reuseDecision': 'Continue adapting the previously inspected finite relation/localization argument; no newly changed endpoint found in this pass.'},
        {'candidate': 'Imperial FLT', 'inspection': 'Live commit, KnownIn1980s source and assumptions README',
         'result': 'Latest commit is a Mathlib compatibility bump. The selected assumptions source explicitly declares knownin1980s as a proof of an arbitrary proposition, and its README lists Poitou-Tate and automorphic results as assumptions/planned assumptions.',
         'reuseDecision': 'Any individual theorem needs transitive dependency inspection; cannot import the project endpoint under the Dubon proof standards.'},
        {'candidate': 'OpenAI math', 'inspection': 'Live head, primary manuscript map, formalization catalogue, complete NumberTheory subtree, five ClassField source bodies and dependency manifest',
         'result': 'The manuscript map contains modularity claims, but the formalization catalogue has no corresponding modularity/automorphy/Poitou-Tate/Selmer entry under the searched terms. The five selected DukePrimeDegree files construct ray-character realization for totally real cyclic extensions using NYLL class-field theory. They do not prove reverse H1 localization for the trace-dual coefficient or higher symmetric-power continuation.',
         'reuseDecision': 'No direct endpoint replacement. The cyclic Artin/ray-character bridge is a concrete proved-source candidate for an appropriate future character obligation, but it does not advance the currently unresolved chain.'}
    ],
    'routeDecision': [
        'Reuse the native canonical-total composition, bottom-prime equivalence and original completion base-change theorem; do not rebuild a class-field library.',
        'Assemble actual indexed local cup total -> coherent source annihilator gives total zero -> arithmeticSPlaceRelationObstruction_zero_of_total_zero.',
        'Use originalUnramifiedStage_exists_constructed_relation_criterion directly, avoiding the extra scalar-readout packaging where the zero obstruction is already available.',
        'Retain the all-local-H1 cup identities for the same existential relation witness; they are needed after extension to recover the prescribed local cohomology classes.',
        'Reuse originalUnramifiedStageInUnion and its literal inclusion/equivalence lemmas, plus the proved finite-stage trace-action restriction, for the required enlarged-stage comparison.'
    ],
    'limits': [
        'A bounded current-source review, not a proof of absence of reusable mathematics on the internet.',
        'No candidate external import closure was newly kernel-audited or incorporated in this refresh.',
        'The full OpenAI recursive tree was truncated; the NumberTheory subtree was fetched separately and is complete (23662 entries). Catalogue searches are only as broad as their recorded terms.',
        'Eight selected TauCeti and five selected OpenAI Lean sources are inert .lean.txt research copies with Git blob checks; their presence is not a local build claim.'
    ],
    'externalCodeCopiedIntoProduction': False,
    'pinsChanged': False
}
(root / 'assessment.json').write_text(json.dumps(assessment, indent=2), encoding='utf-8')
print('Recorded bounded reuse assessment:', root / 'assessment.json')
print('SHA256:', hashlib.sha256((root / 'assessment.json').read_bytes()).hexdigest().upper())

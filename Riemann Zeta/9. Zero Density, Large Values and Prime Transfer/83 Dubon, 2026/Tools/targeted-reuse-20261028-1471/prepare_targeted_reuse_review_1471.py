from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
s=Path(__file__).parent
dirs=['anthropic-parabolic-candidates-1462c','anthropic-gamma-one-geometry-1463b','anthropic-geometry-dependencies-1464','anthropic-degree-genus-leaves-1465','anthropic-integral-slash-1467']
rows=[]
for d in dirs:
 m=json.loads((s/d/'fetch-manifest.json').read_text(encoding='utf-8'))
 for row in m['files']:
  f=Path(row['local']);data=f.read_bytes();assert hashlib.sha256(data).hexdigest().upper()==row['sha256']
  lines=data.decode('utf-8').splitlines()
  row=dict(row)
  row['lexicalMatches']=[dict(line=i+1,text=l[:240]) for i,l in enumerate(lines) if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|sorryAx',l)]
  row['nondefaultOptions']=[dict(line=i+1,text=l) for i,l in enumerate(lines) if re.search(r'set_option (?:maxHeartbeats|synthInstance.maxHeartbeats|linter\.)',l)]
  rows.append(row)
assert len(rows)==29
review=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),revision='6e837e75355538c7f80bab5b956861e86c4eacc2',headChanged=False,completeSolTreeLeanFiles=29511,inspectedSourceFiles=29,files=rows,externalBuild=False,externalTransitiveAxiomAudit=False,externalImport=False,productionMutation=False,scope='Targeted theorem-statement and selected proof/dependency inspection, not certification of the external repository. Filename discovery is confined to the complete P2M/Sol subtree.')
with (s/'targeted-reuse-review-1471.json').open('x',encoding='utf-8') as h:json.dump(review,h,indent=2);h.write('\n')
report='''# Targeted proof reuse review — 28 October 2026

This supplements the October 28 broad repository refresh and LANA/curve reviews. The active objective remains the complete frozen Dubon source contract: DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 require the original non-CM modular-form application through literal higher symmetric-power continuation, automorphy, and original all-weight characteristic-zero association. DUB-17–20 remain OPEN; acceptance stays 16/20.

## What changed in this search

The public Anthropic repository still reports commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, dated September 24, 2026. Its HEAD has not changed since the previous inspection. A targeted API traversal obtained the complete `P2M/Sol` subtree with 29,511 Lean filenames, avoiding the earlier truncated whole-repository listing. Twenty-nine pinned source texts were downloaded as inert `.lean.txt` files and inspected at the statement and selected dependency/proof level. This is a new inspection result, not a claim that these proofs were newly published.

The source is Apache-2.0, as recorded in the existing pinned upstream-license evidence. No external module was imported, no root pin changed, and no external build or transitive axiom audit is claimed. Several source texts raise elaboration limits or suppress linters. Those settings are not adopted; any selected proof must be decomposed and checked under this project's unchanged standards. Lexical scans are recorded separately and are not substitutes for kernel dependency audits.

## Most useful candidate: original Γ1 degree and genus preservation

The newly inspected [degree lower-bound proof](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField.lean) assumes a nonzero level M, a subgroup H of units modulo M, a prime ℓ not dividing M, a valuation over ℓ in the rational algebraic closure, and the literal j-coordinate in the residue integral-ratio field. Its conclusion is the signed ΓH index lower bound for the degree over j. It does not assume degree or genus preservation.

Its proof uses [integral Γ1 Eisenstein series with exact slash transformation](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq.lean). Symmetric unit-coset sums of the weight-four series have first coefficient zero or one. They distinguish diamond cosets after reduction. A proved Γ0 action on the integral-ratio field and the already familiar Γ0 j-degree supply the tower comparison. Crucially, the Γ0 action uses the separate theorem that a power of the level clears slash denominators. Reusing the native diamond-Gauss action conditional on degree equality here would be circular and is explicitly rejected.

The [genus-preservation proof](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.lean) similarly retains only prime-not-dividing-level hypotheses in its final statement. Its upper bound uses regular prolongation and degree equality. Its lower bound uses ramification and cusp counts. The latter includes distinct wild-ramification arguments in characteristics two and three; these primes cannot silently be omitted. This is not a supplied smooth-model certificate and is not merely characteristic-zero genus invariance.

The local repository already proves the actual characteristic-zero integral-ratio field identity, finite original coordinate degree, the exact signed Γ1 index in characteristic zero, the actual residue field and its upper degree bound, the genus machinery, and the downstream geometric Tate/Frobenius consumers. These results should be reused. The new degree route is promising because it supplies explicit integral separating functions instead of demanding further general Fricke-integrality infrastructure. Its full native adaptation and remaining dependency checks are still required; neither degree nor genus preservation is marked proved.

The first necessary comparison has now compiled with zero diagnostics in `SourceGammaOneIntegralRatioResidue1466e`: the residue-characteristic integral-ratio field is contained in the native actual residue image. This theorem assumes neither degree nor genus equality. It reuses the original scalar-extension identity, coefficient Gauss map and residue formula. Exhaustive auditing and production promotion of this new bridge remain pending. The next comparison is degree monotonicity over the same literal reduced j.

## Parabolic transfer candidates and their exact limits

The exact missing input is `sourceGammaOneIntegralParabolicTransfer`: original integral parabolic classes with homogeneous coefficients must have actual constant-coefficient Γ1 parabolic preimages under the native transfer, modulo each required p-power. Full-H1 surjectivity already exists here and does not imply this parabolic statement.

| Inspected source | What it actually supplies | Why it does not directly discharge this input |
| --- | --- | --- |
| `CohCarrier_exists_linearMap_baseChange_parabolicHoms_top_comp_eq_comp_heckeTL_restrict_baseChange` | Hecke-compatible base change of Γ0 constant parabolic H1 over characteristic-zero fields | It requires a characteristic-zero coefficient field, not a finite p-power coefficient ring. |
| `HeckeEis_exists_coeffH1_restrict_injective_range_iff_equivariant_heckeT_of_charZero` | Injective restriction to a finite-level kernel, with exact equivariant image | It requires characteristic zero; restriction is also the opposite direction from the needed parabolic transfer. |
| `HeckeEis_exists_coeffH1par_map_of_equivariant_retraction` | Functorial split maps on parabolic cohomology and Hecke compatibility | It assumes an equivariant coefficient section and retraction. Such a splitting for the actual coinduced finite-modulus coefficient map is not established. |
| `ModularCurve_Period_exists_perfectPairing_parabolicHoms_baseChange` | Transfers a supplied perfect integral pairing | It requires additive torsion-free coefficients and a perfect integral pairing. It does not apply directly to ZMod(p^n). |
| `CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms` | Perfect Hecke/degeneracy pairings over a characteristic-zero local domain, away from two | It is constant Γ0 cohomology, not the required homogeneous finite-coefficient Γ1 map. |
| `LevelRaising_exists_parabolicPairings_perfect_mod_three` | Pairing nondegeneracy modulo three and adjointness | The conclusion is specialized to three and retains specified parabolicity hypotheses. |
| `ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero` | Constructs an integral constant parabolic homomorphism from exact cusp orthogonality | It assumes minus one belongs to the group and does not supply homogeneous finite-modulus liftability. |
| `HeckeEis_exists_coeffH1par_int_modp_eigenclass_of_eigenform` | A primitive integral class with residual eigensystem congruences | Residual eigenclasses are already available natively; this does not produce the p-power Γ1 parabolic preimages. |
| `HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero` | Integral parabolic reduction kernel is p times the module | It requires weight-degree n<p, p≠2, and p not dividing the level. It is not a transfer-surjectivity theorem. |
| `HeckeEis_existsUnique_coeffCocycles_sl2z_apply_S_ST_eq` | Constructs a cocycle from exact S/ST generator relations | It does not impose or derive the needed parabolic preimage condition. |
| `groupCohomology_subsingleton_H1_dual_traceZero_of_toMatrix_eq_conj_specialLinearGroup_map` | H1 vanishing for the dual trace-zero adjoint representation in characteristic three | It is not vanishing for arbitrary homogeneous symmetric powers modulo p^n. |
| `IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure` | Transfer for a normal finite-index subgroup of a free group with abelian quotient | It requires the subgroup to contain all commutators and supplies no parabolic condition. Those requirements do not match the original Γ1 transfer. |

The inspected constant parabolic-to-Tate and residual Galois-module constructions corroborate the existing native geometric route. Their residual-field conclusions do not independently supply the required all-weight characteristic-zero association.

## Route decision and acceptance boundary

Prioritize the integral Eisenstein separation route for the precise coordinate-degree hypothesis, using the existing original field, actual residue image, Γ0 degree, signed Γ1 index and scalar-extension results. Inspect each upstream integrality and ramification proof before expanding it; defer general ΓH infrastructure when Γ1 specialization suffices. Preserve the finite-modulus parabolic transfer as a separate unresolved obligation. Do not substitute characteristic-zero restriction, a given equivariant splitting, residual association, or a different good-reduction model.

The ten-module quotient-character scope independently passed its focused scratch audit: the actual family and its unital original adic character are constructed from separate degree, genus and parabolic-transfer inputs, with the stated coefficient-prime and fixed-exception exclusions. This removes operator-choice, local-Frobenius-witness and character-kernel obligations but does not discharge those three inputs or the required two-dimensional realization. Full assembled verification and every remaining acceptance condition still apply.
'''
with (s/'Dubon Targeted Reuse Review 2026-10-28.md').open('x',encoding='utf-8') as h:h.write(report)
print(json.dumps(dict(files=len(rows),lexicalMatches=sum(len(r['lexicalMatches']) for r in rows),optionCommands=sum(len(r['nondefaultOptions']) for r in rows),productionMutation=False)))

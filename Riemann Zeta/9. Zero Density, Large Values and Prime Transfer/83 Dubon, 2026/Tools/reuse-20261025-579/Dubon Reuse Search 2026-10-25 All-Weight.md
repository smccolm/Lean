# Dubon reuse review: remaining all-weight Galois and automorphy obligations

Reviewed 25 October 2026 (America/Vancouver; retrieval continued on 26 October UTC). This supplements the earlier NYLL and FLT reviews and preserves the frozen Dubon source.

The inspected weight-two Galois construction and Hodge-Tate proof in Tianyi Peng's repository are byte-identical to the corresponding files in the already reviewed Anthropic FLT revision. They are not a new all-weight association theorem. The Hodge-Tate proof remains a candidate for the later local regularity obligation, subject to identifying the actual geometric representation. Existing Dubon local duality, Selmer prime selection, weight-two Tate construction and residual association should be reused.

## Exact dependency

DUB-17 (Theorem 2.6), and then DUB-18 (Corollary 8.2), require continuation and nonvanishing of the literal higher symmetric-power L-functions of the original non-CM form. The current route passes through arithmetic automorphy, the original all-weight characteristic-zero Galois representation, and its local, image and regularity properties. A finite residual representation or universal deformation ring does not discharge that association theorem. A characteristic-zero coefficient ring does not imply that its deformation ring has a characteristic-zero point.

The actual-form residual construction supplies the original Fourier traces, good-prime inertia and determinant exponent. Audited scratch successors derive the global cyclotomic determinant, genuine complex-conjugation determinant and finite coefficient field. The Witt/framed consumer has passed its scratch proof and dependency audits. The original-form fixed-determinant consumer has also passed its public and declaration-value audits. Promotion and assembled verification of these successors remain pending. Acceptance remains 16/20; DUB-17--20 OPEN.

## Candidate assessments

| Primary source, frozen revision | Exact contract and reuse decision |
| --- | --- |
| [Anthropic FLT](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2), 24 September; current head unchanged | CuspForm.exists_galoisRep_of_point constructs an adic representation for a character of the **weight-two** Hecke algebra, with valuation Frobenius polynomials and unramifiedness. This is substantive code, beyond the HeckeGaloisRepDatum interface. It overlaps the existing Dubon weight-two route. The p-divisible-group Hodge-Tate theorem constructs a basis with weights 0 and 1; an appropriate geometric realization is still needed for local regularity. Neither inspected result supplies all-weight association or higher symmetric-power automorphy. Apache-2.0; prior review records Lean 4.33.1 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d. |
| [Tianyi Peng FLT](https://github.com/tianyipeng/fermats-last-theorem/tree/9e5f05a13048588eeef806e16f4cb2161801bc8a), 5 September | Both selected proof files are byte-identical to Anthropic's files above. Generated documentation aided discovery; the Lean source determined the assessment. No duplicate adaptation is warranted. |
| [NYLL](https://github.com/n-yamaguchi-0729/NYLL/tree/8c1b16d10afaca09e0dc72753c6575e230d31a55), 19 October; current head unchanged | Earlier pairing reuse remains applicable. Its Witt residue-equivalence file uses the native constant-coefficient quotient and credits Anthropic FLT. Our existing SourceWittLift.residueMap and native Witt DVR already supply the shorter finite-field route. The specialized finite-place cyclotomic duality file does not replace the original-module duality already proved locally. Retain the prior Apache-2.0/NOTICE provenance and Lean 4.35.0-rc2/Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55 assessment. |
| [Imperial College FLT](https://github.com/ImperialCollegeLondon/FLT/tree/a3210204ad8876e851e32f73dd97d882bf1ccd0a), 22 October | Inspected automorphic Galois definitions are explicitly specialized to weight two and restrictive levels. The selected file retains admitted proof obligations; the assumptions README describes a conditional project. It is not a ready proof of Dubon's all-weight automorphy input. Lean 4.35.0; Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; Apache-2.0 headers. |
| [Karatarakis CICM24 Deligne](https://github.com/mkaratarakis/CICM24_Deligne/tree/8e5b163b30e434e6f68549e9399650923b75fb60), 3 April 2024 | Statement.lean leaves the association theorem and several coefficient/valuation prerequisites admitted. This is partial formalization of the statement. README pins Lean 4.2.0-nightly-2023-09-18 and Mathlib c4bd112a7f09. The earlier Lean-3 repository was also inventoried. GitHub metadata identifies no license for either; no code is adopted. |
| [Ramanujan-Petersson companion](https://github.com/lioristhmus/ramanujan-petersson/tree/8a3653c935925d7adc88c8312ac1820c13a7bcca), 20 March | The witness theorem derives a norm bound from supplied roots and purity. PaperInterfaces.lean postulates algebraic/Galois objects and packages association/purity as inputs. It does not remove the hard assumptions needed here. Lean 4.26.0; Mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67. No license identified; no adoption. |
| [GQ2](https://roed314.github.io/gq2/formalizations/axioms/) and [website revision](https://github.com/roed314/gq2/tree/a2b1481f5e87acbb732b1e0fcf308a7ac2a9013a), 2 September | The project documents nine classical axiom interfaces. Its conditional presentation theorem cannot serve as an unconditional replacement for local foundations. It concerns Q2 rather than the original all-prime modular association. |
| [ANR FALSE](https://anr-false.github.io/), website revision c9614f87db96569a2e754030ad0142a406eeb87b, 9 October | The official project describes modular Galois association as a research objective. Its inspected homepage supplies no completed all-weight proof artifact. This observation does not characterize every participant's work. |

Three additional source-level checks resolve potentially broader theorem names: IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt explicitly takes a Gamma1 cusp form of weight two; both IsNormalizedEigenform Frobenius-quadratic and prescribed-integral-closure specializations explicitly take Gamma0 cusp forms of weight two. Their fixed-revision source blobs are preserved in additional-weight-contract-snapshots.json. These signatures do not supply the missing all-weight construction.

Selected FLT proof files:
- P2M/Sol/S_CuspForm_exists_galoisRep_of_point.lean.
- P2M/Sol/S_PDivisibleGroup_exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers.lean.

## Local reuse and next required step

Reuse rationalArithmeticLocalH1ScalarCup_isPerfPair and rationalArithmetic_symmetric_deformation_auxiliary_dualSelmer_eq_bot. Their original group, coefficient and image assumptions remain visible; the latter's large-image hypothesis must eventually be proved for the actual source representation. Rebuilding generic local duality or Selmer prime selection would not remove that hypothesis.

For the present deformation input, reuse SourceWittLift, native Witt DVR/completeness and ArithmeticFramedUniversalRing. Before expanding fixed-determinant infrastructure, use Mathlib's WittVector.fromPadicInt/WittVector.equiv and coefficient mapping to construct the **actual p-adic cyclotomic** determinant lift and prove that its reduction equals the derived residual determinant. A Teichmuller lift of the finite residual character alone is insufficient. This removes an input to ArithmeticFixedDeterminantUniversality; it does not produce an original-form characteristic-zero specialization.

Defer a broad p-divisible-group/Hodge-Tate import until the original representation has the necessary geometric identification. The inspected theorem addresses later regularity only after this intervening obligation is met.

## Evidence and limits

Tools/reuse-20261025-579 preserves metadata, source text, hashes, exact source comparisons, search scope and selection scripts. Snapshots use .txt extensions and are outside every Lean import closure. Downloaded code has Git-blob and SHA-256 verification. Some recursive GitHub trees are truncated; no absence conclusion is inferred from them. Assessments rest on primary code or official disclosures.

No external project was compiled. Public README build claims are not locally reproduced verification. No dependency, root pin, proof limit, source contract or acceptance condition changes. No inspected ready-made proof closes all-weight association, higher symmetric-power automorphy or literal continuation; the search does not establish that none exists elsewhere.

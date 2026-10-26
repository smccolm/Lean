# Dubon reuse search — 26 October 2026

The renewed search found usable Gamma1 geometry and diamond-normalization arguments. It did not find a ready proof of the original all-weight characteristic-zero Galois association or the required higher symmetric-power continuation among the inspected artifacts. This is a finding about selected sources, not a claim that no such proof exists.

The exact dependency remains DUB-17 (Theorem 2.6) / DUB-18 (Corollary 8.2) → literal higher symmetric-power continuation → arithmetic automorphy → the original all-weight Galois association → arithmetic realization of the original finite Gamma1 Hecke characters → geometric/H1 and diamond comparison, preserving the original homogeneous coefficient endomorphism. **16/20; DUB-17–20 OPEN.** The frozen paper, all twenty acceptance criteria, root pins and proof standards are unchanged.

## Current revisions and decisions

| Primary source | Latest inspected revision | Reuse decision |
| --- | --- | --- |
| [Anthropic FLT](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2) | 24 September; head unchanged on this check | Actual Gamma1 fields, finite Hecke maps and weight-two differential/Tate comparisons are useful. The inspected adic association still requires a characteristic-zero Hecke-and-diamond character. Finite characters are not that input. |
| [Imperial FLT](https://github.com/ImperialCollegeLondon/FLT/tree/a3210204ad8876e851e32f73dd97d882bf1ccd0a) | 22 October; head unchanged | The previously inspected automorphic interface is restricted to weight two and special levels and retains admitted prerequisites. No duplicate adaptation. |
| [ModularFormsMod](https://github.com/dozenalist/ModularFormsMod/tree/bc16671d6781a26216b378773502ba5583845cbf) | 21 October | Concrete Hecke reduction and Fourier coefficient formulas over target rings. Their liftability/source-ring hypotheses remain explicit. Local integral Fourier-character reduction and finite operator descent already supply the needed result. |
| [LeanModularForms](https://github.com/dozenalist/LeanModularForms/tree/f737ca88e0887ecbaad3510b30e37042c243fd17) | 5 October; also the current ModularFormsMod dependency | Useful explicit Gamma1 diamond/coset formula and complex character decomposition. Compare GL2-image, slash and diamond conventions before adapting. Complex semisimplicity does not provide an Artinian character lift. |
| [Current Mathlib](https://github.com/leanprover-community/mathlib4/tree/8d14a32337a069dbae9b92875aeb697de357b5ac) | 26 October, 09:43 UTC | The inspected Hecke definitions concern abstract double-coset modules. Existing local native H1 trace machinery supplies the current dependency without a toolchain change. |
| [OpenAI math](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a) | 12 October | Inspected Ramanujan-named theta files prove finite character-sum identities. The catalog-selected Hecke nonvanishing theorem concerns finite-order Hecke characters over the Eisenstein field. These do not prove the required modular-form symmetric-power result. |
| [zeta-lab](https://github.com/teal-sea/zeta-lab/tree/558eee037f954989986abad4b25851d9a41604ca) | 24 October | The inspected finite-field trace file proves two moments over all Weierstrass equation coefficients at one prime, including singular equations. It explicitly lacks the Tate-module identification. This does not establish horizontal Sato–Tate for a fixed non-CM form. |

The [earlier broad review](Dubon%20Reuse%20Search%202026-10-25%20All-Weight.md) records Tianyi Peng, NYLL, the partial Deligne statement, GQ2 and ANR FALSE. The [Gamma1 follow-up](Dubon%20Reuse%20Follow-up%202026-10-26%20Gamma1.md) records the exact finite-field and Hecke-map adaptations.

## Arguments that shorten the required chain

The actual Gamma1 field and Hecke-map construction reuses the original j coordinate, modular norms, Laurent independence, native modular translation, scalar-extension finiteness and existing divisor/Picard machinery. The arithmetic action on places and Picard groups commutes with the actual Hecke correspondence. The [production proof record](Tools/source-gamma-one-arithmetic-geometry.json) gives its verification status.

The selected [Gamma1 differential proof](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm.lean) compares regular differentials with weight-two cusp forms after complex scalar extension. Its actual curve, canonical-divisor, differential-expansion and cusp-basis prerequisites need local consumers. Existing finite-coordinate curve theorems and regular-differential machinery supply shorter local foundations; the existing Gamma0 analytic period lattice cannot silently be treated as Gamma1.

The selected [Hecke/Tate polynomial comparison](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_map_eq_charpoly_heckeTLinOne_and_charpoly_tateHeckeRepOne_jOne_eq_map_sq.lean) requires the actual Hecke/diamond-compatible period comparison and finite/free Tate module. A matching characteristic polynomial is not itself realization of the original finite binary-coefficient characters.

The [explicit Gamma1 diamond formula](https://github.com/dozenalist/LeanModularForms/blob/f737ca88e0887ecbaad3510b30e37042c243fd17/LeanModularForms/HeckeRIngs/GL2/HeckeT_p_Gamma1.lean) identifies the infinite coset with a diamond lift followed by the lower diagonal matrix. This is a concrete candidate for the normalization obligation. The [complex character decomposition](https://github.com/dozenalist/LeanModularForms/blob/f737ca88e0887ecbaad3510b30e37042c243fd17/LeanModularForms/HeckeRIngs/GL2/CharacterDecomp.lean) has a different coefficient domain from the finite Artinian characters.

The exact upper/geometric subgroup identification, the native geometric H1 pullback/trace equality and both orders of the original coefficient factor passed separate scratch audits in scopes 627, 629 and 631. Their receipts remain separate from production acceptance. Those proofs remove group and cohomological convention assumptions; actual Picard/H1, full/parabolic and diamond compatibility, finite-character Galois realization, original all-weight association, local/image/regularity and higher continuation remain required.

## Evidence and limits

The [assessment](Tools/reuse-20261026-630/reuse-search-assessment-630.json) records seven live repository heads, fourteen selected verified source files, exact contracts and reuse decisions. The [Gamma1 differential assessment](Tools/reuse-20261026-630/gamma1-h1-geometric-reuse-assessment-628.json) records the two additional fixed-revision files.

All downloaded source files have Git-blob and SHA-256 checks and remain non-Lean text snapshots outside import closures. Repository-wide listings for Anthropic and OpenAI were truncated; the OpenAI number-theory subtree was then retrieved completely at the same frozen revision. Filename/catalog searches are discovery tools, not evidence of theorem absence. One guessed scope-note path returned 404; no mathematical conclusion relies on it.

No external project was compiled and no external transitive axiom closure is certified here. An upstream README or proof file is not local verification. Adaptations require exact source consumers, kernel checks, full dependency audits and the retained sequential verification. No arbitrary finite character is assumed to lift to characteristic zero, and neither a Witt ring nor a universal deformation ring supplies such a point.

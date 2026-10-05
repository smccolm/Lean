# Dependency boundary

## Selected finite exponential-sum closure (5 October 2026)

Lemma 5.1 uses the existing foundation's genuine finite A/B and
Kusmin–Landau inputs, not an assumed exponent-pair object.
`LogarithmicBlockBound` consumes
`RiemannZeta.GuthMaynard.logarithmic_weyl_AB_process_simple` and the
actual correlation majorant. `LogarithmicDerivativeBounds` adapts the
first- and second-derivative prefix proofs from `TerminalTypeI.lean`
(SHA-256 `b72b2d6efd64377a0fd3c1ef3f1bd0e5c5c50862feaedcdfc0a353a09695f018`)
and `TypeIFiniteEstimates.lean`
(`6b89e0df449c2529433e7b0fb2273baa9860fb89a6685729f6c6d67f905f58d5`).
Their proof bodies use the narrow existing derivative interfaces.
Attribution is retained; neither large density/dichotomy import tree is copied
or imported. The new actual-prefix adapter, exhaustive range split,
geometric sum assembly and both signed main consumers compile and are audited.

Origin: existing local node-71 sources, unchanged at checkout
`9247776c9c202f66d3ff6e4ecd60e7370d21a75f`, with original notices retained.
The exact nine-file non-Mathlib closure below was read, rehashed and
integrity-scanned; no foundation source, package pin or license was changed.
The root package already supplies this code; no new vendor or external
repository is installed.

| Source under node 71 | SHA-256 |
|---|---|
| `GuthMaynard/WeylExplicit.lean` | `9b84e618a070b0c83f65258e8d138ed7963d444bf4adc2bbd2f333bcee53185c` |
| `GuthMaynard/Weyl.lean` | `c08762638eecb553ca08ecb15043a5d6e0b085a8fbe5d4811b0a4ca4b2b5798f` |
| `GuthMaynard/SecondOrderMeanValue.lean` | `5ad5b1ad61cbd2e1d4d67a164e04d150bcbe0ffb4f8c05fb5d47841cd69ce134` |
| `GuthMaynard/SecondDerivative.lean` | `fd4d4273961c4cf69806a20ad2348f649b10881f4d334d08322f47cbb11609d0` |
| `GuthMaynard/VanDerCorput.lean` | `2e4b891fe01180ce5eb71c4f1f7be1de1e319470c2ed803b7f92b967b419046b` |
| `GuthMaynard/LogarithmicKernel.lean` | `b5d3eb7ad7dd5c23a8f514c77c971d4259cb197582ea39bfa0433e4b0cfab2c5` |
| `GuthMaynard/DirichletPolynomial.lean` | `d69815e49b69aedced12164e4e1b9bcd81646a7d70b24eb997f7ca2a23aa5a1b` |
| `FiniteDirichletPolynomial.lean` | `5034ffc8cb203907c7d7b935b0714f014b96034a75531f2ac58cf175ae4aa178` |
| `CompletedZetaSymmetry.lean` | `31a1aa9ee8062dd13c80671107dd361bc1587d0ce2a718f880b42278fa49a39a` |

A second route was genuinely inspected: node 63's
`continuous_third_derivative_bound` is a valid all-length finite derivative
test. Its selected 42-file non-Mathlib closure is unnecessary here; the
already-present smaller foundation closure suffices. This is a route-selection
decision, not a failure of that theorem. No node-63/73/74 extension is imported.

## Selected foundation zero-count bridge

`XiConjugation` imports `GuthMaynard.ZeroCount` and consumes the proved
`RiemannZeta.GuthMaynard.analyticVanishingOrder_conj`, not an assumed symmetry.
`ZeroCounts` consumes its actual finite `zerosInRect`, `ZeroRectangle` and
multiplicity-weighted `zeroCountRect`. The local import closure adds only
`ZeroCount.lean` to the previously selected `ZetaBounds.lean`; its other
imports are Mathlib. The exact conjugation proof and rectangle definitions
were inspected. At unchanged checkout `9247776c9c202f66d3ff6e4ecd60e7370d21a75f`,
`ZeroCount.lean` has SHA-256
`e2e6fed5f72d6fb3472315ea7bc48ae5bccf2944094eef057f73b1a51bbd73db`.
No foundation file, dependency revision or source notice was changed.
New consumers are checked explicitly and transitively by the paper audit.

## Scoped real log-norm derivative reuse

`GammaRatioBounds` adapts the two generic norm-square/log-norm derivative
proofs from node 74's `Extension/GafniTao/FordLogNormDerivative.lean`,
SHA-256 `acf639b06147fc26f7e631875128c3136d8e5ea1899d797e7d679565ae926779`.
The exact proof bodies and assumptions were inspected. The adaptation uses
Mathlib only and does not import node 74's Ford detector chain. Gamma
nonvanishing, the actual horizontal derivative, its uniform bound and
source quotient are derived here; no conditional gamma estimate is copied.
`XiRepulsion` uses the already-selected installed Hadamard closure.
All new declarations are explicit and exhaustive audit consumers.

## Selected digamma series input

`GammaLogBounds` imports the installed
`PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries`,
at the same immutable PNT+ revision
`4ecb950126c4290293c5662dfe0e884123171df5` (Apache 2.0; Robby
Sneiderman's retained source notice). Its non-Mathlib import closure is
this one file, SHA-256
`496eb57daedb46fe25b84da2ef885ed68786265a3337d3a739e0f30228f2970f`.
The actual series and inverse-square tail proofs were read and scanned;
no dependency source or pin was changed. The new harmonic head/tail
argument retains coefficient one rather than using the installed coarser
O(log) bound. `ZetaLogDerivativeBounds` uses the already-selected
foundation `ZetaBounds` pole removal and Mathlib's actual von Mangoldt
Dirichlet series. All new consumers are in the exhaustive transitive audit.

PROJECT COMPLETE, 5 October 2026. The isolated extension requires the existing root RiemannZeta package by path, sharing its pinned Lean 4.30/Mathlib/PNT graph and existing package cache. No upstream upgrade or node-63/73/74 import is installed. Root `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` remain unchanged.

The selected graph is the existing Lean 4.30 foundation, not the newer upstream HEADs observed in the 4 October survey. See [Sources](../Dong-Wang-Wang-Zhang%20Sources.md) and [Crosswalk](../Dong-Wang-Wang-Zhang%20Crosswalk.md) for the dated observations and actual consumers.

| Inspected source | Relevant use | Final integration decision |
|---|---|---|
| Root RiemannZeta / node 71 | Continuous Montgomery mean square, zero counts, pole removal and finite exponential sums | `GuthMaynard.MeanValueProof` is now imported for DWWZ-05's actual logarithmic coefficient blocks. The four-file local closure is recorded below; the separately selected zero-count and finite exponential-sum closures are also recorded. No foundation source changed. |
| Node 63 extension and ANTEDBFrozen | A/B and first derivative, logarithmic phases, Euler–Maclaurin | Inspected the finite derivative alternatives; selected the smaller existing foundation closure above. No extension import, energy optimizer or historical Python replay is needed. |
| Node 73 `Tao2026` | Inspected, no relevant reuse for the initial DWWZ-03/05/06 obligation; later quantitative-PNT interface found | Crosswalk preserves both scoped findings. The smaller installed `MediumPNT` closure suffices for the later obligation; no node-73 import was selected. |
| Node 74 `PrimeNumberTheoremAndClean` / installed PNT+ | Entire xi, Hadamard product, zero-divisor convergence, log derivative, gamma | Selected the pinned installed PNT+ Hadamard and digamma closures below, not node 74's separate tree. The scoped Mathlib-only Euler/log-norm proof adaptations are separately attributed below. Node 63's derivative subset does not contain the whole Hadamard tree. |
| Installed Mathlib | Fourier Gaussian/inversion, Cauchy kernel, Mellin, integration, compactness, arithmetic functions, analytic orders | Reuse APIs at the installed pin first; prove normalization and semantic bridges. The half-plane Poisson transform is derived from half-line exponential integrals and Fourier inversion; Cauchy supplies kernel integrability and mass. |
| Current external repos | Discovery and comparison | Newer incompatible toolchains are recorded, not selected automatically. |

Before importing any candidate: inspect theorem hypotheses, prove the actual input adapter, compute transitive axioms, verify all source files in its import closure, record upstream URL/commit/license and hashes, and compile with one chosen Mathlib revision. No reference/Python hypothesis object is proof evidence. A conditional Hadamard algebra lemma does not establish its assumed factorization.

If future maintenance requires vendoring, use an immutable source ledger plus documented patches and license; wire its verifier into the paper BAT. No prebuilt olean from a different toolchain is acceptable. Do not create dependency placeholders or postulates during setup.

## Selected continuous mean-value import

`MeanValueFrequency.lean` consumes `RiemannZeta.GuthMaynard.integral_norm_sq_dirichletTime_le`, not merely the proposition `MontgomeryMeanValue`. It proves exact coefficient/phase and translated-interval adapters for `zetaLogBlock`, then positive/negative frequency-shell estimates and a convergent two-sided tail. This does not import node 63, 73 or 74 or assume an infinite-series bound.

Its later full-series estimate uses a separately proved Gaussian Gram-row argument, the installed Mathlib Gaussian Fourier integral, power-sum/integral comparisons and dominated convergence. All actual derivative coefficient hypotheses are discharged. No further local extension import or pin change was required; the four-file foundation closure below remains exact. Crosswalk records the inspected but unsuitable log-lossy prefix estimates.

Origin: this repository's existing node-71 source at baseline `92f2304f630cbed3b76818a7f649e34b98cea209`, unchanged working files; root package and transitive external revisions remain pinned. The local non-Mathlib import closure is exactly the following four files under node 71, inspected/hashed on 4 October 2026. No code was copied or newly vendored; original source notices remain untouched. The full foundation BAT audited the source graph immediately before this integration, and each new consumer's transitive audit checks the imported theorem's logical dependencies.

| Local module | SHA-256 |
|---|---|
| `GuthMaynard.MeanValueProof` | `293be0eaf515bc16c19a1094790e91e85cdb479a814c9b1be7b995181a0326eb` |
| `GuthMaynard.MeanValueCS` | `56875e88b46c3a7ebf5f763db18c09fafd37096bada88c6c508ea565fcf09115` |
| `GuthMaynard.MeanValue` | `f3c093738c95ecf079d47712cc9a35496e74745a3e65b10de7952a5f9a0975b5` |
| `GuthMaynard.Separated` | `09474ad6fc1b196cfe50eb9495aa5bb4afc3f3e5c395c5619e4c0e77fe0c665f` |

## Scoped Euler-log proof adaptation

`MeanValueEuler.lean` adapts the short summability/real-log entry from node 74's `Extension/GafniTao/FordEulerProduct.lean`, inspected on 4 October 2026 with SHA-256 `841a81d0f29940e8a75fc3b63444348c735888df3deba59c9f05ec7a848e8dce`. The useful inputs are `summable_fordEulerZetaLog` and `log_norm_riemannZeta_eq_re_fordEulerZetaLog`; their proofs use installed Mathlib directly. Attribution is retained in the new module header. No node-74 source, package, prebuilt artifact, Fourier-kernel chain or separate PNT graph was imported or changed. The adapted declarations and all new finite-distance consumers are covered by the node-77 transitive audit. The foundation closure above and all package pins remain unchanged.

## Selected installed sieve closure

`MeanValueSmoothing.lean` imports `PrimeNumberTheoremAnd.BrunTitchmarsh` and consumes the proved `BrunTitchmarsh.primesBetween_le`: for `a,h>0`, `z>1`, the prime count in the closed interval `[a,a+h]` is at most `2h/log z + 6z(1+log z)³`. Exact finite-set adapters, quartic-cell logarithmic weights and Mathlib's higher-prime-power bound discharge the actual von Mangoldt input. No strong-PNT/Dusart statement is imported or assumed.

Origin: [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd), installed immutable revision `4ecb950126c4290293c5662dfe0e884123171df5`; Apache 2.0, Arend Mellendijk's retained source notices. The non-Mathlib/Batteries closure is exactly six files under `PrimeNumberTheoremAnd/`, inspected and integrity-scanned on 4 October 2026. No dependency source or pin was changed or copied. New consumers' exhaustive transitive audit checks their logical dependencies.

| Installed source | SHA-256 |
|---|---|
| `BrunTitchmarsh.lean` | `7d237fc88f4888df0ebf812fd59a8785605c0a4324ac91675d8b265ce2103317` |
| `Mathlib/Analysis/Asymptotics/Asymptotics.lean` | `a8f83ac3b8417fcf30e75b639a0ee226946be6ccae0566b61046fd0008ea0d17` |
| `Mathlib/NumberTheory/Sieve/AuxResults.lean` | `76dbd12c7720520e30740604a382afa0681498f2f9b80da5185034841b545c38` |
| `Mathlib/NumberTheory/Sieve/Basic.lean` | `cc28fc5af07f94e7169f76b26d51454f15e76cae2955006b148688bdbe7cc810` |
| `Mathlib/NumberTheory/Sieve/Selberg.lean` | `2dfccc1eba69f38601bc62b90f6704c0c831c55d03db873ecbd6fcdcf87ca61d` |
| `Mathlib/NumberTheory/Sieve/SelbergBounds.lean` | `941f481d0979f47ac776e138c8e1f01b25d2798bfbb606c8a0c584325c5e96d1` |

## Selected foundation pole-removal bridge

`RegularizedTransform` imports the existing `GuthMaynard.ZetaBounds`,
consuming `RiemannZeta.GuthMaynard.differentiableAt_regularizedRiemannZeta`
and its actual update definition for analytic continuation of the genuine
power-sum remainder. The foundational proof and exact definition were inspected.
Source SHA-256:
`16025d55a44e0b7d0950f8c2e1941ba212b6a3f2eedafcd21b239ef7e151e94c`.
This is part of the unchanged, fully verified foundation graph; no source was
copied or modified. Gaussian integration and Mellin convergence use installed
Mathlib. No new external package, pin, or node-73/74 import is needed.

## Selected installed xi/Hadamard closure

`XiZeros` and `XiLogDerivative` import the installed
`PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard`.
The actual entire function, divisor index, analytic multiplicities,
genus-one convergence, polynomial factorization and logarithmic-derivative
theorem interfaces were inspected. Their 61-file non-Mathlib closure was
resolved recursively, integrity-scanned and hashed on 4 October 2026;
the static scan has no prohibited proof-word or postulate matches.
This is a source-integrity check, not a substitute for consumer axiom audits.
The new public consumers are included in the explicit and exhaustive audit.

Origin: the installed PNT+ repository and immutable revision
`4ecb950126c4290293c5662dfe0e884123171df5`, Apache 2.0, with
the existing Matteo Cipollina and other source notices retained.
No source, package pin, node-74 dependency or copied tree is added.
The separate unfinished `IEANTN.Kadiri` source is not in this closure.

| Installed source under `PrimeNumberTheoremAnd/` | SHA-256 |
|---|---|
| `Mathlib/Algebra/Order/Floor/Ring.lean` | `ed988de74566299d2c7a6c5ffb355fe0cfc371e1e66feba2275344e89ac4aee1` |
| `Mathlib/Analysis/Calculus/Deriv/Polynomial.lean` | `8eff3e21a29594c9a9871c80be267e8a3a1cbd08ed81a8961c37fa5d3dfe5e84` |
| `Mathlib/Analysis/Complex/AbsMax.lean` | `da8b5a8fcd63742285c31c124dee1472ac444a90ae78971f9945310ca68d8b91` |
| `Mathlib/Analysis/Complex/Basic.lean` | `23a01f0c7fb9481c810059aacd24ae231d30f33113a20e11df9db1def06017e6` |
| `Mathlib/Analysis/Complex/BorelCaratheodory.lean` | `b832015713b70e4f438800a1378a1945859d0fc86516c91581ecfff508df0bae` |
| `Mathlib/Analysis/Complex/CanonicalProduct.lean` | `075c48f65669c6ea2b523444db226ed7e39c57bfb9ed1ba929351c074495bfbf` |
| `Mathlib/Analysis/Complex/CartanBound.lean` | `1756268c79f95853132113163012fd7dd5cfd6aa68691fc19cf45003f3225098` |
| `Mathlib/Analysis/Complex/CartanInverseFactorBound.lean` | `08939b163ac8054624d109298c7a7cac6fd153483b2672e6ea75bed4a939c506` |
| `Mathlib/Analysis/Complex/CartanMajorantBound.lean` | `e48060bc3e34098ad5e583016b85ad32a6464a56640cff194aee2a30bc655567` |
| `Mathlib/Analysis/Complex/CartanProductBound.lean` | `d0f1f9dfcd398cf9f45e7a6213d77bed011f3fdb888ae359e6a3bd4fbaf22caa` |
| `Mathlib/Analysis/Complex/Convex.lean` | `ce749ad213493a42f5933567e53b54db01b7d1949da1ef5537dff90dd90b7ad9` |
| `Mathlib/Analysis/Complex/Divisor.lean` | `6706b2d880571f5820119265e09102d8f3a7b58bbe2f6c0d154f6f8ef5e5d19d` |
| `Mathlib/Analysis/Complex/DivisorComplement.lean` | `3b7f922c0f972ab29876c7b8d4fdb7548171402e2b2c78bc23113e199f2544b4` |
| `Mathlib/Analysis/Complex/DivisorConvergence.lean` | `407eec989ceae3a390f88e7533e4863adc07ba385509e64dde028baa13db74ae` |
| `Mathlib/Analysis/Complex/DivisorFiber.lean` | `f8170ad7fe24acd8dc93b3a45424ec6523e86c4ca36581620487b1df3ac29930` |
| `Mathlib/Analysis/Complex/DivisorIndex.lean` | `78faa8f7322448b2f333c2cc9daff54659a8291713d436069444582c004e2d3b` |
| `Mathlib/Analysis/Complex/DivisorPartialProductFactor.lean` | `e059e79a29b7062d09871bb076b14aade21f47d3c5d7c40fd4c5b9fe67542bfb` |
| `Mathlib/Analysis/Complex/DivisorQuotientConvergence.lean` | `6aa2a384e1156a87f8c2255ff801e0994c6ba6620dd2940abb975b673dde12e2` |
| `Mathlib/Analysis/Complex/DivisorQuotientRemovable.lean` | `30bf98246b34b998f8c6e7031c61f738deb1618a43e6d2ee9b9c8e38b53b1e79` |
| `Mathlib/Analysis/Complex/DivisorUnits.lean` | `05b6de0e3dce6049c7e84256947852488a5c160692b98fbd6f1f56ff9d93757f` |
| `Mathlib/Analysis/Complex/ExpPoly.lean` | `b8e5d95152de45a3639bae8a87d1be00df24688c522ad53290812c2cbd86db9c` |
| `Mathlib/Analysis/Complex/ExpPoly/Growth.lean` | `1911c5a0052db643cad01b0e42d4e0b2f8eae5cee021ad715c215ca42b6e8bb9` |
| `Mathlib/Analysis/Complex/HadamardFactorization.lean` | `4043d5775a85c320c2cb0c0b68594e712d0036f3b5fec4586c55e662ff24b152` |
| `Mathlib/Analysis/Complex/HadamardFactorization/Growth.lean` | `bdb71e7a07cb47d7a07c292087ffbe6239536071d1851b35541eebe3a82ca201` |
| `Mathlib/Analysis/Complex/HadamardFactorization/Order.lean` | `9998273a21da542d4bb19011ff0d635036db993226d5ff1615e8fe6788dd7af8` |
| `Mathlib/Analysis/Complex/HadamardFactorization/Summability.lean` | `360eba3aae2672c6f13be2f346278f0602212df387b500a6e5efa1fa2720413e` |
| `Mathlib/Analysis/Complex/LocallyUniformLimit.lean` | `04c514b4fe245b18f0c44273c6f7429b86a6236d4db2ce674172d225477e33c1` |
| `Mathlib/Analysis/Complex/Norm.lean` | `b44b8cadedb91b616299c50c8714e8ef613afa5a6f96ee0df9ba7e5a086de048` |
| `Mathlib/Analysis/Complex/Trigonometric.lean` | `39e64a7a11c1fbc1e59010f466bfdb0cbfcfe996871effe5b53f271657e0abdd` |
| `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Basic.lean` | `21f5185452a9fd32b0aed76ff4aac196cddde52532ed169f5c2f1457050ca4a9` |
| `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Growth.lean` | `6a382da50bea09ef4cd0dc4d441c49ea4362bdbbff105657d851b923f66eb30f` |
| `Mathlib/Analysis/Complex/WeierstrassFactor.lean` | `16e40f1fe027c910eac31b328d2ebb4a8338fd15782fc3b42f60ea50ffdf6fea` |
| `Mathlib/Analysis/Meromorphic/DivisorHolomorphic.lean` | `22d19bbd1edb63a1faf723851bb9a2e5fa461ff663d7dafb3b09f192deb16302` |
| `Mathlib/Analysis/Meromorphic/DivisorSupport.lean` | `9af62e515bff9e1d895a0f75c2914ec9e579cf3712cceb47c5d0d78b190b048a` |
| `Mathlib/Analysis/SpecialFunctions/CompletedXi.lean` | `3eb5e595e742b223cfb7798ceb788e47311d01a1d3f992565231f1c747dd539d` |
| `Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean` | `5bde9b84b5aca0a1965ace3e8e387ff02a61066636c9ed1748292ee1cc8ea43a` |
| `Mathlib/Analysis/SpecialFunctions/Exp.lean` | `42a7d3f7376530f77c7341c322f0d8609b021336cd81cdee15a970a6cf81abcd` |
| `Mathlib/Analysis/SpecialFunctions/Gamma/GammaStirlingAux.lean` | `5cbb404b1d2cd2ecbe76b60ea750c2250bac2dbc4f3e206495bef5b675cad889` |
| `Mathlib/Analysis/SpecialFunctions/Gamma/IntegralBounds.lean` | `55b832dd199a1d573e62ba198b3433f42f5122d0ce1f68d79c67f84374e3e479` |
| `Mathlib/Analysis/SpecialFunctions/Gamma/StripBounds.lean` | `d806b8627c51565b5789fabcfd8f4f47b13163a30ce17a1ed27aa43c1a114d8f` |
| `Mathlib/Analysis/SpecialFunctions/GammaBounds.lean` | `9539a8730e6bf7f39ddc3b4922c9afd06c7780089390692b282af9257099d6b3` |
| `Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean` | `41e0bbf0a5a166dd11352909a099224d1f8dd1259fafad1ac90f4d308c510ceb` |
| `Mathlib/Analysis/SpecialFunctions/Log/Dyadic.lean` | `593c1ccef432d1534575dc1cdfc210c849b306f6af66e42af66e239e41959e72` |
| `Mathlib/Analysis/SpecialFunctions/Log/ExpGrowth.lean` | `c2b015a7bf66f881f5e3130fe53dd1e6aae8148657825063648fc8487e853f05` |
| `Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean` | `78de8bc060bdc5444a3b2a38487c988a84b4eef4e59371cf6c8cf24f999086a8` |
| `Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean` | `a9ab562e01fdcab3c3e6fa7142675bcda12746eddaaf553dc7679ed13a442ec4` |
| `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` | `5d12650c550c7b17e59024d68ff7158e20085475e3e6b3306309fa358c071901` |
| `Mathlib/MeasureTheory/Integral/IntegrableOn.lean` | `509e1697ecc74a648e212a3e4cff8f1266ce1b54bae65d87a1981ca57068bfb0` |
| `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` | `236fccabc22d608435822943092ff6a9c46e10cb85ed91d2a7f1cf9273db2d35` |
| `Mathlib/NumberTheory/AbelSummation.lean` | `17da4226229aab82587b90590f9888a88e3dc7ec004236870946bff4238eaa9b` |
| `Mathlib/NumberTheory/LSeries/RiemannZeta.lean` | `11331a4fa066a40a08692bcc548ebc428edf31bdf6b20245de8efa670080b1f7` |
| `Mathlib/NumberTheory/LSeries/RiemannZetaAbelContinuation.lean` | `969f12781228fddbfd2f7a735736e2c63250d8abe1816fca14564469b130042c` |
| `Mathlib/NumberTheory/LSeries/RiemannZetaAbelKernel.lean` | `01453da9eaaf3f372f11ac4a132461f20d58843b9772bcc87796008d3aa4fd6d` |
| `Mathlib/NumberTheory/LSeries/RiemannZetaConvexity.lean` | `f698f7aeba383bece9556ebfe08bfba0539aa2333250c57b64f23f489e57c50a` |
| `Mathlib/NumberTheory/LSeries/RiemannZetaHadamard.lean` | `a7bf1278a435bae113ef4659f8864e6137afce631c23796eab7fbf58587574d8` |
| `Mathlib/NumberTheory/LSeries/RiemannZetaPartialSum.lean` | `1c107ee0e141e4f6032a00ce55ce148cb274305eb976260ab410d6f47562b30d` |
| `Mathlib/NumberTheory/LSeries/RiemannZetaStripBound.lean` | `479c1c2d5393834c723f324021f5aed0fa748c492bc7295382e194a8a716c831` |
| `Mathlib/NumberTheory/LSeries/RiemannZetaValues.lean` | `e6025a1516b92afb9eba7b83e924cf1a551da53a2b87c8f6b38fc2b6956eb37d` |
| `Mathlib/NumberTheory/LSeries/ZetaFiniteOrder.lean` | `0528ca717a96f3688b9235eb3abf1f1dd3ed485187719804b5ba7bcd77b54a72` |
| `Mathlib/NumberTheory/LSeries/ZetaFunctionalEquation.lean` | `2bb0fff76d7958e199a57ba5b915ab2384589576f8fe9df77ca76d633650f9a5` |
| `Mathlib/Topology/MetricSpace/Annulus.lean` | `36ffbaee44341b00072be2e1520a65e8fa43e750afb0b550e9846d1e297f5a98` |

## Selected installed zeta continuation interfaces

`ZetaUniformBounds.lean` consumes global `Zeta0EqZeta` and
`ZetaBnd_aux1b` from installed `PrimeNumberTheoremAnd.ZetaBounds` for
DWWZ-07. Their actual finite polynomial, displayed pole and integrable sawtooth
remainder yield the uniform bound with constant 8. Both interfaces were read;
the file and its import closure are already included in the pinned, hashed
fourteen-file closure below. No new package, copied source or node-74 import is
needed. The new public consumers are explicitly and transitively audited.

## Selected installed quantitative PNT closure

`TwoPointEuler.lean` consumes the proved global declaration `MediumPNT` from installed `PrimeNumberTheoremAnd.MediumPNT`: for some `c>0`, `ψ(x)−x = O(x exp(−c(log x)^(1/10)))`. Mathlib's explicit prime-power error then gives every fixed logarithmic saving for the actual `θ`. Exact Abel summation supplies the reciprocal-prime cosine estimate; this is an actual analytic input, not a PNT premise left to a caller. The installed strong-PNT/Dusart declarations remain unused.

Origin, immutable revision and Apache 2.0 license are the same installed PNT+ source recorded above. The fourteen-file non-Mathlib/non-Architect closure below was read, hashed and scanned on 4 October 2026; no source or pin changed. The only shortcut-word matches were explanatory comments, including a tactic documentation example, not proof declarations. The upstream `#print axioms MediumPNT` reports only `propext`, `Classical.choice`, `Quot.sound`; the node-77 consumers are additionally checked transitively by the paper audit.

| Installed source under `PrimeNumberTheoremAnd/` | SHA-256 |
|---|---|
| `Auxiliary.lean` | `f4b6b2851f89deda28534ad62530ac93d0329305f540d8fd0a9f5b9461fd6264` |
| `EulerMaclaurin.lean` | `7dc051811ddf8b4145e786df5608bc1101218e92361303653465013512852092` |
| `Fourier.lean` | `d7d081528b063f3ab34f4dcae472ea37fe22084376ced2900281c19b762aa04a` |
| `Mathlib/Algebra/Notation/Support.lean` | `8ec01fd3819facd671ae75a435c4b041f50cc305347538ba74c1435b69fee68e` |
| `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | `1275fb3b99aa12a2172e18e166fbcec8513f56e289da459fc84b9e2144e3b705` |
| `MediumPNT.lean` | `b40703d7f79d49ec7a76fbdc43fa37f2b39b100d3fb13699061f2d18be0d09ee` |
| `MellinCalculus.lean` | `14bb47c7be0c53657c8d65a53182bfd6cb0f881c55ca3e164e47e0680bd72e4a` |
| `Rectangle.lean` | `aec62e403b44f2b9571fdab61af7d11654aebac05b19bf14eb16b8161bf72099` |
| `ResidueCalcOnRectangles.lean` | `6096645d82e3e59a308de3d607961943f074c37cda1231c90ceb2387f33aff14` |
| `SmoothExistence.lean` | `bc5417331d50aa5f38081b28725c987932fe7ae7aa6819aa6f230872ae5d39ac` |
| `Sobolev.lean` | `104d4f63ec9013f8e4fffca42aed89b572ba67d60fb085df50ff5747c613a84a` |
| `Tactic/AdditiveCombination.lean` | `19638f18c7d69086a78fb9ba89a6e7e6f717aef5440246f77fd3ecdf1fcb4d5b` |
| `ZetaBounds.lean` | `ce11ab520c7cd2661cc757fa1f0ee149888cce9c7a8e4a99f47d021639da841c` |
| `ZetaConj.lean` | `d66d1541de62879afece693350140a430c2a3ad126d82c7147b51a4ee3af47a9` |

Later scoped node-73 inspection found the relevant, stronger `Tao2026.classicalChebyshevPsiDeLaValleePoussin_native` in `ClassicalQuantitativePNT.lean` (SHA-256 `9fe0acbc87d4ffbae5f70e618d418ac906b7e5fb6d441a197a943e9552be26bf`), with its definition in `QuantitativePNTBridge.lean` (`d4e3b1415469426a99091dc3e5b1eeaed1a3caade51042dcfaf0dfd29f2be3e7`). It proves eventual `|ψ(x)−x|≤Cx exp(−c√log x)`, but its much larger frozen analytic import closure is unnecessary: the smaller installed `MediumPNT` is sufficient. Thus no node-73 import was selected. This later positive interface finding is distinct from the initial scoped “inspected, no relevant reuse” survey.

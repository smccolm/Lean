# Dubon semantic acceptance records

These records distinguish exact source acceptance from compilation and helper counts. DUB-01–15 are accepted after exact source reviews and sequential verification on 6 October 2026. DUB-16 is additionally accepted after exact source review and sequential verification on 7 October 2026. DUB-17–20 remain OPEN. This file does not certify the complete paper.

## Verification shared by the accepted gates

The [369-module receipt](Dubon%20Reproduction%20Manifest.md) records foundation PASS followed by paper DEVELOPMENT PASS, both exit 0 with zero Lean diagnostics: 369 production modules, 146 exact source consumers, 1,778 explicit audit registrations and 3,254 exhaustive theorem checks. Sixteen linters passed. No Lean source, import, toolchain, dependency, audit or runner changed during the acceptance review; only source-review records and gate/document metadata were added. The pre-acceptance log correctly records 0/20 gates at its execution time. Current gate counts are checked separately by the inventory verifier.

## DUB-01 — Source review and frozen contracts

**DONE.** The [source acceptance review](Dubon%20Source%20Acceptance.md) and [individual label/bibliography ledger](Tools/source_acceptance_20261006.json) cover the complete frozen TeX, exact primary PDF contracts, all 139 labels, all 25 bibliography entries and DUB-E01–E08. No source bytes or acceptance clauses changed. E07 is resolved as a retained downstream arithmetic obligation, not a claim to have proved Rankin–Selberg, Deligne, Sato–Tate or the automorphic bridge. This is a documentary source gate and introduces no vacuous Lean theorem.

## DUB-02 — Actual Dirichlet polynomials and support

**DONE.** Reviewed the complete statements and proof bodies in `DirichletPolynomial` and `DirichletZeros`, and the following exact source consumers in `SemanticRegression`:

- `positive_index_foundation_source` and `principal_power_source` identify the literal sum over `Finset.Icc 1 N`, its principal complex powers and the actual `RiemannZeta.dirichletPoly` with the proved positive-natural index adapter. Index zero never enters the source sum.
- `actual_support_maximum_source` proves that the real filtered support has a largest nonzero index M_N between 1 and N and bounds every nonzero coefficient index by it. The theorem uses a₁≠0, which includes the paper’s a₁=1, and N≥1. Empty truncations are explicitly totalized outside that source domain.
- `entire_truncation_source` proves analyticity of the actual sum through its exact exponential representation. `tendsto_dirichletSum_real` proves its limit a₁ at positive real infinity, so nontriviality is derived rather than supplied as a conclusion-equivalent hypothesis.
- `finite_analytic_multiplicity_source` identifies the natural multiplicity with the genuine analytic order and proves that the order is not top. The identity theorem supplies this bridge. `zeroMultiplicity_local_factorization` identifies the corresponding local analytic factor.
- `actual_zero_rectangle_source` unfolds the real zero set with open real-part and symmetric open-height bounds. Finiteness is derived from entire nontriviality and compactness. `multiplicity_weighted_count_source` is the literal finite sum of actual analytic orders; it is a definitional count identity, not a zero-density theorem.

The actual source polynomial, support, entire function and multiplicities are consumed directly; there is no arbitrary polynomial, zero-set certificate, finite-set hypothesis or assumed count limit. The required foundation adapter and all public proof dependencies occur in the root build and explicit/exhaustive audit. DUB-01 is accepted upstream. Density, Jessen and concentration conclusions belong to later gates.

## DUB-03 — Prime factorization and Bohr flow

**DONE.** Reviewed complete proof bodies in `BohrLift`, `PrimeFrequencies`, `SymmetricAverage`, `PrimeTorus`, `TorusEquidistribution` and `TorusPolynomial` against Proposition 3.1 and the displayed finite Bohr lift.

- `PrimeCoordinate N` is literally the primes ≤N; `bohrMonomial` uses natural-number prime factorization. `prime_exponent_vector_injective` and `primeExponent_injectiveOn` recover actual integers in 1..N from their vectors. The outside-coordinate factorization is proved zero.
- `prime_log_integer_independent` separates positive/negative integer exponents into actual nonzero natural products, uses injectivity of the real logarithm on positive numbers, and compares prime valuations. `trivial_prime_resonance_source` exposes the exact zero-resonance conclusion.
- `bohrLift_verticalFlow`, `fourier_one_primeTorusFlow` and `bohrOnTorus_verticalFlow` prove the negative-frequency identity with the actual complex-power Dirichlet sum. `bohr_vertical_substitution_source` unfolds both sides; the torus coordinates and truncation length are linked throughout.
- `torusHaar` is the actual product of normalized circle Haar probabilities. `haar_probability_source` exposes total mass one. `mFourier_primeTorusFlow` retains the 2π normalization and the integer logarithmic frequency sum.
- `norm_symmetricAverage_exp_le` proves the oscillatory integral bound and `tendsto_symmetricAverage_exp_zero` derives its limit. `tendsto_torusAverage_mFourier` consumes the proved nonresonance. Uniform norm-one averaging bounds extend this through the dense Fourier span to every continuous torus test.
- `continuous_torus_test_source` has the literal symmetric `(2T)⁻¹` vertical integral and normalized Haar limit. `continuous_polynomial_test_source` composes that theorem with the actual Bohr polynomial and consumes the proved vertical identity. `denseRange_primeTorusFlow` derives density using full support of Haar measure and a separating continuous function; it is not assumed.

No independence/equidistribution premise is hidden in a structure. These are continuous-test statements; they do not claim to integrate the singular logarithm. DUB-02 is accepted upstream, and DUB-04/05 own the remaining logarithmic review. All listed production modules and exact consumers are included in the 369-module dependency and linter evidence.

## DUB-04 — Torus logarithms and Jensen bounds

**DONE.** Reviewed all statements and proof bodies in `CirclePolynomialLog`, `MultivariateBohrPolynomial`, `TorusPolynomialLog`, `TorusEnergy` and `TorusJensen` against Lemma 3.2 and Proposition 3.6, including their literal displayed energy and normalized Haar measure.

- `multivariate_log_integrability_source` consumes an arbitrary nonzero finite-variable complex polynomial. Zero-set nullity is proved separately by induction over circle coordinates: outside the null zero set of the nonzero leading coefficient, the one-variable fiber has finitely many zeros. This avoids treating Lean's totalized `Real.log 0` as a proof of nullity.
- One-variable logarithmic integrability and Jensen bounds use Mathlib's actual Mahler measure, with the unit-period Haar measure and angular factor `1/(2π)` identified explicitly. The multivariate proof derives integrability of the absolute logarithm through the fiber estimate `2C − log|leading coefficient|`, induction and Fubini. It does not merely assume an integrable dominating function.
- `actual_bohr_polynomial_source` identifies the genuine prime-factorization polynomial and proves its constant coefficient is a₁. `actual_haar_log_integrability_source` applies the general theorem to that polynomial, deriving nontriviality from N≥1 and a₁=1.
- `quadratic_haar_energy_source` uses injectivity of the actual prime-exponent vectors and Fourier orthonormality to obtain exactly `Σ_{1≤n≤N}|a_n|² n^(−2σ)`. `normalized_haar_log_bounds_source` applies iterated constant-coefficient Jensen for the lower bound and the pointwise inequality `log x ≤ x−1` for the upper bound. All required integrability and positivity premises are derived. The result is the actual Haar bound; `actual_jessen_mean_source` supplies its identical vertical-Jessen formulation after DUB-05's mean identity.

DUB-03 is accepted upstream. The null-set convention, finite-variable domain, normalized probability measure, energy indices and factor one half agree with the source. No logarithmic-integrability, orthogonality or desired-bound certificate remains as an input.

## DUB-05 — Actual vertical Jessen identity

**DONE.** Reviewed all 24 registered production modules for this gate, their complete proof bodies and the exact consumers `vertical_log_integrability_source`, `truncated_vertical_then_haar_source`, `actual_uniform_log_tail_source`, `actual_jessen_mean_source` and `bohr_jessen_proposition_source` against Proposition 3.3. The source's appeal to classical almost-periodic logarithmic-mean and convexity theorems is replaced by proved finite-polynomial arguments.

- `LogTruncation` proves finite-interval logarithmic integrability from actual analyticity, vertical zero-set nullity from the discrete nontrivial zero set, continuous-test convergence for every positive truncation, and Haar convergence as the threshold decreases to zero. The majorant is the already integrable absolute logarithm off its proved null zero set.
- `VerticalFamily`–`CompactJetCover` keep the original coefficients, prime phases, real abscissa and vertical variable linked. Nonzero finite jets follow from the analytic identity theorem and a₁≠0. Compactness yields finitely many derivative patches over all phases and a unit height interval; a patch is data whose required inequalities are proved, not assumed analytic input.
- `HigherRolle`, `InterpolationDerivative` and `SublevelCover` derive the spacing and measure estimate by repeated Rolle, actual Lagrange interpolation and a finite interval cover. `UniformVerticalSublevel` chooses K, η and C before all phases and small-value parameters. Layer-cake integration in `LogDeficit` gives exponential logarithmic tails; phase translation and a proved unit-interval averaging bound extend them uniformly to every T≥1.
- `JessenMean` uses this uniform error together with the truncated equidistribution theorem to prove both sides of the full untruncated height limit. `jessenFunction` is literally `limUnder atTop` of the symmetric vertical logarithmic mean, and its equality with the finite real Haar integral follows from the proved limit. No height limit or uniform-integrability premise remains.
- `TorusGridCharacters`–`TorusGridLog` prove uniform convergence of finite product-grid averages for continuous torus functions. `TwistProducts`–`HaarChord` apply Hadamard three-lines to actual finite products of prime-twisted Dirichlet polynomials, deriving strip boundedness and boundary estimates. Their Haar log integrals are exactly the number of factors times the original potential. Removing both endpoint truncations yields the chord inequality. `JessenConvexity` proves convexity and continuity on all ℝ.

The public Proposition 3.3 consumer has only the source polynomial, N≥1 and a₁=1 as inputs, and returns convexity, continuity, every fixed-σ symmetric height limit and its exact normalized Haar identity. The underlying mean and convexity theorems allow the weaker a₁≠0. DUB-04 is accepted upstream. This gate does not certify any zero-frequency or modular conclusion.

## DUB-08 — Bessel characteristic-function inputs

**DONE.** Reviewed complete proof bodies in `CircleCharacteristic`, `CircleMoments`, `CircleGaussian`, `CircleSeries`, `BesselJ0`, `CircleQuarter`, `CircleOscillation`, `BesselDecay` and `CircleRadial`, the actual foundation nonstationary-phase adapter, and both exact consumers against the five registered J₀ source displays.

- `besselJ0` is the literal factorial power series. Two genuinely summable complex exponential series are integrated termwise against normalized circle Haar measure; Fourier orthogonality keeps exactly the diagonal coefficients. `bessel_series_integral_bounds_source` states convergence and the exact `1/(2π)` angular integral for every real argument.
- Half-period translation proves the integral is real. Its modulus is ≤1, and strict inequality for every nonzero argument follows from strict convexity plus the fact that the circle exponential cannot be constant; the latter is proved by its nonzero derivative at π/2. Full support upgrades almost-everywhere constancy where needed.
- The exact second moment is 1/2. Elementary cosine inequalities give the source small-argument bound with explicit admissible choices u₀=1 and c₀=1/π². Splitting a quarter-circle integral at `1/(2√u)` and consuming `ZetaAppendix.nonstationary_phase_integral_bound` gives `|J₀(u)| ≤ (4+1/π)u^(−1/2)` for every u≥1. The phase derivative, its nonvanishing, inverse-derivative continuity and monotonicity are all discharged for the actual cosine phase.
- `circle_radial_fourier_source` proves both conventions on the actual uniform circle law: positive-sign characteristic function at c|ξ| and negative-sign `2π` Fourier transform at `2πc|ξ|`. Rotation is a proved Haar translation, not an assumed radial law.

DUB-01 is accepted upstream. These statements realize all required absolute constants and parameter ranges without using unrelated K₀/Y₀ results. The translated sum and one constant uniform in its dimension and translation remain DUB-09's separate acceptance obligation.

## DUB-09 — Translated Steinhaus logarithmic bound

**DONE.** Reviewed complete statements and proof bodies in all 26 registered modules, from `SteinhausLaw` through `SteinhausLog`, against Lemma 4.1 and all three-region, Fourier-density, small-ball and logarithmic displays in its proof. Reviewed the exact consumers `actual_steinhaus_law_source`, `uniform_steinhaus_planar_L1_source`, `uniform_steinhaus_density_smallBall_source`, `translated_haar_steinhaus_log_source` and `translated_independent_steinhaus_log_source`.

- The real probability measure is the pushforward of the finite product of normalized circle Haar measures under `Σ bᵢZᵢ`. The characteristic function is proved to be the product of the actual J₀ values. The scale is literally `sqrt(Σbᵢ²)` and the comparability assumption is the actual finite maximum divided by minimum. Positivity, unit normalized energy and both `1/(K√m)` and `K/√m` bounds are derived.
- The three radial regions have exactly the source cutoffs with u₀=1 and R=(4+1/π)²+1. Gaussian integrability, the compact Bessel gap, the finite bound on mρ^m, and the exact power-tail integral are proved before assembly. The tail denominator m/2−2 is positive for every m≥5, and m/(m/2−2)≤10 yields one bound independent of dimension. The actual planar polar factor is 2π. `exists_uniform_steinhaus_charFun_L1` chooses its constant using only K.
- The inverse integral uses `(2π)⁻² exp(−i⟨x,ξ⟩)`. Gaussian convolution, its limit, positivity, and agreement on all compact continuous test functions prove equality of the original measure with this continuous bounded density. The density identity is not a structure field or an assumed inversion certificate. Planar ball volume gives the bound simultaneously for every translation and every radius r≥0, and absolute continuity proves translated zero-set nullity.
- Layer cake proves integrability of the negative logarithm from the actual small-ball estimate. The finite sum bounds its positive logarithm for each translation. The proof uses the sufficient bound `C exp(−t)` on the tail for t>0, instead of optimizing the source's `min(1,C exp(−2t))` integral; this gives a larger constant depending only on K and preserves the source conclusion. The scale identity is applied away from the proved null set to restore `log S`.
- `independent_steinhaus_sum_law` proves the joint-law/product-law bridge from actual independence and the literal uniform circle marginal. The final consumer returns integrability and the lower expectation bound on every probability space, for all dimensions m≥5, positive K-comparable coefficient vectors and complex translations, with the existential constant quantified before all of these data.

DUB-08 is accepted upstream. No density, small-ball estimate, logarithmic integrability or conclusion-equivalent premise is assumed in the source consumer. Measurability, independence and the uniform marginal are precisely the source's random-variable hypotheses. The theorem does not restrict to the centered sum or a fixed dimension.

The new DUB-04/05/08/09 acceptance uses the later sequential foundation and paper receipt below, after the inactive-template fixture repair. Both runs returned exit 0 with zero Lean diagnostics and the same 369-module proof scope. The paper log records 3/20 at execution; the subsequent documentary acceptance brings the registry to 7/20. No Lean source or audit changed between these runs and the acceptance.

## DUB-06 — Vertical zero frequency with multiplicity

**DONE.** Reviewed the complete proof bodies of all 108 registered production modules against Proposition 3.4 (`prop:JT-density`, frozen TeX lines 543–578), and the actual finite-count, twist-count and all-endpoint consumers in `SemanticRegression`. The final `jessen_tornehave_nonzero_source` uses N≥1 and a₁≠0, the literal finite sum of analytic orders over Re(s)∈(l,u), |Im(s)|<T, and normalization 1/(2T). Its limit is (J′(u−)−J′(l+))/(2π) for every l<u. Neither endpoint non-atomicity nor finite-height boundary nonvanishing remains a premise.

- `DirichletDivisor` and `RectangleZeroCount` identify the actual entire polynomial's analytic order with the divisor used by the foundation argument principle and with the finite multiplicity sum. Zero-free half-planes and dense usable boundaries follow from actual dominant terms and the countable discrete zero set. Jensen's formula, a uniform positive center and compactness of the genuine twist family give a uniform unit-window multiplicity bound. Height translation preserves analytic orders; bounded unit increments transfer selected-height limits to all real heights.
- The real exponential-sum Rolle argument bounds horizontal crossings. The half-plane logarithm argument bounds each sign interval, yielding a fixed-N horizontal contour error O(2^N/T). Finite-height derivatives are actual log-integral derivatives on zero-free segments. Local finite-jet covers, sublevel bounds and logarithmic tails prove continuity through zeros. Finite exceptional abscissae and convex secants then identify the selected mean-motion limit. Dense regular abscissae and derivative/atom identities give the atom-free strip result.
- The remaining endpoint argument uses the actual torus observable, never an assumed root-count certificate. A zero-free inner rectangle captures every original interior zero; continuity of its contour integral makes that integer count locally constant. Thus the open-rectangle count is lower semicontinuous and measurable. Sliding-window translation and finite indicator integrals give its vertical mean with a uniformly bounded collar error. Haar stationarity, Fubini and shrinking-height estimates prove almost-everywhere horizontal boundary nonvanishing.
- Actual complex phase coefficients extend analytically. Compact Banach-algebra inversion on a zero-free contour gives analytic weighted contour integrals. Residues identify them with multiplicity-weighted powers of the actual zeros; Newton identities identify the coefficients of their genuine zero polynomial. Restricting to a vertical line and multiplying by the conjugate polynomial gives a real polynomial whose real-root multiplicities are exactly twice the analytic zero multiplicities.
- The full Sturm proof, signed Euclidean chain, separable quotient and derivative-GCD layers were reviewed. They derive the open-interval multiplicity count, including its endpoint correction. Bounded Euclidean division and almost-everywhere analytic sign/degree stability give almost-everywhere local constancy of this actual count. The torus phase quotient and Haar transfer preserve the null sets. Exact strip partitioning, fixed total counts and fixed cut-line counts give almost-everywhere continuity of the original observable. Bounded ergodic averaging and inner-interval exhaustion identify its Haar mean with the actual Jessen measure for arbitrary open endpoints.
- `CoefficientScaling` proves identities for the literal polynomial, support, analytic order, finite-height counts, Haar logarithm and derivative measure under every nonzero complex scalar. Its logarithmic identity is justified off the proved Haar-null zero set. `NonzeroFirstCoefficientDensity` applies the normalized theorem to (a₁)⁻¹a and rewrites these proved identities. This removes a normalization restriction in the earlier formalization and restores the printed a₁≠0 domain without changing the source.

The exact consumers `jessen_tornehave_all_endpoints_source`, `jessen_tornehave_nonzero_source`, `twist_count_frequency_source`, `twist_count_measurable_source` and `coefficient_scaling_multiplicity_source` expose these objects and conclusions. DUB-05 is accepted upstream. The 372-module sequential receipt below covers every reviewed module and consumer; no source repair or additional mathematical hypothesis was adopted.

## DUB-07 — Total mass and probability normalization

**DONE.** Reviewed all 16 registered production modules against Proposition 3.7 (`prop:total-mass`) and the normalization example (`rem:normalization-check`), including the printed a₁≠0 hypothesis. Together with DUB-06, the retained review inventory covers 124 distinct modules, including shared supporting modules.

- The convex right derivative defines the positive Stieltjes measure J″. Its Ioo, Ioc and singleton formulas retain the correct one-sided derivatives and jump masses. This is the measure characterization used in the source; it is not an arbitrary supplied measure. Actual uniform Bohr asymptotes and convex secants give derivative limits −log M_N and 0. `JessenGeneralMass` derives the positive-side limit log|a₁| and proves total mass log M_N for a₁≠0, scaled zero-frequency mass log M_N/(2π), probability normalization when M_N>1 and zero measure when M_N=1.
- The binomial check uses the literal function 1+exp(−λs), λ>0. Periodic integral estimates and the actual circle Mahler formula give J(σ)=max(0,−λσ). Its right derivative gives J″=λδ₀. The actual complex exponential equation gives all zeros (2m+1)πi/λ and the nonzero derivative proves simplicity. Exact floor/ceiling bounds on the open height interval yield density λ/(2π), including the cases where a real-strip endpoint is zero and excludes those zeros.
- H2's diagonal lower ratio forces nonzero selected coefficients. Growing block cardinality supplies an isolated prime p>N/2, so N/2<M_N≤N and eventually M_N>1. The logarithm squeeze yields log M_N/log N→1. Thus eventual probability normalization is derived from the actual coefficient support.

The exact consumers `jessen_mass_nonzero_source`, `jessen_probability_nonzero_source`, `binomial_normalization_potential_source`, `binomial_normalization_count_source` and `isolated_prime_support_normalization_source` were checked with their unfolded source objects. DUB-06 is accepted upstream. General first-coefficient scaling changes the potential by an additive constant and leaves this measure unchanged, as proved rather than assumed. The sequential receipt covers the complete reviewed scope with zero diagnostics.


## DUB-10 — Isolated-prime lower bound

**DONE.** Reviewed all seven registered production modules against Proposition 5.1, frozen TeX lines 998–1072. The prime-factorization lemma proves that a prime p>N/2 can divide a positive index n≤N only when n=p. The actual finite Bohr polynomial therefore splits into a complementary-coordinate remainder and a linear sum in the selected prime coordinates. A measure-preserving equivalence splits the genuine product Haar measure; coefficient arguments are absorbed by Haar translations. Logarithmic integrability comes from the actual nonzero polynomial, so Fubini is justified. The translated Steinhaus theorem applies for every complementary phase with the same C_K, and the exact energy sum converts log(sqrt B) to log B/2.

`exists_uniform_isolated_prime_lower_two_sided` and `SemanticRegression.isolated_prime_two_sided_source` expose the printed two-sided ratios and derive nonzero coefficients using p=q and K⁻¹>0. One C_K is chosen before the coefficients, N, block and set of abscissae. The result holds on every set, so covers every compact set I in the source without a restriction I⊂(−∞,α). The chosen bound is the same Steinhaus witness passed through phase rotation, Haar splitting and prime-coordinate reindexing; no new parameter-dependent constant is introduced. The finite max/min and eventual compact-H2 consumers are also retained. Source a₁=1 is included in the proved a₁≠0 domain. DUB-04/05/09 are accepted upstream; no desired lower bound, coordinate independence or nonvanishing certificate remains as an extra input.

## DUB-11 — Abstract locally uniform potential limit

**DONE.** Reviewed `PotentialPointwise`, `JessenSlopeBounds`, `PotentialEquicontinuity` and the previously accepted actual support-normalization chain against Theorem 2.2, frozen TeX lines 144–194. `SemanticRegression.abstract_potential_limit_source` writes the literal finite global and isolated energies, all H1 abscissae, H2 compact-interval constants and local uniform H2 energy convergence explicitly.

The normalized actual Jessen potential is squeezed between the global-energy upper bound and the isolated-prime lower bound for σ<α; C_K/log N tends to zero. For σ≥α, the actual Jensen lower bound zero and H1 give the limit, including the corner σ=α. The two proved asymptotic slopes bound every convex secant between −log M_N and zero. Since M_N≤N, the normalized potentials are 1-Lipschitz for N≥2. Equicontinuity on every compact set upgrades pointwise convergence to local uniform convergence on all ℝ. Only a finite initial segment is replaced in the auxiliary Lipschitz sequence, with eventual equality proved. H2 gives N/2<M_N≤N eventually and hence the required log M_N/log N→1. H1 and H2 are legitimate explicit upstream hypotheses of this abstract criterion, not disguised conclusions.

## DUB-12 — Weak probability limit and tightness

**DONE.** Reviewed all six registered production modules and `SemanticRegression.abstract_concentration_source`. The actual convex Jessen derivatives are squeezed between secants at three points in each affine part of the limiting potential. Dividing by the actual terminal-support logarithm uses the proved log M_N/log N limit. Thus the exact Stieltjes mass of every interval straddling α tends to one.

`jessenProbability` equals J″/log M_N whenever M_N>1. Its Dirac convention for degenerate indices is removed by an explicitly proved eventual equality in the final consumer. Interval concentration supplies a concrete compact interval carrying asymptotically all mass; tightness of the finitely many preceding probabilities and a finite union of compact sets prove tightness of the full sequence. The open-set Portmanteau criterion then proves convergence in Mathlib's actual probability-measure topology to δ_α, and its integral characterization gives convergence for every bounded continuous real test.

This proof uses convex secants and interval masses directly, instead of the paper's intermediate integration-by-parts argument for compact smooth tests. It proves the stronger final bounded-continuous-test conclusion together with tightness, and therefore includes compact smooth tests; it does not stop at vague or distributional convergence. No interval-mass, tightness or weak-convergence premise is assumed for the actual polynomial. The source measure is consumed and the finite-degeneracy convention is discharged in the same exact public theorem. DUB-11 and DUB-07 are accepted upstream.

## DUB-13 — Zeta partial sums and outside-strip density

**DONE.** Reviewed all 16 registered production modules, the previously accepted general endpoint/count modules, Theorem 2.4 and Corollary 6.1 (frozen TeX lines 200–215 and 1284–1393), and the exact consumers `dyadic_prime_count_source`, `zeta_energy_source`, `zeta_concentration_source`, `zeta_zero_count_source`, `zeta_atom_free_count_source`, `zeta_count_tail_source` and `zeta_all_endpoints_count_source`.

- The actual dyadic block is exactly the primes in (N/2,N], including the natural-floor/real-endpoint identity. Its cardinality is the difference of inclusive prime counts. The licensed prime-counting port consumes the existing proved Chebyshev/PNT input through actual partial summation and logarithmic integral estimates. It yields cardinality/(N/log N)→1/2, growth to infinity and log(cardinality)/log N→1; no PNT premise remains in the application.
- Uniform power-ratio estimates on the real dyadic interval give the literal coefficient comparability and energy bounds. Their logarithms give a compact-uniform error controlled by a constant/log N and the proved prime-counting logarithmic error. H2 actually holds locally uniformly on all ℝ. The global energy is bounded above by N^max(1−2σ,0) times the harmonic sum and below by the actual prime subsum when σ<1/2; at and to the right of the transition, the n=1 term gives the lower bound. Log(harmonic N)/log N→0 proves H1, including σ=1/2. This is a faithful alternative to the source's integral-test proof of H1.
- The actual coefficients are identically one and M_N=N. The abstract theorem supplies the real vertical-Jessen potential, its Stieltjes probability and weak limit. Complement interval masses tend to zero. The finite outside count is the sum of analytic multiplicities over |Re(s)−1/2|≥ε and |Im(s)|<T. The source's atom-free boundary convention is implemented by a single countable exceptional set for every truncation; a separate radius-monotonicity argument gives iterated eventual smallness for all positive radii. The already proved general-endpoint theorem further gives the full nested limit for every ε>0, keeping boundary zeros in the outside count. Each fixed N has its T-limit before the N-limit; there is no exchanged or coupled limit.

DUB-12 and the exact actual-zero identification from DUB-06 are accepted upstream. No energy asymptotic, prime-counting estimate, zero-frequency hypothesis or endpoint regularity is hidden in the zeta theorem.

## DUB-14 — Every fixed Dirichlet character

**DONE.** Reviewed all 11 registered production modules against Lemma 7.1 and Theorem 2.5 (frozen TeX lines 217–237 and 1395–1532), with exact consumers `character_energy_source`, `character_sharp_energy_source`, `character_concentration_source` and the actual-zero measure consumer.

- Coefficients are literal values χ(n mod q). Their norm square is the coprimality indicator, proved from the unit/nonunit character laws. This identifies the exact positive-index coprime energy and the actual nonzero support. All positive q are admitted; no primitivity or nonprincipal hypothesis occurs.
- Möbius inversion is proved for the coprimality indicator and for arbitrary weighted finite sums, with the cutoff floor(N/d) linked exactly. The complete-period count gives Σ_{d|q}μ(d)/d=φ(q)/q. Integral comparisons for every real power greater than −1, the floor-scaling limit and the finite divisor sum give the literal left-regime leading term and little-o remainder, including σ=0. At σ=1/2 the harmonic difference has an actual finite limit, stronger than the required O_q(1). Above 1/2, a summable real p-series bounds every partial sum. The sharp source energy lemma is fully assembled, not replaced by an exponent-only assertion.
- Once N≥2q, every selected prime exceeds q, so its character norm is exactly one. The same ordinary dyadic prime block therefore supplies H2, with no progression PNT. The bounded-coefficient/global-prime-subsums theorem proves H1 directly, including its transition. This direct proof is distinct from, and compatible with, the separately proved sharp coprime-energy lemma.
- The abstract actual measure theorem gives local uniform potential convergence, tightness, the weak probability limit and outside-mass convergence. The support is the genuine largest index with χ(n)≠0, equivalently (n,q)=1 by the proved norm identities. Its logarithmic normalization and eventual nondegeneracy follow from the real isolated primes, without needing the source's sharper N−q+1 support bound. Exact consumers expose the coefficient values and the actual Stieltjes normalization; the previously accepted actual-zero consumer also exposes literal analytic multiplicities in every open strip.

All five records above use the subsequent 372-module, 151-consumer sequential verification receipt. The source theorem domains and conclusions are preserved; alternative proof routes and stronger conclusions are identified explicitly. DUB-16–20 remain OPEN, including the genuine modular arithmetic inputs.


## DUB-15 — Actual eigenforms and coefficient translation

**DONE after the 377-module sequential verification.** Reviewed all 113 registered implementation modules in full, their principal definitions and the exact consumers named below. The source contract is the genuine primitive non-CM form in Section 2 and Section 8, its normalized coefficients, and equation `eq:classical-shift` (frozen TeX lines 1534–1536 and 1701–1712). The normalization/translation proofs hold for all integer weights and genuine cusp forms; this includes, without narrowing, the source's even weights k≥2. The deeper arithmetic assertions at lines 1540–1544 and 1618–1642 remain DUB-16/DUB-17 obligations.

- **Actual source object.** `PrimitiveCuspForm` extends Mathlib's actual holomorphic `CuspForm` on Γ₀(Q), with positive Q, trivial character, its actual period-one Fourier coefficient a₁=1, membership in the Petersson newspace, and simultaneous literal good-index Hecke equations. `NonCMPrimitiveCuspForm` adds absence of a nontrivial primitive quadratic coefficient self-twist at primes away from QD. This is the classical coefficient definition, also expressed as inert-prime vanishing by `coefficientSelfTwist_iff_inert_zero`; `cusp_selfTwist_normalization_iff` proves that normalization preserves it. None of the structures contains a mean-square estimate, Ramanujan bound, prime-density assertion or Sato–Tate limit. The further representation-theoretic identification needed to apply a future automorphic theorem is still an open DUB-17 bridge.
- **Real pairing and full oldspace.** `ModularPeterssonMeasure`, `ModularPeterssonDefinite` and `ModularPeterssonLevel` use the actual invariant hyperbolic measure, prove integrability, boundary nullity, Hermitian identities and definiteness by holomorphic continuation, and construct the finite-coset higher-level pairing. `ModularDegeneracy` and `ModularDegeneracyCoefficients` prove the literal maps f(z)↦f(dz), all level divisibilities and sparse coefficient formula. `ModularNewspace` spans all proper lower-level generators, including d=1 ordinary inclusions, and takes their actual Petersson orthogonal complement. `ordinary_inclusion_counterexample_source` uses the genuine discriminant to verify why omitting d=1 would be wrong. `level_one_newspace_source` proves oldspace zero and newspace full at level one.
- **Literal Hecke operators.** `HeckeAveraging` through `HeckeCommutativity` derive the exact Fourier divisor formula from convergent actual q-expansions and a finite root-of-unity sum. The four prime transition cases and finite projective-line permutation prove the Γ₀ transformation laws; holomorphy and all cusp conditions are proved. Prime recurrences and coprime convolution construct actual all-index cusp endomorphisms, identify them with the classical finite Hecke function, and prove commutativity. The consumers `classical_hecke_fourier_source`, `prime_hecke_cusp_source`, `all_index_hecke_cusp_source` and `primitive_coefficients_source` use genuine cusp coefficients, not abstract eigenvalue sequences.
- **Good adjointness and real coefficients.** `FundamentalDomainTransport` through `HeckeGoodAdjoint` review includes the actual projective quotient and central kernel, finite coset domains, invariant hyperbolic measure, exact determinant-normalized slash transport, adjugate identity, upper/lower congruence representatives and their trace integrals. The complete chain proves Petersson self-adjointness of the good operators. `PrimitiveCoefficientReality` consumes positivity and actual normalized eigenvectors to derive real unramified coefficients; `primitive_coefficient_reality_source` unfolds the q-expansion and normalization. Auxiliary finite-orbit inner products used later are explicitly distinct from this analytic Petersson pairing.
- **Arbitrary-level multiplicity one.** The principal cusp action and finite orbit are genuine inverse slash actions. `SL2Reduction` and `PrincipalCongruenceQuotient` prove surjectivity and the exact finite matrix quotient. Actual translation averages retain precisely divisible coefficients, with idempotence and orthogonality in a proved positive invariant auxiliary inner product. Chinese remainder decomposition puts each prime translation in its own local factor. `FiniteCompressionDecomposition` uses only different-index commutation; it never assumes the generally false same-index commutation. Actual upper-invariant components descend to Γ₀ forms with unchanged coefficients. Sparse coefficients force a genuine fractional period; integral matrix factorization then constructs the cusp form at N/d whose degeneracy is the original one. `cusp_coprime_support_old` consumes this chain and puts any actual coprime-vanishing form in the full oldspace. Petersson disjointness gives coprime-coefficient uniqueness in the newspace. `coprime_oldspace_source`, `newspace_coprime_uniqueness_source` and `primitive_multiplicity_one_source` unfold the actual coefficients and Hecke action at every positive level.
- **Bad indices derived, not assumed.** `HeckeBadDegeneracy` proves all three bad-prime generator identities and `HeckeAllOldStability` proves full oldspace preservation. The five attributed dimension modules use actual modular norms and Fourier jets, reducing to pinned Mathlib level-one finite-dimensionality. `CuspOldNewProjection` therefore constructs the real Petersson old/new decomposition and commutation with good operators. `PrimitiveOldEigenExclusion` uses all-index images to show that no nonzero oldform shares the primitive good eigensystem. `PrimitiveFullEigen` then proves `primitiveCuspForm_eigenvector_all` and the literal all-index eigenfunction condition; `PrimitiveFullCoefficients` derives the full multiplicativity and good/bad recurrences. `primitive_all_index_eigen_source` and `primitive_full_coefficients_source` expose these conclusions. The one-dimensional eigenspace is proved by actual coefficient uniqueness, not supplied as a hypothesis.
- **Non-CM meaning and the level-one specialization.** `PrimitiveSelfTwistCoefficients` extends the prime self-twist to every coprime index by the proved Hecke recurrence. `PrimitiveGaussTwist` proves nonzero Gauss sums and exact Fourier inversion; the subsequent twist modules construct a genuine cusp form at D²Q by actual finite translations, prove its transformation law and exact coefficients χ(n)a(n), and derive its Hecke action. The Fricke modules keep the pinned determinant normalization W_N and scalar factors. `CuspFiniteDepletion` constructs the real coprime-supported form by genuine degeneracy maps. Comparing its first Fricke coefficient with the actual twist forces D=1 in `primitiveCuspForm_levelOne_selfTwist_modulus`. Thus `level_one_nonCM_source` constructs the non-CM primitive object from a normalized level-one Hecke eigenform and unfolds the absence of a quadratic self-twist. No general conductor or twist-newness theorem is assumed. This proves the object bridge for Corollary 8.2; it does not prove its concentration conclusion before DUB-16–18.
- **Exact coefficient and zero-measure translation.** `CuspCoefficients` uses the actual convergent period-one q-expansion, proves a₀=0, defines λ(n)=a(n)n^{−(k−1)/2}, and proves normalization, norm and support identities. `CoefficientShift` proves the principal-complex-power identity at positive indices. `ZeroCountShift` transports the actual analytic order, the finite zero set and open-strip count with multiplicity. `JessenShift` transports the fixed-N vertical logarithmic mean, right derivative and Stieltjes measure. `CuspNormalization` assembles the exact shift by (k−1)/2. The consumers `coefficient_shift_source` and `cusp_coefficients_source` expose the actual finite polynomial, q-expansion and measure pushforward. `ProbabilityShift` proves the eventual nondegenerate probability pushforward and continuous-map weak-limit translation; `CuspConditionalConcentration` composes actual cusp inputs and gives the line k/2. Its mean-square and positive selected-prime density hypotheses remain explicit and conditional; they are not evidence for DUB-16–18.

The complete source/object and normalization acceptance clause is satisfied by this actual chain. DUB-16–20 remain OPEN: genuine Rankin–Selberg with the required error, Deligne, Sato–Tate and the automorphic bridge, the unconditional modular/level-one concentration assembly, and final integration/release acceptance are separate obligations. No source theorem, parameter range, multiplicity or endpoint convention was weakened.


## Hashes of the reviewed proof scope

- `Extension/Dubon2026/DirichletPolynomial.lean`: SHA-256 `ac6003444692a13b33e6cc75e0c0efeb9e718934b86ef9f5bb02209dd5911b15`.
- `Extension/Dubon2026/DirichletZeros.lean`: SHA-256 `843e909af7f4fd026701f11bff00d030cceec4c37db58a8f3bd0c0dc0e858fba`.
- `Extension/Dubon2026/BohrLift.lean`: SHA-256 `a057071039665da1d246df6c3c0464e5be8ba813a89de0cac05bfba1ff37cd57`.
- `Extension/Dubon2026/PrimeFrequencies.lean`: SHA-256 `0faeb38353ff69ea9ee4d365887b5c12fb019fad76006b5ad3689fb739adf01e`.
- `Extension/Dubon2026/SymmetricAverage.lean`: SHA-256 `a15ff1facaf1a9fa013c983c628b566ca06aa4c37f1debc1e8c5e4871aab3d8c`.
- `Extension/Dubon2026/PrimeTorus.lean`: SHA-256 `18c00ef24ea002bbe01dfb9ec55f5f49f77d055d5024663d5e89c494dc6c1430`.
- `Extension/Dubon2026/TorusEquidistribution.lean`: SHA-256 `56b3da773fd576c653cb1f4575d90f33bb0f8c4c43ac197977be4de28d354013`.
- `Extension/Dubon2026/TorusPolynomial.lean`: SHA-256 `af043cae91ca6f753913f942c074ee1a0478e3cd603f797b3d91571ec9111989`.
- `Extension/Dubon2026/SemanticRegression.lean`: SHA-256 `147d9f1c0c0402084c561d4dc2f4cdc5ae5d9d527ccbcd6b51439ac71704d6ce`.
- `Extension/Dubon2026/Audit.lean`: SHA-256 `83fc1a073e8e5e4f77903ba83e1f33476a894431c3644f6d3a2607c440225fa0`.
- `Extension/Dubon2026/TorusEnergy.lean`: SHA-256 `970abefb981c61960a6f0dd65ddfd96579e487cbf537b24032c7b4a796e53f5c`.
- `Extension/Dubon2026/CirclePolynomialLog.lean`: SHA-256 `79d8e4398c57da43adc31f069a9cb1e18f5337b2a74b625e9c91f60d8db23ab2`.
- `Extension/Dubon2026/MultivariateBohrPolynomial.lean`: SHA-256 `b28b07522e7f4ff970f77442241fe575e8743670a62d7ed2ac5d1dd71830c2fc`.
- `Extension/Dubon2026/TorusPolynomialLog.lean`: SHA-256 `1d53c9a3c8e92cd0e4ca3797087151f53f1ac5ba0724899de0aef919ce14c8fc`.
- `Extension/Dubon2026/TorusJensen.lean`: SHA-256 `249ed3b313fd690291fc8ee448502a5ce34a52337f50dc8e5105d1738c01db08`.
- `Extension/Dubon2026/LogTruncation.lean`: SHA-256 `a8ba6e49a2d3e9d199ad4820c9b6d0b358416901cf280b9e77abfc359d17c3e8`.
- `Extension/Dubon2026/HigherRolle.lean`: SHA-256 `274398ff447c740ce78dbc71c4acce66f48782c6193dbb7379286dabecf12d23`.
- `Extension/Dubon2026/InterpolationDerivative.lean`: SHA-256 `aed726ed6ec62378e0722f78503b823ba9976bfc054a5e4aba3539a26057cc7d`.
- `Extension/Dubon2026/SublevelCover.lean`: SHA-256 `18f4fcc01b5e818c4eea040a0098e9042e8df271316c572712434069b7022d6e`.
- `Extension/Dubon2026/VerticalFamily.lean`: SHA-256 `d2bcb0fa17ddf12be1cd139d16d2e410bb292d4715a5f4c7ca3bb320576ab5e5`.
- `Extension/Dubon2026/VerticalJets.lean`: SHA-256 `9cf78f358803286a8de1299ff773b8f7f67b02948c608f45174d25f5283c3468`.
- `Extension/Dubon2026/RealVerticalJets.lean`: SHA-256 `364f9bd632fda51c6f018a15975ae7f69b9f9bd74c2c3026a7eb07b2b4201282`.
- `Extension/Dubon2026/CompactJetCover.lean`: SHA-256 `4db090b43dcab0d3a1efe639252b2527a5559bb1d53db7479dfd24f736ff4d8b`.
- `Extension/Dubon2026/UniformVerticalSublevel.lean`: SHA-256 `2f35b70635a8132d8179b6bed1cbd956a98e8be575484bd4f933d56d54640218`.
- `Extension/Dubon2026/ExponentialTailIntegral.lean`: SHA-256 `ccd0432c24c920f296b188e257531b06dc2c2e55a4375b3cea452681db145fc1`.
- `Extension/Dubon2026/LogDeficit.lean`: SHA-256 `39bba1d8f96fc3cf19ad72ddc608801197f0dcb9064114a260749a90eac1de35`.
- `Extension/Dubon2026/UnitLogTail.lean`: SHA-256 `38f6ec6191a10d5581cc171c627fa32e90564e38d4403c3a1bc1a7a75628043b`.
- `Extension/Dubon2026/UnitIntervalAverage.lean`: SHA-256 `e4887fdfcee733ac6a5aeaccf04ebc8582773c049d79f6f39107140a024723ea`.
- `Extension/Dubon2026/VerticalLogTail.lean`: SHA-256 `e0e78bce0ea4fbc4e76ec1203d52d2c65493ea2eef38be57b58ab919fc2837ed`.
- `Extension/Dubon2026/JessenMean.lean`: SHA-256 `c0d5c8ecc12fcaa94d40a40982a3ec3ff4fb1db67e7c6e14bd3c8aecd28d2365`.
- `Extension/Dubon2026/TorusGridCharacters.lean`: SHA-256 `f56a17f5abc95f56c0d9c282d3693bf64d282a4438f608fba872f470da6cf4f3`.
- `Extension/Dubon2026/TorusGridAverage.lean`: SHA-256 `1444e270e768b05b7febd568d981bd6b94b0cfea078a5a22836926b071a1ee25`.
- `Extension/Dubon2026/TorusGridApproximation.lean`: SHA-256 `145e2bdbe8c58635616f19c20b86c324e3979f0a5649f43add16c0df4158b6ac`.
- `Extension/Dubon2026/TorusGridLog.lean`: SHA-256 `cc99cf08c4a1db43dfe5fbe580c5915fb90f06a60fca260e9a510a53901cf868`.
- `Extension/Dubon2026/TwistProducts.lean`: SHA-256 `0c4efea7085e8d950d1bc8ecb1cdc98d0339a8ffcdd2daa13687020ff2792fcc`.
- `Extension/Dubon2026/TwistProductStrip.lean`: SHA-256 `f98de124b0645e1a618c6e8ec7c5530a3c88375cbcd2545c5eea7158f50e0c0e`.
- `Extension/Dubon2026/GridProductBounds.lean`: SHA-256 `093cc5bfcbea341dfd4a7272eb66edd7fcaf73de3787a129947ed54d3ceee202`.
- `Extension/Dubon2026/HaarChord.lean`: SHA-256 `de93d5411d3de8878df7964b57551fa4b8e1f9dc0e70304802153f80e8019111`.
- `Extension/Dubon2026/JessenConvexity.lean`: SHA-256 `b190889a6174381107bf0cc9a592dad8023703de6da1e56941bffc5e6ca7f30e`.
- `Extension/Dubon2026/CircleCharacteristic.lean`: SHA-256 `d3bdbc46b0c618416d371e930a3985b1df4c6e8e237446a65bbd55525af6f89b`.
- `Extension/Dubon2026/CircleMoments.lean`: SHA-256 `f3046233a1d032e6a721b165de03d8a3ac7cd062b55ee50c78ede87b46737257`.
- `Extension/Dubon2026/CircleGaussian.lean`: SHA-256 `085d6ef8d4338f402d258f6eff66d09e1423aaeefffca92c34b536851449da37`.
- `Extension/Dubon2026/CircleSeries.lean`: SHA-256 `83d48dd8c144746bf4987aa793a8d545d6c0ae7947f102367b373500bdc4e08d`.
- `Extension/Dubon2026/BesselJ0.lean`: SHA-256 `19a9e3d9d90ca82a3ce21ece9235533e76fa9f07d54a51137a83b9e027d05f8b`.
- `Extension/Dubon2026/CircleQuarter.lean`: SHA-256 `93e6d48077ce7102faf590a15c3f1646d45cf7278e998b6bb905702911437561`.
- `Extension/Dubon2026/CircleOscillation.lean`: SHA-256 `2bf394be5f758c04eae208109fa721d8813c331b38f8ab7f3495ceed8becf8b3`.
- `Extension/Dubon2026/BesselDecay.lean`: SHA-256 `ca08acda51f9a95730b51a775c15528fb1d82443c95d8d44ccc01003c080dcf8`.
- `Extension/Dubon2026/CircleRadial.lean`: SHA-256 `03a9019efff73647439f9d075f835c060585557ffb5bfc4fa5e76268a91d2aed`.
- `Extension/Dubon2026/SteinhausLaw.lean`: SHA-256 `4a057a7454f1390441796d47e7c8459685963e3fc1ca6daa217bdc298cf6c33c`.
- `Extension/Dubon2026/SteinhausNormalization.lean`: SHA-256 `c5c0accb035fbdf46bc61e8787676c02d07e0c95c7dd8645ca27f69a5807658e`.
- `Extension/Dubon2026/SteinhausRegionBounds.lean`: SHA-256 `6905fd28b43350a0455f2ad88dcea7e78d6188b5de468a06cd2551dd0a255f00`.
- `Extension/Dubon2026/SteinhausRegions.lean`: SHA-256 `969049f44ba9459a80e685af3da24a014e8d81f49e5407c0cc9d27135cb7f8df`.
- `Extension/Dubon2026/RadialTailIntegral.lean`: SHA-256 `029c47f0da41ea7b52743ba5a98039d25ca9e1c53eb853ca1c4b24ae068fa13d`.
- `Extension/Dubon2026/RadialInnerIntegrals.lean`: SHA-256 `93c0dee9c68e30dccaa52602459e8c3a0876fb791c8ff30b756b81a8ad9a2272`.
- `Extension/Dubon2026/ThreeRegionIntegral.lean`: SHA-256 `d77b02a4cef36e7a8d6c7c1f86e26e400e7c4194ff8390f8a59935b0ca1d1772`.
- `Extension/Dubon2026/SteinhausRadialIntegral.lean`: SHA-256 `fbc072724b7c907df59ed97146913e98d4b57b27a7a5ad6dbe52683fcd61dbf5`.
- `Extension/Dubon2026/PolarRadialIntegral.lean`: SHA-256 `36e432964fd2c7dafa969735d39658419a154657786b896eb27516bc0e9d6795`.
- `Extension/Dubon2026/SteinhausFourierL1.lean`: SHA-256 `ef63d352eaef37649f9aa6cf104900921f79db21009ff3fcd8014ad48dbae2c4`.
- `Extension/Dubon2026/InverseCharacteristic.lean`: SHA-256 `a1b49ccc5794ec06ff42ae8d8eddbd59444ad25d08569e59f8f9a472cd466d8b`.
- `Extension/Dubon2026/PlanarGaussian.lean`: SHA-256 `abec75c7762902db78396a8bbe092af605ae7a1727eed4907f511e1d6d220406`.
- `Extension/Dubon2026/InverseCharacteristicMeasure.lean`: SHA-256 `4fc2f099782205c987ca86233656c3e62b70df8a460a8dda8ff6e11903063429`.
- `Extension/Dubon2026/GaussianDensityLimit.lean`: SHA-256 `c900a261c507cef1da813ad752ff38571aaba5a036d86974f1f8ccbe1e8901f6`.
- `Extension/Dubon2026/GaussianTestKernel.lean`: SHA-256 `51aef62f4eca72f8c889be639386b0443b7182e73bc8c14502e6f78c61edd2ce`.
- `Extension/Dubon2026/GaussianSmoothingBounds.lean`: SHA-256 `1f74f3cbaf8a518ce1de75d0c1cee48fd10796f3d398eadd8031b256031585cf`.
- `Extension/Dubon2026/GaussianTestPairing.lean`: SHA-256 `2ebf76adb630acd2b9316b931082b08e6eea111947bd14dd5ee1d0212f5ab73c`.
- `Extension/Dubon2026/PlanarDensity.lean`: SHA-256 `fdcca5e928f46e55ac5ef80bc1a272d47447de8244dfb118468391dbbeeb1f70`.
- `Extension/Dubon2026/PlanarSmallBall.lean`: SHA-256 `d4eb4c5bfe4b043b738779364a5ff69b16a06576c9e4eb155b3aa1122d7efcfe`.
- `Extension/Dubon2026/SteinhausDensity.lean`: SHA-256 `69d0b08a2f448dd68e21b244629b4b80cced71ff9ca36884bf3c2d8b60805e4d`.
- `Extension/Dubon2026/SmallBallLog.lean`: SHA-256 `d316b4d5410a8a9012b8a45d2d15a8b7d39699edc1f3bacfd3ef39712344f9cf`.
- `Extension/Dubon2026/BoundedLogExpectation.lean`: SHA-256 `665a5a27e3b2c8908b59825d67bcc81f4b0938e0f51640cb3499d7491d32cbe3`.
- `Extension/Dubon2026/SteinhausLogNormalized.lean`: SHA-256 `9d5ba9fdf89ffa0fd67a5e1d1ef5f7020998681f3c541b776f227c07e9f89d59`.
- `Extension/Dubon2026/SteinhausLogScale.lean`: SHA-256 `342f452dc272b56df0f8f79516b5f33568a9712b5ae8270ab2c33e394a836006`.
- `Extension/Dubon2026/SteinhausIndependentLaw.lean`: SHA-256 `5378f737884270ed80d8930ed3eaaf545be6388bed7cb804821c5eea7523cc4e`.
- `Extension/Dubon2026/SteinhausLog.lean`: SHA-256 `643d7638b6cb3133936210a05ed905c56ea9f80ed3e864d3a44f304f8e811589`.
- `Extension/Dubon2026/ActualZeroConcentration.lean`: SHA-256 `0fab71b67255e64237109e67f158bc87ba75893ad28427e291c27db81083552e`.
- `Extension/Dubon2026/AlmostAnalytic.lean`: SHA-256 `c770a8b884d45a13698905718b684633c6dfd78baa1865ce9cadd374252d934e`.
- `Extension/Dubon2026/AlmostAnalyticGcd.lean`: SHA-256 `08b24f6dd4f8f705c5e47dd0c880631a8053c5ce191567d0a966bddddce95c74`.
- `Extension/Dubon2026/AlmostAnalyticPolynomialDegree.lean`: SHA-256 `001115dae78f92c45413e3164bc1701280704cf976f3bc4aa86365b2f9042266`.
- `Extension/Dubon2026/AlmostAnalyticPolynomialDivision.lean`: SHA-256 `320204914c72dd6482b3f8ce89d8f372af21a34019ff11c9061b4de022fdd61b`.
- `Extension/Dubon2026/AlmostAnalyticPolynomialOperations.lean`: SHA-256 `d025078ddefa86c6882412ad57ac588ca2bc4b6c1ceac8335a21c0228121d773`.
- `Extension/Dubon2026/AlmostAnalyticRootCount.lean`: SHA-256 `c0ea195c52395127212ca32ea5b296a96cb601ea34ace00dc194cc502717ad8d`.
- `Extension/Dubon2026/AlmostAnalyticRootLayers.lean`: SHA-256 `59a0ce873ffbec9e593fd20f2344941cb27d2c2daebbda0887d4d6802df0d679`.
- `Extension/Dubon2026/AlmostAnalyticSturmSigns.lean`: SHA-256 `c8c7f189b7b28b8255f51bbcc0a22c539b09c27e111e14fe5bc36d6d2c47ad67`.
- `Extension/Dubon2026/AnalyticCompactIntegral.lean`: SHA-256 `c7303400b1ff2c7bcfee677b46b054b80d827f3c4ad73be6ce1397e1664d5b57`.
- `Extension/Dubon2026/AnalyticRectangleMoments.lean`: SHA-256 `928f0034807c291fb9f3826a23337c43bfff1b54d62114cf6917bfecd0fbb69d`.
- `Extension/Dubon2026/AnalyticVerticalPolynomial.lean`: SHA-256 `5b4934ad064cf3c712ebcfdbc07e4f02dc427e77ff436484c95fc13e2a8da46c`.
- `Extension/Dubon2026/AnalyticZeroPolynomial.lean`: SHA-256 `4ed42fa3c9a74c42b39974efc69df352f4a1caffb29ed1918decaa4c0b34ac52`.
- `Extension/Dubon2026/AtomFreeZeroDensity.lean`: SHA-256 `8f6c2d246ab742ca91d6386ec69b190f92164189b66ccecd505b51bf14e694af`.
- `Extension/Dubon2026/BinomialJessen.lean`: SHA-256 `dc0f101bddfbcd8f39ff9b8aa729c5bc56db546c1eb1cc968c34fec1e5620349`.
- `Extension/Dubon2026/BinomialMeasure.lean`: SHA-256 `415a0a240484294b1023f9df53d60f68140f881d9b6462206a7013d2926499e6`.
- `Extension/Dubon2026/BinomialZeroCount.lean`: SHA-256 `d701baf049b44b92701568798515b4f42e5b97380958d4288c467e86f2fdbb8e`.
- `Extension/Dubon2026/BinomialZeros.lean`: SHA-256 `7be0080ef4cc134212feba2a783bca8641474581b7df5925c4334901156302ea`.
- `Extension/Dubon2026/BoundaryAtoms.lean`: SHA-256 `b213a0471247873588500512cb8cfa3e5ea30199769960e615a04abd8d34e8d7`.
- `Extension/Dubon2026/BoundedEuclideanGcd.lean`: SHA-256 `1cd9f5022eb3edd946a2fbf98a7be5f279da95096d746b6a661a76cd79b80d9e`.
- `Extension/Dubon2026/CoefficientScaling.lean`: SHA-256 `d7eefb91d20cdf44415d009c3f7f4458094da9f1564fe6b36784a04baa2e1714`.
- `Extension/Dubon2026/CompactParameterIntegral.lean`: SHA-256 `38368b27c334e8906f7aaee80fd4858d36d42f35bfc511187c2c0ddb255828b3`.
- `Extension/Dubon2026/CompactPhaseAlgebra.lean`: SHA-256 `ae0a076e8cac9e5a4152fb21580da35a7667497e8c53e4e6e15bc32baab74c9a`.
- `Extension/Dubon2026/ComplexPhaseFamily.lean`: SHA-256 `09608058b3dd800c57e153a8c2b8b5a7f45f8932b1d6ed5a379ff42fca4e5698`.
- `Extension/Dubon2026/ContinuousEndpointZeroDensity.lean`: SHA-256 `0348b148514e246d8834ed66d3aa976138ef93a449612717bb680dc3632d0317`.
- `Extension/Dubon2026/ContourSlopeControl.lean`: SHA-256 `33d3508cedc2ef2ecfeb0e3f54b4ec89c594d4929dfa72dd33d443db53d662be`.
- `Extension/Dubon2026/ConvexAsymptotes.lean`: SHA-256 `1115d146b2030eba5ebaba08558fc4f2195f4593e2702fb488ab9a084f3f0ac0`.
- `Extension/Dubon2026/ConvexDerivatives.lean`: SHA-256 `787fc121502dab93291618b9df83c154727187fe745f0cf2eee87df15ac573d8`.
- `Extension/Dubon2026/DerivativeGcdLayers.lean`: SHA-256 `438313695271979271db4749c245a410cda9c6b18082f1a1ab53c12cf3aed9cd`.
- `Extension/Dubon2026/DirichletDivisor.lean`: SHA-256 `af63c2c128688e196e95840f6bb772484fedbff72a0490f5a99ea4e3a18cd3b4`.
- `Extension/Dubon2026/EuclideanSturm.lean`: SHA-256 `5ffcb7bb91f27aa57bc59ea3d62d901a4f984c46d3b0204617c6f30a01a1925d`.
- `Extension/Dubon2026/FiniteCrossingArgument.lean`: SHA-256 `59243dc164955f3826319ed35d53f2c3d5b9683618fcfc7275b84f0c7e4aceee`.
- `Extension/Dubon2026/FiniteExceptionalMeanValue.lean`: SHA-256 `9b675493d5623384ebd1b8eb408544bc42e2018765c8b1106727348c9f670561`.
- `Extension/Dubon2026/FiniteHeightContinuity.lean`: SHA-256 `77d6c13cbe6e010d90800c874c27c45109a2fed36dfc1d8a2d0d7dbc947ea2be`.
- `Extension/Dubon2026/FiniteHeightDerivative.lean`: SHA-256 `0057dda0b2ec5c67cd59908e8e8946571b353fc74cd5a3f123fcfd53f8fa3407`.
- `Extension/Dubon2026/FiniteHeightSecants.lean`: SHA-256 `7bf0b980fe9c2676f9adba895f2111074fbcdd4ef4085bd68249e4cb7c756986`.
- `Extension/Dubon2026/FiniteVerticalExceptions.lean`: SHA-256 `98a19adffc07da4ede77212f514d0bff437e7288e0f93864d8fbfbed113668e1`.
- `Extension/Dubon2026/GeneralOutsideDensity.lean`: SHA-256 `463e7b2636a5b94efb995a4b956a46551fcabe0a9cfba1e2d1cdc82eba72946d`.
- `Extension/Dubon2026/GeneralZeroDensity.lean`: SHA-256 `43ab663e618bb222bf12e44fbf62388ed03e0e600e601ebcad32410d74783d7a`.
- `Extension/Dubon2026/HeightLimitTransfer.lean`: SHA-256 `f5632498fb746f031d5847524be5de7c7ff337081b5121b59cefa9b5150e6d56`.
- `Extension/Dubon2026/HorizontalArgumentBound.lean`: SHA-256 `904dc2018a47648404dcbf71127ee47247bdc984a7acb49b9e3033c6216c9a85`.
- `Extension/Dubon2026/HorizontalPhaseNull.lean`: SHA-256 `397ae9d434a88d92f0f605afb868efb6ce4d23a7aa10a1811f899483345106ed`.
- `Extension/Dubon2026/HorizontalPhaseZeros.lean`: SHA-256 `0e409d0686f2a25930eb2542712e4f64c2d0d50cfa92e268d7f79ebc06b6a4b7`.
- `Extension/Dubon2026/HorizontalRealZeros.lean`: SHA-256 `08208ce84a738fe1c62cbfc45bd86adc980774303eed4aeec760ad8d7dba53a6`.
- `Extension/Dubon2026/HorizontalZeroCount.lean`: SHA-256 `f6fb5e4b57134bebc5cac2186416005edffa77428f5ec2a622c434d085418911`.
- `Extension/Dubon2026/InnerCountConvergence.lean`: SHA-256 `7cf88c26d036a85a451bbbf4e5d7d67282c5828de5cdf10275a2dc8d76a9f5ba`.
- `Extension/Dubon2026/InnerZeroRectangle.lean`: SHA-256 `288dd2799f19b4c5e3996007500379abe6daedec5cf41140aee6aa7e3994847b`.
- `Extension/Dubon2026/IsolatedPrimeSupport.lean`: SHA-256 `3febee8df5da611fed30257099044e80bbb461bdedb8943f763f31cbc7149dd0`.
- `Extension/Dubon2026/JensenZeroBound.lean`: SHA-256 `b88b4690cc309a3d0a770dd95045ece3c6f4cb9069e2aa49e85dd13276c631bb`.
- `Extension/Dubon2026/JessenAtomRegularity.lean`: SHA-256 `577002306b4a8a45d166eee09f44004725defb134cfb174f03e4fe2dde0e7314`.
- `Extension/Dubon2026/JessenGeneralMass.lean`: SHA-256 `0a23bbd6df3f863aabc6667ded98cbc5b3ce1a951faac8e0a778454eb95a0c86`.
- `Extension/Dubon2026/JessenLeftLimit.lean`: SHA-256 `d818b0531da2c773f26ace6296e3a1e51208aeabbd7f65383839ef54a7ae2180`.
- `Extension/Dubon2026/JessenMass.lean`: SHA-256 `f9efba7ea79003bbb3d976f2fb64edd1abeb5a6bd3c2f2d2a0b897b43d9b260a`.
- `Extension/Dubon2026/JessenRightLimit.lean`: SHA-256 `3749c97ed2cafc9982968c1684b253f12b9cd133cce68953cc9dafaf28ff7511`.
- `Extension/Dubon2026/JessenStieltjes.lean`: SHA-256 `c60fbeeef8832e13b385946bba7e1dc9c2a96f1e14f8d467ba4d62dc6caa66d3`.
- `Extension/Dubon2026/LeadingBohrTerm.lean`: SHA-256 `6d6005af3f26499caa8c04813bbadb5aa9e6d4639d9b1a0be8b770420bb9aaf1`.
- `Extension/Dubon2026/LocalLogTail.lean`: SHA-256 `1771bfbc12e4120fc41077ba46e11851d402517e619d614bd968a78b48d09059`.
- `Extension/Dubon2026/LocalVerticalJetCover.lean`: SHA-256 `90762570fe70f91a763752153dbe0db129238c2afc400acc817c33ed4f09081d`.
- `Extension/Dubon2026/LocalVerticalSublevel.lean`: SHA-256 `6c2b2b91ea909b8d691918c34b00fb547def4d365678918326749cb947c792d7`.
- `Extension/Dubon2026/LogDerivativeHalfPlane.lean`: SHA-256 `9571c699e86375dc0fe17102dfcc975e9266378a819c889622dabe2044948cfd`.
- `Extension/Dubon2026/LogNormDerivative.lean`: SHA-256 `aaa1be463f793c6421041e939b2752dbd7ee38490994e2708ee5f5832adfbb47`.
- `Extension/Dubon2026/NonzeroFirstCoefficientDensity.lean`: SHA-256 `7143a0d570feb6e2f2e5aa0a1e0ade06d0c858f023d0733ec44eb628bebb5fcd`.
- `Extension/Dubon2026/OutsideZeroDensity.lean`: SHA-256 `849ab77386b0f019399ba1b872be3d10e200e58e35654682cb4d8af14111b324`.
- `Extension/Dubon2026/PeriodicMean.lean`: SHA-256 `ef179f422042093adecdff3a8e6bcb18317e576ae8ed30a297100710cc2c0bff`.
- `Extension/Dubon2026/PhaseDerivatives.lean`: SHA-256 `e5a7bdbd1040ba20599c78e282b3c48391d04368f21009593def14a42835de16`.
- `Extension/Dubon2026/PhasePolynomialDegree.lean`: SHA-256 `a878d63f269bf5eb081c548864cb977d2d3e3de8edc747b37f27d9ad0c86f03a`.
- `Extension/Dubon2026/PhasePolynomialSigns.lean`: SHA-256 `97e9c522dd3dd2affec0abb2175a6d8769a7c0819202102895384085a5ba7fc2`.
- `Extension/Dubon2026/PhaseSturmCount.lean`: SHA-256 `9fadda297da736bf7f630541cf07c8037dadd44bf9fc681d98b8bcb31cc31bad`.
- `Extension/Dubon2026/PhaseVerticalCountRegularity.lean`: SHA-256 `0cb71342217b45c39e24af53b640cfa435bfaa93eb976a7bbb3954f0f67b3f59`.
- `Extension/Dubon2026/PhaseVerticalRoots.lean`: SHA-256 `a707f077d001fe48037e89dd1d99e88324245dc12ae93f68659e2d7260005174`.
- `Extension/Dubon2026/PhaseZeroMoments.lean`: SHA-256 `508e24816595e39ee1394355e78a4c38064d029076714a6e1f937db24f3eb0b0`.
- `Extension/Dubon2026/RealAnalyticRadialZeros.lean`: SHA-256 `6e49d4283f2c9f95d16d1074de9317cc2ed25d2dfcb39085b7fbc30a6bbc82cd`.
- `Extension/Dubon2026/RealAnalyticSign.lean`: SHA-256 `da9db7ea48e151aac9e413a50dde4b2810fe4741908e521831ec86cbe3c4b405`.
- `Extension/Dubon2026/RealAnalyticZeroNull.lean`: SHA-256 `54baa4add92261c8481fbfb5858aba2a897e601c0c7ab0a313da030c4f18982c`.
- `Extension/Dubon2026/RealExponentialZeroCount.lean`: SHA-256 `349b8fc6970490812c721bb5cd5b340a994acbf523167b7037f2a49e71aff4b3`.
- `Extension/Dubon2026/RealExponentialZeros.lean`: SHA-256 `ffd4d7aad32eec462f0899a081f9e65db9729bd7b18943de115f95c9c24b3df8`.
- `Extension/Dubon2026/RealNormPolynomial.lean`: SHA-256 `fe35bb98c75b148432aca25d37b6bb86aa20bf22901d02a76a75e26538a80d62`.
- `Extension/Dubon2026/RealRootCountLayers.lean`: SHA-256 `fc95dcbd2aed065a91a51d730a34c05b913e2fd175119067373d5db2229e77bc`.
- `Extension/Dubon2026/RectangleRealParts.lean`: SHA-256 `de90bda3a729b14f5b2faf8756e1a8709b72f06b7388a87f624e5d158adf586b`.
- `Extension/Dubon2026/RectangleZeroCount.lean`: SHA-256 `97cbde17a8d621f1be8b79580a655cb76d9716c077dcecd9950af7d8903d6c1b`.
- `Extension/Dubon2026/RectangleZeroPolynomial.lean`: SHA-256 `e3346eed6036ecbdcccfabb37137194d64e82ea9988a40e0bf0d97a53cd6000e`.
- `Extension/Dubon2026/RegularAbscissae.lean`: SHA-256 `3c90fc58615b21c2286d4ea59358236a42221015c23d8c54b14b519ccf3c6981`.
- `Extension/Dubon2026/RegularApproximation.lean`: SHA-256 `300cb732117944cdd069b8186ece75486306114d9ced9e18b7e4d7435fbaef71`.
- `Extension/Dubon2026/RegularZeroDensity.lean`: SHA-256 `9b4ee252bf5cfef10d1c15fa1061379e9786480fce8d05fd0b2006e113e834a9`.
- `Extension/Dubon2026/RootMultiplicityMapGcd.lean`: SHA-256 `9ab2d8826d227da3d16b3ffc6242bd348f03aff100e595083993fb99c51b93f4`.
- `Extension/Dubon2026/SecantLimit.lean`: SHA-256 `d9192fcaec137912887ec03241d16a2915c193252b037b72371d461604df5441`.
- `Extension/Dubon2026/SelectedMeanMotion.lean`: SHA-256 `a4534e9813e4d440edacc24763e2be1ff9ca29c0d46b1017dd4e42959855455e`.
- `Extension/Dubon2026/SeparableRootQuotient.lean`: SHA-256 `eb648c0c4f5527c342fd608c44368ff843724002141bc86d5f809463544771ac`.
- `Extension/Dubon2026/SlidingCountIntegral.lean`: SHA-256 `8a24d34cf992ff4e5b521eabf94f916226e435fe93eb87c14792796372751019`.
- `Extension/Dubon2026/SlidingRadiusBound.lean`: SHA-256 `51c4eeee0fb0769edc19c6cebdc7f2914046321e0a0eb7054d05f1f2abb4f04f`.
- `Extension/Dubon2026/SlidingZeroCount.lean`: SHA-256 `32992e97303cf831a342eca1891c0cbcad009f7649e9cb233514bcb9b8cbc318`.
- `Extension/Dubon2026/SturmCertificate.lean`: SHA-256 `db13067335984819501b8a6296d03662a9eb2adc96e9365ac0ac1869e736a9a5`.
- `Extension/Dubon2026/SturmChainDefs.lean`: SHA-256 `4b36f99fea441703d740713a5dd3e71a8a9efd7629bf316564ad5d6b31d961b5`.
- `Extension/Dubon2026/SturmRootCount.lean`: SHA-256 `2aba2bd46fc7c68e7c862a8f77ba015db9f63db158d73c0047eae85f11d85037`.
- `Extension/Dubon2026/SturmSign.lean`: SHA-256 `5588091a3459007b9595129e7efca840b94504e35060793d2b6d4a830e2fa048`.
- `Extension/Dubon2026/SturmTheorem.lean`: SHA-256 `51f620cbe5b860f8e9d125ba68ea74b98580922d1d587d1936171b70d286fce5`.
- `Extension/Dubon2026/TorusDiscreteAverage.lean`: SHA-256 `b8219caeea6b5426647ad78d6779abbf376ba14fb8c53d43c1fadc8913d7532b`.
- `Extension/Dubon2026/TorusPhaseRegularity.lean`: SHA-256 `7f1f8d9ae06a0274eabd5e052aaf305bc76f045be7c83bc3d70e47567a9ed4e6`.
- `Extension/Dubon2026/TotalVerticalZeros.lean`: SHA-256 `041332d618e99d2fbd59145602f01e716b6eb452f2c8a77e384bbbe20bf26ca0`.
- `Extension/Dubon2026/TotalZeroDensity.lean`: SHA-256 `4da0ef2ee2211eacad54eb4fe2094271a325870e978181f4466a0be2273e5b21`.
- `Extension/Dubon2026/TwistContourContinuity.lean`: SHA-256 `b674b4f9e433201870779d3cfce3e1af0a3624d12df9c75e71218e86c471c5b5`.
- `Extension/Dubon2026/TwistCountBound.lean`: SHA-256 `4c4fda134ee4b51a88225b0c27dd4c4e9f4646610678186c99657487954eb2fc`.
- `Extension/Dubon2026/TwistCountFrequency.lean`: SHA-256 `04062970ea220dad83b23f8ddce544b7431456a668d89a346bf33b8165451ccd`.
- `Extension/Dubon2026/TwistCountMeasurable.lean`: SHA-256 `3a09c3ed8c6a71ec8aa70d131b80b4e36e53a6e5d75d8d33dfbae9c8dbfa24a7`.
- `Extension/Dubon2026/TwistCountPartition.lean`: SHA-256 `c7595d0e0eee1a3706f2e3b910ad2c05a1b09b5463e0654623d0ca7d8a7e93af`.
- `Extension/Dubon2026/TwistCountRegularity.lean`: SHA-256 `9923bb8f6298c74a9a56ed0c329e43f48574dff420a97f4a14fd752e4ac9c0f9`.
- `Extension/Dubon2026/TwistCountStationarity.lean`: SHA-256 `edad2bff781e3c33240f94c47468e19f10505be46e82a4ee4d4d368e7f346193`.
- `Extension/Dubon2026/TwistMeanSmallHeight.lean`: SHA-256 `cf53e6b2e12ffdf2952a828aedee5794e5db87d9af293b90d9054b13280f4b77`.
- `Extension/Dubon2026/UniformLocalZeroCount.lean`: SHA-256 `245cee0470f25d858df8e83f74863425040abc2bf7ac3df353c760f42e69afd9`.
- `Extension/Dubon2026/UniformLogIntegral.lean`: SHA-256 `fddb757423f2aef7e7dc46da913e132c1bcd8e7830c6186b62142008e3783810`.
- `Extension/Dubon2026/UniformTwistZeroBound.lean`: SHA-256 `6078ca2adce1478e4c2c9c81ca24cc239277aa889d1b34957f15e82224233f38`.
- `Extension/Dubon2026/UniversalMonicDivision.lean`: SHA-256 `8a572c101f3d0532cb691acb8bbff1e437fae953479765feb6cc91b5066f6ddc`.
- `Extension/Dubon2026/VerticalLineCountRegularity.lean`: SHA-256 `d68b45e3c86bfe88495a56d6faf38fb19bb8571ad1585e2ae1b95977da2de11d`.
- `Extension/Dubon2026/VerticalMeanMotionTransfer.lean`: SHA-256 `bf4561549028150c32080ead2afeebdf8cdea7123fa9de0bac7a6a5bcc4545f2`.
- `Extension/Dubon2026/VerticalPolynomial.lean`: SHA-256 `ee27cc5c83a2e65b7d146576792b41d48e397d502841f807f68cc95ead732b8d`.
- `Extension/Dubon2026/VerticalZeroTranslation.lean`: SHA-256 `5a4a184399a2974e01bb4a7eb723a238c7f2a82e80ea0f3b4d2db7792203746f`.
- `Extension/Dubon2026/WeightedLogResidue.lean`: SHA-256 `196cba95750dcb8e63e09c92efc62e93f998ba412752e5a5f80e2dd3497c70b0`.
- `Extension/Dubon2026/WeightedRectangleZeros.lean`: SHA-256 `3e8b7782d45dd0ad4a3e6191c2503e4797837b6675dc16fc848d126bb938152e`.
- `Extension/Dubon2026/ZeroCountHeight.lean`: SHA-256 `cecc8b2fc63c1a187883bf439a126cf5a108011977ab5972e77e1361bd808313`.
- `Extension/Dubon2026/ZeroCountInterval.lean`: SHA-256 `64117735e1678d98556d71915d27414984dddf0436200e51bab246e86d51a346`.
- `Extension/Dubon2026/ZeroFreeBoundaries.lean`: SHA-256 `8ff324ba64c832ba0b7993cfafb453f91e2e9e69769630506203d9f88d430e20`.
- `Extension/Dubon2026/ZeroFreeHalfPlanes.lean`: SHA-256 `245857656ea4ad5cfea3320c0259375fac58aa72effdb90e4273ed446c1202f8`.
- `Extension/Dubon2026/ZeroFreeRealSign.lean`: SHA-256 `ee3878b09d517ca992ff79b2874145750af9f7521a95812999fef6d9a11d4928`.
- `Extension/Dubon2026/ZeroPolynomialNewton.lean`: SHA-256 `7ed2b63d83d4b1215ccfc517de3f5c77f05c179c6e7d09e6318eaeee841130c3`.
- `Extension/Dubon2026/BoundedCoefficientEnergy.lean`: SHA-256 `3f491df4dad77e5f3bf3f8cbd0a800a8af5fc5961be946e839fb06a3e6acba37`.
- `Extension/Dubon2026/CharacterCoefficients.lean`: SHA-256 `74d7a247940f12b80a27e59ab916d2676976e5c4d2e681b3262bcd3aab6199f0`.
- `Extension/Dubon2026/CharacterEnergy.lean`: SHA-256 `47af1a2905e61e182cbba81dd387179a42f99c7ff206f6b03a0dc2fddcf77aef`.
- `Extension/Dubon2026/CharacterEnergyAsymptotic.lean`: SHA-256 `ca853f2d51e4328ca1988f66874933bb50d52e0d65bb0d0fae46c09c43e97c0d`.
- `Extension/Dubon2026/ComparablePowerWeights.lean`: SHA-256 `d92eb5ad688c09ee5b2b044c5349735fb38b6c8ed053e8c6aa8fe15fbf05e1f5`.
- `Extension/Dubon2026/ConcentrationTails.lean`: SHA-256 `b4544866704a2ce7b107e06c644ad54af70a6ab6de5344aaa91c61fe0d017aca`.
- `Extension/Dubon2026/ConvexDerivativeLimit.lean`: SHA-256 `1eb16e3a7677bcbeffdaf48756ca33ca49e546215c145218a5ce13c1107b04a4`.
- `Extension/Dubon2026/CoprimeHarmonic.lean`: SHA-256 `bd2a150e424e74ce0f94ff728f186983590a9865b3231a254cb8bcfa2616d30c`.
- `Extension/Dubon2026/CoprimeMobius.lean`: SHA-256 `052ef4359d3391809213ce807cb55e7df928c5674cb1555cb11c233f7e3d397f`.
- `Extension/Dubon2026/CoprimePowerAsymptotic.lean`: SHA-256 `b3355bc3eb3afbc200478ef2c90ad255feed3bee6ea7b96090a7aab3d86f3eba`.
- `Extension/Dubon2026/CoprimeWeightSum.lean`: SHA-256 `701d540d70daa4bcbd03ff0bb04d55da8c3b0c6fe34a82f9bf49826d681144a8`.
- `Extension/Dubon2026/DirichletApplication.lean`: SHA-256 `bc93e322a0fc72cc51d229ec2b0cac5932d14ecc35f730f7dfe8dd2ee69e32bc`.
- `Extension/Dubon2026/DyadicEnergyBounds.lean`: SHA-256 `c4ec71de1cd19f8e110019850a8f84d19829a8226d7127b55291212dd2199ce9`.
- `Extension/Dubon2026/DyadicEnergyLimit.lean`: SHA-256 `14b793a05ca50bdbcd6fc8b32447934449f30a2b2296ed25e281795a0f57bebb`.
- `Extension/Dubon2026/DyadicPrimeGrowth.lean`: SHA-256 `e3d625caf45c650b0e328eff559ad6815cec55a21a63e447af1c5ba50ad6afc3`.
- `Extension/Dubon2026/DyadicPrimes.lean`: SHA-256 `4a4ac6006985c036bf2e27bd7836879aa4e584d3725c2bfa0ec544dcf83b5d97`.
- `Extension/Dubon2026/HarmonicPowerEnergy.lean`: SHA-256 `ab97bdc1e5cb09d3c874b118d04e03ee8bd98a97694b812e7794f114822deeca`.
- `Extension/Dubon2026/IsolatedBohrDecomposition.lean`: SHA-256 `9d9c64b9b94f211b41b2285896b0e2010268ad6ae437224c0f99b21bd06b76f7`.
- `Extension/Dubon2026/IsolatedHaarLower.lean`: SHA-256 `3b5892f09d727229b14faaeabd7b79ca3d242395321bf6dea34e8f40d7d58abb`.
- `Extension/Dubon2026/IsolatedPrimeLower.lean`: SHA-256 `8cc69a828be82ff5068a23859bec552b83ecc490bfc5336438586599acc10151`.
- `Extension/Dubon2026/IsolatedPrimeMonomials.lean`: SHA-256 `9adf3e9e8e8c8a16bbe0b081090cc3be34c9b486aabdc79a3a810ea41434882d`.
- `Extension/Dubon2026/IsolatedTorusSplit.lean`: SHA-256 `ec7d7c538f144196982dfb6602d66f9146324936c5bea79dae88ac1d693b764b`.
- `Extension/Dubon2026/JessenDerivativeLimit.lean`: SHA-256 `cd61fc72d7ab070954f9e11aef0f684694102cb8a41927be79b5ad4e01649975`.
- `Extension/Dubon2026/JessenIntervalLimit.lean`: SHA-256 `85ecccea8e78154eb4606716e342e0fb434a717bfa5cffc91c8bd0c35ad7a1cd`.
- `Extension/Dubon2026/JessenProbability.lean`: SHA-256 `5af57deaeb1e64d72df8cf81a9e625e2e17e51f3fc660e2f255dcb5b8c65cc4c`.
- `Extension/Dubon2026/JessenSlopeBounds.lean`: SHA-256 `a9998325eff4f274ae9f57c6cd5a09ca9403ee21626f7064af6536c8de1cc6bb`.
- `Extension/Dubon2026/LogarithmicScale.lean`: SHA-256 `14703a2d5d3e3146d2f04ed731a57f7b4c181cf4b141628439da419ddab1ccf4`.
- `Extension/Dubon2026/NeighborhoodConcentration.lean`: SHA-256 `8ea0aa2d5d2a42b0cf487972d7336008cd41ca77ec6ec35371b2876d8b89a9e4`.
- `Extension/Dubon2026/PotentialEquicontinuity.lean`: SHA-256 `6187b6949f0ae091a957fae4a4bd8674fcccfbdde07fdc075c24cb79bf86143a`.
- `Extension/Dubon2026/PotentialPointwise.lean`: SHA-256 `2cf627a2eb5a282d902db4c20d1cd3c0a962b711b88eaa0aa4ffa5768cafe915`.
- `Extension/Dubon2026/PowerSumIntegral.lean`: SHA-256 `4f579f38dc78d9f5bca3e79702b03875d4e6b4fc8256f4c1f9d55e488f4fdf0b`.
- `Extension/Dubon2026/PowerSumLimit.lean`: SHA-256 `ff3db571714a07a485973fa77bebdd5c552e825353d76d56df02849de441b090`.
- `Extension/Dubon2026/PrimeCountAsymptotics.lean`: SHA-256 `b180cbb9d4a29389f37ec53368914fcee1017fa5c75655075571fd6f459f0054`.
- `Extension/Dubon2026/PrimeCountingPNT.lean`: SHA-256 `4be2ad548b0790dd5c3b8eb94720e1789e5e7981bc3bf48ec81b884841bf5b85`.
- `Extension/Dubon2026/PrimeSelection.lean`: SHA-256 `b31aab7ccdd1b47a80b0d12a6a71f720e35622535497924f465cf8f1f4dd5558`.
- `Extension/Dubon2026/ScaledPowerSum.lean`: SHA-256 `4af5eb48dc7e6c325d29a6e0a79127717296a0e20ebff1d7419f2d64bc15aef4`.
- `Extension/Dubon2026/SteinhausPhases.lean`: SHA-256 `47733222293c5d0856320002ca0a1bc5e9c7b22e157e8ab7f1ceed8b58f00882`.
- `Extension/Dubon2026/WeakLimit.lean`: SHA-256 `a0b99c4bde8d7b4f15b5b992ebd0f1bc88c545f899c5ddc5a16b8211a8fc8d0c`.
- `Extension/Dubon2026/ZeroCountRadius.lean`: SHA-256 `a4b25cd284bd740d3b9e37cdf96b04b041549fc30ff2f40960aabadedcbd9872`.
- `Extension/Dubon2026/ZetaApplication.lean`: SHA-256 `13aa173e16719556bbc99d112dcc4058b98307e34f82554b6fe79c2d2350542e`.
- `Extension/Dubon2026/ZetaCountTails.lean`: SHA-256 `5a138a028ca4596f6c5e819ea0ed13ed90b6bf7995ecebf218c03be6dddf3040`.
- `Extension/Dubon2026/ZetaEnergy.lean`: SHA-256 `0bdb759c4b198e08f2787d625a7b8aa927dbf9a0d3d8c6f5ea2e9883cda28a06`.
- `Extension/Dubon2026/ZetaZeroCount.lean`: SHA-256 `421826aff8956b438ea4c3ffd4d096a5e4514d62f4769d031535c2192becbdc0`.
- `Extension/Dubon2026/BadPrimeDilationArithmetic.lean`: SHA-256 `0f76e38d0788458dad30cee3fc5feffa981b743b7a867664b108abf9e5b554b1`.
- `Extension/Dubon2026/CharacterTwistCongruence.lean`: SHA-256 `f08096909a84adaf69c3bedc7358f65744301764cfc0349c475c8eacb178548a`.
- `Extension/Dubon2026/CharacterTwistInvariant.lean`: SHA-256 `7dd14df36deedd05638e4b4f59887dab9eced22325b0df93435ed3b35b1a277b`.
- `Extension/Dubon2026/ClassicalHeckeFunctions.lean`: SHA-256 `fe7afe7c9f02794eeb1f2ee5a15bd84c26a084fed532c9bfe8ccbcad7a301296`.
- `Extension/Dubon2026/CoefficientShift.lean`: SHA-256 `1733209d99416cbf9774198d06d495dded8c728a4df69c989cd4874a6409ae25`.
- `Extension/Dubon2026/CuspCoefficients.lean`: SHA-256 `2910e8045f228250c25055337a09415449547464eeced2fedd45b7613f7ad1a1`.
- `Extension/Dubon2026/CuspConditionalConcentration.lean`: SHA-256 `8fca878054fef45fbb9cc44c2a2f5e83f410685a4c567590da053f04c70612f5`.
- `Extension/Dubon2026/CuspCoprimeOldspace.lean`: SHA-256 `f31cbc7656325cf5105555440829b74616cd881968a239690a3c08edaf1530d6`.
- `Extension/Dubon2026/CuspFiniteDepletion.lean`: SHA-256 `d5332afc82a719462082f1947d5c142fbf8e07c24d33007180b9a586fe17e0f5`.
- `Extension/Dubon2026/CuspLowerFunction.lean`: SHA-256 `99ff51a238dcc2d15e440dadae29c969b96b24fd548f5d54d4332aea694b52d9`.
- `Extension/Dubon2026/CuspNormalization.lean`: SHA-256 `90026359f2da38a878b6ab4da8ffdcc2533c465ab51711ab54fac66c126bf5b1`.
- `Extension/Dubon2026/CuspOldNewProjection.lean`: SHA-256 `7939e9ecc57f6aa38ee19371854baaa1e8c4dccb3491e11aa44e8245e186e66a`.
- `Extension/Dubon2026/CuspPeterssonCore.lean`: SHA-256 `bffa8a596b8bdf48ef4d01b2fd474e093e3a25610120e41d3790dd0f349f385b`.
- `Extension/Dubon2026/CuspPrimeDepletion.lean`: SHA-256 `db13482e6f7903560494796c2bfb6e8317d0c88b405b4d0f8dc5af3f74bb31f9`.
- `Extension/Dubon2026/CuspQuadraticTwist.lean`: SHA-256 `81f07fc43f66d246936170ffcbb57ec73aa10893fb635297fc1365a327326829`.
- `Extension/Dubon2026/CuspSelfTwists.lean`: SHA-256 `1272b74ab5f569dc2a4d063540441f55e684debd5092f127c2c6d5cd9a66f371`.
- `Extension/Dubon2026/CuspSparseLowering.lean`: SHA-256 `190271e7f3a3bab494fda1c7f4f4c2e65d6023e4e7a26372c6b72772c0b939ff`.
- `Extension/Dubon2026/CuspSparseOldspace.lean`: SHA-256 `a0f872a1518bcd2c0e0bae7989ca94c3da2aa340fb836235fbfbb7d3a90c094a`.
- `Extension/Dubon2026/CuspSparsePeriod.lean`: SHA-256 `b4983c7bf8b1a00ef11d9a075218d31a85977722c83c3f64fc73a02fa689655c`.
- `Extension/Dubon2026/CuspTwistFunction.lean`: SHA-256 `80c21af6b4af98948a6a066c7499b005b870105157b326620270f7e1f4d0c254`.
- `Extension/Dubon2026/CuspUpperCongruence.lean`: SHA-256 `1c76f2ec007899a2ecf2bd94711d619c96736d4334e82889243c0fd0fcc2ff9a`.
- `Extension/Dubon2026/FiniteCompressedProducts.lean`: SHA-256 `587fc91afe22e2c0f710b0fc424b214576acd649745a1330bac000470bcc1a0e`.
- `Extension/Dubon2026/FiniteCompressionDecomposition.lean`: SHA-256 `1b030c0131b468c1e62c7548051c0914f955f96b23218ead2682204eed27e4e8`.
- `Extension/Dubon2026/FiniteCyclicRepresentation.lean`: SHA-256 `6de943d72ab9bd7a0cd9ab81220bbfde5fdaf72ebac63d6f52c5dd3262bac769`.
- `Extension/Dubon2026/FiniteGroupProjection.lean`: SHA-256 `5af641f925e2c3838224865c73233143883e2c93f3e60c769a14abd6d769cc0f`.
- `Extension/Dubon2026/FiniteLowerTriangular.lean`: SHA-256 `e182d15a44a4bffdfc7a5b3757bb42e1dc9d7c9694669a397ed89d4cf3842cbb`.
- `Extension/Dubon2026/FiniteProjectedKernels.lean`: SHA-256 `54674742211277561813c430713d77c420dffa4ab303a81d0894f807f27fbbc2`.
- `Extension/Dubon2026/FiniteProjectionCommutation.lean`: SHA-256 `727bab35cde1967185b03512364be3cdccb9f16c52111714ff6dbd4e38c077fe`.
- `Extension/Dubon2026/FiniteRepresentationInnerProduct.lean`: SHA-256 `a2ddb4beb2a44733283c9fe4a45615edea286d5c5d1702340d811521b23db174`.
- `Extension/Dubon2026/FiniteSymmetricKernels.lean`: SHA-256 `c5640be7efc9d47e9c1df545f054ba70042b2799f6a27696f4af919ab013ff20`.
- `Extension/Dubon2026/FrickeCusp.lean`: SHA-256 `98ca630e6c4af63b3ae9078928b23cab1d84526ddfdb38ee59ca7752011e7f39`.
- `Extension/Dubon2026/FrickeDegeneracy.lean`: SHA-256 `2fe682e59994b2c9fcddcb289d4727d68f9d627f775eb2e74dc2fcd33fd77a63`.
- `Extension/Dubon2026/FrickeMatrices.lean`: SHA-256 `8598da7d050b7f4989e744e8892c9f570bcef9255b47ee58ec4df466e3cb6c1a`.
- `Extension/Dubon2026/FundamentalDomainTransport.lean`: SHA-256 `490210e86e5c2513a669b2f86a9639e3291421580afed260de69ed76ed290754`.
- `Extension/Dubon2026/HeckeAllIndices.lean`: SHA-256 `f3bc624e60e8b7218ddcdae1990375461f2b018ac00f3b5a18b019c46ef066e9`.
- `Extension/Dubon2026/HeckeAllOldStability.lean`: SHA-256 `b7fa613ceebdca8f906b2ddf09f98dcbe14fdf1c930169d62f8017aca77e10a5`.
- `Extension/Dubon2026/HeckeAveraging.lean`: SHA-256 `c9c94b8f231b8013cf7f196466ade240d65cb4d6f0b0f23556088fc92ad6a6e1`.
- `Extension/Dubon2026/HeckeBadDegeneracy.lean`: SHA-256 `9c4941a7e6da211cf13e47a4ec62f8cecb3a3717c1541840493016610e4f88c8`.
- `Extension/Dubon2026/HeckeCommutativity.lean`: SHA-256 `e8cc6dc608c1431714d2c3aa30e8489594eb6998198dd20a16f826b31a233aa4`.
- `Extension/Dubon2026/HeckeCongruenceConjugation.lean`: SHA-256 `928bafad6f73d4ca7767c61a776bee989429b8e0ab1f291a0d9f552ebd92fe59`.
- `Extension/Dubon2026/HeckeCuspBehavior.lean`: SHA-256 `f36e3e6a21fbf361773fa461c759ace18ae6d1137e9928fae984709e0244cfce`.
- `Extension/Dubon2026/HeckeDegeneracyPrime.lean`: SHA-256 `e671de6bfe8d2637d7e21ce488778e94e0954954369f1fce43711504953c60c3`.
- `Extension/Dubon2026/HeckeDivisorConvolution.lean`: SHA-256 `0c3dd8d83621c6c4f8f88b05da1c8c3b8b18b34c6550e7b68e2c69897079f890`.
- `Extension/Dubon2026/HeckeGoodAdjoint.lean`: SHA-256 `563aac44f0d12944e48ca647b9fc0b0830046e8b78a694ef13e2aeef1aebcb55`.
- `Extension/Dubon2026/HeckeLowerCosets.lean`: SHA-256 `22b2db4aa69e00552968df67a722f18485ddaa4a8f38b4b6fa8cecc9822e9bf6`.
- `Extension/Dubon2026/HeckeLowerTrace.lean`: SHA-256 `b0234d37846fd233725e79ba60115cdb09a0c92d09905e339530d627338c62ea`.
- `Extension/Dubon2026/HeckeOldNewStability.lean`: SHA-256 `b5bb9f71966f1ed3baa8f2e258a53ec6fa29c715a146dc219a7fadbab91b76bd`.
- `Extension/Dubon2026/HeckePrimeAdjoint.lean`: SHA-256 `5bf3ba626cb5c6c8dfa303c3a9aa0006f7d252b8c3b2e63a4ba63d545dfdb816`.
- `Extension/Dubon2026/HeckePrimeInvariance.lean`: SHA-256 `21758a61fee3fba65157df139afc6c964e45e6497f70be46595a63236d4d3ed2`.
- `Extension/Dubon2026/HeckePrimeLinear.lean`: SHA-256 `5229817082c6ecc3108f68bc3b8bffc142384a36285c1f5861efdb8410233b37`.
- `Extension/Dubon2026/HeckePrimeOrbits.lean`: SHA-256 `39178cfde857bdf40014ba81976581a6de8a035c14852e200d55b18d4b08dbda`.
- `Extension/Dubon2026/HeckePrimePowerArithmetic.lean`: SHA-256 `bbf0febf759064f625f363a323842dc69fd30e26b12d7f461772d1cc95fc7c16`.
- `Extension/Dubon2026/HeckePrimeReindex.lean`: SHA-256 `9f60e7a5da720ce46ab0c9c260ab2ee1be5e493a51b7773fc6059f27ec459a98`.
- `Extension/Dubon2026/HeckeProjectiveConjugation.lean`: SHA-256 `4cfbf7cb724b4ad449d4e261cd850930a6a9f9afd6269d270e92d5630be9d747`.
- `Extension/Dubon2026/HeckeProjectiveCosets.lean`: SHA-256 `70714175fd8d336a0677f8a8a1121f3be3d973b993d1d2388a54beb9c31dcc2e`.
- `Extension/Dubon2026/HeckeSlashIntegrability.lean`: SHA-256 `69a5d37cd14b98105280b840cfac71fddcc0a89978925aecad256a5f2da89b5f`.
- `Extension/Dubon2026/HeckeTraceIntegral.lean`: SHA-256 `4cf931234a859ccb401a8f79a38e2a6c129f1921f9df3faf46ba066b11cbf6d5`.
- `Extension/Dubon2026/HeckeTransversalTrace.lean`: SHA-256 `df48e73399290422275a29e6a812928723883b63a1119c684b9adb983c54fddc`.
- `Extension/Dubon2026/HeckeTriangular.lean`: SHA-256 `4ee6d4b05014a95ab941d36473ae98261c8040a828d775f358e917f00a61d249`.
- `Extension/Dubon2026/HeckeUpperCosets.lean`: SHA-256 `e1b567625b4e9f2677271ca99d6b7a6ab89324f7fd61e41b0271b941053eabc5`.
- `Extension/Dubon2026/JessenShift.lean`: SHA-256 `29d8151fa305ce30b413e65a9555acd3517dc3bb14593a2fdfd9078d80ebd6f6`.
- `Extension/Dubon2026/LevelLowerFactorization.lean`: SHA-256 `cc0f26e97fcecc70f1e27db2878277e1931a621662bcd1fa9181c30bfb96b6bc`.
- `Extension/Dubon2026/LevelOneSelfTwist.lean`: SHA-256 `12e208bc28e9d461b04734970e2d417baddc579efcb3721e061f980fd9c1c2ed`.
- `Extension/Dubon2026/ModularCoefficientJets.lean`: SHA-256 `d0a10823c2d4abc061d8e6808d7b9eb08abf9c7b6a24c907a84c8fbe0935697f`.
- `Extension/Dubon2026/ModularCoefficientOrder.lean`: SHA-256 `ce63ac4883884e54d11fe64629fd6c3fcfd7f9c21471c2c07a6e91df88196060`.
- `Extension/Dubon2026/ModularCosetProjection.lean`: SHA-256 `ab956ad140628ed7723ffe1b7649e0b14b66a9a26663b5cf1a42083cae953781`.
- `Extension/Dubon2026/ModularDegeneracy.lean`: SHA-256 `5d04f34cfdff8993da27b553691dea2212f68e154537120aaf46e5fa3b20f0c4`.
- `Extension/Dubon2026/ModularDegeneracyCoefficients.lean`: SHA-256 `8ca385239348efe2dd2a164f64e539be6e07d9035c7b393ce6f6458607e3237f`.
- `Extension/Dubon2026/ModularFiniteDimension.lean`: SHA-256 `fb5fb1112d5a8a381d506d6a79da5e30d9dcb667a25aa8d75bff1d55738de3b4`.
- `Extension/Dubon2026/ModularGamma0Domain.lean`: SHA-256 `bf4c540651b8b672d184285095f31154c7e0d2012bec41a2e12a7971844bc6eb`.
- `Extension/Dubon2026/ModularNewspace.lean`: SHA-256 `2ac70ac991f590add361416a60e583db24ce51e3fe27ea9d80e17367816a5e9d`.
- `Extension/Dubon2026/ModularNormFactors.lean`: SHA-256 `9be126a14fd756b4d88c5a92dc9d5329451363245eb01996c528be135b09b1d6`.
- `Extension/Dubon2026/ModularNormOrder.lean`: SHA-256 `04a515959fdf74275ffa6d6f96dbf288446549a19a09c20150ac1a98162f5e56`.
- `Extension/Dubon2026/ModularOldspaceWitness.lean`: SHA-256 `04c6c7064b2a887c17d4d7fabc2eddea6789c0d100d3224e5c0f6ba9e18eecf3`.
- `Extension/Dubon2026/ModularPeterssonDefinite.lean`: SHA-256 `2945455df0b1f3910b52eac8c8f5f45813b9d85c093bc3aff1a4d49f0e838e35`.
- `Extension/Dubon2026/ModularPeterssonLevel.lean`: SHA-256 `cbc0f916b9c2a489ce2861f5becea4e8396b26cc2c0d2169a18b77549fe1600f`.
- `Extension/Dubon2026/ModularPeterssonMeasure.lean`: SHA-256 `abaf73a3d9fa71f6db9a8ec02bdbc55f98f535c4c87c168dd53b1586ed084296`.
- `Extension/Dubon2026/ModularProjectiveDomain.lean`: SHA-256 `74704b24b71ee8a5a951fdc7736b8e7031e99a2c94d67583b377dd2441cf4cc0`.
- `Extension/Dubon2026/ModularRealProjective.lean`: SHA-256 `8c9a83b3e4d3cf4bf785800193c963d36e927d21981c8531d0161fc5eaf637c2`.
- `Extension/Dubon2026/PeterssonAdjugate.lean`: SHA-256 `3c8cc38b9413132a16b026556f44409c2016b14dff8818e53155b4e5d619b2f8`.
- `Extension/Dubon2026/PeterssonSlashTransport.lean`: SHA-256 `fc5e3be09ed3a5cc86e86191a4f7cb3b48f3e951530393e3909615ec77b2a4f2`.
- `Extension/Dubon2026/PrimitiveCoefficientReality.lean`: SHA-256 `e10c4d5ec06d7fdabfdcef2c7a565c00a94ee3416413e5d8e80fc6469ef831fe`.
- `Extension/Dubon2026/PrimitiveCuspForms.lean`: SHA-256 `f6c0d3d16d8dcbb01931af35241ee68ca6e4090d2fa1cb365103b2765c7e7a0c`.
- `Extension/Dubon2026/PrimitiveEigenSpace.lean`: SHA-256 `0de9c0e47cf9a9b810f4d30e9fa07d883d7f12c4d3685ab16cc9e0df7aae3498`.
- `Extension/Dubon2026/PrimitiveFullCoefficients.lean`: SHA-256 `da683c9672e4fad91152b9072532dd9590d68dfb727bdc3a8058606c33cabf5e`.
- `Extension/Dubon2026/PrimitiveFullEigen.lean`: SHA-256 `ba31bea33c21876ba27ff2eff75d46e7222b20702ea5180bc0cab3258f73a688`.
- `Extension/Dubon2026/PrimitiveGaussTwist.lean`: SHA-256 `f3d81dbf557e21cdf16e1421b6ba1556548434b6f2f3e58abd149f62551bfbbc`.
- `Extension/Dubon2026/PrimitiveMultiplicityOne.lean`: SHA-256 `7c19cc447aa4d240d9a90238f281602f16bcbe1557ea029ff86e35666fe1c8d9`.
- `Extension/Dubon2026/PrimitiveOldEigenExclusion.lean`: SHA-256 `f7e89497da213ff2da1a82112d75db934b71b90de18eedd590a4464857bf8ef3`.
- `Extension/Dubon2026/PrimitiveSelfTwistCoefficients.lean`: SHA-256 `53cb5aee08392688b6b36d06adaabe2c5272ef1ef37aa27a9431f03727987151`.
- `Extension/Dubon2026/PrincipalCharacterTwist.lean`: SHA-256 `8fb73e804b57561357d6d7bf5117af1361d5073ee1db1e9466cdb61ba128c784`.
- `Extension/Dubon2026/PrincipalCommonInvariant.lean`: SHA-256 `ff4fd4873b967de5a8dabcbbe516b3548a88735b2bb5bfa1ca575444d45d3230`.
- `Extension/Dubon2026/PrincipalCongruenceQuotient.lean`: SHA-256 `04a08777e43228494ccfaac6adb066b1e6206324e39e3c51628fa178ab2e7d82`.
- `Extension/Dubon2026/PrincipalCoprimeProjection.lean`: SHA-256 `906714b475d22d69f0df22efecefd9922f8208b138d4a7ee6b6b01a20f0608bb`.
- `Extension/Dubon2026/PrincipalCuspAction.lean`: SHA-256 `4bdd82df7401da24146fb97c5aa28cfd73e4ef56cdd790169b01e3e527946a47`.
- `Extension/Dubon2026/PrincipalCuspOrbit.lean`: SHA-256 `92e14be86e28f77ebb63d9b282465c2575c3a2a93c46d9212d41871aea7203b2`.
- `Extension/Dubon2026/PrincipalCyclicLocality.lean`: SHA-256 `30f31370dea57f5b82465a40f9711afac6ffaf863a3c3bca423275aee960a98c`.
- `Extension/Dubon2026/PrincipalCyclicProjection.lean`: SHA-256 `bfb40e61ac9418761eadcb4da4eec316e72a6d7188d1248a2093be1cf40c54b2`.
- `Extension/Dubon2026/PrincipalDivisorProjection.lean`: SHA-256 `841bde4eec5a4aedd3d7503c1dfe8661f72a0943c7afaaecbbf9822b85a36052`.
- `Extension/Dubon2026/PrincipalLowerProjection.lean`: SHA-256 `dacf61d48b21d54f935a6b1c3a2826b6ecf941b573860d6bf9c6be110d43567b`.
- `Extension/Dubon2026/PrincipalOrbitCoprime.lean`: SHA-256 `d84492caa4d241d9e9f61544aabbc9887fc5f511d8c6faddda5fdf2994fdbb74`.
- `Extension/Dubon2026/PrincipalOrbitProjection.lean`: SHA-256 `d86cef512c71a726f75051c35d05dc3b385857bbf22fdbbada4e0672e509984c`.
- `Extension/Dubon2026/PrincipalPrimeFactors.lean`: SHA-256 `f7255e52a3f835ff95ce6363dca947d172ef1f49bf24d87e349ce23782ab04a4`.
- `Extension/Dubon2026/PrincipalRescaledCoefficients.lean`: SHA-256 `b41bd61cd8bca65821161e5bb0fbbed566e567bfdcd4a5c6fc5e9c7b1cb68161`.
- `Extension/Dubon2026/PrincipalSupportDecomposition.lean`: SHA-256 `b812f183f2b5f5426d67ff4e5590ec242fb0848715de48426f16dcae66ae98d4`.
- `Extension/Dubon2026/PrincipalTranslation.lean`: SHA-256 `801ab551f2ca677c10f0116b6056fe4163e7c0555532ea3fefafb374c240231c`.
- `Extension/Dubon2026/PrincipalUpperDescent.lean`: SHA-256 `e28da361def2e867e25fc8a9ce744c55b03886484ce3116c50b3bb4b58d19e24`.
- `Extension/Dubon2026/ProbabilityShift.lean`: SHA-256 `6395c320d54addce58ac1087824e11dff49ddfc62d3e02191c554ba5a67ef032`.
- `Extension/Dubon2026/QuadraticTwistFricke.lean`: SHA-256 `4e836eb4529b469657b0337fbf672b617558e31df5f182bc9e562ccf3fe32073`.
- `Extension/Dubon2026/QuadraticTwistHecke.lean`: SHA-256 `fb98fba86cdb5dba8c1a933fe3903e38eb2f977af41939e8e4fd0ed891b3ed83`.
- `Extension/Dubon2026/SL2Reduction.lean`: SHA-256 `9dd40dde2439aab39fdd9f96bace4f866d547d14c31a1e86b2567c67598ef226`.
- `Extension/Dubon2026/TwistFrickeTransition.lean`: SHA-256 `17f2b2234e92994f3164de269a8f3fa08446b10c7810583fa6273586cad3adcc`.
- `Extension/Dubon2026/ZeroCountShift.lean`: SHA-256 `f06a71ed285a7f8506300b18e338b3dba8a6b8b99b89899cb094670c2a4b1d1e`.

### Shared verification scope at DUB-15 acceptance

The earlier shared-file hashes record their earlier review state. The appended consumers and registrations are covered by the current 377-module receipt:

- `Extension/Dubon2026/SemanticRegression.lean`: SHA-256 `f759d92b1bcb3df5ea7198e56ebff08cde234de438b43675104d20315c1a2579`.
- `Extension/Dubon2026/Audit.lean`: SHA-256 `37f04015f68aa6761fa54e68ea7c2bc6b0285b769ad2eedba8f9d3f08e785cbe`.


## DUB-16 — Actual general-level Rankin–Selberg and weighted energy

**DONE after the 604-module sequential verification on 7 October 2026.** The acceptance clause is unchanged. The frozen source at lines 1534–1605 uses actual normalized Fourier coefficients of a primitive non-CM eigenform of even weight k>=2, positive level and trivial character. The public theorem `general_rankin_selberg` proves a stronger result for every nonzero actual cusp form at every positive level and every integer weight k>=2. It uses the same genuine period-one q-expansion and normalization lambda_f(n)=a_f(n)n^(-(k-1)/2). Primitive normalization implies nonzero; no source form is excluded.

- **Actual input and positive constant.** `cuspRankinResidue` is the proved Petersson-integral residue, not a freely supplied main-term constant. Its positivity follows from nonvanishing of the actual cusp form. `general_rankin_selberg_source` exposes the literal finite sum over 1<=n<=floor(x), a form-dependent uniform constant for all real x>=1, the actual positive residue and the exact O_f(x^(3/5)) assertion.
- **Genuine general-level reflection.** The completed Gamma0 lattice/Petersson integral is unfolded and reflected into its actual finite divisor family. `general_rankin_riesz_reflection_source` expands the signed Mobius amplitudes and positive conductors. The dual coefficients come from actual rescaled q-expansions; their reality, nonnegativity, linear mean and absolute convergence are proved. No scalar general-level functional equation is assumed.
- **Contour and infinite sums.** The numerator is entire with the genuine two pole residues removed. The true reflected coefficients give the left boundary bound; the generalized strip argument controls the whole rectangle and makes both horizontal edges vanish. Finite vertical integrals are identified with actual coefficient-weighted Gamma cutoff series. A uniform summable majorant justifies the infinite-height interchange, and the finite signed divisor sum commutes with that limit. `general_rankin_riesz_dual_source` has the literal original Riesz sum, both residue terms and the actual dual coefficient series. No integral-value premise or formal interchange remains.
- **Sharp error and original coefficients.** Actual low/high coefficient power bounds and Gamma-kernel second differences give C_f x^(3/5), using the same natural floor cutoff at both forward/backward base points. Positivity is applied to the original Rankin convolution sequence; signed dual amplitudes are bounded by their norms. Positive Riesz unsmoothing gives the original convolution estimate. Genuine Mobius deconvolution and its convergent inverse series transfer exactly this error to the original normalized cusp squares and retain the genuine main term.
- **Every weighted source case.** `general_cusp_weighted_rankin_selberg` applies the proved uniform remainder to the exact Abel identity. It proves the asymptotic below 1/2 for every real sigma, bounded additive error at 1/2, and bounded nonnegative energy above 1/2. `general_cusp_weighted_energy_source` unfolds the actual finite norm-square sum. The error theorem retains the literal real integral with coefficient 2|sigma|. `general_cusp_weighted_energy_endpoints_source` explicitly supplies the three-fifths error at sigma=0 and the logarithmic transition at sigma=3/10. Neither the Rankin conclusion nor an energy certificate is a caller premise.

The existing DUB-15 object/normalization theorem supplies the actual source form. Every registered implementation module, all five new source consumers and all transitive theorem dependencies were included in both zero-diagnostic audit executions: 5,046 exhaustive theorems, 2,838 explicit registrations; all sixteen linters passed. The foundation and paper logs and shared source hashes are recorded in the corresponding reproduction receipt. Only documentary/gate metadata changed after verification. Deligne, non-CM Sato–Tate, the classical/automorphic bridge and the final unconditional modular conclusion remain separate DUB-17–20 obligations.

### Implementation hashes at DUB-16 acceptance

- `Extension/Dubon2026/PrefixEnergyBounds.lean`: SHA-256 `49ab5b854c637996b3165d608218face629268f25d4eb3b7d3b9003d515c352f`.
- `Extension/Dubon2026/MeanSquareEnergy.lean`: SHA-256 `3a44a077a64fd25bdf37b3a3f6b675fb161122085972776087e70dbbccb62eea`.
- `Extension/Dubon2026/WeightedEnergyAbel.lean`: SHA-256 `961fff40c8e1dd42df1ac5e487ecbbad47c805a476bce680c11dff162316b9ad`.
- `Extension/Dubon2026/PowerIntegralAsymptotics.lean`: SHA-256 `474a93de1e2a1860dc983c1233a8a85d8100da59ae247658cc479e9440219925`.
- `Extension/Dubon2026/WeightedEnergyError.lean`: SHA-256 `e7d565977b3bcd7d3476928b72ff981e7cc7bbde0ccb567ab2d1d9001607d6c4`.
- `Extension/Dubon2026/WeightedEnergyAsymptotic.lean`: SHA-256 `e5044f3f777bae0603447d7d55e2e1be49d556118eedd472bd3070638ba682ce`.
- `Extension/Dubon2026/RankinSelbergEnergyConsequences.lean`: SHA-256 `b263beb7381bc41143e9984a219f28fc6ea25af25b21e1a870d167ebec0dbe91`.
- `Extension/Dubon2026/RankinSelbergInputBridge.lean`: SHA-256 `c956f3ab026c26882d3d48285ad2622cdace2181a10523ed48d2d7b5faf3cd5d`.
- `Extension/Dubon2026/FourierNormSeries.lean`: SHA-256 `8e79feb3eac3e936b9924c8da06fdc0c282a45d2c553c80e6210e708fee05e29`.
- `Extension/Dubon2026/CuspFourierEnergy.lean`: SHA-256 `7e8ff6bb90646aaefb6233261d2e511acfd6e22f7bb6f47f2889f5071effef48`.
- `Extension/Dubon2026/CuspEnergyBound.lean`: SHA-256 `a78c286313e1acf307a8e3314415801127405c6132e4d26b7d1966fce4f3819a`.
- `Extension/Dubon2026/CuspSquareDirichlet.lean`: SHA-256 `f3e2f3d19a875082877d88cbdc60fd328fa08355f6e9d9da2a6ae7a1610d062c`.
- `Extension/Dubon2026/CuspMellinEnergy.lean`: SHA-256 `939db5542fdab266486e3399a18ba2c0a6f7ec482dec7adc507379f1a15ffcba`.
- `Extension/Dubon2026/CuspComplexMellin.lean`: SHA-256 `3da46c6ce96a0488acf6c4bc5f4726be40f76626566d614d28eaffb08376ab0c`.
- `Extension/Dubon2026/CuspRankinSeries.lean`: SHA-256 `8061cb8e764d5ba2b98852e3383a4b8d937523480660b788d292e3d7da9b8d84`.
- `Extension/Dubon2026/EisensteinLatticeKernel.lean`: SHA-256 `fa7f682769fd00300292a38743bf17329ba5568db95ff27712962507b32c12f4`.
- `Extension/Dubon2026/Gamma0Eisenstein.lean`: SHA-256 `ec588f809389c31bbe215f3c3a81fef8a3795cf43874464be086acac9860db97`.
- `Extension/Dubon2026/Gamma0EisensteinHolomorphic.lean`: SHA-256 `aa4822c3f07d852884433b8357e041b82b25c4fcd61ec5ebce31373c7bfe7252`.
- `Extension/Dubon2026/PrimitiveEisensteinCosets.lean`: SHA-256 `4a04a36bfad57e4d1298d420612b76ca9b5474c0c3aa377c2bd38d22f84c074d`.
- `Extension/Dubon2026/ProjectiveTranslationStrip.lean`: SHA-256 `c02ed6f974aace2c8e2de2312a368838f15e8cdc2df2ed2dc4a1348ea28af3b4`.
- `Extension/Dubon2026/FundamentalDomainUnfolding.lean`: SHA-256 `fc6f5a8447ef0245700509543b28821f3a520e7214151201e911ffcfdb633632`.
- `Extension/Dubon2026/Gamma0CosetUnfolding.lean`: SHA-256 `b8d01190ef4a294b961acf7af4d4f78d8b9f2c52ac930fe84b3a53490865a8f2`.
- `Extension/Dubon2026/ProjectiveEisensteinCosets.lean`: SHA-256 `428a7315a41978dde9810962e6e17b07066626008b1551972e0786d84acde286`.
- `Extension/Dubon2026/EisensteinRowFibers.lean`: SHA-256 `3c961870cfc62551cf09a74e25e6a4ad351a351d72f66d84f5d20f4b28257ca8`.
- `Extension/Dubon2026/EisensteinRowCosetSum.lean`: SHA-256 `a65f0105f18e89726d5041a116a441e453427cecd877c3c658b3d55392efc4d5`.
- `Extension/Dubon2026/Gamma0EisensteinUnfolding.lean`: SHA-256 `7526d58d2b1c7d91e59a4c134d300bffb888f7642a77a6583e9dd035ce28a6e6`.
- `Extension/Dubon2026/HyperbolicStripIntegral.lean`: SHA-256 `1f8dcd4f7b8948898cde9f909969c67d0bb5e76e36db1c23ade313f9e4522357`.
- `Extension/Dubon2026/PeterssonStripMellin.lean`: SHA-256 `fb3331e665f78da778a6f51b16d2a46199a4e64f2be6e11deda6af42fa7819c0`.
- `Extension/Dubon2026/CuspRankinUnfolding.lean`: SHA-256 `225edb48bb3e11734faa3121a91851949012eb3c008843fbd9a4d4b8be909592`.
- `Extension/Dubon2026/LatticeThetaKernel.lean`: SHA-256 `d504cb3202e3f3a83a8460b16fc9842ad55049cb3ab5e649080aa7a260fc7156`.
- `Extension/Dubon2026/ShiftedGaussianPoisson.lean`: SHA-256 `f697f78764e69de36b5aca1b7e8fd55343c27da2802b757f6dd7a46bcb8752da`.
- `Extension/Dubon2026/LatticeThetaFourier.lean`: SHA-256 `8827a7bea10af06b4a2e101fd4ae10e6732fc82772a05dc08b7914aa3c111cdd`.
- `Extension/Dubon2026/LatticeThetaPoisson.lean`: SHA-256 `a9f338ff2661077a6571dff4f36807dd093a4d6a4644173b62a2a11298538d1f`.
- `Extension/Dubon2026/LatticeThetaDecay.lean`: SHA-256 `feb691d598292f8fba08d8443bf3dd317c01b90fa7a6a50226d04c9f19169668`.
- `Extension/Dubon2026/LatticeThetaMellin.lean`: SHA-256 `ec5bab483ffb2c5864e33caaae7c08179a80fe5c39e66c22ea60a92281c8ca10`.
- `Extension/Dubon2026/LatticeThetaHolomorphic.lean`: SHA-256 `1d0229e36b3c917b845c5285e547c834b5e8e10264fa4a458c2c5cd7bd372966`.
- `Extension/Dubon2026/LatticeThetaFEPair.lean`: SHA-256 `3e9ea2a37d2495c21788af77515a74d4cac46b68d16361d9bf15482067cdd8c4`.
- `Extension/Dubon2026/LatticeCompletedMellin.lean`: SHA-256 `792263a18ef8a5c71d506de41d2466bef49a47c04893289929f89ea973fb6523`.
- `Extension/Dubon2026/LatticeEpsteinMellin.lean`: SHA-256 `efb5ef61aaaa0b7a248d2e127122fe6e4cd4f624343a5e2540152ea4bccd6420`.
- `Extension/Dubon2026/PrimitiveLatticeScaling.lean`: SHA-256 `3d7df063900f27ac2c9c3e563ec6d48498b8527ca9f69061bab8575390b43fe7`.
- `Extension/Dubon2026/PrimitiveLatticeSum.lean`: SHA-256 `d0c695611f2a8fa9512f920a058eaca56cf033fbcabc670bf2bd9b035031fc2c`.
- `Extension/Dubon2026/LatticeEpsteinPrimitive.lean`: SHA-256 `85fabc0f08d328eb487cd5afa59ce0b7258278e73c073766a5f1a2c43208cfd8`.
- `Extension/Dubon2026/LevelOneEisensteinContinuation.lean`: SHA-256 `90a185b6a05c904e3329f9138655c6b1cef6bdbe7bb424f6a02995a433993e9c`.
- `Extension/Dubon2026/Gamma0LatticeSieve.lean`: SHA-256 `5eaf579c2f3691534b957e3a726250054c3198bae9d6a00762851c34f2b46bb1`.
- `Extension/Dubon2026/Gamma0SievedPrimitive.lean`: SHA-256 `f7a5d4f7106ad19101a2ba435e8ea31b61a87c1a01d57a90985d3f7d5a49c89e`.
- `Extension/Dubon2026/Gamma0PrincipalFactor.lean`: SHA-256 `b6304047545752b5e715fb0046d494496b64aaf888378165f82e1c85ab9eddfb`.
- `Extension/Dubon2026/RectangularLatticeRows.lean`: SHA-256 `44783cfe334a99242555061cf8a8ada1380cfa20c970e7e1e05479067f8023dd`.
- `Extension/Dubon2026/Gamma0EpsteinSieve.lean`: SHA-256 `dd238c84fae87aae2489bcc22b805366388569ed2c33295172888cb98f0c86f8`.
- `Extension/Dubon2026/Gamma0EisensteinContinuation.lean`: SHA-256 `bf5d1138c227f926fdcfdeb2904ccd6c5abef6af4142169bb8a419ab059cdb83`.
- `Extension/Dubon2026/Gamma0EisensteinResidue.lean`: SHA-256 `22e4ebe361c8ed9615bb177ff64f17f353bc5e3b65536280bdbc6ce582219aa7`.
- `Extension/Dubon2026/LatticeMellinMajorant.lean`: SHA-256 `58da84d76a2dd96f4487a03c18b52e3cc8c933e735af5b16468bf1366a3d72f1`.
- `Extension/Dubon2026/LatticeMellinTailSplit.lean`: SHA-256 `777cc1bb28683f35e9970cfb002b47b6eeefefcbf6dc1ab133f68c978be03378`.
- `Extension/Dubon2026/LatticeEpsteinMajorant.lean`: SHA-256 `d46a55b604a787b7f4d1ab8ba4483b5d565b19e41cbdd3a5efa475be4db58c6d`.
- `Extension/Dubon2026/LatticeSpatialMeasurable.lean`: SHA-256 `484db0bfec0b2f245601b4a30c65dac023ee08a4507b9719aea8c67889172057`.
- `Extension/Dubon2026/LatticeFundamentalBound.lean`: SHA-256 `8b65f4169cde184c0adec936ed9b9d103fe090cf7ca2fc66ff805cc084ac323b`.
- `Extension/Dubon2026/CuspPolynomialDecay.lean`: SHA-256 `d4c03be219d4946c6b1d16c54fff8a96e944457f6711234b874e3abfe2f5ab1b`.
- `Extension/Dubon2026/LatticeCuspMajorant.lean`: SHA-256 `6b5f46b4c415f6fc9470c8f4373be4a5f00a5202cbb56163a1b67018c384543f`.
- `Extension/Dubon2026/RectangularLatticeMajorant.lean`: SHA-256 `a84b3be8643360b640839658c417117871a8e61b10edc5aa6e0481aa597bb49e`.
- `Extension/Dubon2026/LatticeCuspContinuationIntegral.lean`: SHA-256 `a7baa969066708c547d81393708233cc7911c6a1fdc0cc91208914c5fb5d4e3a`.
- `Extension/Dubon2026/LatticeCuspHolomorphic.lean`: SHA-256 `3bb3d527816e17208894d9eec967b73bd5d2c2163f1811bc1139ae24b7bccb76`.
- `Extension/Dubon2026/LatticeCuspResidue.lean`: SHA-256 `450d577d389c7de2b5c024e80b6b4e7cf5bdfd9deae6238a55009f5c6cae8651`.
- `Extension/Dubon2026/Gamma0CompletedCusp.lean`: SHA-256 `26c0daf87ba2c1f18fafe9ec6cccb30f07bfae45c732950eab724da855c4b134`.
- `Extension/Dubon2026/Gamma0CuspContinuation.lean`: SHA-256 `441b318ac92e4059150b48779dac9598c41df35683736f4bf1ef79347f5b4753`.
- `Extension/Dubon2026/CuspRankinFactor.lean`: SHA-256 `e919b8890df38c806438f62259ef54fcbd096921db95b081f3ab350272a1ce3b`.
- `Extension/Dubon2026/CuspRankinRealContinuation.lean`: SHA-256 `eca371d8d41214f32c858f9308bb197123c9adb59ebb6d281edeb96afb4cde31`.
- `Extension/Dubon2026/CuspRankinComplexContinuation.lean`: SHA-256 `26ed434e23898f452980399098050f7e7e23c90833d1bab5d244e05fd2d7c4d4`.
- `Extension/Dubon2026/CuspRankinContinuation.lean`: SHA-256 `b0bd4a47e82453c22a8bfe3854aafe077071c1e1bb469e2342e13b97b2c6a5ee`.
- `Extension/Dubon2026/CuspRankinResidue.lean`: SHA-256 `00bcd2fc5770b69d344783819a0c450a378ec03b27c5f2581dbcb93f6fbf4761`.
- `Extension/Dubon2026/LatticeCuspFunctionalEquation.lean`: SHA-256 `787a66094a224c019041634b6e6cfa1d464c6ad2b7abc29d73f3e0412fda79ba`.
- `Extension/Dubon2026/LatticeCuspStripBound.lean`: SHA-256 `3dee8ec5245b9475745cffb8857351d79cca5c530cac500900431e378a977b72`.
- `Extension/Dubon2026/Gamma0CuspEntire.lean`: SHA-256 `bb639d68b7a9a893f2241380a61ab4da9cc45064f6b3c5599a5541da32a08713`.
- `Extension/Dubon2026/SquareLiftLSeries.lean`: SHA-256 `c20d45bdba34cb6332b0775157bc44e3a90f6b2d34ef5b1972598a7be8a41b91`.
- `Extension/Dubon2026/PrincipalSquareSeries.lean`: SHA-256 `380e492b51aad809c6ccae84c01a996da2a39e9a2edb001741f642a355eae52d`.
- `Extension/Dubon2026/RankinConvolution.lean`: SHA-256 `f270f4ff4fda5a72374602bc781264b0ce5469d3ff7887ff22d7f3716b21cc0e`.
- `Extension/Dubon2026/RankinConvolutionCompleted.lean`: SHA-256 `899e6b41c358646e41c2d84c2a9b6f8abb84bb65ae990d38b8cb1d3a2a024f1d`.
- `Extension/Dubon2026/Gamma0CuspStripBound.lean`: SHA-256 `2566efe4d679ae5306b0421b52629e182de91d7c6ae11ec114a7fdc06670512c`.
- `Extension/Dubon2026/CuspRankinPoleNumerator.lean`: SHA-256 `b89467c627b600111cd4d14aff1afd2738be294f296e499f7764b71a911cb6da`.
- `Extension/Dubon2026/CuspRankinRegular.lean`: SHA-256 `94077f45f0cd02efd3b7c7115132b6057c14118e091334dfb85538e423e96f73`.
- `Extension/Dubon2026/CuspNormalizedEnergy.lean`: SHA-256 `ea75cd98a79f773c705564c2e5e0649691be9323c4ab00a08047abd8d03d3622`.
- `Extension/Dubon2026/CuspRankinMean.lean`: SHA-256 `28ff272db9ddea77ecc8fddb2bc62a92602305790cd166480e54d35811a34207`.
- `Extension/Dubon2026/MoebiusSquareSeries.lean`: SHA-256 `c601ac3f4ed08a87e1e9ace4930a5150ead605e44dbe59fd722cdc21e96b27ca`.
- `Extension/Dubon2026/RankinDeconvolution.lean`: SHA-256 `d8ba4f17e7b69966c3f2a733cedfd22871f3d9db8a1ab22dd91017d005a9e7fb`.
- `Extension/Dubon2026/MeanWeightedEnergy.lean`: SHA-256 `0ebbcb7d36c9d4265cffa95815ccfbb3dba85223565e64d646f4415ad456d545`.
- `Extension/Dubon2026/CuspWeightedEnergy.lean`: SHA-256 `84ec16522adc9b8d538c97831e601fd3795f9f506128e3ecc220c3bf5e676387`.
- `Extension/Dubon2026/NewmanKernel.lean`: SHA-256 `bb04a855195bd3f1861175908039f6728071bd7d3d6bfe67570eb80288e54e86`.
- `Extension/Dubon2026/NewmanLaplace.lean`: SHA-256 `c9a60ab5a88b5ce0e81319c02ea4dbb446d7dbcad4d789577132eb23a27fe536`.
- `Extension/Dubon2026/NewmanHolomorphic.lean`: SHA-256 `cf3a60a5409723e7da5369ee1ab76fefe4041048e0887535b4df503309582ce8`.
- `Extension/Dubon2026/NewmanRectangle.lean`: SHA-256 `9fbcf77f2055da803172b0048c20d801c0d645b8fd2c97f6a38827795620154b`.
- `Extension/Dubon2026/NewmanIntegrandBounds.lean`: SHA-256 `2d90a14d2ada2b4fc76507be1d45361ec2be55bae286590ac526c3ea3942f5ba`.
- `Extension/Dubon2026/NewmanContourBounds.lean`: SHA-256 `3c6cccec665fef4496a0afadec994cce3a1b18b1a56bd5cdf57548fbd2510a24`.
- `Extension/Dubon2026/NewmanDecay.lean`: SHA-256 `1012dea74d134a1fb8f4bfa221bc9a8b29a67a1cd7f3706d831bbbca51db286e`.
- `Extension/Dubon2026/NewmanContourIdentity.lean`: SHA-256 `f9f60b8cbe8023059cb3562cb9d3adc3337d75873bc2cc1ac2d44bb1bbb58bb8`.
- `Extension/Dubon2026/NewmanTauberian.lean`: SHA-256 `11cdff4a2071f4a1fc4966113d1a66283129448db9bd2206f5f6036b4f8b4a49`.
- `Extension/Dubon2026/NewmanSquareData.lean`: SHA-256 `58b5a402ac58fd3baccfc083d20a56577651f69e6087a018492d0364ea1eeafe`.
- `Extension/Dubon2026/NewmanSquareLaplace.lean`: SHA-256 `03887bbc6d7e1ef59ef05255669bf3931bd8d7aa22d14e7bc6e69ba38b4fe125`.
- `Extension/Dubon2026/CuspCentralTauberian.lean`: SHA-256 `e30260509271670dc061e4fa54d54b97831ed03874fa1a0e341797f3cfdf40b6`.
- `Extension/Dubon2026/NewmanSquareAbel.lean`: SHA-256 `fb31e458260fc3b06d9e9f68e8b2d7d421d00d660b5a5df372d1a2a8153b78b3`.
- `Extension/Dubon2026/CuspCentralEnergy.lean`: SHA-256 `27a408ce48b764133caf11fa4dae3b3a4376011a96849a44472f8b268d86c83c`.
- `Extension/Dubon2026/ConvolutionSummatory.lean`: SHA-256 `dfe92bfb1b870d5caf46088c9972b91b41c45f2cd857dfb196e73019bc550a7b`.
- `Extension/Dubon2026/RankinConvolutionEnergy.lean`: SHA-256 `991e06f6a175788e1ae45a9eb9a1d393c85d063451ba990f0a5a4b0a924e73f8`.
- `Extension/Dubon2026/PrincipalSquareMass.lean`: SHA-256 `0fea31086797df0893204f6c2088e2961e12b9e14bea31138f3b316d4fdf1fb9`.
- `Extension/Dubon2026/RankinConvolutionRegular.lean`: SHA-256 `cad3636934a3d5025053ce8d291bdc9c8a715874eefeeebdd7c0f93e485e56d4`.
- `Extension/Dubon2026/RankinConvolutionMean.lean`: SHA-256 `1b3bf6d06fc541163ea37bc79394191e7b3d8edaa4ea908bf4ed8c5287df0e62`.
- `Extension/Dubon2026/RieszSecondKernel.lean`: SHA-256 `c0c3f2e615690d99c45ab57230e1335f4b0da90e5ba75ac6c1d2c56ea0dbaecd`.
- `Extension/Dubon2026/RieszSecondSum.lean`: SHA-256 `5e72c9588323929806afd74aac9b438bc4e437a4d71afdd3251190df8a09e61d`.
- `Extension/Dubon2026/RieszSecondError.lean`: SHA-256 `c91aed994e5b144a827e2f99d127094ee33c613861bf3ad7a24ceeb4e72ec698`.
- `Extension/Dubon2026/RankinConvolutionRiesz.lean`: SHA-256 `1bf814acaabbca9e0ed14cd2977d3d7794c6f3b4af51a2fbcebe0aeb8b535b04`.
- `Extension/Dubon2026/GammaVerticalPhase.lean`: SHA-256 `5e7d1e3e99f60597a96f00c86c66c38dd94c8f95136cf8a7b78a2d4c5411c1ba`.
- `Extension/Dubon2026/TrigammaIntegral.lean`: SHA-256 `6eec448d9f63e77f91d6e06e0e44f05b94835794acfc8ec52667d26ccc1061a9`.
- `Extension/Dubon2026/TrigammaAsymptotic.lean`: SHA-256 `bece584f42f24afdf6ff36177afab5ab7f64bb113b243e3d2c972969c776402c`.
- `Extension/Dubon2026/GammaPhaseCurvature.lean`: SHA-256 `9014ea4521a774d434e40e38fbb4deab049617a9c09651b9b6742f79b8ed8eba`.
- `Extension/Dubon2026/RankinGammaPhase.lean`: SHA-256 `3ad6908e412fd12a91832496df0f9b0424e58a4b462e058cb9bf09ac7da56079`.
- `Extension/Dubon2026/RieszMellinKernel.lean`: SHA-256 `1204e5f776b36b119715e3ad7543aa836cb2ff7d129b4b0174beb3dc337fb2c1`.
- `Extension/Dubon2026/RieszMellinInversion.lean`: SHA-256 `b592dc479ad5c8325016fbc460851a04818729e6814385071b4a9c2edc68f80d`.
- `Extension/Dubon2026/RieszInverseKernel.lean`: SHA-256 `2f19557cd14a0a2d2860cda0b8a4736d476f16b249c1f5a0f4ae389910dd7c59`.
- `Extension/Dubon2026/RieszDirichletInterchange.lean`: SHA-256 `731a07e2188ec67d2fa8301ec7988d5ac185c55a9be41ba67bae377a60890c2a`.
- `Extension/Dubon2026/RieszPerron.lean`: SHA-256 `872aa1d66f84cb1587416f2968cacd5169453beac58afeb850b810199ebc0580`.
- `Extension/Dubon2026/RieszPerronIntegral.lean`: SHA-256 `19e79175f21bb9c9797a8df196614b565c5255f7ec1ee7acd9b4dc29630d63bc`.
- `Extension/Dubon2026/RankinConvolutionPerron.lean`: SHA-256 `6aa19cd0c590274d18a8427682bd0127ff5aae023448e26289f88aa613984447`.
- `Extension/Dubon2026/IntegratedFrequency.lean`: SHA-256 `c88436eba1cf1c93f5fd99a99c83c2da0de854715c556b7b9dc966fcaeca71d8`.
- `Extension/Dubon2026/PhaseFirstDerivative.lean`: SHA-256 `d5b9c881c88195164c58846da05cb3d57066b20c2645517eed15d17ec08593b4`.
- `Extension/Dubon2026/PhaseCurvatureBand.lean`: SHA-256 `5ea9ff3b86cb16ca91314aa95620eb2a43180699952a24584eb9ee9b8e350377`.
- `Extension/Dubon2026/PhaseSecondDerivative.lean`: SHA-256 `e515439cd55011dd3ffee3147f12d858b751ff76a5cf6d8132705405ab04f2c2`.
- `Extension/Dubon2026/RankinOscillatoryPhase.lean`: SHA-256 `5e2411f790f4c549beb07a7f72ae3389d2c444562c48de5a0b4f8964b0b5689f`.
- `Extension/Dubon2026/NormalizedComplexPhase.lean`: SHA-256 `f432ebcc5762a02c909474b76c301190f14655d9208082f6d0f9baa6536064d2`.
- `Extension/Dubon2026/GammaRatioPhase.lean`: SHA-256 `6ca307f233df1604b58f665d518b07bf26dfda6dccc47f7df02c656a2eb446a4`.
- `Extension/Dubon2026/GammaRatioCurvature.lean`: SHA-256 `d8039226ec98f4b7dfd1eb02038c24589f350e67b826c4052fc34e3a7b77289b`.
- `Extension/Dubon2026/DoubleGammaOscillation.lean`: SHA-256 `4a0bbd0943bf466cdebeecaf3911d4d4d844ed9ffe97cc7b9f9917f18caf946f`.
- `Extension/Dubon2026/GammaHorizontalLogNorm.lean`: SHA-256 `d4fdb6d500d5fe51f436bc67efbe05643d5c47b431538cc0b773133067281024`.
- `Extension/Dubon2026/GammaHorizontalDigamma.lean`: SHA-256 `f09b4b797a497c6896a6d10a5a9776cb99b200190f8dae4a5f2eaf3c67e47c26`.
- `Extension/Dubon2026/GammaRatioAmplitude.lean`: SHA-256 `0dca6a060b4d4a2d4d2f18cf02a8b39f982f1bd42ac5a381da9e738530086392`.
- `Extension/Dubon2026/OscillatoryAmplitude.lean`: SHA-256 `7919498fd384bad5aeac019c32d7cc45c6a41a3eb70096b1e489aa1693d64424`.
- `Extension/Dubon2026/DoubleGammaAmplitude.lean`: SHA-256 `f6de17f99ad0cded46d7cccb4a93d34ea3c482c2b84ae23d5ad94abc3c7028e6`.
- `Extension/Dubon2026/GammaDyadicAmplitude.lean`: SHA-256 `7dd191b24ad52ca9b79e059c3b3597c392d9e4d3c96b1ef76e109c2cfbe0547b`.
- `Extension/Dubon2026/GammaWeightedOscillation.lean`: SHA-256 `c42c659a2574e9dd7013c136258c9d57676bb64d35e80ac049fae93a7b5c0e53`.
- `Extension/Dubon2026/GammaFrequencySeparation.lean`: SHA-256 `49f874a6cfcf4b7a30478cdd2d4c458690e5ab8e53b4173c17b1cd0908ba9cc0`.
- `Extension/Dubon2026/GammaRieszSymbol.lean`: SHA-256 `6c242a03363194a8e4cc0cfe77caac755a727753851fe924026c98f4db2b36b7`.
- `Extension/Dubon2026/GammaRieszDyadic.lean`: SHA-256 `4dc0aa9de80888d89fd62fd1db26507fbb2ab427ca6a74d37fad2b39f32d8fa4`.
- `Extension/Dubon2026/GammaTailVariation.lean`: SHA-256 `36c2de35a9909dc9e4da6ed3a8048ab6e83756f3cfc3bd8ccc5f354134a00eac`.
- `Extension/Dubon2026/GammaNonstationaryTail.lean`: SHA-256 `21061ec96d4fcf126b2f89694dccce278703784e7923b16c6d506941dcf9e349`.
- `Extension/Dubon2026/GammaRieszTail.lean`: SHA-256 `6af84aa2bf3a7bfec595fd41c87efebd50c0735532d3e03c399bc06d59f28c6a`.
- `Extension/Dubon2026/GammaRieszKernel.lean`: SHA-256 `58b227237bc2bec65d28fa8fe288d166509833bff23df2a239c2e79fd472fb98`.
- `Extension/Dubon2026/GammaRieszWindow.lean`: SHA-256 `f9f582d0378cb0aff950196f15244a0fc42c7dcbd9839681b37aa13cf0b40b29`.
- `Extension/Dubon2026/GammaRieszCompact.lean`: SHA-256 `4bad5860822a8c0b00db9be3bd0f0a046062bb14b28f3c68889c71ba17ecb283`.
- `Extension/Dubon2026/GammaRieszBounds.lean`: SHA-256 `e36d74efc5bf1b9f437a79ba851ef2afee5b463f08747ad560fb386a006326de`.
- `Extension/Dubon2026/GammaRieszTruncation.lean`: SHA-256 `5f4bd57288ab7be57d23f44b0323e118e4cdd8b2ccebaf790ebc0063396fa385`.
- `Extension/Dubon2026/GammaRieszUniformConvergence.lean`: SHA-256 `db0181ef6ffbddc1ea3556530d41e21e67dbec995002f114a607f3b2d31738cd`.
- `Extension/Dubon2026/GammaRieszHolomorphic.lean`: SHA-256 `4adadfd90aabbd982e2884cbb72154719a23a602026447bdc4b944fc545aacd6`.
- `Extension/Dubon2026/GammaRieszStripAmplitude.lean`: SHA-256 `f41a6011c7bf9c41ff02ecfba7402ca850a3deab30827f81626435a751c37489`.
- `Extension/Dubon2026/GammaRieszHorizontal.lean`: SHA-256 `e27e314ac9344655835aeb1c9ab38bd811e4296545ffed9d2475ad1e48e953cd`.
- `Extension/Dubon2026/GammaRieszContourShift.lean`: SHA-256 `11110989737bd6b641d43e42846d6f7b768e6be895fac7a945d25d9b76e502d9`.
- `Extension/Dubon2026/GammaRieszShiftUniform.lean`: SHA-256 `4dc578247134ad31c90ca5c7baeee93bd01542c33206cb55eb3e04bf103999b4`.
- `Extension/Dubon2026/GammaRieszRecurrence.lean`: SHA-256 `42f925dc44bc68d8f62246de35488d1967acb78f83c94a3d300a8d7bb1803b6f`.
- `Extension/Dubon2026/CompactParameterDerivative.lean`: SHA-256 `2854a07b734ec0dbb28021aed22c64e96e7e7fae9a6eea1020b32863ac0bff9d`.
- `Extension/Dubon2026/GammaRieszJointContinuity.lean`: SHA-256 `50afb8773c8ec50269227f1bd9f92bb8a85526cb682b63f75b432959756d5e65`.
- `Extension/Dubon2026/GammaRieszFiniteDerivative.lean`: SHA-256 `2f36ece0a6f66708512206d1d79c3686838c0ba2ed1d44d22bdc703ac58df4c5`.
- `Extension/Dubon2026/GammaRieszWeightedConvergence.lean`: SHA-256 `3716b688d19f40535448af5ac8b344b2272e3d62637ac043ab10371ba31caeb8`.
- `Extension/Dubon2026/GammaRieszKernelDerivative.lean`: SHA-256 `207fb4e506bf66e4de1f222d873616de7812dbce9dd6b7d87c7140eb1f461a61`.
- `Extension/Dubon2026/SecondDifferenceDerivative.lean`: SHA-256 `9d32b5e4c7131672f64ea58567c444193ed4ef0815db3f91c997a9c42feeee68`.
- `Extension/Dubon2026/GammaRieszDifferenceBounds.lean`: SHA-256 `82343291682364e5f0038e1cac56974e2d7ea750660473a50c94782a164a773f`.
- `Extension/Dubon2026/LinearSummatoryPower.lean`: SHA-256 `e48c22b38f04e0591d1debb36853f46f9887faa871f0a874694b10cdd7ebe338`.
- `Extension/Dubon2026/LinearMeanPowerBounds.lean`: SHA-256 `2d3710aa286bc9383f87ac8df9a1fe3d92159a7a6b7e6d30a37629955e95f0f5`.
- `Extension/Dubon2026/LinearMeanPowerTail.lean`: SHA-256 `3c24d2aa3de45632eba4a173aa9cccb9cdfd13659b615f7cfcaa28e2b1ec3f3c`.
- `Extension/Dubon2026/RankinConvolutionPowerBounds.lean`: SHA-256 `596fbfb2edf160cda29e49a687a6ced4788c6bd5197191b35425cd440bff4fe4`.
- `Extension/Dubon2026/GammaRieszDualTerm.lean`: SHA-256 `830347a23f7d4f0910a24081190518d76287518cc7a379f8cf1ca021b67de47f`.
- `Extension/Dubon2026/GammaRieszDualSeries.lean`: SHA-256 `6cda3f521a93ccf3af16190057eaf30fc232d413bf72501f18885e24924e9763`.
- `Extension/Dubon2026/GammaRieszDualDifference.lean`: SHA-256 `655875acf0725092d0402d225bf6713eca604fe09b10c89fcfbd571ffab2f0c8`.
- `Extension/Dubon2026/GammaRieszDualSplit.lean`: SHA-256 `5f2f83735ca2575ef2f1f30588c2e8df1a5b6d5399243be70d4430f83393b7c3`.
- `Extension/Dubon2026/RankinGammaDualSeries.lean`: SHA-256 `1884e14254a241a7086781e3e0373fdbdd191ecaedc37b206c4ebc208064a5d7`.
- `Extension/Dubon2026/RankinDualOptimization.lean`: SHA-256 `6a897cb67ef34fb4fd7ad67b93d7a04e21939f2085048d41e47c42c005c9c810`.
- `Extension/Dubon2026/RankinConvolutionGlobal.lean`: SHA-256 `d8cfa9d37230a370947a91ce15252be77b93e2ee9581e7a6532f2316bd8d68e8`.
- `Extension/Dubon2026/RankinConvolutionGlobalResidue.lean`: SHA-256 `f93a7197403576a0215d1c95aaef396bc04aefcd91c495964cd7b8057781edad`.
- `Extension/Dubon2026/RankinConvolutionReflection.lean`: SHA-256 `205b132310c5e9fada7374db9e8d1c3cf5348d84a426b667029f00049a0d6cff`.
- `Extension/Dubon2026/GammaInverseStripGrowth.lean`: SHA-256 `4e08dcc7b9d0276de6a0a2766f5c018f0573221dec9d9a8be1130a50b72c8d70`.
- `Extension/Dubon2026/RankinConvolutionExponential.lean`: SHA-256 `a50450fe3f894a4dcd4b49e4018b63ee6b5337db45a424bfa1912cab3a254e97`.
- `Extension/Dubon2026/RankinConvolutionBoundary.lean`: SHA-256 `3112d7c7005daea285e066a318add7ae313637f0221250e771534b79db6b70cc`.
- `Extension/Dubon2026/RankinStripNormalized.lean`: SHA-256 `d294beecef61fcc7d773afd16665b6b6c6d2e8f4d0f1e64017de7194d1a18e18`.
- `Extension/Dubon2026/RankinStripPhragmenLindelof.lean`: SHA-256 `eca26e1e1d87dc44c3c454db0d902cfec0341f38d5dd508889ec8656cd1f2774`.
- `Extension/Dubon2026/RankinPerronContinuation.lean`: SHA-256 `44be33822baa003124a93a6edee037d2142bbf54c263081f8c8f982a40607b17`.
- `Extension/Dubon2026/RankinPerronHorizontal.lean`: SHA-256 `f79b99b553a6050320e4c010c645ac6e4357c9185ee62c01ddf37234e7f887ea`.
- `Extension/Dubon2026/ConvolutionPowerRemainder.lean`: SHA-256 `eaa0a891376b6c45e198ef3461bb08455a503d0bc1bddbac9993c3a917cecb76`.
- `Extension/Dubon2026/ConvolutionRealCutoff.lean`: SHA-256 `7bed334ea3566b971bf8f537e8ac7e56cc4f4fb559e7fdeb518616242a0c323d`.
- `Extension/Dubon2026/GammaRieszAllCutoffs.lean`: SHA-256 `733a9cdc6ec649b7b72657b56dac6d805a3c4763d54b98d2e1b8802864256145`.
- `Extension/Dubon2026/GammaRieszDualCutoff.lean`: SHA-256 `2f3d93c782f92ef3a771123f2b1f3bc7070effeeb89eb3967edd14f05a2aea29`.
- `Extension/Dubon2026/GammaRieszPartialBounds.lean`: SHA-256 `63994d02a9110fdde354dadfb97e00b19c4a1026fe29ce6f202bf45752e3a662`.
- `Extension/Dubon2026/LSeriesFiniteContourInterchange.lean`: SHA-256 `6d398342bc03a34491cb81b5687895792a78288ce872d5013585fd5f38154056`.
- `Extension/Dubon2026/LevelOneRankinSelberg.lean`: SHA-256 `fee829ad8c206fad941d32f3c83ea83dfecba9c9ba134bdc7823c20f893549cb`.
- `Extension/Dubon2026/RankinConductorMellin.lean`: SHA-256 `38c9c8938b788050befc9664459fde2c3bc013a936b3594bb3e96d2e84f2fa1c`.
- `Extension/Dubon2026/RankinConvolutionThreeFifths.lean`: SHA-256 `11529432a0e7652db46a5cf06becfc375ad4a9c15cf65ceacbac0e2c1ded960d`.
- `Extension/Dubon2026/RankinDeconvolutionRemainder.lean`: SHA-256 `eeac2996ceafb8ee3b5801a051c610663ccfdd04c42d8133e082f6fa965fce7e`.
- `Extension/Dubon2026/RankinDualShiftedOptimization.lean`: SHA-256 `8852b82e4d1f94c496a7147b874ceee00b79ebde43b59c61fe9792d72449898f`.
- `Extension/Dubon2026/RankinPerronContourShift.lean`: SHA-256 `ce8eb75558f6bf9444381ae8a56203888661bc99877951c3a9851563bd521092`.
- `Extension/Dubon2026/RankinPerronCutoffs.lean`: SHA-256 `b17e5abf2bfac2f9a3b846ff3ee8b3d0b80d60fefcec7be9289fb53e3ea014a0`.
- `Extension/Dubon2026/RankinPerronDualInterchange.lean`: SHA-256 `0c5980318053a12e1ba2951d0a7076d08985406e3e40a49021f3e876f35093f3`.
- `Extension/Dubon2026/RankinPerronPoles.lean`: SHA-256 `5f7fd661a3395aba33c6cd8c1fa868038109deb8f2ddc36bc31bb9614fe5bfa5`.
- `Extension/Dubon2026/RankinPerronTermTransform.lean`: SHA-256 `75a1892de94fd469c13f8f0f10ec1d0278c629c187106c82d36f7c230ba454bf`.
- `Extension/Dubon2026/RankinRectanglePoles.lean`: SHA-256 `0cece1e6a44332fd5d4ba99c7b6f52335486627dcbdcf98c07d5b531922f2821`.
- `Extension/Dubon2026/RankinRieszDifferenceEstimate.lean`: SHA-256 `4413f9dcb99e7b1e8c38ea2f91b62f744c881590da6488b51d454e3e2cf0a183`.
- `Extension/Dubon2026/RankinRieszDualIdentity.lean`: SHA-256 `0a85d22d2aafadb7dd88eb6a48ede71766cdbed263f3a38ce4192d155492fdd8`.
- `Extension/Dubon2026/CongruenceTraceDomain.lean`: SHA-256 `761c7c0466139786b86480e53d1c170e3973fcb435fd9b8feff6c6305582eff8`.
- `Extension/Dubon2026/CuspCommonPeriodIntegral.lean`: SHA-256 `2bb5e15d15571cd553915193162398f454fcd55f9079bf17ccf275fd64835f23`.
- `Extension/Dubon2026/CuspCosetTrace.lean`: SHA-256 `5879eb4e4b2a1e965e0fa0950d86d5ada8b52199ad3d95ccc1ce5a0d8338b59c`.
- `Extension/Dubon2026/CuspPeriodEnergyBound.lean`: SHA-256 `21b9126b884758f9a8838eb0440dc16195f559b3a853940e668739e3cd613d8a`.
- `Extension/Dubon2026/CuspPeriodFourierEnergy.lean`: SHA-256 `826427be1c7e423191f32d53aeed0bca1204d9a15194d613e2f4b6e643fe5330`.
- `Extension/Dubon2026/CuspPeriodMellin.lean`: SHA-256 `0e0695305112e196012767924c29426efc2c425a413b0197f69dadc9bea3d899`.
- `Extension/Dubon2026/CuspPeriodNormalizedEnergy.lean`: SHA-256 `b1b4a4a9884a17d7d6357ee5d28147cf21456f6efe976b6dbeaaa03f080c4545`.
- `Extension/Dubon2026/CuspPeriodRankinSeries.lean`: SHA-256 `c70f7a3e1e2e4904a62abf4d4af8eba30e6e7b3ba30d961c5d18ec7a8fe32536`.
- `Extension/Dubon2026/CuspTraceCoefficients.lean`: SHA-256 `59d7d339fefcf969573fc8feef9fa45e60b9af2133de848ab92741937ea48be2`.
- `Extension/Dubon2026/CuspTraceMellin.lean`: SHA-256 `8bba7b2490f6c87f6c00bbc3db8850bdc8b8d75ad6b62353705baf39d07a7245`.
- `Extension/Dubon2026/CuspTraceRankinConvolution.lean`: SHA-256 `5c071901648123c683b0137c4300d2a6a5d442e772df60e49e5aad21b28f3752`.
- `Extension/Dubon2026/ExponentialMellinSeries.lean`: SHA-256 `512f300c40f8a5e6b93bb30fa18a599334d0fe5d79aea30eb00c9195cab62953`.
- `Extension/Dubon2026/FiniteCosetTrace.lean`: SHA-256 `5042e58c0bfda8df0c3928f01d0799f2c8e0f49874ff3a0fd39b99f250fd9387`.
- `Extension/Dubon2026/RectangularCongruence.lean`: SHA-256 `4b2bafc31c86dbc2040274ed7ce548c1d3f3e52c75480bf087cbc8abab26ce26`.
- `Extension/Dubon2026/RectangularConjugation.lean`: SHA-256 `b65e7dea9738c294751373dbe1b540df209449119a91906565e354c5f9e5905d`.
- `Extension/Dubon2026/RectangularDualCoefficients.lean`: SHA-256 `acc414ed42a59cea71cf16e040099c16668138cb6d70489e14dc298961da9417`.
- `Extension/Dubon2026/RectangularProjectiveDomain.lean`: SHA-256 `588ea5300f0337597dc800916a386f6f1cb236696ac08182bf348002e10c5f1e`.
- `Extension/Dubon2026/CuspTraceCompletedSeries.lean`: SHA-256 `c146dd7fff64f86e734d6ab375621a10cb31dd1a4da5cacce3a2f30b9a7fc962`.
- `Extension/Dubon2026/CuspTraceEisensteinMellin.lean`: SHA-256 `392f91da2cf5da49d88df78493b44189a35ea516e0e9e8a18be005dd16374840`.
- `Extension/Dubon2026/CuspTraceLatticeIntegral.lean`: SHA-256 `6cc73105c8eeda40cc6372c46e08fa7631e3cda6224bfaae8586fbba209b6851`.
- `Extension/Dubon2026/CuspTraceStripMellin.lean`: SHA-256 `cf1d7a071501088f9b4b7acb114d58dbdd8caaa273563e83d6a1853241834759`.
- `Extension/Dubon2026/DivisorRectangularDual.lean`: SHA-256 `4655115c25bb5c98f6598b3aea43b63600821f5968647f6fa39caa34310e54b3`.
- `Extension/Dubon2026/FullLevelTraceUnfolding.lean`: SHA-256 `c7ec6b10cdbb262c20d4e993a9fb9c6725103149c0072cf4deabc16a451abfd4`.
- `Extension/Dubon2026/RectangularDualSeries.lean`: SHA-256 `11a3bd6a4c91925ff302e879b11b0e77fe641c6b3ec727f3b70eb0c3b7c0650f`.
- `Extension/Dubon2026/RectangularDualSeriesReal.lean`: SHA-256 `0106f6f1bacfd1d1dcc3e694eddc3e76427288eb2dcdb78a529461e3d4c69151`.
- `Extension/Dubon2026/RectangularLatticeTransport.lean`: SHA-256 `d01f0b23c4417d01e9af7ca19aea42a73cddeb6c0cefb5452adae38b699a605d`.
- `Extension/Dubon2026/DivisorGammaDualSeries.lean`: SHA-256 `8d11b4b28bf81103c3c8314ef7932a44238c0a65c629f73b1ab4f341198556c8`.
- `Extension/Dubon2026/GammaDualFiniteTransform.lean`: SHA-256 `fb739538f194176338dcdebda0a5995fd4810d40e6194f26924bda0bd333ce3d`.
- `Extension/Dubon2026/GammaDualMellinTerm.lean`: SHA-256 `c0eccaf1cb7a41e7874e19d9bba714e90e9f57931f4f989fe5a63e89b72cff32`.
- `Extension/Dubon2026/GammaDualSharpOptimization.lean`: SHA-256 `f3947d525f8aa11710cf6c0060d0f20a1a0b98fc5c5e8a0f3d74b5943ce757b5`.
- `Extension/Dubon2026/GeneralRankinBoundary.lean`: SHA-256 `49e7192d5c0cd987b5eb150d0fb36e36e2784fb1862875353a5081d61e6a6aef`.
- `Extension/Dubon2026/GeneralRankinDualCutoffs.lean`: SHA-256 `1b498e984fa4ec5d06faa2717a07bced0a3893f93dfad5147576ce0e92014468`.
- `Extension/Dubon2026/GeneralRankinDualDifference.lean`: SHA-256 `fbff6ff5de66b017c7c6267acc4cf821283692f59f023183d2c60b2e557f2cc1`.
- `Extension/Dubon2026/GeneralRankinReflection.lean`: SHA-256 `f8accbe58fa8c094f5c96940f112f68cc4048c60d73d9df9d041c101c46b3a04`.
- `Extension/Dubon2026/GeneralRankinRieszDifference.lean`: SHA-256 `f6db31fad0302a6a5ed1533f0fb2fd1ee129d0192013ef99604705edc3dd174a`.
- `Extension/Dubon2026/GeneralRankinRieszIdentity.lean`: SHA-256 `08b5b0e40386ed9f95a3b11eebf166b6088269079f595c978d8b0f65648e5b4f`.
- `Extension/Dubon2026/GeneralRankinSelberg.lean`: SHA-256 `3ab99b65e32884f90675707b1ce3c6c6dcae0878800caac901fbad8facc65ce4`.
- `Extension/Dubon2026/GeneralRankinThreeFifths.lean`: SHA-256 `abcbfc18cef965236887c30455f4828bc349a5c4686e227aed4525173fc11fed`.
- `Extension/Dubon2026/ModularEnergy.lean`: SHA-256 `6253116c90c2b3e65eef903049d350ba0cd7d68ee2d5276832367168ae9eb6f1`.
- `Extension/Dubon2026/RectangularConductorPower.lean`: SHA-256 `668a768997201ee679c1993af70c146821cfcb446a68a107024a936f8407b656`.

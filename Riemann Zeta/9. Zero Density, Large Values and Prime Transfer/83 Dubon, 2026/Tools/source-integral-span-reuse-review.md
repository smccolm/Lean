# Original weight-two integral-span alternative

Exact dependency: DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power continuation -> residual Galois association -> the original all-prime weight-two H1 class -> integral-span or detected finite-order alternative.

The native consumer proves this alternative for the actual H1 returned by sourcePrimitive_exists_residualWeightTwo_charP. Its integral-span branch discharges the required integral-span premise of the characteristic-zero Hecke eigenvalue lift; its other branch supplies the actual finite-order element needed by the Eisenstein Hecke calculation.

Reuse checked: the pinned native cocycle and trivial-H1 APIs, existing SourceIntegralCohomologyFinite, permutationCoordinateRep, SourceSL2Cocycle_exists, original cosetTransition, SourceCupThree.zY and identity-coset evaluation. No existing proved integral-span theorem was found. The external anthropics/fermats-last-theorem proof at revision 6e837e75355538c7f80bab5b956861e86c4eacc2, S_CohCarrier_mem_span_int_of_forall_isOfFinOrder_apply_eq_zero, supplied the orbit potential and finite-support arguments (Apache-2.0, retained LICENSE/NOTICE).

Shorter route adopted: reuse the proved native SL2 modular-generator existence theorem, derive uniqueness only where needed, lift the two orbit potentials through the free integral module, and evaluate at the actual identity coset. This avoids the external Kurosh, PSL2 quotient and free-product bridge. It requires no supplied integral lift, cohomological vanishing, or finite-generation premise.

Scope still open: the characteristic-zero Hecke eigenvalue lift, finite-order Hecke scalar calculation and both geometric/reducible Galois association branches. The full adic, purity, crystallinity and higher symmetric-power obligations remain. Acceptance stays 16/20; DUB-17--20 remain open. These six modules are audited scratch, pending production integration.

# Research agenda and current status

**PLANNING ONLY. GOAL INACTIVE. 0/20 proof gates complete.** The completed deliverable for 5 October is the researched project template, not mathematics in Lean.

The immediate task on activation is source review, not choosing tactic syntax. E01–E04 are concrete display/proof/sign inconsistencies. E05–E07 concern hypotheses and endpoints; E08 concerns the certification gap in author computations. Resolving them gives a stable theorem surface before an expensive implementation.

After that review, use the local digamma and finite-sum libraries to close the harmonic and tail estimates. Prove the actual weighted truncated-Poisson statement in two stages, preserving the endpoint terms. Reuse the exact zeta truncation identity to reach AFE1 first: it is the smallest complete advertised AFE endpoint and supplies an early test of the sharp cutoff conventions. Follow with the stationary-phase and explicit gamma work needed for the second kind. The full weighted Poisson theorem remains independently required even if an AFE specialization has been completed.

For AFE2, prove the direct branch from the actual oscillatory integral and then derive the reflected branch with the real χ identity. The x=y seam, σ=1/dual σ=0 endpoint and t<0 conjugation are explicit semantic regressions. Do not begin table certification until these exact branch functions are fixed.

Numerical replay already establishes that the bundled Python script is runnable locally and that its displayed Table 1 matches. It also exposes nearest-rounding and domain questions. Future certification needs analytic monotonicity or a kernel-checked interval/rational checker with global coverage. A densely sampled plot or optimizer convergence does not discharge that task.

## Existing completed local base

- Node 71 documents the complete Guth–Maynard/publication density chain and substantial analytic infrastructure at the frozen Lean 4.30 graph.
- Node 63 documents 42/42 accepted gates, including the original closed Pintz endpoint strengthenings and preserved source errors/repairs. Its B-process, gamma and sharp-cutoff infrastructure should be inspected before duplication.
- Node 73 documents the four-theorem release with explicitly scoped PNT and sieve substitutions. Those acceptance decisions belong to node 73 and do not authorize unmarked substitutions in this paper.
- Node 74 supplies the exceptional-interval release and substantial PNT+/gamma/sharp-truncation machinery.
- Node 77 documents 20/20 gates completed on 5 October, including exact main contracts and recent digamma/logarithmic-prefix work.

These are the existing projects' recorded statuses, supported by source/interface inspection during setup; this survey is not a fresh full rerun of all five extension audits. Later imports require an exact dependency closure and current verification. Preserve all prior findings and avoid rebuilding completed foundations unnecessarily.

## Scope controls

No new zero-density theorem, sub-Weyl constant optimization, all-real AFE2 cutoff theorem or RH claim is required. No new external package is selected. Broad searches should stop once a useful candidate is identified and its exact interface inspected; work then moves to the actual terminal analytic obligation. Use the twenty-gate architecture to track genuine source consumers, not an ever-growing collection of conditional wrappers. No recovery record is required.

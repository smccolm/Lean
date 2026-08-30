# Prime Shell Research Agenda

Status date: 2026-08-30

Prime Shell is an isolated post-Guth–Maynard experiment. Its frozen inputs are:

- Guth–Maynard project boundary: commit `2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be`, tag `gm-foundation-freeze-v1.0.1`, Lean `v4.30.0`;
- Zeta23 boundary: Anthropic `formal-math` tag `v1.0`, commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, Lean `v4.33.0-rc2`, Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`.

Nothing under the frozen `RiemannZeta/` proof is modified or imported into this experiment. Prime Shell is not presented as a path to the Riemann Hypothesis.

## Question tested

The proposed mechanism was to add a separated high-frequency shell to the source used by the Alpoge–Furman/Zeta23 rank/inertia argument, control its prime-pair contribution using unconditional arithmetic information, and test whether the exact spectral certificate improves the simple-critical-line proportion beyond `2/3`.

The terminal result is **ROUTE DISPROVED** for the faithful separated-amplitude mechanism. It is a non-vacuous spectral no-go, not a failure of one taper or one arithmetic theorem.

## Authoritative sources

1. Alpoge–Furman, arXiv:2608.13637v2, especially equation (2.7), equations (5.10)–(5.11), Proposition 5.4, Theorem 5.7, and Section 7.2.
2. Guth–Maynard, arXiv:2405.20552v2, Corollary 1.4 and Section 13.2.
3. Matomäki–Radziwiłł–Tao, arXiv:1707.01315, Theorem 1.3(i).
4. The exact pinned Zeta23 release and its cited classical inputs.

The detailed declaration-level source crosswalk and reproduction evidence are retained in the Phase-I report and source ledger.

## Phase I: exact source and arithmetic boundary

### PSH-01 and PSH-02 — reproduction and crosswalk

The exact Zeta23 release was reproduced at immutable pins. The upstream project builds but emits its own warnings under the pinned release; these are disclosed. Direct Prime Shell source elaboration is evaluated separately and is warning-free.

The source crosswalk distinguishes equality, specialization, and nonmatch. In particular, the pinned `X ≤ T` theorem is not silently treated as an `X > T` theorem, and a displayed PairCeiling enclosure input is not treated as an internally proved unconditional bound.

### PSH-03 — exact prime-prime decomposition

The actual `M[P_X,P_X]` source object is decomposed into diagonal and off-diagonal frequency pieces. Same-sign resonant, opposite-sign, boundary, and remainder pieces remain separately accessible. The existing pinned prime-term theorem is recovered from this decomposition as a regression theorem.

### PSH-04 — exact shift kernel

The dangerous contribution is dyadically localized and rewritten with the literal two-variable kernel under `m=n+h`. Endpoint restrictions, support, resonant range, coefficient weights, and the variation remainder are explicit; no unspecified bounded weight replaces the kernel.

### PSH-05 and PSH-06 — arithmetic interfaces and F1

The narrow finite Guth–Maynard interface records the required pi-to-Lambda conversion, prime powers, exceptional-set weights, simultaneous intervals, dyadic subdivision, endpoints, epsilon margins, and the additional Section 13.2 inputs. It is a specification, not an axiom.

The actual pinned kernel has nonconstant rows in a common admissible dyadic block. `concrete_literal_prefix_only_transfer_fails` proves that collapsed shift-prefix information alone cannot furnish the proposed two-variable transfer. Abel identities and exact variation consumers remain available for genuinely stronger n-local arithmetic hypotheses.

## Correction of the original F2 model

The earlier terminal claim combined a strictly positive total `WindowProfile v` with an imposed zero gap and proved that class empty. That was a useful interface diagnostic but not a faithful no-go: the gap may be placed in an amplitude `q`, with the source constructed from `v = q²`.

The corrected source layer is now formalized:

- `AmplitudeProfile q` requires evenness, `C³` regularity, nonnegativity, a unit bound, and uniform derivative bounds, but permits zeros.
- `atAmplitude_phi` proves the literal physical identity `q(u/L(T)) * phi(u)` for `atV (q²)`.
- `extendedFamilyHyps_atAmplitude` proves the extended explicit-formula family contract from the actual amplitude and taper assumptions in the full range `3 * lambda < 4`.
- `twoBandAmplitude` is an explicit compactly supported two-bump amplitude. Its source autocorrelation and difference-set support are proved exactly.
- `concreteFaithfulAmplitudeShell` packages the real source, strict separated geometry, same-band support-one blocks, cross-band frequencies beyond support one, and positive mass.
- `faithfulAmplitudeShell_nonempty` proves the corrected admissible class inhabited.

This also corrects the scale ledger. The MRT threshold `33/25` and the explicit-formula upper endpoint `4/3` overlap strictly. The formal concrete value `199/150` witnesses that overlap.

## F3: exact universal pricing verdict

### Faithful class

`FaithfulAmplitudeShell` contains:

- a `PrimeShellFullChainAdmissible` source parameter and taper;
- a real amplitude `q` with `AmplitudeProfile q`;
- two ordered symmetric band edges inside `[-1/2,1/2]`;
- exact support localization to the two closed bands;
- witnesses that both bands are present;
- same-band support-one bounds;
- strict cross separation `1 < lambda * (rightEdge - leftEdge)`; and
- positive integral mass.

The arithmetic estimate is deliberately absent: the final obstruction is independent of it.

### Support-loss theorem

Let `gap = rightEdge - leftEdge`, `v = q²`,

```text
I = ∫ v,    J = ∫ v²,    W = jWin D1 lambda v.
```

The exact permitted support has Lebesgue measure `1 - gap`. A set-integral Hölder/Cauchy argument proves

```text
I² ≤ (1 - gap) J.
```

Strict cross separation and `lambda < 4/3` imply

```text
3 lambda (1 - gap) < 1.
```

Positive mass implies `I>0` and hence `J>0`; the exact D1 kernel gives `W≥0`. Unfolding the pinned spectral definition yields

```text
kappaXi lambda v = (J + lambda W) / (lambda I²) > 3.
```

This is `FaithfulAmplitudeShell.kappaXi_gt_three`.

### Terminal theorem

The exact Zeta23 rank/inertia output is `2 - kappaXi`. Therefore every faithful separated shell satisfies a value below `-1`, and in particular cannot exceed `2/3` by a positive amount. The public theorem is `primeShell_universal_no_gain_native`.

The direct success proposition

```lean
def FaithfulSeparatedAmplitudeGain : Prop :=
  ∃ S : FaithfulAmplitudeShell, ∃ delta : ℝ, 0 < delta ∧
    (2 / 3 : ℝ) + delta < 2 - kappaXi ...
```

is proved equivalent to `False` by `faithfulSeparatedAmplitudeGain_iff_false`. This is the trusted-statement check. The explicit inhabitant prevents vacuous quantification.

## Why native GM/MRT formalization stops here

The full-goal contract permits terminal B when every faithful admissible construction is ruled out or the complete admissible class cannot yield positive improvement. `primeShell_universal_no_gain_native` supplies the latter verdict and is stronger than failure of GM, MRT, any particular fixed-shift theorem, or any numerical candidate: it survives perfect arithmetic input.

Consequently the success-branch obligations to formalize an external prime-correlation theorem, prove a native positive trace, and derive a new zero theorem are not required and would not change the verdict. Existing exact arithmetic consumers are preserved as reusable infrastructure, but are not relabelled unconditional arithmetic theorems.

## Verification and integrity contract

Completion requires all of the following:

- the isolated root and every changed module elaborate at exact pins;
- direct Prime Shell elaboration emits no project warning or linter diagnostic;
- explicit axiom audits list only `propext`, `Classical.choice`, and `Quot.sound`;
- scans find no `sorry`, `admit`, `sorryAx`, project `axiom`/`constant`, `unsafe`, `native_decide`, or `implemented_by` in Prime Shell source;
- the frozen GM verifier still passes and no frozen source is modified;
- the two-sided gain comparator elaborates;
- the source manifest records every production file by SHA-256; and
- architecture, Shitlist, agenda, source ledger, README, reports, audit, and reproduction instructions agree.

The immutable Zeta23 dependency’s own warning output remains disclosed. It is not suppressed and is not described as a zero-warning upstream build.

## Completion levels and nonclaims

- **Kernel-checked terminal theorem:** achieved internally for the faithful separated-amplitude mechanism.
- **Independent expert review (PSH-21):** open and external.
- **Peer review, publication, community acceptance:** not claimed.
- **New zero theorem or positive Prime Shell constant:** not claimed.
- **No-go for connected windows or other source mechanisms:** not claimed.

The research program is complete at terminal state B only in the precise formal sense above.

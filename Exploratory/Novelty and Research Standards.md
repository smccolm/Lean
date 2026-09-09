# Exploratory - Novelty and Research Standards

Status: governing research standard for exploratory mathematical projects.

Purpose: this file defines when an exploratory idea is worth maturing into a serious Lean campaign, a mathematical research project, an operational research project, or both.

The standard is intentionally strict.

## 1. Core research intent

The primary theorem goal is to prove something that mathematics did not already know.

The medium is irrelevant.

A result does **not** become mathematically new because it is expressed as:

- Lean code;
- a formal analytical proof;
- a computer-assisted proof;
- a different notation;
- a different basis or coordinate system;
- a different programming language;
- a diagram;
- a computational experiment;
- a machine-checked version of an existing paper;
- a statement that happens not to have been written down verbatim before.

The object of interest in the theorem track is the mathematical theorem itself.

The governing theorem principle is:

```math
\boxed{
\text{I want to prove something mathematics did not already know,}
\text{ not merely say something mathematics already knew in a new language.}
}
```

However, theorem novelty is not the only legitimate form of research contribution.

For purposes of this research program, contributions are evaluated independently on at least two axes:

```math
\boxed{
\begin{array}{c}
\textbf{Theorem Novelty: expanding what mathematics knows to be true.}\\
\textbf{Operational Novelty: expanding what mathematics can be made to do}\\
\textbf{in an explicit, reliable, reusable, and validated way.}
\end{array}
}
```

The error is not in pursuing operational novelty. The error is:

```math
\boxed{
\text{masquerading operational novelty as theorem novelty.}
}
```

The reciprocal error is also prohibited:

```math
\boxed{
\text{discarding a genuine operational advance merely because its mathematical ingredients are old.}
}
```

Thus:

```math
\boxed{
\text{formal novelty}
\neq
\text{mathematical theorem novelty}
}
```

but also:

```math
\boxed{
\text{known mathematics}
\not\Rightarrow
\text{no possible research contribution}.
}
```

A known theorem may still support an operationally novel capability if that capability itself survives the standards below.
## 2. Strict theorem novelty standard

A candidate theorem qualifies as a serious research target only if all of the following survive scrutiny.

### 2.1 The exact theorem is not already known

Reject the candidate if the historical or current literature already contains:

- the same theorem;
- an equivalent formulation;
- a stronger theorem that implies it routinely;
- the same result in another notation;
- the same result for a broader class;
- the same result stated in a different mathematical language.

Absence from keyword search is not evidence of novelty.

### 2.2 The theorem is not an immediate consequence of existing theory

Reject the candidate if a competent specialist can obtain it by:

- directly substituting into a known theorem;
- applying a standard classification theorem;
- chaining a few standard lemmas;
- performing routine Jordan-form or spectral decomposition;
- specializing parameters;
- renaming variables;
- removing redundant hypotheses;
- taking an obvious corollary;
- carrying out standard finite case analysis after invoking known machinery.

A theorem may be apparently unstated and still fail the novelty standard.

An unstated corollary is not enough.

### 2.3 The proof contains substantive mathematical work

A qualifying proof should contain at least one mathematical step for which existing theory does not already dictate the result mechanically.

This may take the form of a:

- new construction;
- new obstruction;
- new invariant;
- new reduction;
- new estimate;
- new equivalence;
- new structural lemma;
- new interaction between known theories;
- new proof mechanism;
- new boundary between possible and impossible cases.

The proof may use large amounts of existing mathematics. That is normal.

What matters is that some substantive part of the proof is not merely supplied by the old machinery.

### 2.4 The theorem has mathematical significance

Novelty alone is not enough.

Reject artificial statements manufactured only to be unprecedented.

A good theorem target should do at least one of the following:

- answer a natural mathematical question;
- resolve a genuine ambiguity;
- sharpen a meaningful boundary;
- improve a known result nontrivially;
- connect previously separate structures;
- produce a reusable method;
- expose a previously unknown mechanism;
- rule out a meaningful possibility;
- open a route to further mathematics.

The desired combination is:

```math
\boxed{
\text{worthwhile theorem target}
=
\text{theorem novelty}
+
\text{non-routine proof}
+
\text{mathematical significance}.
}
```
## 3. Operational novelty standard

Operational novelty is a distinct research contribution when known or partly known mathematics is transformed into a materially new, reusable, and validated capability.

Operational novelty is **not** established by:

- translating an old theorem into Lean;
- renaming variables;
- changing notation;
- writing a thin wrapper around an existing library call;
- reproducing a known algorithm in a different programming language;
- exposing an old result through a new UI;
- automating a single isolated example;
- replacing a human proof with opaque automation without broader reuse;
- finding a known counterexample and presenting it more conveniently.

A candidate operational artifact must survive the following tests.

### 3.1 Data-contract test

An operational contribution may qualify when it resolves an implicit ambiguity, missing datum, or type error that materially affects mathematical use.

A valid contribution should do some combination of the following:

- identify tacit mathematical data that informal practice suppresses;
- supply an explicit type signature that prevents category conflation;
- separate operators on different spaces that informal notation blurs;
- distinguish an operator on \(V\), an operator on \(\operatorname{End}(V)\), and an element of a tensor-product operator space;
- expose branch, orientation, regularization, domain, or boundary data that must be supplied for an operation to be reproducible;
- prove that omitting the hidden datum creates nonuniqueness, ambiguity, invalid composition, type mismatch, information loss, or computational failure;
- provide a corrected interface in which invalid operations are difficult or impossible to express.

Merely exposing a hidden parameter is not enough.

The contribution must establish:

```math
\boxed{
\text{hidden datum}
+
\text{demonstrated consequence of omitting it}
+
\text{usable corrected interface}.
}
```

### 3.2 Executability and effective-procedure test

An operational contribution may qualify if it turns mathematics into an effective procedure with explicit inputs, outputs, guarantees, and failure modes where no comparable procedure was previously available.

Examples include:

- an exact decision procedure;
- a deterministic executable construction;
- a certified approximation algorithm;
- constructive witness extraction;
- a terminating normalization procedure;
- sharp computable error certificates;
- automatic certificate generation;
- a reduction in the computational complexity of verifying a property;
- an algorithm that makes a previously impractical computation routine.

Do not conflate:

```math
\text{decidable},
\qquad
\text{computable},
\qquad
\text{approximable with certificate}.
```

Each claim must be stated precisely.

### 3.3 Diagnostic and falsification-engine test

A tool may qualify as operationally novel if it creates a reusable capability for discovering or certifying failure.

Examples include a system that:

- searches systematically for minimal counterexamples across a family of problems;
- identifies the smallest admissible dimension in which a conjecture can fail;
- parameterizes candidate counterexamples structurally rather than by blind random search;
- turns floating-point evidence into exact rational or algebraic witnesses;
- converts a numerical counterexample into a Lean-checkable certificate;
- extracts a precise obstruction from a failed proof attempt;
- produces a reusable diagnostic certificate explaining why a class of arguments cannot work.

A **known counterexample itself** is not operational novelty.

A reusable machine that discovers, minimizes, certifies, and explains counterexamples may be.

### 3.4 Proof-complexity compression test

Formalizing an existing paper step-by-step is usually an infrastructure contribution.

An operational formalization may qualify as research when it introduces a structural refactoring that materially changes proof capability.

Examples include:

- replacing many ad-hoc proofs with a small family of composable abstractions;
- unifying historically separate theorem families into one reusable hierarchy;
- exposing a structural lemma that collapses many downstream proofs;
- reducing dependency depth;
- removing duplicated arguments;
- enabling automation across a class of results that previously required bespoke proofs;
- replacing fragile manual rewrites with stable typed interfaces.

Compression should be evidenced where practical by measurable changes such as:

- lines of proof;
- number of duplicated lemmas removed;
- dependency depth;
- number of downstream theorems reused;
- automation success rate;
- hypotheses eliminated;
- manual rewrite steps eliminated;
- new examples made feasible.

Shorter is not automatically better.

An opaque tactic blast is not necessarily an operational advance over a longer transparent proof.

### 3.5 Operational prior-art test

Operational novelty requires its own historical audit.

Ask:

> Has anyone already built substantially this capability?

Search, where relevant:

- Mathlib;
- Lean packages;
- Coq;
- Isabelle;
- HOL;
- Mathematica;
- Maple;
- SageMath;
- MATLAB;
- numerical linear algebra libraries;
- symbolic algebra systems;
- specialized research software;
- theorem-prover APIs;
- supplementary code attached to papers;
- GitHub and other code archives;
- algorithms described in older papers but never widely packaged.

Reject an operational-novelty claim if an existing artifact already supplies substantially the same capability with comparable domain, guarantees, and usability.

A different implementation language does not by itself establish operational novelty.

### 3.6 Capability-delta test

Before promotion, state the operational contribution in this form:

> Before this artifact, one could not practically do \(X\) under conditions \(C\); after this artifact, one can do \(X\) with guarantees \(G\).

Define the capability delta conceptually as:

```math
\boxed{
\Delta_{\mathrm{cap}}
=
\text{post-artifact capability}
-
\text{best prior capability}.
}
```

If the capability delta cannot be stated clearly, the operational contribution is immature.

Examples of meaningful deltas include:

- broader mathematical domain;
- stronger correctness guarantees;
- branch-explicit or type-safe semantics;
- exact rather than heuristic output;
- reusable certificates;
- lower asymptotic cost;
- materially lower human effort;
- better failure diagnostics;
- information preservation that prior representations discarded;
- ability to compose outputs into downstream calculations.

### 3.7 Composability test

Operational novelty is stronger when the artifact creates an intermediate representation or calculus rather than a terminal display.

Ask whether outputs remain usable under operations such as:

- addition;
- multiplication;
- composition;
- tensor product;
- restriction;
- normalization;
- asymptotic comparison;
- extraction of leading terms;
- transformation into further certified objects.

A representation that merely says "diverges" is weaker than one that returns a structured asymptotic object that supports further computation.

The preferred pattern is:

```math
\boxed{
\text{representation}
\to
\text{closed or composable calculus}
\to
\text{new downstream capability}.
}
```

### 3.8 Operational significance test

Operational novelty must matter.

Ask:

1. What mathematical task becomes possible, safer, faster, clearer, or more reproducible?
2. What class of users or proofs benefits?
3. Does it prevent a real class of errors?
4. Is it reusable across a family of problems?
5. Does it create a capability absent from existing systems?
6. Would the capability still matter if implemented in another sufficiently expressive system?

If the answer to question 6 is no, the contribution may merely exploit a local implementation convenience.

That may still be useful, but it is weaker evidence of operational novelty.

The desired combination is:

```math
\boxed{
\text{worthwhile operational target}
=
\text{capability delta}
+
\text{prior-art absence}
+
\text{reuse}
+
\text{validation}
+
\text{significance}.
}
```
## 4. Lean is not a theorem novelty certificate

Lean can establish that a proof is formally correct.

Lean does not establish that the theorem is historically new.

The following are formalization contributions, not automatically mathematical discoveries:

- the first Lean proof of an old theorem;
- the first machine-checked proof of an unstated classical corollary;
- a new Mathlib implementation of established mathematics;
- a cleaner formal statement of an existing theorem;
- an executable verification of a theorem already known on paper.

These may still be valuable.

If theorem novelty fails, do **not** automatically discard the work.

Instead:

```math
\boxed{
\text{demote the theorem-novelty claim}
\quad\text{and then independently evaluate operational novelty.}
}
```

A formalization may therefore be:

- mathematically old and operationally ordinary;
- mathematically old but operationally novel;
- mathematically new but operationally ordinary;
- mathematically new and operationally novel.

The two axes must remain distinct.

## 5. AI is not a novelty certificate

AI can generate:

- conjectures;
- examples;
- counterexamples;
- proof sketches;
- theorem statements;
- research architectures;
- bibliographies;
- Lean implementations;
- operational interfaces;
- algorithm sketches;
- software abstractions.

AI can also produce:

- an elaborate research program around a theorem that is already known;
- an operational framework that already exists elsewhere;
- a polished type hierarchy built around a false mathematical premise;
- an impressive "frontier" that is not actually open.

Therefore no amount of generated structure counts as novelty evidence.

Research expansion must wait until the relevant triage has been performed.
## 6. Mandatory pre-campaign triage

Before a candidate becomes a major theorem or operational campaign, apply the appropriate tests in order.

### Test 1. Try to disprove or break it

For theorem candidates, actively search for:

- low-dimensional counterexamples;
- degenerate cases;
- repeated eigenvalues;
- singular cases;
- boundary cases;
- parameter collisions;
- pathological branch choices;
- hidden symmetry;
- centralizer freedom;
- exceptional arithmetic cases;
- examples suggested by known classification theorems.

For operational candidates, actively search for:

- type mismatches;
- hidden dependencies;
- branch ambiguities;
- noncanonical outputs;
- nontermination;
- unstable representations;
- information loss;
- failure under composition;
- examples where the proposed abstraction provides no benefit.

A counterexample or failed design is a successful exploratory result.

Do not repair a failed candidate until the mechanism of failure is understood.

### Test 2. Try to derive or reconstruct it immediately from known work

For theorem candidates, ask:

> What is the strongest known theorem that touches this statement?

Then attempt to derive the candidate directly from that theorem.

For operational candidates, ask:

> What is the strongest existing tool, algorithm, library, or abstraction that already does this?

If the candidate is just a thin wrapper, direct transcription, or routine consequence, reject or demote it.

### Test 3. Search for the exact theorem or capability

For theorem candidates, search:

- exact statement;
- exact equations;
- exact hypotheses;
- exact conclusion;
- author terminology;
- older terminology;
- alternate notation.

For operational candidates, search:

- exact tool behavior;
- equivalent APIs;
- software packages;
- published algorithms;
- theorem-prover libraries;
- code supplements;
- historical implementations.

### Test 4. Search for equivalent formulations or implementations

For theorem candidates, translate into:

- coordinate-free form;
- Jordan form;
- spectral form;
- operator form;
- algebraic form;
- topological form;
- category-theoretic form where relevant;
- historical terminology.

For operational candidates, translate into:

- alternative data structures;
- equivalent type signatures;
- symbolic versus numerical forms;
- theorem-prover versus CAS implementations;
- direct versus certificate-producing algorithms.

A contribution can be old even if the wording or implementation language is new.

### Test 5. Search for stronger prior results or capabilities

For theorem candidates, ask:

> Is there an existing theorem from which this follows routinely?

For operational candidates, ask:

> Is there an existing system that already provides a stronger capability?

This test is more important than exact-title search.

### Test 6. Search backward through classical references

Trace citations behind the modern source.

Do not stop at the newest paper.

If a result relies on classical machinery, inspect the older source that actually contains the classification, construction, or algorithm.

For operational candidates, inspect whether a supposedly "new" implementation was already described algorithmically in older literature.

### Test 7. Search forward from the likely source

Use forward citations to see whether later work already:

- proved the theorem;
- disproved it;
- extracted the consequence;
- implemented the algorithm;
- generalized the tool;
- built the operational artifact.

### Test 8. Apply the specialist test

For theorem candidates:

> If a domain specialist already knew the relevant classical theorem, could they derive this result in one sitting without inventing a new idea?

If yes, classify it as routine unless there is strong evidence otherwise.

For operational candidates:

> If a domain specialist had the strongest existing tools, could they already perform this task comparably well without inventing a new architecture?

If yes, the capability delta is probably too small.

### Test 9. State the non-routine step or capability delta

For theorem candidates, write one paragraph identifying exactly what part of the proof is not already supplied by known theory.

For operational candidates, write one paragraph identifying exactly what capability did not previously exist in comparable form.

If this paragraph cannot be written clearly, the candidate is not mature.

### Test 10. Only then authorize substantial Lean or engineering work

Large campaigns begin only after the candidate survives the relevant preceding tests.

Early Lean work, prototypes, scripts, and numerical experiments are still encouraged when cheap and useful for falsification or capability testing.
## 7. Dual-track exploration statuses

Every exploratory topic should have one explicit status on each relevant track.

```text
                         ┌── THEOREM CANDIDATE
EXPLORATORY ─────────────┤
                         └── OPERATIONAL CANDIDATE

THEOREM CANDIDATE
    ↓
RESEARCH TARGET
    ↓
NOVELTY-SUPPORTED THEOREM

OPERATIONAL CANDIDATE
    ↓
OPERATIONAL TARGET
    ↓
NOVELTY-SUPPORTED ARTIFACT
```

The two tracks may interact.

An operational artifact may expose a theorem candidate.

A new theorem may enable a new operational capability.

A project may eventually qualify on both tracks.

### `EXPLORATORY`

An interesting phenomenon, question, example, conjecture, representation, algorithm, or tool idea.

No novelty assessment has been completed.

This is the default status for new ideas.

### `THEOREM CANDIDATE`

The theorem has survived obvious counterexamples and a quick prior-art check.

It is still not ready for a major campaign.

### `OPERATIONAL CANDIDATE`

The artifact appears to create a useful capability and has survived obvious design failures and a quick operational prior-art check.

It is still not ready for a major campaign.

### `RESEARCH TARGET`

The theorem candidate has survived:

- adversarial falsification;
- reduction to known theory;
- exact and equivalent-form literature search;
- stronger-theorem search;
- specialist routine-consequence test.

There appears to be a real mathematical gap.

This status authorizes substantial theorem-proving work.

### `OPERATIONAL TARGET`

The operational candidate has survived:

- explicit defect identification;
- operational prior-art search;
- capability-delta analysis;
- reuse/composability analysis;
- demonstration that the abstraction is not merely a language-specific wrapper;
- evidence that the artifact creates a materially new capability.

This status authorizes substantial formalization or engineering work.

### `NOVELTY-SUPPORTED THEOREM`

The proof is complete and a separate novelty audit has failed to locate:

- the theorem;
- an equivalent theorem;
- a stronger theorem implying it routinely;
- a classical result making the proof immediate.

This status still does not claim absolute historical priority.

It means the theorem-novelty claim has survived reasonable serious investigation.

### `NOVELTY-SUPPORTED ARTIFACT`

The artifact is complete and a separate operational audit has failed to locate a substantially equivalent prior capability.

Require:

- complete implementation or formalization;
- no `sorry` in Lean deliverables;
- explicit type-theoretic or algorithmic contract;
- documented inputs, outputs, failure modes, and guarantees;
- evidence of capability delta;
- evidence of reuse across a family of problems;
- comparison against the strongest prior artifacts;
- demonstrated compression, decidability, certification, composability, or error elimination.

This status does not imply theorem novelty.
## 8. Required evidence before promotion

### `EXPLORATORY` to `THEOREM CANDIDATE`

Require:

- precise theorem statement or research question;
- known assumptions stated;
- at least one serious attempt to falsify;
- quick literature reconnaissance;
- list of strongest known related theorems.

### `EXPLORATORY` to `OPERATIONAL CANDIDATE`

Require:

- precise capability statement;
- explicit informal defect or operational limitation being addressed;
- prototype, worked example, or type contract;
- at least one serious attempt to break the design;
- quick operational prior-art reconnaissance;
- statement of the proposed capability delta.

### `THEOREM CANDIDATE` to `RESEARCH TARGET`

Require:

- no known counterexample;
- exact candidate statement stabilized;
- direct derivability from known theory tested;
- strongest classical machinery identified;
- exact theorem search performed;
- equivalent-form search performed;
- stronger-theorem search performed;
- brief paper proof outline attempted;
- reason recorded for why the proof appears non-routine.

### `OPERATIONAL CANDIDATE` to `OPERATIONAL TARGET`

Require:

1. explicit identification of the informal or operational defect;
2. search showing that existing libraries or tools do not already provide a comparable capability;
3. a clear capability-delta statement;
4. evidence of reuse across a family of problems;
5. evidence that the proposed type/interface prevents real classes of errors or ambiguity;
6. composability plan;
7. benchmark or comparison plan against prior methods;
8. reason recorded for why the contribution is not merely transcription or implementation-language novelty.

### `RESEARCH TARGET` to `NOVELTY-SUPPORTED THEOREM`

Require:

- complete proof;
- Lean proof where Lean is part of the project;
- no `sorry`;
- no hidden unproved assumptions;
- independent mathematical write-up;
- serious historical and current literature audit;
- backward and forward citation search;
- explicit comparison with the strongest prior result;
- documented explanation of the genuinely non-routine step.

### `OPERATIONAL TARGET` to `NOVELTY-SUPPORTED ARTIFACT`

Require:

- complete implementation or certified formalization;
- no `sorry` in Lean deliverables;
- complete type or algorithmic specification;
- documented failure modes;
- regression tests;
- reuse demonstrated on multiple nontrivial examples;
- benchmark against prior artifacts;
- explicit capability-delta evidence;
- operational prior-art audit;
- documentation sufficient for another user to apply the artifact without reconstructing the theory from scratch.
## 9. The paper-proof-before-token-furnace rule

Before launching a long-running agent on a theorem that appears close to classical theory, attempt a concise mathematical proof on paper or in Markdown.

The purpose is diagnostic.

If the entire proof reduces to:

1. invoke known classification theorem;
2. decompose into standard cases;
3. apply elementary lemmas;
4. recombine;

then the theorem is probably not a worthwhile theorem-novelty target.

Do not spend days formalizing it merely because the exact statement appears absent from the literature.

However, if theorem novelty fails, independently ask whether the proof or formalization exposes a genuine operational contribution.

For operational candidates, perform the analogous prototype-before-token-furnace test:

1. state the defect;
2. build the smallest working prototype;
3. compare it to the strongest existing tool;
4. demonstrate a real capability delta;
5. attempt to break composability and type safety.

If the prototype is merely a wrapper around existing capability, stop or demote it.

## 10. Counterexamples and failed artifacts are first-class outputs

A failed conjecture is not wasted work if the failure is understood.

When a theorem conjecture fails:

1. preserve the exact failed statement;
2. preserve the smallest clean counterexample;
3. identify the mechanism of failure;
4. add the counterexample as a permanent Lean regression test if practical;
5. repair the conjecture only after understanding the obstruction;
6. rerun theorem novelty triage on the repaired statement.

When an operational design fails:

1. preserve the failed contract;
2. preserve the smallest example showing the defect;
3. identify the type, semantic, algorithmic, or compositional failure;
4. convert it into a regression test where practical;
5. repair the design only after understanding the failure mechanism;
6. rerun operational prior-art and capability-delta triage.

Do not silently mutate a conjecture or interface until it becomes true or usable.

The history of failure is informative.
## 11. Novelty language discipline

Before a full theorem novelty audit, permitted language includes:

- exploratory;
- theorem candidate;
- candidate theorem;
- candidate result;
- formal target;
- apparently unstated;
- apparently unstated consequence;
- apparently absent from the searched literature;
- plausible research target.

Before a full operational novelty audit, permitted language includes:

- operational candidate;
- candidate abstraction;
- candidate capability;
- prototype;
- apparently absent from existing tools;
- candidate operational target.

Avoid, until justified:

- new theorem;
- novel theorem;
- first proof;
- first result;
- previously unknown;
- original theorem;
- discovered theorem;
- first implementation;
- novel tool;
- unprecedented capability;
- operationally novel.

The phrase "apparently unstated" does not imply theorem novelty.

The phrase "apparently unavailable" does not imply operational novelty.

## 12. Literature and prior-art search standard

A serious theorem novelty audit should search, where relevant:

- journal articles;
- monographs;
- conference proceedings;
- theses;
- preprints;
- historical sources;
- MathSciNet or equivalent indexes when available;
- zbMATH or equivalent indexes when available;
- arXiv;
- Google Scholar;
- author publication pages;
- references cited by the strongest known source;
- papers citing the strongest known source;
- non-English literature when the field has substantial work outside English.

Search both terminology and equations.

Search the theorem in multiple mathematical representations.

A serious operational prior-art audit should additionally search:

- Mathlib;
- Lean packages;
- Coq;
- Isabelle;
- HOL;
- Mathematica;
- Maple;
- SageMath;
- MATLAB;
- numerical and symbolic libraries;
- GitHub;
- supplementary code;
- research software;
- published pseudocode;
- old algorithms and implementation papers.

Search both the exact interface and the underlying capability.
## 13. Strong prior theory and prior tooling must be treated as hostile evidence

If a complete classification theorem already exists near the problem, assume initially that it may already contain the answer.

Examples of dangerous prior machinery include:

- Jordan classification;
- spectral theorem;
- Galois correspondence;
- representation classification;
- structure theorem for finitely generated modules;
- canonical forms;
- complete solution parametrizations;
- universal properties;
- known equivalence classifications.

The burden is on the theorem candidate to show that it is not merely an output of that machinery.

Likewise, if mature mathematical software exists near an operational candidate, assume initially that it may already provide the capability.

The burden is on the operational candidate to demonstrate a real capability delta.

## 14. Significance tests

### 14.1 Theorem significance test

Before promotion to `RESEARCH TARGET`, answer:

1. Why would a mathematician care if this theorem were true?
2. What question does it resolve?
3. What becomes possible after proving it?
4. Does it reveal a mechanism not already visible from known theory?
5. Is the theorem reusable?
6. Would the theorem still be interesting if Lean were removed from the story?

If the answer to question 6 is no, it is probably a formalization or operational project rather than a theorem-novelty project.

That is acceptable, but it should be labeled honestly.

### 14.2 Operational significance test

Before promotion to `OPERATIONAL TARGET`, answer:

1. What task becomes possible, safer, faster, clearer, or more reproducible?
2. What precise defect in current practice is removed?
3. What errors become impossible or easier to diagnose?
4. What downstream work becomes easier?
5. Is the capability reusable?
6. Would the capability still matter if implemented outside Lean?

If the answer to question 6 is no, the operational claim may be too implementation-specific.
## 15. Recommended exploratory file header

Every exploratory project should begin with something like:

```text
Status: EXPLORATORY

Theorem candidate:
<exact theorem or question, if any>

Operational candidate:
<exact capability or artifact, if any>

Known prior theory:
<strongest known related results>

Known prior tools:
<strongest known related implementations>

Counterexample status:
<tested / found / unresolved>

Design-break status:
<tested / found / unresolved>

Immediate-corollary status:
<tested / unresolved>

Capability-delta status:
<tested / unresolved>

Literature status:
<quick search / serious search / novelty audit complete>

Operational prior-art status:
<quick search / serious search / audit complete>

Reason theorem may be non-routine:
<one concise paragraph>

Reason capability may be operationally new:
<one concise paragraph>

Next falsification test:
<one concrete action>

Next operational break test:
<one concrete action>
```

This keeps both research axes visible.

## 16. Stop and demotion conditions

Stop, demote, or reclassify a theorem project when:

- an equivalent theorem is found;
- a stronger theorem makes it routine;
- the proof collapses to a short standard corollary;
- the mathematical significance disappears;
- repeated conjecture repairs merely chase counterexamples without revealing a coherent mechanism;
- the project becomes a classification exercise with no sharp target.

If theorem novelty fails:

```math
\boxed{
\text{demote the theorem claim}
\quad\text{and independently test for operational novelty.}
}
```

Stop, demote, or reclassify an operational project when:

- an equivalent tool already exists;
- the proposed capability delta disappears;
- the artifact is only a wrapper around an existing implementation;
- the abstraction is useful only for one manufactured example;
- the type/interface does not prevent a real class of errors;
- the output cannot be reused downstream;
- no meaningful benchmark advantage can be demonstrated;
- the only distinction is implementation language.

A demoted project may still be valuable as:

- infrastructure;
- education;
- Mathlib contribution;
- formal verification;
- reproducibility work;
- documentation;
- engineering.

It simply should not be mislabeled.
## 17. Example: matrix-matrix exponentiation work

The matrix exponentiation investigation illustrates why the dual standard is needed.

| Component | Theorem Track | Operational Track |
|---|---|---|
| Claiming \(A^B\) is a universal complete theory | Rejected | Rejected |
| Type-invalid orientation tensor | Rejected | Rejected |
| Typed definition \((A,B,L)\mapsto\exp(B\otimes L)\) | Probably routine mathematically | `OPERATIONAL CANDIDATE` until prior-art audit |
| Explicit distinction between \(V\), \(\operatorname{End}(V)\), superoperators, and tensor operators | Not theorem novelty | `OPERATIONAL CANDIDATE` |
| Singular regularization \((A,B,\mathcal R)\mapsto[\varepsilon\mapsto\cdots]\) | Novelty unestablished | `OPERATIONAL CANDIDATE` |
| Known published counterexample found in literature | Known result | Not operational novelty by itself |
| Reusable pipeline that discovers, minimizes, exactifies, and Lean-certifies counterexamples | Not theorem novelty by itself | Potential `OPERATIONAL CANDIDATE` if actually built and prior-art survives |

Nothing in this table is promoted merely because it is useful.

Nothing in this table is discarded merely because its ingredients are old.

Each claim must survive its own track.

## 18. Final governing rules

The project exists to discover mathematically substantive results and to build materially useful mathematical capabilities.

For theorem novelty:

```math
\boxed{
\begin{array}{c}
\text{not already in the literature}\\
+\ \text{not a routine consequence of known theory}\\
+\ \text{contains a substantive mathematical step}\\
+\ \text{answers a natural question of independent interest}
\end{array}
}
```

For operational novelty:

```math
\boxed{
\begin{array}{c}
\text{not already available in comparable form}\\
+\ \text{creates a clear capability delta}\\
+\ \text{is reusable and composable}\\
+\ \text{has explicit guarantees and failure modes}\\
+\ \text{matters independently of implementation language}
\end{array}
}
```

Only after the relevant criteria survive serious scrutiny should a result mature from `Exploratory` into a major theorem or operational campaign.

The governing discipline is:

```math
\boxed{
\textbf{Question first. Answer correctly. Operationalize what is useful. History judges the category afterward.}
}
```

# Exploratory - Novelty and Research Standards

Status: governing research standard for exploratory mathematical projects.

Purpose: this file defines when an exploratory idea is worth maturing into a serious Lean campaign or research project.

The standard is intentionally strict.

## 1. Core research intent

The goal is to prove something that mathematics did not already know.

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

The object of interest is the mathematical theorem itself.

The governing principle is:

```math
\boxed{
\text{I want to prove something mathematics did not already know,}
\text{ not merely say something mathematics already knew in a new language.}
}
```

## 2. Strict novelty standard

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

A good target should do at least one of the following:

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
\text{worthwhile target}
=
\text{theorem novelty}
+
\text{non-routine proof}
+
\text{mathematical significance}.
}
```

## 3. Lean is not a novelty certificate

Lean can establish that a proof is formally correct.

Lean does not establish that the theorem is historically new.

The following are formalization contributions, not automatically mathematical discoveries:

- the first Lean proof of an old theorem;
- the first machine-checked proof of an unstated classical corollary;
- a new Mathlib implementation of established mathematics;
- a cleaner formal statement of an existing theorem;
- an executable verification of a theorem already known on paper.

These may still be valuable projects, but they belong in a different category.

The distinction must remain explicit:

```math
\boxed{
\text{formal novelty}
\neq
\text{mathematical novelty}.
}
```

## 4. AI is not a novelty certificate

AI can generate:

- conjectures;
- examples;
- counterexamples;
- proof sketches;
- theorem statements;
- research architectures;
- bibliographies;
- Lean implementations.

AI can also produce an elaborate research program around a statement that turns out to be an immediate corollary of old theory.

Therefore no amount of generated structure counts as novelty evidence.

Research expansion must wait until novelty triage has been performed.

## 5. Mandatory pre-campaign novelty triage

Before a candidate becomes a major Lean campaign, apply the following tests in order.

### Test 1. Try to disprove it

Actively search for:

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

A counterexample is a successful exploratory result.

Do not repair a failed conjecture until the mechanism of failure is understood.

### Test 2. Try to derive it immediately from known theory

Ask:

> What is the strongest known theorem that touches this statement?

Then attempt to derive the candidate directly from that theorem.

Search especially for:

- complete classification theorems;
- normal forms;
- universal properties;
- representation theorems;
- structure theorems;
- canonical decompositions;
- known equivalence criteria.

If the candidate falls out by a short routine argument, reject it as a novelty target.

### Test 3. Search for the exact theorem

Search:

- exact statement;
- exact equations;
- exact hypotheses;
- exact conclusion;
- author terminology;
- older terminology;
- alternate notation.

Search books, papers, theses, proceedings, preprints, and non-English literature where practical.

### Test 4. Search for equivalent formulations

Translate the theorem into:

- coordinate-free form;
- Jordan form;
- spectral form;
- operator form;
- algebraic form;
- topological form;
- category-theoretic form where relevant;
- historical terminology.

A theorem can be old even if the wording is new.

### Test 5. Search for stronger prior results

Ask:

> Is there an existing theorem from which this follows routinely?

This test is more important than exact-title search.

A candidate should be rejected if it is merely one easy output of a known complete theory.

### Test 6. Search backward through classical references

Trace citations behind the modern source.

Do not stop at the newest paper.

If a result relies on classical machinery, inspect the older source that actually contains the classification or structural theorem.

### Test 7. Search forward from the likely source

Use forward citations to see whether later work already extracted the consequence.

### Test 8. Apply the specialist test

Ask:

> If a domain specialist already knew the relevant classical theorem, could they derive this result in one sitting without inventing a new idea?

If yes, classify it as routine unless there is strong evidence otherwise.

### Test 9. Only then authorize substantial Lean work

Large formalization effort begins only after the candidate survives the preceding tests.

Early Lean work is still encouraged when it is cheap and useful for falsification.

## 6. Exploration statuses

Every exploratory topic should have one explicit status.

### `EXPLORATORY`

An interesting phenomenon, question, example, or conjecture.

No novelty assessment has been completed.

This is the default status for new ideas.

### `CANDIDATE`

The idea has survived obvious counterexamples and a quick prior-art check.

It is still not ready for a large campaign.

### `RESEARCH TARGET`

The candidate has survived:

- adversarial falsification;
- reduction to known theory;
- exact and equivalent-form literature search;
- stronger-theorem search.

There appears to be a real mathematical gap.

This status authorizes substantial Lean work.

### `NOVELTY-SUPPORTED RESULT`

The proof is complete and a separate novelty audit has failed to locate:

- the theorem;
- an equivalent theorem;
- a stronger theorem implying it routinely;
- a classical result making the proof immediate.

This status still does not claim absolute historical priority.

It means the novelty claim has survived reasonable serious investigation.

## 7. Required evidence before promotion

### `EXPLORATORY` to `CANDIDATE`

Require:

- precise theorem statement or research question;
- known assumptions stated;
- at least one serious attempt to falsify;
- quick literature reconnaissance;
- list of strongest known related theorems.

### `CANDIDATE` to `RESEARCH TARGET`

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

### `RESEARCH TARGET` to `NOVELTY-SUPPORTED RESULT`

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

## 8. The paper-proof-before-token-furnace rule

Before launching a long-running agent on a theorem that appears close to classical theory, attempt a concise mathematical proof on paper or in Markdown.

The purpose is diagnostic.

If the entire proof reduces to:

1. invoke known classification theorem;
2. decompose into standard cases;
3. apply elementary lemmas;
4. recombine;

then the theorem is probably not a worthwhile novelty target.

Do not spend days formalizing it merely because the exact statement appears absent from the literature.

Lean may still be useful later if the formalization itself is independently valuable.

## 9. Counterexamples are first-class outputs

A failed conjecture is not wasted work if the failure is understood.

When a conjecture fails:

1. preserve the exact failed statement;
2. preserve the smallest clean counterexample;
3. identify the mechanism of failure;
4. add the counterexample as a permanent Lean regression test if practical;
5. repair the conjecture only after understanding the obstruction;
6. rerun novelty triage on the repaired statement.

Do not silently mutate a conjecture until it becomes true.

The history of failure is mathematically informative.

## 10. Novelty language discipline

Before a full novelty audit, permitted language includes:

- exploratory;
- candidate theorem;
- candidate result;
- formal target;
- apparently unstated;
- apparently unstated consequence;
- apparently absent from the searched literature;
- plausible research target.

Avoid:

- new theorem;
- novel theorem;
- first proof;
- first result;
- previously unknown;
- original theorem;
- discovered theorem.

The phrase "apparently unstated" does not imply mathematical novelty.

## 11. Literature-search standard

A serious novelty audit should search, where relevant:

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

## 12. Strong prior theory must be treated as hostile evidence

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

The burden is on the candidate theorem to show that it is not merely an output of that machinery.

## 13. Significance test

Before promotion to `RESEARCH TARGET`, answer:

1. Why would a mathematician care if this theorem were true?
2. What question does it resolve?
3. What becomes possible after proving it?
4. Does it reveal a mechanism not already visible from known theory?
5. Is the theorem reusable?
6. Would the theorem still be interesting if Lean were removed from the story?

If the answer to question 6 is no, it is probably a formalization project rather than a mathematical novelty project.

That is acceptable, but it should be labeled honestly.

## 14. Recommended exploratory file header

Every exploratory project should begin with something like:

```text
Status: EXPLORATORY

Candidate statement:
<exact theorem or question>

Known prior theory:
<strongest known related results>

Counterexample status:
<tested / found / unresolved>

Immediate-corollary status:
<tested / unresolved>

Literature status:
<quick search / serious search / novelty audit complete>

Reason this may be non-routine:
<one concise paragraph>

Next falsification test:
<one concrete action>
```

This keeps research state visible.

## 15. Stop conditions

Stop or demote a project when:

- an equivalent theorem is found;
- a stronger theorem makes it routine;
- the proof collapses to a short standard corollary;
- the only novelty is Lean formalization;
- repeated conjecture repairs merely chase counterexamples without revealing a coherent new mechanism;
- the mathematical significance disappears;
- the project becomes a classification exercise with no sharp target.

A demoted project may still be valuable as infrastructure, education, Mathlib contribution, or formal verification.

It simply no longer counts toward the mathematical novelty objective.

## 16. Final governing rule

The project exists to discover and prove mathematically substantive results, not to manufacture novelty by changing the mode of expression.

The standard is:

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

Only after all four survive serious scrutiny should a result mature from `Exploratory` into a major proof campaign.

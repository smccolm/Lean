# Tau Ceti Explorer

An interactive atlas of mathematical roadmaps: one universe with Mathlib at its centre, in which subjects are galaxies, roadmaps are constellations, layers are stars and the mathematics itself orbits them as planets.

**[Open the interactive atlas](https://cbirkbeck.github.io/tauceti-explorer/)**

Since 21 October 2026 the atlas shows Tau Ceti's own roadmaps, with each layer's state from Tau Ceti's [Progress page](https://taucetiproject.github.io/TauCeti/progress/), and every roadmap proposed in an open pull request to [TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap), whoever opened it, in place of the campaign's own planned roadmaps. A proposed roadmap's layers come from the README on its pull request's branch; they count as not started, and its panel links to the pull request. [The Tau Ceti atlas](https://cbirkbeck.github.io/tauceti-explorer/tauceti/) shows Tau Ceti's roadmaps alone. Both are rebuilt four times a day by `.github/workflows/tauceti-progress.yml`.

The atlas also runs entirely offline. Download `index.html` and open it in a browser; its roadmap text, data, graph library, and interface are embedded in that single file. No installation, account, or local server is required.

## Explore

- Mathlib is the sun at the centre. The farther out a subject or roadmap lies, the more theory must be built before its targets can be stated and proved.
- Scroll or pinch toward a **subject** to see its **roadmap constellations**, toward a constellation to read its **layer stars**, and toward a star to discover its **orbiting mathematical planets**.
- Tap or click a roadmap, star or planet to make the same journey directly. Zoom out or use the back control to return to the previous level.
- Formula planets have short plain-text names; clicking them opens the typeset definition, theorem target or construction from the source. The details also list citations from the topic or layer and broader roadmap reading, with links back to the embedded source. Progress belongs to its layer star; planets do not carry independent completion claims.
- The details panel explains the mathematics, tracked progress, prerequisites and consumers. The Links tab exposes the actual stage pairs behind dependencies.
- Search for a subject, roadmap, or individual stage. Open the full roadmap to read its outline and source text.
- Drag to pan and use Fit to recover the current scene. Export the current graph as SVG.
- Open **Mission status** for a progress breakdown by subject. Filter the collection by layer activity, and pin roadmaps for your next visit.
- Use **Browse** on a phone, or **⌘/Ctrl K** on a keyboard to search. Mobile details share the screen with the chart; pinch, tap and back controls remain available. View links preserve the current roadmap and planetary system.
- Mathematics is typeset offline with native MathML; hover a formula to see its source.

The atlas is one continuous universe. Subjects are galaxies, roadmaps are the constellations inside them, layers are the stars of a constellation, and a layer's definitions, theorems and constructions are the planets of its star. Everything sits in a single coordinate system, so zooming is a camera movement rather than a change of page: from the whole universe the areas are named and each roadmap is a point; inside a galaxy the constellations resolve into their stars and figures; inside a constellation the stars show their names and planets; inside a star system the planets are named. The address bar and breadcrumbs follow the camera, and only what the camera can see and resolve is drawn, which keeps zooming quick. Names are placed only where they fit: never across another planet, star or control, and a name with no room waits for more zoom rather than shrinking or overlapping. Clicking an object travels to it; the back control steps out one level. A large roadmap is given room in proportion to its number of layers, and each layer's planetary system is kept clear of its neighbours, so dense roadmaps separate as the camera closes in.

Mathlib sits at the centre of the universe as a small sun: a disc that darkens from a white-gold centre to an orange rim, with a faint corona, light granulation and two small spots. On the published pages, each roadmap belongs to the galaxy of its arXiv category, named on the map with its identifier (`math.NT`): the `topic` its `metadata.toml` declares, which the Progress page passes on for Tau Ceti's roadmaps and a pull request's own `metadata.toml` gives for a proposed one. A roadmap that declares none takes the category of the folder above it, else that of most of the roadmaps it is linked to, else that of the subject its title names, and otherwise waits under "No arXiv category" (`scripts/arxiv_groups.py`). The categories go round Mathlib in a fixed order, so related subjects are neighbours, each with a share of the circle that grows with its size. The explorer's own planned map (`scripts/build.py --campaign`, not published) keeps its 28 subject galaxies, chosen from the Mathematics Subject Classification of each roadmap's principal references, which are looked up in zbMATH: one galaxy for each subject cluster of that classification, two clusters split by primary subject class (elementary number theory, computational number theory and finite fields; and algebraic K-theory and motives).

Where everything sits is measured by `scripts/measure_distances.py`:

- **Distance from Mathlib** is a score from 0 to 10, measured from the theory a roadmap still needs. Over the prerequisite closure of the roadmap's layers, it counts the targets still missing from Mathlib and Tau Ceti, T, and the longest chain of layers still to be built, D, and combines them as w_T ln(1 + T) + w_D D. The reviewed library audits count the missing targets: a target absent from both libraries counts one, a partial one a half, and a process layer none; a layer not yet audited counts the mean of the audited layers still to be built. Layers recorded as complete, or found built by a reviewed audit, are library material. The two weights are fitted to pairwise judgements: independent judges on the swarm compared two roadmaps at a time and decided which needs more new theory on top of the pinned libraries, and a difference of one in the measurement means odds of e to one that the higher roadmap is judged farther. Each roadmap then moves from its measurement with its own judgements, in a Bradley–Terry model that takes the measurement as its prior, which also gives it an interval. On the atlas's scale, 0 means everything in the prerequisite closure is built and 10 is the farthest roadmap in the atlas. The judging design and its jobs are made by `research/blueprint/make_compare_jobs.py`.
- **Validation.** Each block of judgements is predicted by the function fitted to the other blocks, and compared with the measurement alone, the reference classification's own 0-to-10 score, and the previous method, which moved the classification's score with the judgements. The adopted function predicts held-out verdicts best, and every completed roadmap sits at zero. The figures are kept in the validation block of `data/roadmap-distances.json`.
- **Direction** follows relatedness. On the published pages it is the fixed order of the arXiv categories, above; on the planned map, two galaxies are related when they rest on the same prerequisite layers, with rare layers and layers still to be built counting more, and when their references share subject classes. Directions are fitted so that related galaxies point the same way, while galaxies may not overlap. The result is turned so that the bulk of the roadmaps lies to the right, with algebraic geometry above that axis and number theory below it. Number theory and geometry, which hold most of the roadmaps, therefore fan out together, and the other subjects sit on the far side of the centre, where new roadmaps will fill the space.
- A galaxy lies at the mean distance of its roadmaps, and the distance on the map grows faster than the score, so the farthest subjects stand clearly apart. Inside a galaxy, the nearer roadmaps sit on the side facing the centre. The map is the same on every screen. A phone opens it at the scale a desktop window gives it, with Mathlib a third of the way across, and the reader pans to see the rest.

A roadmap's overview gives its distance, the measures behind it and its subject class. The older layout, with areas at fixed anchors and no centre, opens by adding `#layout=areas` to the address.

No links are drawn at rest. Selecting a roadmap shows its prerequisite links to other roadmaps. On the published pages these include every roadmap its README names in a dependency section ("Dependencies", "Prerequisites", "Builds on", a layer's own "Dependencies" list) or on a line saying it consumes, builds on or depends on it, and, the other way, those a "Downstream consumers" section names (`scripts/roadmap_dependencies.py`); the Links tab gives the README line each comes from. Selecting a star shows the prerequisites and consumers of that layer, prerequisite → consumer; hovering a subject heading shows the routes between subjects, drawn from rim to rim. Selecting a link names the two things it joins, the prerequisite first, and either name travels to its end; each link has a wide invisible edge, so a finger can pick it out. The faint figure joining a constellation's stars prefers real prerequisite pairs and is a shape, not a claim. Planet orbits express membership in a layer, not additional prerequisites. Planets are meant to be key definitions, named theorems and central constructions; extracted paragraphs that are instructions, checks, scope caveats or bookkeeping are hidden from the map through `data/landmark-hidden.json`, each with a recorded reason, and an editorial pass is replacing the remaining sentence-fragment names with short names drawn from the passages themselves. Related-plan links can be switched on and carry no prerequisite claim. Positions, discs and orbits are visual aids, not astronomical coordinates or mathematical measurements.

On subjects, roadmaps and layers, colour means one thing: recorded progress, shown as brightness. A layer, roadmap or area recorded as not started is red; it warms through salmon as work is recorded and turns white when complete, so a subject's galaxy brightens as its roadmaps fill in. An open ring means no progress has been recorded, and nothing is ever coloured as started or as zero percent to fill the gap. Planets carry no progress of their own. They are round, and what they look like says what they are: a definition or construction is an Earth, a blue disc with green land, and a result is a Saturn, a sand-coloured disc with a tilted ring, drawn a little larger, most of all for a named theorem. Their colours lie outside the progress ramp, and a legend appears inside a star system. All marks are flat: solid fills and thin strokes, with no gradients, glows or shaded spheres, except the sun at the centre. The page uses system type, one dark palette and no decorative elements; headline statistics live in Mission status. Scene artwork is generated locally as SVG. There are no external fonts or image downloads, transitions are short, and reduced-motion preferences are respected.

## Source-decomposed refinements

Roadmap layers can carry reviewed refinements: constructions, lemmas, theorems and comparisons read from the primary references by the source-expansion programme, each with its statement, hypotheses, proof route, acceptance conditions and source locators. Refinements orbit their layer as planets, drawn with a dashed edge, and open to their statement, sources and dependencies. They are planning detail: they never enter the progress denominators, never inherit a status from their layer, and carry an unchecked implementation status. A refinement added during review, rather than verified in it, says so. Reviewed packets live under `data/decompositions/` and are merged into the immutable snapshot at build time; the snapshot itself is never edited.

## Included snapshot

| Item | Count |
| --- | ---: |
| Subject galaxies | 27 |
| Roadmaps | 211 (one retired, see below) |
| Recorded stage entries | 1,962 |
| Reviewed source refinements | 646 (51 roadmaps, partial coverage) |
| Mathematical layer stars | 1,898 |
| Source-backed mathematical planets | 4,125 extracted targets shown (609 procedural paragraphs hidden) + 646 refinements |
| Terminal targets counted for progress | 1,890 |
| Roadmap dependency links | 1,029, including those from reviewed refinements |
| Stage dependency links | 4,239, including those from reviewed refinements |
| Sanitized source Markdown documents | 296 |

The September 2026 edition combines 152 revised number-theory campaign roadmaps with 60 roadmaps from [TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap): its `main` branch at commit fa4d030 (14 September 2026), including the four roadmaps the maintainers have archived as complete, plus the modular-curves roadmap from open pull request #81. The source documents are bundled under [`content/`](content/). The 12 companion guides include the campaign execution protocol, conventions and scope. Reference PDFs and extracted book text are not included. [`data/PUBLICATION.json`](data/PUBLICATION.json) records the publication checks; the atlas and status data retain source hashes, reported commit IDs, and dates.

All 211 overview summaries explain the mathematical objects, results and scope for readers of the atlas. Star names and descriptions present mathematics first; curated entries in `data/stage-presentation.json` replace administrative wording without changing source records. Other descriptions use mathematical passages from the source. The 64 duplicate readiness checkpoints remain in the full source and progress totals, and are accessible under Project tasks in the Layers tab. They do not appear as mathematical stars. Original roadmap texts remain available in full.

One roadmap of the snapshot has been retired: `FoundationsAndLibraryIntegration` inventoried general algebra, analysis and category theory that Mathlib already has, re-listed roadmaps that exist in their own right, such as class field theory and Chebotarev density, and was otherwise process. `data/roadmap-retirements.json` records the reason; `scripts/retirements.py` removes a retired roadmap, its layers and every link through it wherever the atlas is read, and an old link to it opens the whole atlas. A library audit (`research/blueprint/make_audit_jobs.py`) is checking every layer against the pinned Mathlib and Tau Ceti, with an independent review (`scripts/merge_library_audit.py`, `data/library-coverage.json`). On a Tau Ceti roadmap, a layer the reviewed audit finds already built counts as complete, with the declarations as evidence. A proposed roadmap shows only what still has to be built: what the libraries already contain is its starting point, never its progress, so the audit never colours a proposed roadmap, and a proposed layer the audit finds already built, or finds to be process rather than mathematics, is hidden, with the reason.

Each subject's panel says why it is in the atlas: which other subjects use its roadmaps directly, with examples, and how many frontier roadmaps (distance 7 or more) rest on its layers through chains of prerequisites. A roadmap's overview names the subjects that use it.

The source snapshot includes local working-tree material and older maintained progress reports. It is not a fresh verification of the Tau Ceti code or of every mathematical proof. Roadmap-level cycles can reflect dependencies between different early and late stages; the encoded stage dependency graph is acyclic.

## Progress colours and local updates

Stage colours run from red (not started) through salmon (in progress) to white (complete). Layers without recorded status have no progress label or status colour. For upstream roadmaps, a roadmap the maintainers archived under `Completed/` is complete with all its layers; otherwise layer statuses are mapped from the roadmap's maintained STATUS.md report, sentence by sentence, and each mapped status carries the quoted sentence and its line numbers. A report is a machine-written snapshot of what has landed, not a fresh proof audit. The salmon midpoint is a status category, not a claim that a theorem is half proved.

Roadmap and subject percentages count **completed terminal targets divided by all tracked terminal targets**. Unknown targets remain in the denominator; no percentage is shown when an entire roadmap or subject has no status data. A parent stage and its children are never counted twice; collection roadmaps aggregate their child roadmaps. Completing every extracted target does not by itself certify all source-proof, acceptance, or formal-verification requirements. A separately displayed roadmap-level report retains its own provenance.

Open a stage to change its status and add an evidence note. A parent-stage update includes its descendants. Your changes are local overrides, stored in the current browser when storage is available; they do not edit the published data or upstream repositories. “Use recorded status” removes the corresponding local override and its descendants.

Use **Progress → Download offline atlas** for a standalone HTML copy.

Use **Progress → Export progress** to save a JSON backup. Import restores a validated local snapshot, replacing the current local overrides. Export before changing browsers or opening the atlas from a different location: browser storage is tied to its origin and may be unavailable or cleared. If storage is blocked, updates remain available during the current page session and can still be exported.

## Rebuild

Requires Python 3.9 or later, using only its standard library:

```sh
python3 scripts/build.py
```

This writes the self-contained `index.html` and a `BUILD.json` report containing counts and input/output hashes, and makes no network requests. The proposed roadmaps' READMEs are too large to keep in the repository, so first fetch them (Python 3.11 or later, with an authenticated `gh`): `python3 scripts/tauceti_prs.py --fetch`; the build stops rather than drop them when they are missing. `--tauceti` builds the Tau Ceti atlas, and `--campaign` the campaign's own planned map with its blueprints, papers and links (`campaign/index.html`, not published since 21 October 2026). An alternate output location can be supplied with `--output`.

The builder packages the checked-in snapshot. To update the published mathematics or imported reports, update the corresponding documents and data, retain their provenance, and rebuild. Rebuilding does not fetch upstream changes or import anyone's browser-local progress.

### Repository layout

- `src/`: interface, graph, Markdown reader, progress state, and styles.
- `src/camera.js`: mouse, touch and button navigation between the three spatial levels.
- `vendor/`: bundled D3, KaTeX, and their licences.
- `data/atlas.json`: roadmap text, stage hierarchy, and graph relationships.
- `data/status.json`: explicitly mapped source-status evidence.
- `data/galaxies.json`: the subject galaxies, with descriptions, topics, subject classes, families and directions from the centre.
- `data/roadmap-classification.json`: each roadmap's galaxy and subject classes, with the classification's own 0-to-10 score, which is kept only as a cross-check, generated by `scripts/classification.py` from the classification results and `data/classification-estimates.json`.
- `data/roadmap-distances.json` and `data/galaxy-layout.json`: each roadmap's measured distance from Mathlib with the measures behind it, and each galaxy's direction, generated by `scripts/measure_distances.py` (`scripts/theory_graph.py`, `scripts/bradley_terry.py`, `scripts/radial_layout.py`).
- `data/landmark-labels.json`: short mathematical names for formula planets, separate from their source excerpts.
- `data/landmark-hidden.json`: extracted paragraphs that are not planets (instructions, checks, caveats, bookkeeping), each with a recorded reason.
- `data/roadmap-summaries.json`: edited overview summaries applied over the snapshot at build time.
- `data/stage-status-reports.json`: layer statuses mapped from the maintained STATUS.md reports of upstream roadmaps, each with the quoted sentence and its line numbers.
- `scripts/snapshot/`: the pipeline and procedure that rebuild `data/atlas.json`, `data/status.json` and `content/` from an upstream checkout.
- `data/bibliography.json`: supplied bibliographic identities for common source abbreviations; no local reference files.
- `src/references.js`: extracts cited reading with its topic, layer or roadmap scope.
- `src/landmarks.js`: source-faithful extraction of key definitions, results and constructions.
- `content/`: sanitized source Markdown documents.
- `scripts/build.py`: portable offline builder. `scripts/galaxies.py` regroups roadmaps into the subject galaxies at build time.
- `index.html`: generated entry point for offline use and GitHub Pages.

The GitHub Pages target is [cbirkbeck.github.io/tauceti-explorer](https://cbirkbeck.github.io/tauceti-explorer/).

## Browser validation

The optional browser suite needs Python's `playwright` package and its Chromium browser:

```sh
python3 tests/validate_browser.py
```

It checks navigation, status persistence/import, mathematics rendering, companion links, filters, pins, mobile browsing and the independent offline download. Reports and screenshots are written to a temporary directory. To check the hosted site, pass its URL as the first argument.

## Licence and acknowledgements

This repository uses the [Apache License 2.0](LICENSE), copied from the TauCetiRoadmap source. The roadmap material is derived from Tau Ceti and its contributors; see [NOTICE](NOTICE). Bundled D3 v5.15.0 retains Mike Bostock's copyright and its [BSD-style licence](vendor/D3-LICENSE.txt). KaTeX 0.16.28 is distributed under its [MIT licence](vendor/KaTeX-LICENSE.txt).

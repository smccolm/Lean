# Tao2026 Lean package

This isolated package contains the active node-73 formalization. The production
root currently imports source-faithful arithmetic-anatomy, interval, literal
counting, and asymptotic-language definitions. It is pinned to Lean `v4.30.0`
and Mathlib commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

No theorem from Tao's paper is proved yet. Do not add imports from nodes 71 or
74 until the exact source dependency recorded in `Tao Crosswalk.md` has a
deliberate immutable snapshot under `Dependencies/`.

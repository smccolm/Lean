# Planned Lean extension

This directory intentionally contains no Lean package yet. The toolchain split
between the reusable ANTEDB code (`v4.32.0`) and the completed local
Guth--Maynard foundation (`v4.30.0`) must be resolved by EPZAE-01 first.

Creating a `lakefile.toml` now would either float a dependency, select an
unverified upgrade, or encode two incompatible mathlib graphs. The proposed
module tree is frozen in the goal prompt and may be initialized after the
compatibility spike passes.

## Bootstrap acceptance test

The first committed package must:

1. pin one Lean toolchain and one mathlib revision;
2. import at least one selected ANTEDB foundation module and one local
   Guth--Maynard publication-contract module from source;
3. expose no new mathematical theorem;
4. build with zero warnings;
5. include a real root import, semantic regression module, and axiom audit; and
6. be covered by a runner that clearly distinguishes bootstrap success from
   paper-theorem completion.

See `../Tao-Trudgian-Yang Goal Prompt.md` for the proposed production modules.

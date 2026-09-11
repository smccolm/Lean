# Frozen Gafni-Tao theorem dependency

This directory is the exact local Lean import closure of
`GafniTao.Theorem11` and the native Wooley VMVT bridge used by the Tao 2026
formalization. It is copied from
the adjacent `74 Gafni-Tao, 2026` node by
`Tools/refresh_gafnitao_snapshot.ps1`.

The snapshot contains three source namespaces in their required package
layout:

- `GafniTao`: 965 reachable modules;
- `RiemannZeta`: 291 reachable frozen-foundation modules;
- `PrimeNumberTheoremAnd`: 83 reachable PNT+ modules.

`SOURCE_SHA256SUMS.txt` hashes every copied Lean source.  The upstream
foundation and PNT+ provenance manifests are retained alongside it. This
package must be treated as immutable input: changes belong in the upstream
nodes and are imported here only by regenerating and reviewing the snapshot.

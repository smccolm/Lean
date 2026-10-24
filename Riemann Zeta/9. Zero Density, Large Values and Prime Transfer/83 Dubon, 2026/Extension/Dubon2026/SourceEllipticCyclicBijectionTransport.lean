import Dubon2026.SourceEllipticCyclicKernelBijection

/-! Transport the actual all-level cyclic-root bijection through the original
field embedding and coordinate change. Exact cyclic counts give kernel
surjectivity, and native polynomial splitting gives root surjectivity.
No torsion-lift or root-descent certificate is added. This removes the final
transport requirements of the all-level transcendental cyclic-root theorem. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial SourceFunctionField SourceFunctionField.IntegralJCoordinate
noncomputable section
variable {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
variable [IsAlgClosed F] [IsAlgClosed L]

/-- The actual cyclic-root bijection transports to any algebraically closed coefficient overfield. -/
theorem cyclicQuotientJ_bijOn_map
    (f : F →+* L) (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : F) ≠ 0)
    (h : Set.BijOn (cyclicQuotientJ W N hN) Set.univ
      {y | (relationAtSeed (modularPolynomial N) W.j).IsRoot y}) :
    let hNL : (N : L) ≠ 0 := by simpa only [map_natCast] using (_root_.map_ne_zero f).mpr hN
    Set.BijOn (cyclicQuotientJ (W.map f) N hNL) Set.univ
      {y | (relationAtSeed (modularPolynomial N) (W.map f).j).IsRoot y} := by
  intro hNL
  have hb := cyclicKernelMap_bijective f W N hN
  let P := relationAtSeed (modularPolynomial N) W.j
  have hm : P.Monic := (modularPolynomial_monic N).map _
  have he : relationAtSeed (modularPolynomial N) (W.map f).j = P.map f := by
    rw [map_j, relationAtSeed_map]
  have hroot (x : F) : (relationAtSeed (modularPolynomial N) (W.map f).j).IsRoot (f x) ↔ P.IsRoot x := by
    rw [he, IsRoot.def, eval_map, eval₂_hom, map_eq_zero_iff f f.injective, IsRoot.def]
  refine ⟨?_, ?_, ?_⟩
  · intro H' _
    obtain ⟨H, rfl⟩ := hb.2 H'
    rw [cyclicQuotientJ_map f W N hN H]
    exact (hroot _).mpr (h.mapsTo (Set.mem_univ _))
  · intro H' _ J' _ hv
    obtain ⟨H, rfl⟩ := hb.2 H'
    obtain ⟨J, rfl⟩ := hb.2 J'
    rw [cyclicQuotientJ_map f W N hN H, cyclicQuotientJ_map f W N hN J] at hv
    exact congrArg (primeCyclicKernelMap f W N) (h.injOn (Set.mem_univ _) (Set.mem_univ _) (f.injective hv))
  · intro y hy
    have hym : y ∈ (P.map f).roots := by
      apply (mem_roots (hm.map f).ne_zero).mpr
      rwa [he] at hy
    rw [(IsAlgClosed.splits P).roots_map f, Multiset.mem_map] at hym
    obtain ⟨x, hx, hxy⟩ := hym
    obtain ⟨H, _, hH⟩ := h.surjOn ((mem_roots hm.ne_zero).mp hx)
    refine ⟨primeCyclicKernelMap f W N H, Set.mem_univ _, ?_⟩
    rw [cyclicQuotientJ_map f W N hN H]
    exact (congrArg f hH).trans hxy

/-- The actual cyclic-root bijection transports under the original change of elliptic model. -/
theorem cyclicQuotientJ_bijOn_variableChange
    (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic] (N : ℕ) [NeZero N]
    (hN : (N : F) ≠ 0)
    (h : Set.BijOn (cyclicQuotientJ W N hN) Set.univ
      {y | (relationAtSeed (modularPolynomial N) W.j).IsRoot y}) :
    Set.BijOn (cyclicQuotientJ (C • W) N hN) Set.univ
      {y | (relationAtSeed (modularPolynomial N) (C • W).j).IsRoot y} := by
  have hb := cyclicKernelVariableChange_bijective C W N hN
  rw [variableChange_j]
  refine ⟨?_, ?_, ?_⟩
  · intro H' _
    obtain ⟨H, rfl⟩ := hb.2 H'
    rw [cyclicQuotientJ_variableChange]
    exact h.mapsTo (Set.mem_univ _)
  · intro H' _ J' _ hv
    obtain ⟨H, rfl⟩ := hb.2 H'
    obtain ⟨J, rfl⟩ := hb.2 J'
    rw [cyclicQuotientJ_variableChange, cyclicQuotientJ_variableChange] at hv
    exact congrArg (cyclicKernelVariableChange C W N) (h.injOn (Set.mem_univ _) (Set.mem_univ _) hv)
  · intro y hy
    obtain ⟨H, _, hH⟩ := h.surjOn hy
    refine ⟨cyclicKernelVariableChange C W N H, Set.mem_univ _, ?_⟩
    exact (cyclicQuotientJ_variableChange C W N hN H).trans hH

end
end Dubon2026.SourceEllipticVelu

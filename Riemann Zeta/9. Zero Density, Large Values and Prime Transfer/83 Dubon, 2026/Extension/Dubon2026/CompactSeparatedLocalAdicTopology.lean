import Mathlib.Topology.Algebra.Ring.Compact
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.AdicCompletion.Basic

/-! # The actual topology on a compact separated Noetherian local ring is adic -/

namespace Dubon2026
noncomputable section

open IsLocalRing Filter Topology

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] [IsLocalRing R] [IsNoetherianRing R]
  [IsHausdorff (maximalIdeal R) R]

/-- In the original compact Hausdorff topology, the actual maximal-ideal
powers form the neighborhood basis. Compactness and actual adic separatedness
prove cofinality; the topology is not replaced by a new one. -/
theorem compactSeparatedLocalRing_isAdic : IsAdic (maximalIdeal R) := by
  apply isAdic_iff.mpr
  refine ⟨isOpen_maximalIdeal_pow R, ?_⟩
  intro U hU
  apply exists_subset_nhds_of_compactSpace
    (V := fun n : ℕ => ((maximalIdeal R ^ n : Ideal R) : Set R))
  · intro i j
    exact ⟨max i j, Ideal.pow_le_pow_right (le_max_left i j),
      Ideal.pow_le_pow_right (le_max_right i j)⟩
  · intro n
    exact IsNoetherianRing.isClosed_ideal _
  · intro x hx
    have hx0 : x = 0 := by
      apply IsHausdorff.haus' (I := maximalIdeal R) x
      intro n
      simpa [SModEq.sub_mem, Ideal.smul_eq_mul] using Set.mem_iInter.mp hx n
    simpa [hx0] using hU

variable {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
  [CompactSpace S] [T2Space S] [IsLocalRing S] [IsNoetherianRing S]
  [IsHausdorff (maximalIdeal S) S]

/-- A genuine local ring homomorphism between the original compact separated
Noetherian local rings is continuous in their actual topologies. -/
theorem compactSeparatedLocalRingHom_continuous (f : R →+* S) [IsLocalHom f] :
    Continuous f := by
  apply continuous_of_tendsto_nhds_zero f
  rw [(compactSeparatedLocalRing_isAdic (R := R)).hasBasis_nhds_zero.tendsto_iff
    (compactSeparatedLocalRing_isAdic (R := S)).hasBasis_nhds_zero]
  intro n _
  refine ⟨n, trivial, Ideal.map_le_iff_le_comap.mp ?_⟩
  simpa [Ideal.map_pow] using Ideal.pow_right_mono (map_maximalIdeal_le f) n

end
end Dubon2026

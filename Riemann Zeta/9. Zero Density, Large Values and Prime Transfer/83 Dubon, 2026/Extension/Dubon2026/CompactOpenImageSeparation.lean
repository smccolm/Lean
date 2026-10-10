import Mathlib.Topology.Separation.Profinite

/-! # Genuine clopen separation of original compact open images -/

namespace Dubon2026

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [T2Space Y]

/-- A genuine continuous open quotient of an original compact totally disconnected space remains totally separated. -/
theorem compactOpenSurjection_totallySeparated (f : X → Y)
    (hf : Continuous f) (hopen : IsOpenMap f) (hsurj : Function.Surjective f) :
    TotallySeparatedSpace Y := by
  apply totallySeparatedSpace_iff_exists_isClopen.mpr
  intro y z hyz
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨V, hV, hxV, hsub⟩ := compact_exists_isClopen_in_isOpen
    (isOpen_compl_singleton.preimage hf) hyz
  refine ⟨f '' V, ⟨hf.isClosedMap V hV.isClosed, hopen V hV.isOpen⟩,
    ⟨x, hxV, rfl⟩, ?_⟩
  rintro ⟨t, ht, heq⟩
  exact hsub ht heq

end Dubon2026

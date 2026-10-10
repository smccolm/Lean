import Dubon2026.CompleteLocalAdicCompactness

/-! # Compactness and separatedness in the actual proved original local coefficient topology -/

namespace Dubon2026
noncomputable section

variable {R : Type*} [CommRing R] [IsLocalRing R]
  [t : TopologicalSpace R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- Actual maximal-adic completeness makes the original coefficient topology Hausdorff after its genuine adic equality is explicitly transported. -/
theorem originalAdicCompleteLocal_t2Space
    (hR : IsAdic (IsLocalRing.maximalIdeal R)) : T2Space R := by
  change t = (IsLocalRing.maximalIdeal R).adicTopology at hR
  subst t
  letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
  exact completeLocalAdic_t2Space rfl

/-- The actual original topology of complete Noetherian local coefficients with finite true residue field is compact; no alternative coefficient topology is introduced. -/
theorem originalAdicCompleteLocal_compactSpace [IsNoetherianRing R]
    [Finite (IsLocalRing.ResidueField R)]
    (hR : IsAdic (IsLocalRing.maximalIdeal R)) : CompactSpace R := by
  change t = (IsLocalRing.maximalIdeal R).adicTopology at hR
  subst t
  letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
  exact completeLocalAdic_compactSpace rfl

end
end Dubon2026

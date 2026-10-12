import Dubon2026.CosetTraceCochains

/-! # The original coset trace preserves actual coboundaries -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (S : Subgroup G)

/-- The actual degree-one differential commutes term by term with
coset trace, with the last original coset translated by h. -/
theorem cosetTraceTwoTerm_differential (f : S → A) (g h : G) (q : G ⧸ S) :
    cosetTraceTwoTerm A S (groupCohomology.d₁₂ (restrictedCoefficientRep A S.subtype) f) g h q =
      A.ρ g (cosetTraceOneTerm A S f h q) - cosetTraceOneTerm A S f (g * h) q +
        cosetTraceOneTerm A S f g (h • q) := by
  change A.ρ (g • h • q).out
      (A.ρ (cosetTransition S g (h • q)) (f (cosetTransition S h q)) -
        f (cosetTransition S g (h • q) * cosetTransition S h q) +
        f (cosetTransition S g (h • q))) = _
  rw [map_add, map_sub, cosetTransition_action, ← cosetTransition_mul]
  simp only [cosetTraceOneTerm, mul_smul]

/-- The genuine finite coset trace of a coboundary is the actual
coboundary of the same finite trace of its original one-cochain. -/
theorem cosetTraceTwo_differential [Fintype (G ⧸ S)] (f : S → A) :
    cosetTraceTwo A S (groupCohomology.d₁₂ (restrictedCoefficientRep A S.subtype) f) =
      groupCohomology.d₁₂ A (cosetTraceOne A S f) := by
  funext z
  obtain ⟨g, h⟩ := z
  change (∑ q, cosetTraceTwoTerm A S
      (groupCohomology.d₁₂ (restrictedCoefficientRep A S.subtype) f) g h q) =
    A.ρ g (∑ q, cosetTraceOneTerm A S f h q) -
      (∑ q, cosetTraceOneTerm A S f (g * h) q) + (∑ q, cosetTraceOneTerm A S f g q)
  calc
    _ = ∑ q, (A.ρ g (cosetTraceOneTerm A S f h q) -
        cosetTraceOneTerm A S f (g * h) q + cosetTraceOneTerm A S f g (h • q)) :=
      Finset.sum_congr rfl (fun q _ => cosetTraceTwoTerm_differential A S f g h q)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, map_sum]
      congr 1
      exact Equiv.sum_comp (MulAction.toPerm h) (fun q : G ⧸ S => cosetTraceOneTerm A S f g q)

end
end Dubon2026

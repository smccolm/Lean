import Dubon2026.CosetCupProjectionTerms

/-! # The explicit original homotopy for the cup projection formula -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A B C : Rep R G)
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))
  (S : Subgroup G) [Fintype (G ⧸ S)]

/-- The original projection-formula homotopy is the literal finite sum of
the actual coset correction terms. -/
def cosetCupProjectionCorrection (c : groupCohomology.cocycles₁ A)
    (v : groupCohomology.cocycles₁ (restrictedCoefficientRep B S.subtype)) : G → C :=
  fun g => ∑ q : G ⧸ S, cosetCupProjectionCorrectionTerm A B C β S c v g q

include hβ in
/-- The actual traced restricted cup equals cup with the actual traced
one-cocycle plus the original differential of the explicit coset correction. -/
theorem cosetCupProjection_homotopy
    (c : groupCohomology.cocycles₁ A)
    (v : groupCohomology.cocycles₁ (restrictedCoefficientRep B S.subtype)) :
    cosetTraceTwo C S (fun z => β (c z.1) (B.ρ z.1 (v z.2))) =
      (fun z : G × G => β (c z.1) (B.ρ z.1 (cosetTraceOne B S v z.2))) +
        groupCohomology.d₁₂ C (cosetCupProjectionCorrection A B C β S c v) := by
  funext z
  obtain ⟨g, h⟩ := z
  change (∑ q : G ⧸ S,
    cosetTraceTwoTerm C S (fun z => β (c z.1) (B.ρ z.1 (v z.2))) g h q) =
    β (c g) (B.ρ g (∑ q : G ⧸ S, cosetTraceOneTerm B S v h q)) +
      (C.ρ g (∑ q : G ⧸ S, cosetCupProjectionCorrectionTerm A B C β S c v h q) -
        (∑ q : G ⧸ S, cosetCupProjectionCorrectionTerm A B C β S c v (g * h) q) +
        ∑ q : G ⧸ S, cosetCupProjectionCorrectionTerm A B C β S c v g q)
  simp_rw [cosetCupProjection_term A B C β hβ S c v]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← map_sum]
  have hr : (∑ q : G ⧸ S, cosetCupProjectionCorrectionTerm A B C β S c v g (h • q)) =
      ∑ q : G ⧸ S, cosetCupProjectionCorrectionTerm A B C β S c v g q :=
    Equiv.sum_comp (MulAction.toPerm h)
      (fun q : G ⧸ S => cosetCupProjectionCorrectionTerm A B C β S c v g q)
  rw [hr]
  abel

end
end Dubon2026

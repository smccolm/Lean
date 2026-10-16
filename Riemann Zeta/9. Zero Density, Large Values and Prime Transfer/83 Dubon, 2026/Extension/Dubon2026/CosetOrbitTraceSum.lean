import Dubon2026.CosetOrbitTraceComparison

/-! # The exact orbit sum and coboundary for restricted transfer

This is the algebraic cochain identity underlying the continuous Mackey
formula used in DUB-17's arithmetic invariant comparison.
-/

namespace Dubon2026
noncomputable section
open scoped BigOperators

variable {R D G : Type} [CommRing R] [Group D] [Group G]
  (A : Rep R G) (φ : D →* G) (S : Subgroup G)

/-- The actual stabilizer quotient is finite because its orbit embeds in
the original finite coset space. -/
instance cosetOrbitQuotientFinite [Finite (G ⧸ S)] (q : G ⧸ S) :
    Finite (D ⧸ cosetOrbitStabilizer φ S q) :=
  Finite.of_injective (cosetOrbitMap φ S q) (cosetOrbitMap_injective φ S q)

variable [Fintype (G ⧸ S)] [Fintype (cosetOrbitIndex φ S)]
  [∀ ω : cosetOrbitIndex φ S, Fintype (D ⧸ cosetOrbitStabilizer φ S ω.out)]

/-- The literal changed global trace is the sum of the literal original
stabilizer traces over all actual smaller-group orbits. -/
theorem cosetOrbit_changedTrace_sum
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype)) (d e : D) :
    (∑ q : G ⧸ S, changedCosetTraceTwoTerm A S (cosetOrbitRepresentativeChange φ S)
      c (φ d) (φ e) q) =
      ∑ ω : cosetOrbitIndex φ S,
        cosetTraceTwo (restrictedCoefficientRep A φ) (cosetOrbitStabilizer φ S ω.out)
          (cosetOrbitCocycle A φ S ω.out c) (d, e) := by
  rw [← Equiv.sum_comp (cosetOrbitDecomposition φ S).symm]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro ω _
  change (∑ x, changedCosetTraceTwoTerm A S (cosetOrbitRepresentativeChange φ S)
    c (φ d) (φ e) ((cosetOrbitDecomposition φ S).symm ⟨ω, x⟩)) = _
  simp_rw [cosetOrbit_changedTraceTerm]
  rfl

/-- Restricting the original transfer differs from the sum of original
stabilizer transfers by the differential of the explicit restricted
representative-comparison cochain. -/
theorem cosetOrbit_trace_restriction_coboundary
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype)) :
    (fun z : D × D => ∑ ω : cosetOrbitIndex φ S,
        cosetTraceTwo (restrictedCoefficientRep A φ) (cosetOrbitStabilizer φ S ω.out)
          (cosetOrbitCocycle A φ S ω.out c) z) -
      (fun z : D × D => cosetTraceTwo A S c (φ z.1, φ z.2)) =
      groupCohomology.d₁₂ (restrictedCoefficientRep A φ)
        (fun d => cosetRepresentativeHomotopy A S (cosetOrbitRepresentativeChange φ S) c (φ d)) := by
  funext z
  obtain ⟨d, e⟩ := z
  have ht := congrFun (changedCosetTraceTwo_sub A S (cosetOrbitRepresentativeChange φ S) c)
    (φ d, φ e)
  change (∑ q : G ⧸ S, changedCosetTraceTwoTerm A S (cosetOrbitRepresentativeChange φ S)
      c (φ d) (φ e) q) - cosetTraceTwo A S c (φ d, φ e) =
    A.ρ (φ d) (cosetRepresentativeHomotopy A S (cosetOrbitRepresentativeChange φ S) c (φ e)) -
      cosetRepresentativeHomotopy A S (cosetOrbitRepresentativeChange φ S) c (φ d * φ e) +
      cosetRepresentativeHomotopy A S (cosetOrbitRepresentativeChange φ S) c (φ d) at ht
  rw [cosetOrbit_changedTrace_sum] at ht
  change _ =
    A.ρ (φ d) (cosetRepresentativeHomotopy A S (cosetOrbitRepresentativeChange φ S) c (φ e)) -
      cosetRepresentativeHomotopy A S (cosetOrbitRepresentativeChange φ S) c (φ (d * e)) +
      cosetRepresentativeHomotopy A S (cosetOrbitRepresentativeChange φ S) c (φ d)
  rw [map_mul]
  exact ht

end
end Dubon2026

import Dubon2026.ClosedCoefficientSubalgebraLocality

/-! # Actual closed coefficient locality in the original proved adic topology -/

namespace Dubon2026
noncomputable section

variable {O R : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]
  [t : TopologicalSpace R] [IsTopologicalRing R]

/-- A closed coefficient subalgebra reflects actual original units in any original topology proved maximal-adic. -/
theorem originalAdicCoefficientSubalgebra_isUnit
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) (hS : IsClosed (S : Set R)) (x : S)
    (hx : IsUnit (x : R)) : IsUnit x := by
  change t = (IsLocalRing.maximalIdeal R).adicTopology at hR
  subst t
  letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
  exact closedCoefficientSubalgebra_isUnit rfl eR S hS x hx

/-- The original closed coefficient inclusion is a local homomorphism in its genuine original adic topology. -/
theorem originalAdicCoefficientSubalgebra_isLocalHom
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) (hS : IsClosed (S : Set R)) : IsLocalHom S.val.toRingHom := by
  exact ⟨fun x hx => originalAdicCoefficientSubalgebra_isUnit hR eR S hS x hx⟩

/-- The same genuine original closed coefficient subalgebra is local. -/
theorem originalAdicCoefficientSubalgebra_isLocalRing
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (S : Subalgebra O R) (hS : IsClosed (S : Set R)) : IsLocalRing S := by
  letI := originalAdicCoefficientSubalgebra_isLocalHom hR eR S hS
  exact S.val.toRingHom.domain_isLocalRing

end
end Dubon2026

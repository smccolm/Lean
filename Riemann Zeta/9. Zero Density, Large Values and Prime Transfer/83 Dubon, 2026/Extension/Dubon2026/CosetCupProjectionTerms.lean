import Dubon2026.CosetTraceOneRestriction
import Dubon2026.EquivariantCocycleCup

/-! # The original cochain correction for the cup projection formula

This compares the actual coset trace of a restricted cup with cup against the
actual degree-one trace, for cyclotomic descent of local nondegeneracy.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A B C : Rep R G)
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))
  (S : Subgroup G)

/-- The explicit correction at the original coset representative, with the
same original cocycle and coefficient pairing. -/
def cosetCupProjectionCorrectionTerm (c : groupCohomology.cocycles₁ A)
    (v : groupCohomology.cocycles₁ (restrictedCoefficientRep B S.subtype))
    (g : G) (q : G ⧸ S) : C :=
  β (c (g • q).out) (cosetTraceOneTerm B S v g q)

include hβ in
/-- The original traced cup differs from cup with the traced cocycle by
the differential of the explicit correction, term by actual coset term. -/
theorem cosetCupProjection_term
    (c : groupCohomology.cocycles₁ A)
    (v : groupCohomology.cocycles₁ (restrictedCoefficientRep B S.subtype))
    (g h : G) (q : G ⧸ S) :
    cosetTraceTwoTerm C S (fun z => β (c z.1) (B.ρ z.1 (v z.2))) g h q =
      β (c g) (B.ρ g (cosetTraceOneTerm B S v h q)) +
        C.ρ g (cosetCupProjectionCorrectionTerm A B C β S c v h q) -
        cosetCupProjectionCorrectionTerm A B C β S c v (g * h) q +
        cosetCupProjectionCorrectionTerm A B C β S c v g (h • q) := by
  have hv : cosetTraceOneTerm B S v (g * h) q =
      B.ρ g (cosetTraceOneTerm B S v h q) + cosetTraceOneTerm B S v g (h • q) := by
    have hc : v (cosetTransition S g (h • q) * cosetTransition S h q) =
        B.ρ (cosetTransition S g (h • q)) (v (cosetTransition S h q)) +
          v (cosetTransition S g (h • q)) :=
      (groupCohomology.mem_cocycles₁_iff _).mp v.property
        (cosetTransition S g (h • q)) (cosetTransition S h q)
    change B.ρ ((g * h) • q).out (v (cosetTransition S (g * h) q)) = _
    rw [cosetTransition_mul, hc, mul_smul]
    rw [map_add, cosetTransition_action]
    rfl
  have hc := cosetTraceOneTerm_restriction A S c g (h • q)
  change C.ρ (g • h • q).out
    (β (c (cosetTransition S g (h • q)))
      (B.ρ (cosetTransition S g (h • q)) (v (cosetTransition S h q)))) = _
  rw [← hβ, cosetTransition_action]
  change β (cosetTraceOneTerm A S (fun s => c s) g (h • q))
    (B.ρ g (cosetTraceOneTerm B S v h q)) = _
  rw [hc]
  simp only [cosetCupProjectionCorrectionTerm, hv, mul_smul, ← hβ,
    map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

end
end Dubon2026

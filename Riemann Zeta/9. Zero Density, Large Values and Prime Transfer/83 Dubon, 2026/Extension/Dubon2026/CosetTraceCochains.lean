import Dubon2026.CosetTransitionCoordinates
import Dubon2026.ContinuousRepresentationRestriction

/-! # Literal finite coset sums on the original inhomogeneous cochains -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (S : Subgroup G)

/-- The original coefficient action respects the exact coset transition. -/
theorem cosetTransition_action (g : G) (q : G ⧸ S) (a : A) :
    A.ρ (g • q).out (A.ρ (cosetTransition S g q) a) = A.ρ g (A.ρ q.out a) := by
  rw [← Module.End.mul_apply, ← map_mul, cosetTransition_factor, map_mul]
  rfl

/-- One actual degree-one trace summand, with its genuine subgroup coordinate. -/
def cosetTraceOneTerm (f : S → A) (g : G) (q : G ⧸ S) : A :=
  A.ρ (g • q).out (f (cosetTransition S g q))

/-- One actual degree-two trace summand, with both genuine subgroup coordinates. -/
def cosetTraceTwoTerm (c : S × S → A) (g h : G) (q : G ⧸ S) : A :=
  A.ρ (g • h • q).out (c (cosetTransition S g (h • q), cosetTransition S h q))

/-- The actual subgroup cocycle identity holds term by term in the original
coset trace after moving the last coset by k. -/
theorem cosetTraceTwoTerm_cocycle
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype))
    (g h k : G) (q : G ⧸ S) :
    cosetTraceTwoTerm A S c (g * h) k q + cosetTraceTwoTerm A S c g h (k • q) =
      A.ρ g (cosetTraceTwoTerm A S c h k q) + cosetTraceTwoTerm A S c g (h * k) q := by
  have hc := (groupCohomology.mem_cocycles₂_iff _).mp c.property
    (cosetTransition S g (h • k • q)) (cosetTransition S h (k • q)) (cosetTransition S k q)
  have ht := congrArg (A.ρ (g • h • k • q).out) hc
  change A.ρ (g • h • k • q).out
      (c (cosetTransition S g (h • k • q) * cosetTransition S h (k • q), cosetTransition S k q) +
        c (cosetTransition S g (h • k • q), cosetTransition S h (k • q))) =
    A.ρ (g • h • k • q).out
      (A.ρ (cosetTransition S g (h • k • q))
        (c (cosetTransition S h (k • q), cosetTransition S k q)) +
        c (cosetTransition S g (h • k • q), cosetTransition S h (k • q) * cosetTransition S k q)) at ht
  rw [map_add, map_add, cosetTransition_action, ← cosetTransition_mul] at ht
  simp only [cosetTraceTwoTerm, mul_smul, cosetTransition_mul]
  simpa only [cosetTransition_mul, mul_smul] using ht

variable [Fintype (G ⧸ S)]

/-- The actual degree-one coset trace is the finite sum over the original quotient. -/
def cosetTraceOne : (S → A) →ₗ[R] (G → A) where
  toFun f g := ∑ q : G ⧸ S, cosetTraceOneTerm A S f g q
  map_add' f j := by
    ext g
    simp only [cosetTraceOneTerm, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r f := by
    ext g
    simp only [cosetTraceOneTerm, Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

/-- The actual degree-two coset trace uses the original coefficient action and coordinates. -/
def cosetTraceTwo : (S × S → A) →ₗ[R] (G × G → A) where
  toFun c z := ∑ q : G ⧸ S, cosetTraceTwoTerm A S c z.1 z.2 q
  map_add' c d := by
    ext z
    simp only [cosetTraceTwoTerm, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r c := by
    ext z
    simp only [cosetTraceTwoTerm, Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

/-- The genuine finite coset trace takes original subgroup two-cocycles to
original group two-cocycles. The proof reindexes the original cosets. -/
theorem cosetTraceTwo_mem_cocycles
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype)) :
    cosetTraceTwo A S c ∈ groupCohomology.cocycles₂ A := by
  apply (groupCohomology.mem_cocycles₂_iff _).mpr
  intro g h k
  have hreindex := Equiv.sum_comp (MulAction.toPerm k)
    (fun q : G ⧸ S => cosetTraceTwoTerm A S c g h q)
  change (∑ q, cosetTraceTwoTerm A S c (g * h) k q) +
      (∑ q, cosetTraceTwoTerm A S c g h q) =
    A.ρ g (∑ q, cosetTraceTwoTerm A S c h k q) +
      (∑ q, cosetTraceTwoTerm A S c g (h * k) q)
  rw [← hreindex, map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun q _ => cosetTraceTwoTerm_cocycle A S c g h k q)

end
end Dubon2026

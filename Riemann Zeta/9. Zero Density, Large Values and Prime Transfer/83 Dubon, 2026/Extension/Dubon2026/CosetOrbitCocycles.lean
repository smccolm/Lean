import Dubon2026.CosetOrbitCoordinates
import Dubon2026.CosetTraceCochains

/-! # Actual cocycles on the stabilizers of restricted coset orbits

The conjugated coefficient map and the original trace summand are proved
to agree. These are the orbit terms needed in DUB-17's local/global
transfer comparison, before arithmetic completion identifications.
-/

namespace Dubon2026
noncomputable section

variable {R D G : Type} [CommRing R] [Group D] [Group G]
  (A : Rep R G) (φ : D →* G) (S : Subgroup G)

/-- The actual conjugation map intertwines the original coefficient
actions by the literal orbit representative. -/
theorem cosetOrbitSubgroupMap_action (q : G ⧸ S)
    (d : cosetOrbitStabilizer φ S q) (b : A) :
    A.ρ q.out (A.ρ (cosetOrbitSubgroupMap φ S q d) b) =
      A.ρ (φ d) (A.ρ q.out b) := by
  rw [← Module.End.mul_apply, ← map_mul, cosetOrbitSubgroupMap_factor, map_mul]
  rfl

/-- The original subgroup cocycle restricts and conjugates to the actual
orbit stabilizer, with the original smaller-group coefficient action. -/
def cosetOrbitCocycle (q : G ⧸ S)
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype)) :
    groupCohomology.cocycles₂ (restrictedCoefficientRep (restrictedCoefficientRep A φ)
      (cosetOrbitStabilizer φ S q).subtype) :=
  ⟨fun z => A.ρ q.out (c (cosetOrbitSubgroupMap φ S q z.1, cosetOrbitSubgroupMap φ S q z.2)), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro d e f
    have hc := congrArg (A.ρ q.out)
      ((groupCohomology.mem_cocycles₂_iff _).mp c.property
        (cosetOrbitSubgroupMap φ S q d) (cosetOrbitSubgroupMap φ S q e)
        (cosetOrbitSubgroupMap φ S q f))
    change A.ρ q.out
        (c (cosetOrbitSubgroupMap φ S q d * cosetOrbitSubgroupMap φ S q e,
            cosetOrbitSubgroupMap φ S q f) +
          c (cosetOrbitSubgroupMap φ S q d, cosetOrbitSubgroupMap φ S q e)) =
      A.ρ q.out
        (A.ρ (cosetOrbitSubgroupMap φ S q d)
          (c (cosetOrbitSubgroupMap φ S q e, cosetOrbitSubgroupMap φ S q f)) +
          c (cosetOrbitSubgroupMap φ S q d,
            cosetOrbitSubgroupMap φ S q e * cosetOrbitSubgroupMap φ S q f)) at hc
    rw [map_add, map_add, cosetOrbitSubgroupMap_action] at hc
    simpa only [map_mul, Subgroup.coe_mul] using hc⟩

/-- The original stabilizer trace term is exactly the literal global
coefficient action at the compatible orbit representative. -/
theorem cosetOrbitCocycle_traceTerm (q : G ⧸ S)
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype))
    (d e : D) (x : D ⧸ cosetOrbitStabilizer φ S q) :
    cosetTraceTwoTerm (restrictedCoefficientRep A φ) (cosetOrbitStabilizer φ S q)
        (cosetOrbitCocycle A φ S q c) d e x =
      A.ρ (cosetOrbitRepresentative φ S q (d • e • x))
        (c (cosetOrbitSubgroupMap φ S q (cosetTransition (cosetOrbitStabilizer φ S q) d (e • x)),
          cosetOrbitSubgroupMap φ S q (cosetTransition (cosetOrbitStabilizer φ S q) e x))) := by
  change A.ρ (φ (d • e • x).out) (A.ρ q.out _) = A.ρ (φ (d • e • x).out * q.out) _
  rw [← Module.End.mul_apply, ← map_mul]

end
end Dubon2026

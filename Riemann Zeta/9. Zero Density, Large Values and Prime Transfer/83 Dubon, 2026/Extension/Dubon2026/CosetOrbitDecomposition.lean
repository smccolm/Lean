import Dubon2026.CosetOrbitCoordinates

/-! # The actual orbit decomposition of the restricted global cosets

The pinned orbit-stabilizer equivalence supplies the exact reindexing
needed by the local/global cochain transfer comparison for DUB-17.
-/

namespace Dubon2026
noncomputable section

variable {D G : Type} [Group D] [Group G] (φ : D →* G) (S : Subgroup G)

/-- The actual orbits of the original coset space under the restricted action. -/
abbrev cosetOrbitIndex :=
  letI := cosetOrbitRestrictedAction φ S
  Quotient (MulAction.orbitRel D (G ⧸ S))

/-- The original coset space is the disjoint union of its genuine
stabilizer quotient spaces, using the pinned orbit-stabilizer equivalence. -/
def cosetOrbitDecomposition : (G ⧸ S) ≃
    Σ ω : cosetOrbitIndex φ S, D ⧸ cosetOrbitStabilizer φ S ω.out :=
  letI := cosetOrbitRestrictedAction φ S
  MulAction.selfEquivSigmaOrbitsQuotientStabilizer D (G ⧸ S)

/-- The inverse orbit decomposition has the original concrete orbit map. -/
theorem cosetOrbitDecomposition_symm (ω : cosetOrbitIndex φ S)
    (x : D ⧸ cosetOrbitStabilizer φ S ω.out) :
    (cosetOrbitDecomposition φ S).symm ⟨ω, x⟩ = cosetOrbitMap φ S ω.out x := rfl

/-- Restriction acts within the same original orbit and by the actual
left coset action in its stabilizer quotient. -/
theorem cosetOrbitDecomposition_smul (d : D) (q : G ⧸ S) :
    cosetOrbitDecomposition φ S (φ d • q) =
      ⟨(cosetOrbitDecomposition φ S q).1, d • (cosetOrbitDecomposition φ S q).2⟩ := by
  apply (cosetOrbitDecomposition φ S).symm.injective
  rw [Equiv.symm_apply_apply, cosetOrbitDecomposition_symm, cosetOrbitMap_smul]
  congr 1
  exact ((cosetOrbitDecomposition φ S).symm_apply_apply q).symm

/-- A global representative selected compatibly with every smaller-group orbit. -/
def cosetOrbitGlobalRepresentative (q : G ⧸ S) : G :=
  cosetOrbitRepresentative φ S (cosetOrbitDecomposition φ S q).1.out
    (cosetOrbitDecomposition φ S q).2

/-- The compatible global representative represents the original coset. -/
theorem cosetOrbitGlobalRepresentative_mk (q : G ⧸ S) :
    (QuotientGroup.mk (cosetOrbitGlobalRepresentative φ S q) : G ⧸ S) = q := by
  unfold cosetOrbitGlobalRepresentative
  rw [cosetOrbitRepresentative_mk, ← cosetOrbitDecomposition_symm]
  exact (cosetOrbitDecomposition φ S).symm_apply_apply q

/-- On a specified original orbit, the compatible global representative
is precisely the product of the two original representatives. -/
theorem cosetOrbitGlobalRepresentative_apply (ω : cosetOrbitIndex φ S)
    (x : D ⧸ cosetOrbitStabilizer φ S ω.out) :
    cosetOrbitGlobalRepresentative φ S ((cosetOrbitDecomposition φ S).symm ⟨ω, x⟩) =
      cosetOrbitRepresentative φ S ω.out x := by
  unfold cosetOrbitGlobalRepresentative
  rw [Equiv.apply_symm_apply]

end
end Dubon2026

import Dubon2026.CosetOrbitDecomposition
import Dubon2026.CosetOrbitCocycles
import Dubon2026.CosetTraceRepresentativeChange

/-! # Exact orbit comparison of the original finite trace summands

The global representative change is constructed from the actual orbit
decomposition. Its transitions are the original stabilizer transitions,
which supplies the cochain edge in DUB-17's local/global transfer formula.
-/

namespace Dubon2026
noncomputable section

variable {D G : Type} [Group D] [Group G] (φ : D →* G) (S : Subgroup G)

/-- The orbit-compatible representatives differ from the original ones
by these explicitly constructed elements of the original subgroup. -/
def cosetOrbitRepresentativeChange (q : G ⧸ S) : S :=
  ⟨q.out⁻¹ * cosetOrbitGlobalRepresentative φ S q, by
    apply QuotientGroup.leftRel_apply.mp
    apply Quotient.exact'
    exact (Quotient.out_eq' q).trans (cosetOrbitGlobalRepresentative_mk φ S q).symm⟩

/-- The constructed change recovers the exact compatible representative. -/
theorem cosetOrbitRepresentativeChange_factor (q : G ⧸ S) :
    q.out * (cosetOrbitRepresentativeChange φ S q : G) = cosetOrbitGlobalRepresentative φ S q := by
  change q.out * (q.out⁻¹ * cosetOrbitGlobalRepresentative φ S q) = _
  group

/-- The changed global transition factors the original group product
using the exact orbit-compatible representatives. -/
theorem cosetOrbitChangedTransition_factor (g : G) (q : G ⧸ S) :
    cosetOrbitGlobalRepresentative φ S (g • q) *
        (changedCosetTransition S (cosetOrbitRepresentativeChange φ S) g q : G) =
      g * cosetOrbitGlobalRepresentative φ S q := by
  rw [← cosetOrbitRepresentativeChange_factor φ S (g • q),
    ← cosetOrbitRepresentativeChange_factor φ S q]
  have ht := cosetTransition_factor S g q
  change ((g • q).out * (cosetOrbitRepresentativeChange φ S (g • q) : G)) *
      ((cosetOrbitRepresentativeChange φ S (g • q) : G)⁻¹ *
        (cosetTransition S g q : G) * (cosetOrbitRepresentativeChange φ S q : G)) = _
  calc
    _ = ((g • q).out * (cosetTransition S g q : G)) * (cosetOrbitRepresentativeChange φ S q : G) := by group
    _ = _ := by rw [ht, mul_assoc]

/-- The actual inverse orbit decomposition intertwines the restricted action. -/
theorem cosetOrbitDecomposition_symm_smul (ω : cosetOrbitIndex φ S)
    (x : D ⧸ cosetOrbitStabilizer φ S ω.out) (d : D) :
    (cosetOrbitDecomposition φ S).symm ⟨ω, d • x⟩ =
      φ d • (cosetOrbitDecomposition φ S).symm ⟨ω, x⟩ := by
  rw [cosetOrbitDecomposition_symm, cosetOrbitDecomposition_symm, cosetOrbitMap_smul]

/-- The compatible global transition is the image of the original
stabilizer transition under the original conjugation map. -/
theorem cosetOrbitChangedTransition (ω : cosetOrbitIndex φ S)
    (x : D ⧸ cosetOrbitStabilizer φ S ω.out) (d : D) :
    changedCosetTransition S (cosetOrbitRepresentativeChange φ S) (φ d)
        ((cosetOrbitDecomposition φ S).symm ⟨ω, x⟩) =
      cosetOrbitSubgroupMap φ S ω.out (cosetTransition (cosetOrbitStabilizer φ S ω.out) d x) := by
  apply Subtype.ext
  apply mul_left_cancel (a := cosetOrbitRepresentative φ S ω.out (d • x))
  have ht := cosetOrbitChangedTransition_factor φ S (φ d)
    ((cosetOrbitDecomposition φ S).symm ⟨ω, x⟩)
  rw [← cosetOrbitDecomposition_symm_smul, cosetOrbitGlobalRepresentative_apply,
    cosetOrbitGlobalRepresentative_apply] at ht
  exact ht.trans (cosetOrbitRepresentative_factor φ S ω.out d x).symm

variable {R : Type} [CommRing R] (A : Rep R G)

/-- Each actual global trace summand, after the proved representative
change, is exactly its original stabilizer corestriction summand. -/
theorem cosetOrbit_changedTraceTerm (ω : cosetOrbitIndex φ S)
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype))
    (d e : D) (x : D ⧸ cosetOrbitStabilizer φ S ω.out) :
    changedCosetTraceTwoTerm A S (cosetOrbitRepresentativeChange φ S) c (φ d) (φ e)
        ((cosetOrbitDecomposition φ S).symm ⟨ω, x⟩) =
      cosetTraceTwoTerm (restrictedCoefficientRep A φ) (cosetOrbitStabilizer φ S ω.out)
        (cosetOrbitCocycle A φ S ω.out c) d e x := by
  unfold changedCosetTraceTwoTerm
  rw [← Module.End.mul_apply, ← map_mul, cosetOrbitRepresentativeChange_factor]
  simp only [← cosetOrbitDecomposition_symm_smul, cosetOrbitGlobalRepresentative_apply,
    cosetOrbitChangedTransition]
  exact (cosetOrbitCocycle_traceTerm A φ S ω.out c d e x).symm

end
end Dubon2026

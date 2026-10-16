import Dubon2026.CoinducedEvaluationTwoHomotopy
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Original H2 is unchanged by the actual inner-conjugation map

Reuse the already proved explicit conjugation coboundary. This is the
cohomological comparison needed when DUB-17's actual prime representatives
differ by a global automorphism; no normalized-cocycle premise is added.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)

/-- The actual coefficient action intertwines restriction by inverse inner conjugation. -/
def originalInnerConjugationRepHom (r : G) :
    Rep.res (MulAut.conj r⁻¹).toMonoidHom A ⟶ A :=
  Rep.ofHom ⟨A.ρ r, by
    intro g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    change A.ρ r * A.ρ (r⁻¹ * g * r) = A.ρ g * A.ρ r
    rw [← map_mul, ← map_mul]
    congr 1
    group⟩

/-- The actual group-conjugation and coefficient-action map fixes every original H2 class, by the existing explicit coboundary. -/
theorem originalH2_innerConjugation (r : G) (x : groupCohomology A 2) :
    groupCohomology.map (MulAut.conj r⁻¹).toMonoidHom
      (originalInnerConjugationRepHom A r) 2 x = x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    rw [groupCohomology.H2π_comp_map_apply]
    apply (groupCohomology.H2π_eq_iff _ c).mpr
    refine ⟨coefficientConjugationTwoHomotopy A c r, ?_⟩
    funext z
    change groupCohomology.d₁₂ A (coefficientConjugationTwoHomotopy A c r) z =
      A.ρ r (c (r⁻¹ * z.1 * (r⁻¹)⁻¹, r⁻¹ * z.2 * (r⁻¹)⁻¹)) - c z
    simpa only [inv_inv] using coefficientConjugationTwoHomotopy_differential A c r z.1 z.2

end
end Dubon2026

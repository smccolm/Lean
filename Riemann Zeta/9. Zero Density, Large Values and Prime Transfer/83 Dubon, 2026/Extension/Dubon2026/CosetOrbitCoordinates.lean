import Dubon2026.CosetTransitionCoordinates
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Original stabilizers and representatives in a restricted coset action

These are the orbit coordinates for the local restriction of the actual
global transfer, needed by the DUB-17 global/local invariant comparison.
-/

namespace Dubon2026
noncomputable section

variable {D G : Type} [Group D] [Group G] (φ : D →* G) (S : Subgroup G)

/-- The original smaller group acts on the original cosets through its
given arithmetic restriction homomorphism. -/
abbrev cosetOrbitRestrictedAction : MulAction D (G ⧸ S) :=
  MulAction.compHom (G ⧸ S) φ

/-- The actual stabilizer of an original coset under the restricted action. -/
def cosetOrbitStabilizer (q : G ⧸ S) : Subgroup D :=
  letI := cosetOrbitRestrictedAction φ S
  MulAction.stabilizer D q

/-- Stabilizing the coset is exactly the condition that the conjugated
original group element lies in the original subgroup. -/
theorem cosetOrbitStabilizer_mem (q : G ⧸ S) (d : D) :
    d ∈ cosetOrbitStabilizer φ S q ↔ q.out⁻¹ * (φ d * q.out) ∈ S := by
  letI := cosetOrbitRestrictedAction φ S
  change φ d • q = q ↔ _
  rw [← QuotientGroup.leftRel_apply, ← Quotient.eq'']
  rw [Quotient.out_eq']
  have he : (Quotient.mk'' (φ d * q.out) : G ⧸ S) = φ d • q :=
    MulAction.Quotient.mk_smul_out S (φ d) q
  rw [he]
  exact eq_comm

/-- The stabilizer maps into the original subgroup by literal conjugation
with the chosen representative, preserving its actual group elements. -/
def cosetOrbitSubgroupMap (q : G ⧸ S) : cosetOrbitStabilizer φ S q →* S where
  toFun d := ⟨q.out⁻¹ * (φ d * q.out), (cosetOrbitStabilizer_mem φ S q d).mp d.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' d e := by
    apply Subtype.ext
    change q.out⁻¹ * (φ (d * e) * q.out) =
      (q.out⁻¹ * (φ d * q.out)) * (q.out⁻¹ * (φ e * q.out))
    rw [map_mul]
    group

/-- The original conjugation map satisfies its exact factorization in G. -/
theorem cosetOrbitSubgroupMap_factor (q : G ⧸ S) (d : cosetOrbitStabilizer φ S q) :
    q.out * (cosetOrbitSubgroupMap φ S q d : G) = φ d * q.out := by
  change q.out * (q.out⁻¹ * (φ d * q.out)) = _
  group

/-- The actual orbit map from the original stabilizer cosets. -/
def cosetOrbitMap (q : G ⧸ S) : (D ⧸ cosetOrbitStabilizer φ S q) → G ⧸ S :=
  letI := cosetOrbitRestrictedAction φ S
  MulAction.ofQuotientStabilizer D q

/-- The orbit map keeps the original action of the quotient representative. -/
theorem cosetOrbitMap_out (q : G ⧸ S) (x : D ⧸ cosetOrbitStabilizer φ S q) :
    cosetOrbitMap φ S q x = φ x.out • q := by
  letI := cosetOrbitRestrictedAction φ S
  change MulAction.ofQuotientStabilizer D q x = x.out • q
  conv_lhs => rw [← Quotient.out_eq' x]
  rfl

/-- Distinct original stabilizer cosets give distinct original global cosets. -/
theorem cosetOrbitMap_injective (q : G ⧸ S) : Function.Injective (cosetOrbitMap φ S q) := by
  letI := cosetOrbitRestrictedAction φ S
  exact MulAction.injective_ofQuotientStabilizer D q

/-- The original orbit map intertwines the two actual coset actions. -/
theorem cosetOrbitMap_smul (q : G ⧸ S) (d : D) (x : D ⧸ cosetOrbitStabilizer φ S q) :
    cosetOrbitMap φ S q (d • x) = φ d • cosetOrbitMap φ S q x := by
  letI := cosetOrbitRestrictedAction φ S
  exact MulAction.ofQuotientStabilizer_smul D q d x

/-- A compatible representative in G for each actual stabilizer coset. -/
def cosetOrbitRepresentative (q : G ⧸ S) (x : D ⧸ cosetOrbitStabilizer φ S q) : G :=
  φ x.out * q.out

/-- The compatible representative represents precisely the original orbit coset. -/
theorem cosetOrbitRepresentative_mk (q : G ⧸ S) (x : D ⧸ cosetOrbitStabilizer φ S q) :
    (QuotientGroup.mk (cosetOrbitRepresentative φ S q x) : G ⧸ S) = cosetOrbitMap φ S q x := by
  rw [cosetOrbitMap_out]
  exact MulAction.Quotient.mk_smul_out S (φ x.out) q

/-- The actual stabilizer transition gives exactly the G transition
between compatible representatives, without an assumed coordinate match. -/
theorem cosetOrbitRepresentative_factor (q : G ⧸ S) (d : D)
    (x : D ⧸ cosetOrbitStabilizer φ S q) :
    cosetOrbitRepresentative φ S q (d • x) *
        (cosetOrbitSubgroupMap φ S q (cosetTransition (cosetOrbitStabilizer φ S q) d x) : G) =
      φ d * cosetOrbitRepresentative φ S q x := by
  have ht := congrArg φ (cosetTransition_factor (cosetOrbitStabilizer φ S q) d x)
  simp only [map_mul] at ht
  change (φ (d • x).out * q.out) *
      (q.out⁻¹ * (φ (cosetTransition (cosetOrbitStabilizer φ S q) d x) * q.out)) =
    φ d * (φ x.out * q.out)
  calc
    _ = (φ (d • x).out * φ (cosetTransition (cosetOrbitStabilizer φ S q) d x)) * q.out := by group
    _ = _ := by rw [ht, mul_assoc]

end
end Dubon2026

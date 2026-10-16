import Dubon2026.CosetOrbitTraceSum
import Dubon2026.ContinuousCosetRepresentativeChange

/-! # Actual continuity on the stabilizers of restricted coset orbits

The open stabilizers and conjugated cocycles retain the original
topologies. This supplies the continuous orbit terms in the local/global
transfer comparison needed by DUB-17's reciprocity route.
-/

namespace Dubon2026
noncomputable section

variable {R D G : Type} [CommRing R] [Group D] [Group G]
  [TopologicalSpace R] [TopologicalSpace D] [TopologicalSpace G]
  [IsTopologicalGroup D] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (φ : D →* G) (hφ : Continuous φ) (S : Subgroup G)

include hφ in
omit [IsTopologicalGroup D] in
/-- The actual conjugation map from an orbit stabilizer is continuous
in the original subgroup topologies. -/
theorem cosetOrbitSubgroupMap_continuous (q : G ⧸ S) :
    Continuous (cosetOrbitSubgroupMap φ S q) := by
  apply Continuous.subtype_mk
  exact continuous_const.mul ((hφ.comp continuous_subtype_val).mul continuous_const)

include hφ in
omit [IsTopologicalGroup D] in
/-- Each actual orbit stabilizer is open when the original global
subgroup is open and the original restriction homomorphism is continuous. -/
theorem cosetOrbitStabilizer_isOpen (hS : IsOpen (S : Set G)) (q : G ⧸ S) :
    IsOpen (cosetOrbitStabilizer φ S q : Set D) := by
  have he : (cosetOrbitStabilizer φ S q : Set D) =
      (fun d : D => q.out⁻¹ * (φ d * q.out)) ⁻¹' (S : Set G) :=
    Set.ext (fun d => cosetOrbitStabilizer_mem φ S q d)
  rw [he]
  exact hS.preimage (continuous_const.mul (hφ.mul continuous_const))

include hA hφ in
omit [IsTopologicalGroup D] in
/-- Restriction and literal conjugation preserve joint continuity of
the original two-cocycle at every genuine orbit stabilizer. -/
theorem cosetOrbitCocycle_continuous (q : G ⧸ S)
    (c : continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype)) :
    Continuous (cosetOrbitCocycle A φ S q c.val :
      cosetOrbitStabilizer φ S q × cosetOrbitStabilizer φ S q → A) := by
  have hψ := cosetOrbitSubgroupMap_continuous φ hφ S q
  exact hA.comp (continuous_const.prodMk
    (c.property.comp ((hψ.comp continuous_fst).prodMk (hψ.comp continuous_snd))))

/-- The original conjugated stabilizer cocycle with its proved continuity. -/
def continuousCosetOrbitCocycle (q : G ⧸ S)
    (c : continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype)) :
    continuousRepresentationCocyclesTwo
      (restrictedCoefficientRep (restrictedCoefficientRep A φ) (cosetOrbitStabilizer φ S q).subtype) :=
  ⟨cosetOrbitCocycle A φ S q c.val, cosetOrbitCocycle_continuous A hA φ hφ S q c⟩

end
end Dubon2026

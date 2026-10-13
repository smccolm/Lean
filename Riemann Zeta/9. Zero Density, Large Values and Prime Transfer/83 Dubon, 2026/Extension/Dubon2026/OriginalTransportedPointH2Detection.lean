import Dubon2026.OriginalTransportedH2LocalDetection

/-! # Actual point restriction detects transported H2

For DUB-17 global localization, the existing orbit detection is expressed
through literal stabilizers of the original points. The comparison keeps
all coefficient values unchanged and is used to compare original finite
and infinite completion maps without an orbit-representative assumption.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))

/-- The stabilizer of an original orbit point maps to the stabilizer of the same original ambient point. -/
def originalOrbitStabilizerPointHom (ω : MulAction.orbitRel.Quotient G ι) :
    MulAction.stabilizer G (originalOrbitPoint G ι ω) →*
      MulAction.stabilizer G ω.out where
  toFun g := ⟨g.val, congrArg Subtype.val g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The original orbit and ambient stabilizer coefficients retain the same original values. -/
def originalOrbitPointCoefficientHom (ω : MulAction.orbitRel.Quotient G ι) :
    Rep.res (originalOrbitStabilizerPointHom G ι ω)
      (transportedStabilizerRep R G ι M T T_one T_mul ω.out) ⟶
        transportedOrbitPointRep R G ι M T T_one T_mul ω (originalOrbitPoint G ι ω) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- Vanishing under the literal original point-stabilizer restriction and evaluation detects the transported H2 class. -/
theorem originalTransportedH2_zero_of_points
    (x : groupCohomology (transportedPiRep R G ι M T T_one T_mul) 2)
    (hx : ∀ i : ι, groupCohomology.map (MulAction.stabilizer G i).subtype
      (transportedStabilizerEvaluation R G ι M T T_one T_mul i) 2 x = 0) : x = 0 := by
  apply originalTransportedH2_zero_of_local R G ι M T T_one T_mul x
  intro ω
  let j := originalOrbitStabilizerPointHom G ι ω
  let f := transportedStabilizerEvaluation R G ι M T T_one T_mul ω.out
  let h := originalOrbitPointCoefficientHom R G ι M T T_one T_mul ω
  have hc := groupCohomology.map_comp
    (A := transportedPiRep R G ι M T T_one T_mul)
    (B := transportedStabilizerRep R G ι M T T_one T_mul ω.out)
    (MulAction.stabilizer G ω.out).subtype j f h 2
  change groupCohomology.map ((MulAction.stabilizer G ω.out).subtype.comp j)
    ((Rep.resFunctor j).map f ≫ h) 2 x = 0
  rw [hc]
  change groupCohomology.map j h 2 (groupCohomology.map
    (MulAction.stabilizer G ω.out).subtype f 2 x) = 0
  rw [hx ω.out, map_zero]

end
end Dubon2026

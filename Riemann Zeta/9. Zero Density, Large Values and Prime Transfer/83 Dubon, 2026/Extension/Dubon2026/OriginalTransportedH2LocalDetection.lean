import Dubon2026.OriginalTransportedH2Restriction

/-! # Original transported H2 is detected by actual orbit-stabilizer restrictions

This composes original orbit projection with literal subgroup restriction
and point evaluation. Its zero-kernel statement is the precise local map
needed for DUB-17's original idele H2 detection; neither cyclicity nor
finiteness of the place set is assumed.
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

/-- The actual original coefficient restricted to one original place orbit. -/
def originalTransportedOrbitProjection (ω : MulAction.orbitRel.Quotient G ι) :
    transportedPiRep R G ι M T T_one T_mul ⟶
      transportedOrbitFactorRep R G ι M T T_one T_mul ω :=
  (transportedOrbitProductIso R G ι M T T_one T_mul).hom ≫
    originalPiRepProjection (transportedOrbitFactorRep R G ι M T T_one T_mul) ω

/-- Literal original point evaluation after restricting the whole transported coefficient to its orbit stabilizer. -/
def originalTransportedOrbitEvaluation (ω : MulAction.orbitRel.Quotient G ι) :
    Rep.res (MulAction.stabilizer G (originalOrbitPoint G ι ω)).subtype
      (transportedPiRep R G ι M T T_one T_mul) ⟶
        transportedOrbitPointRep R G ι M T T_one T_mul ω (originalOrbitPoint G ι ω) :=
  (Rep.resFunctor (MulAction.stabilizer G (originalOrbitPoint G ι ω)).subtype).map
      (originalTransportedOrbitProjection R G ι M T T_one T_mul ω) ≫
    transportedStabilizerEvaluation R G ω.orbit (fun j => M j.val)
      (fun g j k h => T g j.val k.val (congrArg Subtype.val h))
      (fun j x => T_one j.val x)
      (fun g h j k l hh hg hgh x => T_mul g h j.val k.val l.val
        (congrArg Subtype.val hh) (congrArg Subtype.val hg) (congrArg Subtype.val hgh) x)
      (originalOrbitPoint G ι ω)

/-- The original stabilizer evaluation retains the literal coordinate at the chosen original place. -/
theorem originalTransportedOrbitEvaluation_apply (ω : MulAction.orbitRel.Quotient G ι)
    (x : ∀ i, M i) :
    (originalTransportedOrbitEvaluation R G ι M T T_one T_mul ω).hom x = x ω.out := rfl

/-- Vanishing of every actual orbit-stabilizer restriction forces an original transported H2 class to vanish. -/
theorem originalTransportedH2_zero_of_local
    (x : groupCohomology (transportedPiRep R G ι M T T_one T_mul) 2)
    (hx : ∀ ω : MulAction.orbitRel.Quotient G ι,
      groupCohomology.map (MulAction.stabilizer G (originalOrbitPoint G ι ω)).subtype
        (originalTransportedOrbitEvaluation R G ι M T T_one T_mul ω) 2 x = 0) : x = 0 := by
  let A := transportedOrbitFactorRep R G ι M T T_one T_mul
  let e := (groupCohomology.functor R G 2).mapIso
    (transportedOrbitProductIso R G ι M T T_one T_mul)
  apply e.toLinearEquiv.injective
  change e.hom x = e.hom 0
  rw [map_zero]
  apply originalPiH2_zero_of_coordinates A
  intro ω
  let p := originalTransportedOrbitProjection R G ι M T T_one T_mul ω
  let q := transportedStabilizerEvaluation R G ω.orbit (fun j => M j.val)
    (fun g j k h => T g j.val k.val (congrArg Subtype.val h))
    (fun j x => T_one j.val x)
    (fun g h j k l hh hg hgh x => T_mul g h j.val k.val l.val
      (congrArg Subtype.val hh) (congrArg Subtype.val hg) (congrArg Subtype.val hgh) x)
    (originalOrbitPoint G ι ω)
  have hi := originalTransportedStabilizerH2_injective R G ω.orbit (fun j => M j.val)
    (fun g j k h => T g j.val k.val (congrArg Subtype.val h))
    (fun j x => T_one j.val x)
    (fun g h j k l hh hg hgh x => T_mul g h j.val k.val l.val
      (congrArg Subtype.val hh) (congrArg Subtype.val hg) (congrArg Subtype.val hgh) x)
    (originalOrbitPoint G ι ω)
  have hp : (groupCohomology.functor R G 2).map p x = 0 := by
    apply hi
    change groupCohomology.map (MulAction.stabilizer G (originalOrbitPoint G ι ω)).subtype q 2
        ((groupCohomology.functor R G 2).map p x) =
      groupCohomology.map (MulAction.stabilizer G (originalOrbitPoint G ι ω)).subtype q 2 0
    rw [map_zero]
    have hc := groupCohomology.map_comp
      (A := transportedPiRep R G ι M T T_one T_mul) (B := A ω) (MonoidHom.id G)
      (MulAction.stabilizer G (originalOrbitPoint G ι ω)).subtype p q 2
    have h := hx ω
    change (groupCohomology.map ((MonoidHom.id G).comp
      (MulAction.stabilizer G (originalOrbitPoint G ι ω)).subtype)
      ((Rep.resFunctor (MulAction.stabilizer G (originalOrbitPoint G ι ω)).subtype).map p ≫ q) 2) x = 0 at h
    rw [hc] at h
    exact h
  have hc := (groupCohomology.functor R G 2).map_comp
    (transportedOrbitProductIso R G ι M T T_one T_mul).hom (originalPiRepProjection A ω)
  change (groupCohomology.functor R G 2).map
    ((transportedOrbitProductIso R G ι M T T_one T_mul).hom ≫ originalPiRepProjection A ω) x = 0 at hp
  rw [hc] at hp
  exact hp

end
end Dubon2026

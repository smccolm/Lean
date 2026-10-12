import Dubon2026.GaloisFixingRootCohomology
import Dubon2026.ContinuousH1CorestrictionIndex
import Dubon2026.KummerCharacterZModModules

/-! # Coprime finite-field restriction detects original root H1

The field restriction is the literal original subgroup restriction transported
by the proved fixing-subgroup identification. Its kernel vanishes at degree
coprime to the root modulus, the condition proved for the cyclotomic stage.
-/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω] (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Reuse the original root coefficient topology on the same roots over the finite base. -/
local instance rootRestrictionStageTopology : TopologicalSpace (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
/-- The unchanged original root coefficient topology remains discrete. -/
local instance rootRestrictionStageDiscrete : DiscreteTopology (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
/-- Reuse the original unit coefficient topology on the same units over the finite base. -/
local instance rootRestrictionUnitTopology : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω))
/-- The unchanged original unit coefficient topology remains discrete. -/
local instance rootRestrictionUnitDiscrete : DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω))

/-- Restriction to the original finite base field on actual continuous root H1. -/
def galoisRootContinuousRestriction :
    GaloisRootContinuousH1 (K := K) (Ω := Ω) n →+
      GaloisRootContinuousH1 (K := E) (Ω := Ω) n :=
  (galoisFixingRootH1Equiv K Ω E n).symm.toAddMonoidHom.comp
    (continuousRepresentationH1Restriction
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
      (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)
      E.fixingSubgroup.subtype continuous_subtype_val).toAddMonoidHom

/-- Field restriction and the genuine fixing-subgroup identification give
exactly the original continuous subgroup restriction. -/
theorem galoisFixingRootH1Equiv_restriction
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n) :
    galoisFixingRootH1Equiv K Ω E n (galoisRootContinuousRestriction K Ω E n x) =
      continuousRepresentationH1Restriction
        (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
        (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)
        E.fixingSubgroup.subtype continuous_subtype_val x :=
  (galoisFixingRootH1Equiv K Ω E n).apply_symm_apply _

/-- At actual finite degree coprime to the modulus, the original root H1
restriction has zero kernel, using the proved exponent and actual coset trace. -/
theorem galoisRootContinuousRestriction_coprime_zero [FiniteDimensional K E]
    [IsAlgClosed Ω] [NeZero n] (hn : n.Coprime (Module.finrank K E))
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n)
    (hx : galoisRootContinuousRestriction K Ω E n x = 0) : x = 0 := by
  letI : Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup) := Fintype.ofFinite _
  apply continuousRepresentationH1Restriction_coprime_zero
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
    (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)
    E.fixingSubgroup E.fixingSubgroup_isOpen n
    (by simpa only [galoisFixingCosets_card] using hn) x
    (galoisRootContinuousH1_nsmul_eq_zero n x)
  rw [← galoisFixingRootH1Equiv_restriction, hx]
  exact (galoisFixingRootH1Equiv K Ω E n).map_zero

end
end Dubon2026

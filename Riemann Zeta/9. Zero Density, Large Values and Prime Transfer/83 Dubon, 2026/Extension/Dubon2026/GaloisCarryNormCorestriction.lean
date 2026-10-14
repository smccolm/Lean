import Dubon2026.ContinuousCarryCorestriction
import Dubon2026.GaloisCosetUnitNorm
import Dubon2026.GaloisUnitContinuousCorestriction
import Dubon2026.ContinuousKummerCarryBoundary

/-! # Genuine field corestriction of original character carries

The original continuous character is restricted along the literal base-change
map. Genuine coset corestriction sends its carry with an original finite-base
unit to the carry with that unit's actual field norm. This is the exact input
to local reciprocity norm compatibility in DUB-17's cyclotomic calculation.
-/
namespace Dubon2026
noncomputable section
open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω] {n : ℕ} [NeZero n]
  (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n))

/-- Restrict an original continuous character through the actual change of fixed base. -/
def galoisFiniteBaseCharacterRestriction : Gal(Ω/E) →ₜ* Multiplicative (ZMod n) where
  toMonoidHom := χ.toMonoidHom.comp (galoisBaseChangeRestriction K E Ω Ω)
  continuous_toFun := χ.continuous.comp (galoisBaseChangeRestriction_continuous K E Ω Ω)

omit [IsGalois E Ω] [NeZero n] in
/-- The restricted original character retains the same values on its actual fixing subgroup. -/
theorem galoisFiniteBaseCharacterRestriction_fixing (s : E.fixingSubgroup) :
    galoisFiniteBaseCharacterRestriction K Ω E χ (E.fixingSubgroupEquiv s) = χ s := by
  change χ (galoisBaseChangeRestriction K E Ω Ω (E.fixingSubgroupEquiv s)) = χ s
  rw [galoisBaseChangeRestriction_eq_fixingSubgroup, MulEquiv.symm_apply_apply]

variable [FiniteDimensional K E] [IsAlgClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]

attribute [local instance] carryCoefficientContinuousSMul

/-- Actual continuous corestriction sends the original restricted-character carry to the carry of the literal original field norm. -/
theorem continuousGaloisCharacterCarryCocycle_corestriction_norm (u : Eˣ) :
    galoisUnitContinuousCorestriction K Ω E
      (Submodule.Quotient.mk (continuousGaloisCharacterCarryCocycle n
        (galoisFiniteBaseCharacterRestriction K Ω E χ) u)) =
      (Submodule.Quotient.mk (continuousGaloisCharacterCarryCocycle n χ
        (Units.map (Algebra.norm K (S := E)) u)) :
        GaloisUnitContinuousH2 (K := K) (Ω := Ω)) := by
  letI : Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup) := Fintype.ofFinite _
  let A := Rep.ofAlgebraAutOnUnits K Ω
  let hA := discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)
  let a := galoisIntermediateUnitCoefficient K Ω E u
  let ha := galoisIntermediateUnitCoefficient_fixed K Ω E u
  have hc : galoisFixingUnitCocycle K Ω E (continuousGaloisCharacterCarryCocycle n
      (galoisFiniteBaseCharacterRestriction K Ω E χ) u) =
      continuousRepresentationCarryCocycle (restrictedCoefficientRep A E.fixingSubgroup.subtype)
        ⟨χ.toMonoidHom.comp E.fixingSubgroup.subtype, χ.continuous.comp continuous_subtype_val⟩
        a ha := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change zmodAdditionCarry
      (galoisFiniteBaseCharacterRestriction K Ω E χ (E.fixingSubgroupEquiv z.1)).toAdd
      (galoisFiniteBaseCharacterRestriction K Ω E χ (E.fixingSubgroupEquiv z.2)).toAdd • a = _
    rw [galoisFiniteBaseCharacterRestriction_fixing, galoisFiniteBaseCharacterRestriction_fixing]
    rfl
  change continuousRepresentationH2Corestriction A hA E.fixingSubgroup E.fixingSubgroup_isOpen
    (Submodule.Quotient.mk (galoisFixingUnitCocycle K Ω E
      (continuousGaloisCharacterCarryCocycle n (galoisFiniteBaseCharacterRestriction K Ω E χ) u))) = _
  rw [hc, continuousRepresentationCarryCocycle_corestriction]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  apply Subtype.ext
  funext z
  change zmodAdditionCarry (χ z.1).toAdd (χ z.2).toAdd •
    (∑ q : Gal(Ω/K) ⧸ E.fixingSubgroup, A.ρ q.out a) =
      zmodAdditionCarry (χ z.1).toAdd (χ z.2).toAdd •
        galoisUnitsBaseCoefficient (L := Ω) (Units.map (Algebra.norm K (S := E)) u)
  rw [galoisIntermediateUnitCoefficient_coset_norm K Ω E u]

end
end Dubon2026

import Dubon2026.OriginalGaloisCosetNorm
import Dubon2026.FiniteGaloisUnitNormRange

/-! # Original subgroup-fixed unit coefficients and their coset norm

This identifies the coefficient in the proved carry projection formula with
the literal field norm of the original finite-base unit. No norm formula is
assumed in the local reciprocity dependency for DUB-17.
-/
namespace Dubon2026
noncomputable section
open scoped BigOperators

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  (E : IntermediateField K Ω)

/-- An original intermediate-field unit in the original ambient unit representation. -/
def galoisIntermediateUnitCoefficient (u : Eˣ) : Rep.ofAlgebraAutOnUnits K Ω :=
  Rep.toAdditive.symm (Additive.ofMul (Units.map E.val.toMonoidHom u))

/-- The original intermediate-field coefficient is fixed by its genuine fixing subgroup. -/
theorem galoisIntermediateUnitCoefficient_fixed (u : Eˣ) (s : E.fixingSubgroup) :
    (Rep.ofAlgebraAutOnUnits K Ω).ρ s (galoisIntermediateUnitCoefficient K Ω E u) =
      galoisIntermediateUnitCoefficient K Ω E u := by
  change s.val • Units.map E.val.toMonoidHom u = Units.map E.val.toMonoidHom u
  apply Units.ext
  exact (IntermediateField.mem_fixingSubgroup_iff E s.val).mp s.property u.val u.val.property

variable [IsGalois K Ω] [FiniteDimensional K E] [IsAlgClosed Ω]
  [Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup)]

/-- The actual additive coset trace of an original unit is exactly the base coefficient of its field norm. -/
theorem galoisIntermediateUnitCoefficient_coset_norm (u : Eˣ) :
    (∑ q : Gal(Ω/K) ⧸ E.fixingSubgroup,
      (Rep.ofAlgebraAutOnUnits K Ω).ρ q.out (galoisIntermediateUnitCoefficient K Ω E u)) =
      galoisUnitsBaseCoefficient (L := Ω) (Units.map (Algebra.norm K (S := E)) u) := by
  apply Rep.toAdditive.injective
  change (∑ q : Gal(Ω/K) ⧸ E.fixingSubgroup,
    Additive.ofMul (q.out • Units.map E.val.toMonoidHom u)) =
      Additive.ofMul (Units.map (algebraMap K Ω).toMonoidHom
        (Units.map (Algebra.norm K (S := E)) u))
  apply Additive.toMul.injective
  change (∏ q : Gal(Ω/K) ⧸ E.fixingSubgroup, q.out • Units.map E.val.toMonoidHom u) = _
  apply Units.ext
  change (Units.coeHom Ω)
    (∏ q : Gal(Ω/K) ⧸ E.fixingSubgroup, q.out • Units.map E.val.toMonoidHom u) = _
  rw [map_prod]
  exact originalGaloisCosetProduct_eq_norm K Ω E u.val

end
end Dubon2026

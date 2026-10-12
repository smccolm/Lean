import Dubon2026.GaloisUnitBaseChange
import Dubon2026.GaloisUnitCharacterCarryPeriod

/-! # Actual base change of original field-unit carry cocycles -/

namespace Dubon2026
noncomputable section

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]

omit [IsGalois E M] in
/-- The genuine base-change map sends an original carry cocycle to the
carry of the restricted original character, with the actual included base unit. -/
theorem finiteGaloisUnitBaseChangeCocycle_characterCarry
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    finiteGaloisUnitBaseChangeCocycle K E L M (galoisUnitCharacterCarryCocycle χ u) =
      galoisUnitCharacterCarryCocycle (χ.comp (galoisBaseChangeRestriction K E L M))
        (Units.map (algebraMap K E).toMonoidHom u) := by
  apply Subtype.ext
  apply Subtype.ext
  funext z
  let a := zmodAdditionCarry
    (χ (galoisBaseChangeRestriction K E L M z.1)).toAdd
    (χ (galoisBaseChangeRestriction K E L M z.2)).toAdd
  change (Units.map (algebraMap L M).toMonoidHom).toAdditive
    (a • Additive.ofMul (Units.map (algebraMap K L).toMonoidHom u)) =
      a • Additive.ofMul (Units.map (algebraMap E M).toMonoidHom
        (Units.map (algebraMap K E).toMonoidHom u))
  rw [map_nsmul]
  congr 1
  apply Additive.toMul.injective
  apply Units.ext
  exact (IsScalarTower.algebraMap_apply K L M u.val).symm.trans
    (IsScalarTower.algebraMap_apply K E M u.val)

/-- The original carry identity descends to the literal continuous H2
base-change map and the original quotient classes. -/
theorem finiteGaloisUnitBaseChangeH2_characterCarry
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    finiteGaloisUnitBaseChangeH2 K E L M
      (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) =
        Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle
          (χ.comp (galoisBaseChangeRestriction K E L M))
          (Units.map (algebraMap K E).toMonoidHom u)) := by
  rw [finiteGaloisUnitBaseChangeH2_mk, finiteGaloisUnitBaseChangeCocycle_characterCarry]

end
end Dubon2026

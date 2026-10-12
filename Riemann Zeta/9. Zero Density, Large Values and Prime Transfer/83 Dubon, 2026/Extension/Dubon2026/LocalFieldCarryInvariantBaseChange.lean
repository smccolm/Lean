import Dubon2026.GaloisUnitCarryBaseChange
import Dubon2026.LocalFieldFrobeniusBaseChange
import Dubon2026.LocalFieldCharacterCarryInvariant
import Dubon2026.LocalFieldUnitOrderBaseChange

/-! # Original unramified carry invariants scale by the actual base degree -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [IsGalois K L] [IsGalois E M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]

/-- Genuine base change multiplies the original rational invariant of
every character carry class by the actual base-field extension degree.
The ramification and residue factors are both derived from original objects. -/
theorem localFieldPeriodRationalInvariant_baseChange_characterCarry
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : FiniteDimensional E M := localField_field_module_finite
    localFieldPeriodRationalInvariant E M
      (finiteGaloisUnitBaseChangeH2 K E L M
        (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u))) =
          Module.finrank K E • localFieldPeriodRationalInvariant K L
            (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : FiniteDimensional E M := localField_field_module_finite
  rw [finiteGaloisUnitBaseChangeH2_characterCarry,
    localFieldPeriodRationalInvariant_characterCarry_smul,
    localFieldPeriodRationalInvariant_characterCarry_smul]
  change localFieldUnitOrder E (Additive.ofMul (Units.map (algebraMap K E).toMonoidHom u)) •
    rationalCyclicInvariant n
      (χ (galoisBaseChangeRestriction K E L M (localFieldArithmeticFrobenius E M))).toAdd = _
  rw [localFieldArithmeticFrobenius_baseChange, map_pow, toAdd_pow, map_nsmul,
    localFieldUnitOrder_algebraMap]
  rw [← natCast_zsmul _ (Module.finrank 𝓀[K] 𝓀[E]),
    ← natCast_zsmul _ (Module.finrank K E), smul_smul, smul_smul]
  congr 1
  have h : ((IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx
      (IsLocalRing.maximalIdeal 𝒪[E]) : ℤ) * (Module.finrank 𝓀[K] 𝓀[E] : ℤ) =
        (Module.finrank K E : ℤ) := by
    exact_mod_cast localField_ramification_mul_residue_degree K E
  rw [← h]
  ring

end
end Dubon2026

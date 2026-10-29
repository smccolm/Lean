import Dubon2026.SourceGammaOneIntegralToricSlash
import Dubon2026.SourceGammaOneIntegralToricReconstruction

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> original-field toric invariants. Assemble the actual modular
forms, integer coefficients, Gamma0 slash action and residue-field series
identities. No modularity, integrality, action or reconstruction certificate
is assumed. Exact-order elliptic points and the finite-fiber comparison
remain separate obligations. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ToricFourier
noncomputable section
open UpperHalfPlane CongruenceSubgroup HahnSeries
open scoped MatrixGroups ModularForm

theorem exists_integralToricInvariantForms (M : ℕ) [NeZero M] :
    ∃ (B : ZMod M → ModularForm (Gamma1 M) 2)
      (D : ZMod M → ModularForm (Gamma1 M) 4)
      (b d : ZMod M → PowerSeries ℤ),
      (∀ c, IsIntegralQExp (B c) (b c)) ∧
      (∀ c, IsIntegralQExp (D c) (d c)) ∧
      (∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ Gamma0 M →
        (B c : ℍ → ℂ) ∣[(2 : ℤ)] γ = (B (c * (γ 0 0 : ZMod M)) : ℍ → ℂ) ∧
        (D c : ℍ → ℂ) ∣[(4 : ℤ)] γ = (D (c * (γ 0 0 : ZMod M)) : ℍ → ℂ)) ∧
      ∀ (K : Type*) [Field K] (ζ : K), IsPrimitiveRoot ζ M →
        ∀ s : ZMod M, s ≠ 0 →
          (M : LaurentSeries K) ^ 3 *
              (1 + 12 * ofPowerSeries ℤ K (xS (ζ ^ s.val))) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (b c) ∧
          (M : LaurentSeries K) ^ 5 *
              (ofPowerSeries ℤ K (xS (ζ ^ s.val)) +
                6 * ofPowerSeries ℤ K (xS (ζ ^ s.val)) ^ 2 + 2 * intSeriesC K tateA4) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (d c) :=
  ⟨B M, D M, fun c => PowerSeries.mk (bZ M c), fun c => PowerSeries.mk (dZ M c),
    isIntegralQExp_B M, isIntegralQExp_D M,
    fun c γ hγ => ⟨B_slash M c γ hγ, D_slash M c γ hγ⟩,
    fun K _ _ζ hζ s hs => ⟨weightTwo_series K hζ s hs, weightFour_series K hζ s hs⟩⟩

end
end Dubon2026.SourceFunctionField.GammaOne.ToricFourier

import Dubon2026.SourceOriginalResidueLabeledCuspPlace
import Dubon2026.SourceOriginalResidueDiamondFiberStabilizer

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> actual stabilizers of complete labeled fibers.
Construct the matrix and a place over the existing base label, then use actual
diamond transitivity and its proved commutativity to fix every place in that
fiber. No original-field place, transitivity or stabilizer certificate remains. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open CongruenceSubgroup GammaOne IntegralDiamond SourceCurve
open scoped MatrixGroups
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
  [CharP (IsLocalRing.ResidueField A) ℓ]
local notation "kk" => IsLocalRing.ResidueField A
private local instance : IsAlgClosed kk := valuation_residue_isAlgClosed A
private local instance : Algebra kk (qExpFunctionFieldC kk (Gamma1 N)) :=
  (qExpFunctionFieldC kk (Gamma1 N)).toSubalgebra.algebra
private local instance : Algebra kk (modularFunctionFieldCoeff N kk) :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

theorem exists_originalResidueLabeledCuspFiber_stabilizer (hℓN : ¬ ℓ ∣ N)
    (ζ : kkˣ) (hζ : IsPrimitiveRoot (ζ : kk) N) (s : {s // s ∈ CuspLabels.labels N}) :
    let hN : (N : kk) ≠ 0 := fun h => hℓN ((CharP.cast_eq_zero_iff kk ℓ N).mp h)
    ∃ g : SL(2, ℤ), g 1 0 = (s.1.1 : ℤ) ∧
      ∀ (w : Place kk (qExpFunctionFieldC kk (Gamma1 N))),
        w.toValuationSubring.comap
          (IntermediateField.inclusion (fullBase_le_originalField kk N)).toRingHom =
            (CoefficientCuspLabels.place N kk hN ζ hζ s).toValuationSubring →
        ∀ (γ : Gamma0 N) (j : ℤ),
          (g⁻¹ * γ.val * g = ModularGroup.T ^ j ∨
            g⁻¹ * γ.val * g = -(ModularGroup.T ^ j)) →
          w.comapEquiv (originalResidueDiamondAction A N ℓ hℓN γ⁻¹) = w := by
  dsimp only
  obtain ⟨g, w₀, hg, hw₀, _, hfix⟩ := exists_originalResidueLabeledCuspFixedPlace A N ℓ hℓN ζ hζ s
  refine ⟨g, hg, fun w hw γ j hγ => ?_⟩
  exact originalResidueDiamond_fixes_of_same_fullBase A N ℓ hℓN w₀ w (hw.trans hw₀.symm)
    γ⁻¹ (hfix γ j hγ)

end
end Dubon2026.SourceFunctionField.IntegralSlash

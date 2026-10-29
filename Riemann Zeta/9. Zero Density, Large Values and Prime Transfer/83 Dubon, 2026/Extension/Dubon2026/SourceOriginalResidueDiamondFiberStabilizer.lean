import Dubon2026.SourceOriginalResidueDiamondCommute
import Dubon2026.SourceOriginalResidueDiamondFiberTransitivity

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> one stabilizer fixes every place in the actual
fiber. The native actual-action fiber transitivity and the proved commutativity
transport a fixed-place identity across that fiber. No transitivity or
commutativity certificate is added to the theorem's hypotheses. -/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open CongruenceSubgroup GammaOne SourceCurve
open scoped MatrixGroups
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
  [CharP (IsLocalRing.ResidueField A) ℓ]
local notation "kk" => IsLocalRing.ResidueField A
private local instance : Algebra kk (qExpFunctionFieldC kk (Gamma1 N)) :=
  (qExpFunctionFieldC kk (Gamma1 N)).toSubalgebra.algebra

private local instance : Algebra kk (modularFunctionFieldCoeff N kk) :=
  (modularFunctionFieldCoeff N kk).toSubalgebra.algebra

theorem originalResidueDiamond_fixes_of_same_fullBase (hℓN : ¬ ℓ ∣ N)
    (w₀ w : Place kk (qExpFunctionFieldC kk (Gamma1 N)))
    (h : w.toValuationSubring.comap
        (IntermediateField.inclusion (fullBase_le_originalField kk N)).toRingHom =
      w₀.toValuationSubring.comap
        (IntermediateField.inclusion (fullBase_le_originalField kk N)).toRingHom)
    (γ : Gamma0 N) (hfix : w₀.comapEquiv (originalResidueDiamondAction A N ℓ hℓN γ) = w₀) :
    w.comapEquiv (originalResidueDiamondAction A N ℓ hℓN γ) = w := by
  obtain ⟨δ, rfl⟩ := originalResidueDiamond_exists_comapEquiv_of_fullBase_comap_eq A N ℓ hℓN w₀ w h
  have hc := originalResidueDiamondAction_commute A N ℓ hℓN δ γ
  apply Place.ext
  ext x
  rw [Place.mem_iff_ord_nonneg, Place.mem_iff_ord_nonneg,
    Place.ord_comapEquiv, Place.ord_comapEquiv, Place.ord_comapEquiv]
  have hcomm : originalResidueDiamondAction A N ℓ hℓN δ
      (originalResidueDiamondAction A N ℓ hℓN γ x) =
      originalResidueDiamondAction A N ℓ hℓN γ
        (originalResidueDiamondAction A N ℓ hℓN δ x) :=
    congrArg (fun e : qExpFunctionFieldC kk (Gamma1 N) ≃ₐ[kk] qExpFunctionFieldC kk (Gamma1 N) => e x) hc.eq
  rw [hcomm]
  have ho := congrArg (fun v : Place kk (qExpFunctionFieldC kk (Gamma1 N)) =>
    v.ord (originalResidueDiamondAction A N ℓ hℓN δ x)) hfix
  dsimp only at ho
  rw [Place.ord_comapEquiv] at ho
  rw [ho]

end
end Dubon2026.SourceFunctionField.IntegralDiamond

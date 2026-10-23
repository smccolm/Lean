import Dubon2026.SourceOriginalPicardHeckePeriods
import Dubon2026.SourceOriginalTatePeriod
import Dubon2026.SourceOriginalHeckeComplexPicard

/-! DUB-17/18 -> rank-two Hecke/Frobenius realization -> the actual
original Jacobian Tate Hecke action. The proved complex Hecke comparison
and full Picard-period equivariance identify the original arithmetic Tate
operator with the Tate functor applied to the genuine period quotient
operator. No equivariance premise remains.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential OriginalConstantField
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

private local instance {N : ℕ} (ell : sourceBinaryHeckePrime N) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

theorem originalTatePeriodQuotientEquiv_originalHecke
    (ell : sourceBinaryHeckePrime N) (p : ℕ) [Fact p.Prime] {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (x : TateModule p (originalJZero N)) :
    originalTatePeriodQuotientEquiv N p b P₀
        (TateModule.tateMap p (originalHeckePicard (AlgebraicClosure ℚ) N ell.val) x) =
      TateModule.tateMap p (originalPeriodQuotientHecke N ell b).toAddMonoidHom
        (originalTatePeriodQuotientEquiv N p b P₀ x) := by
  apply Subtype.ext
  funext k
  have hC := complexPicardMap_originalHeckePicard N ell.val ((x : ℕ → originalJZero N) k)
  have hP := originalPicardPeriodEquiv_originalHecke N ell b P₀
    (complexPicardMap N ((x : ℕ → originalJZero N) k))
  exact (congrArg (originalPicardPeriodEquiv N b P₀) hC).trans hP

end
end Dubon2026.SourceFunctionField.OriginalChart

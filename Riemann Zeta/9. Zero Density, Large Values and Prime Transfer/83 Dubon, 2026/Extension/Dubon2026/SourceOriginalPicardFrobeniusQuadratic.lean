import Dubon2026.SourceOriginalHeckeTorsionReduction
import Dubon2026.SourceOriginalFrobeniusPicardReduction

/-! DUB-17/18 -> actual original Tate Frobenius quadratic relation.
The same constructed modular reduction intertwines actual arithmetic
Frobenius and the Hecke correspondence on torsion and is injective there.
The proved residue operator identity therefore gives the exact quadratic
identity on every residue-invertible torsion subgroup of the original Picard
group. No reduction or compatibility witness is assumed in the conclusion. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N p : ℕ) [NeZero N] [Fact p.Prime]
variable [CharP (IsLocalRing.ResidueField A) p]
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fo" => modularFunctionFieldOver N Qbar
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem original_hecke_frobenius_reduction_quadratic
    (hpN : ¬ p ∣ N) (hNk : (N : kk) ≠ 0)
    (R : ConstantReduction A (modularFunctionFieldCoeff N Qbar) (modularFunctionFieldCoeff N kk))
    (hR : R.toRegularProlongation =
      modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk)
    (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hF : ∀ z : Pic0 Qbar Fo,
      R.pic0Map (originalCoefficientPicardEquiv N (originalArithmeticPicard N τ z)) =
        residueCoefficientPicard N kk (frobeniusEquiv kk p)
          (R.pic0Map (originalCoefficientPicardEquiv N z)))
    (m : ℕ) (hm : m ≠ 0) (x : Pic0 Qbar Fo) (hx : m • x = 0) :
    R.pic0Map (originalCoefficientPicardEquiv N
        (originalHeckePicard Qbar N p (originalArithmeticPicard N τ x))) =
      R.pic0Map (originalCoefficientPicardEquiv N
        (originalArithmeticPicard N τ (originalArithmeticPicard N τ x) + p • x)) := by
  have hxF : m • originalArithmeticPicard N τ x = 0 := by
    rw [← map_nsmul, hx, map_zero]
  rw [original_hecke_reduction_torsion_picard A N p hpN hNk R hR _ m hm hxF,
    hF, residueFrobeniusPicardOperator_coefficient]
  symm
  let φ := R.pic0Map.comp (originalCoefficientPicardEquiv N).toAddMonoidHom
  have hFF := (hF (originalArithmeticPicard N τ x)).trans
    (congrArg (residueCoefficientPicard N kk (frobeniusEquiv kk p)) (hF x))
  exact (map_add φ _ _).trans (congrArg₂ (· + ·) hFF (map_nsmul φ p x))

theorem originalArithmeticPicard_frobenius_quadratic
    (hpN : ¬ p ∣ N) (hNk : (N : kk) ≠ 0) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hτ : ∃ hd : τ ∈ A.decompositionSubgroup ℚ,
      ∀ a : kk, (⟨τ, hd⟩ : A.decompositionSubgroup ℚ) • a = a ^ p)
    (m : ℕ) (hm : (m : kk) ≠ 0) (x : Pic0 Qbar Fo) (hx : m • x = 0) :
    originalHeckePicard Qbar N p (originalArithmeticPicard N τ x) =
      originalArithmeticPicard N τ (originalArithmeticPicard N τ x) + p • x := by
  obtain ⟨R, hR, _hgen, hinj, hF⟩ :=
    exists_modular_reduction_arithmeticFrobenius_picard A N p hNk
  have hm0 : m ≠ 0 := fun h => hm (by rw [h, Nat.cast_zero])
  have hxF : m • originalArithmeticPicard N τ x = 0 := by
    rw [← map_nsmul, hx, map_zero]
  have hleft : m • originalHeckePicard Qbar N p (originalArithmeticPicard N τ x) = 0 := by
    rw [← map_nsmul, hxF, map_zero]
  have hright : m • (originalArithmeticPicard N τ (originalArithmeticPicard N τ x) + p • x) = 0 := by
    rw [nsmul_add, ← map_nsmul, hxF, map_zero, smul_comm m p, hx, smul_zero, add_zero]
  apply (originalCoefficientPicardEquiv N).injective
  apply hinj m hm
  · exact originalCoefficientPicardEquiv_torsion N m _ (Pic0.mem_torsion_iff.mpr hleft)
  · exact originalCoefficientPicardEquiv_torsion N m _ (Pic0.mem_torsion_iff.mpr hright)
  exact original_hecke_frobenius_reduction_quadratic A N p hpN hNk R hR τ (hF τ hτ)
    m hm0 x hx

end
end Dubon2026.SourceFunctionField.GaussReduction

import Dubon2026.SourceGammaOneArithmeticTateFiniteH1
import Dubon2026.SourceGammaOneFiniteParabolicHecke

/-! DUB17/18 -> original all-weight arithmetic realization -> actual
finite Gamma1 H1/arithmetic Tate comparison. The canonical finite Tate
dual equivalence intertwines the actual arithmetic Picard prime Hecke
operator, contravariantly, with the native H1 Hecke correspondence.
Both the coefficient prime and the Hecke prime may divide the level.
Full/parabolic passage and homogeneous coefficients remain separate. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
variable (M p : ℕ) [NeZero M] [Fact p.Prime] (n : ℕ)

private local instance : Algebra ℤ_[p] (ZMod (p ^ n)) :=
  (PadicInt.toZModPow n).toAlgebra

theorem arithmeticTateCharacterEquiv_hecke (q : ℕ) [Fact q.Prime]
    (φ : TateModule p (Pic0 (AlgebraicClosure ℚ)
      (functionFieldOver (Gamma1 M) (AlgebraicClosure ℚ))) →ₗ[ℤ_[p]] ZMod (p ^ n)) :
    arithmeticTateCharacterEquiv M p n
        (φ.comp (TateModule.tateMap p (heckePicard (AlgebraicClosure ℚ) M q))) =
      (arithmeticTateCharacterEquiv M p n φ).comp (periodLatticeHecke M q).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro l
  exact congrArg φ (arithmeticPeriodInclusion_hecke M p q l)

theorem arithmeticTateFiniteH1Equiv_hecke (q : ℕ) [Fact q.Prime]
    (φ : TateModule p (Pic0 (AlgebraicClosure ℚ)
      (functionFieldOver (Gamma1 M) (AlgebraicClosure ℚ))) →ₗ[ℤ_[p]] ZMod (p ^ n)) :
    (arithmeticTateFiniteH1Equiv M p n
        (φ.comp (TateModule.tateMap p (heckePicard (AlgebraicClosure ℚ) M q)))).val =
      sourceGammaOneConstantHeckeH1 (ZMod (p ^ n)) (ZMod (p ^ n)) M q LinearMap.id
        (arithmeticTateFiniteH1Equiv M p n φ).val := by
  change (finiteLatticeH1Equiv M (p ^ n) (arithmeticTateCharacterEquiv M p n
      (φ.comp (TateModule.tateMap p (heckePicard (AlgebraicClosure ℚ) M q))))).val = _
  rw [arithmeticTateCharacterEquiv_hecke]
  exact finiteLatticeH1Equiv_hecke M (p ^ n) q (arithmeticTateCharacterEquiv M p n φ)

theorem arithmeticTateFiniteH1Equiv_hecke_restrict (q : ℕ) [Fact q.Prime]
    (φ : TateModule p (Pic0 (AlgebraicClosure ℚ)
      (functionFieldOver (Gamma1 M) (AlgebraicClosure ℚ))) →ₗ[ℤ_[p]] ZMod (p ^ n)) :
    arithmeticTateFiniteH1Equiv M p n
        (φ.comp (TateModule.tateMap p (heckePicard (AlgebraicClosure ℚ) M q))) =
      finiteParabolicHecke M (p ^ n) q (arithmeticTateFiniteH1Equiv M p n φ) :=
  Subtype.ext (arithmeticTateFiniteH1Equiv_hecke M p n q φ)

end
end Dubon2026.SourceFunctionField.GammaOne

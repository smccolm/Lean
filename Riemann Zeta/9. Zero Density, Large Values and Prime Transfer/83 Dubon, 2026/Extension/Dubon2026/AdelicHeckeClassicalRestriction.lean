import Dubon2026.AdelicHeckeRationalRepresentatives

/-! # Exact classical Hecke normalization of the original finite-adelic trace -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm BigOperators

/-- The actual full-function right representation restricted to the original finite adelic embedding. -/
def adelicFunctionFiniteRepresentation :
    Representation ℂ (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (RationalAdelicGL2 → ℂ) :=
  (TannakaDuality.FiniteGroup.rightRegular (k := ℂ) (G := RationalAdelicGL2)).comp
    rationalAdelicFiniteGL2Embedding

/-- Each literal finite-adelic Hecke summand is its original classical slash summand with the same genuine determinant-root scalar. -/
theorem canonicalAdelic_HeckeTerm_real {N p : ℕ} [NeZero N] [NeZero p] {k : ℤ}
    (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hpN : p.Coprime N)
    (x : Option (ZMod p)) (g : SL(2, ℝ)) :
    canonicalAdelicGL2CuspLift N k F (adelicRealSL2Embedding g *
      rationalAdelicFiniteGL2Embedding
        ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN x)).val⁻¹ *
          (finiteAdelicHeckeDiagonal p)⁻¹)) =
      (Real.sqrt (p : ℝ) : ℂ) ^ (2 - k) *
        realWeightLift k (((F : ℍ → ℂ) ∣[k] heckeTriangularMatrix 1 p 0) ∣[k]
          mapGL ℝ (heckeUpperRepresentative p N hpN x).val) g := by
  have h := canonicalAdelic_rational_translate_real F (positiveHeckeRationalRepresentative N p hpN x) g
  rw [positiveHeckeRationalRepresentative_finite, _root_.mul_inv_rev,
    positiveHeckeRationalRepresentative_root, positiveHeckeRationalRepresentative_real,
    SlashAction.slash_mul] at h
  exact h

/-- The actual finite-adelic trace on the original cusp lift restricts to the literal classical good-prime Hecke operator with exactly sqrt(p)^(2-k). -/
theorem canonicalAdelic_HeckeTrace_real {N p : ℕ} [NeZero N] [NeZero p] {k : ℤ}
    (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hp : p.Prime) (hpN : p.Coprime N)
    (g : SL(2, ℝ)) :
    finiteAdelicHeckeTrace adelicFunctionFiniteRepresentation N p hpN
      (canonicalAdelicGL2CuspLift N k F) (adelicRealSL2Embedding g) =
        (Real.sqrt (p : ℝ) : ℂ) ^ (2 - k) *
          realWeightLift k (classicalHeckeFunction N k p F) g := by
  simp only [finiteAdelicHeckeTrace, LinearMap.sum_apply]
  change (∑ x : Option (ZMod p),
    TannakaDuality.FiniteGroup.rightRegular
      (rationalAdelicFiniteGL2Embedding
        ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN x)).val⁻¹ *
          (finiteAdelicHeckeDiagonal p)⁻¹)) (canonicalAdelicGL2CuspLift N k F))
      (adelicRealSL2Embedding g) = _
  simp only [Finset.sum_apply, TannakaDuality.FiniteGroup.rightRegular_apply]
  simp_rw [canonicalAdelic_HeckeTerm_real F hpN]
  rw [← Finset.mul_sum]
  congr 1
  have h := congrArg (fun u : ℍ → ℂ => realWeightLiftLinear k u g) (heckeUpperTrace_eq hp hpN F)
  simp only [map_sum, Finset.sum_apply] at h
  exact h

end
end Dubon2026

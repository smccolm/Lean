import Dubon2026.FinitePlaceHeckeRadialDeterminant
import Dubon2026.FinitePlaceDirichletDeterminant

/-! # The inverse-prime determinant and genuine Dirichlet value of each original Hecke summand -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Every actual original Hecke representative has determinant equal to the original prime unit inverse. -/
theorem finitePlaceHeckeCoset_det (N p : ℕ) [NeZero N] [NeZero p]
    (hpN : p.Coprime N) (v : HeightOneSpectrum ℤ) (i : Option (ZMod p)) :
    GeneralLinearGroup.det (GeneralLinearGroup.map (finiteAdelePlace v)
      ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
        (finiteAdelicHeckeDiagonal p)⁻¹)) = (finitePlacePrimeUnit p v)⁻¹ := by
  have h := finitePlaceHeckeRadialMatrix_det N p hpN v 0 i
  simp only [finitePlaceHeckeRadialMatrix, pow_zero, one_mul, map_mul, map_inv,
    GeneralLinearGroup.det_scalar, Fintype.card_fin, zero_add, pow_one] at h
  simp only [map_mul, map_inv]
  apply mul_left_cancel (a := (finitePlacePrimeUnit p v) ^ 2)
  calc
    _ = finitePlacePrimeUnit p v := h
    _ = _ := by simp [pow_two, mul_assoc]

/-- The actual unramified Dirichlet determinant character has the inverse original prime value on each genuine Hecke coset. -/
theorem finitePlaceDirichletDeterminant_hecke {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (N p : ℕ) [NeZero N] [NeZero p]
    (hp : p.Prime) (hpN : p.Coprime N) (hpD : p.Coprime D) (i : Option (ZMod p)) :
    finitePlaceDirichletDeterminant χ (rationalPrimePlace p hp)
      (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
        ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
          (finiteAdelicHeckeDiagonal p)⁻¹)) = (χ (p : ZMod D))⁻¹ := by
  rw [finitePlaceDirichletDeterminant_apply, finitePlaceHeckeCoset_det]
  change finiteIdeleDirichletCharacter χ
    (finiteAdeleLocalUnitHom (rationalPrimePlace p hp) ((finitePlacePrimeUnit p _)⁻¹)) = _
  rw [map_inv, map_inv]
  exact congrArg Inv.inv (finiteIdeleDirichletCharacter_uniformizer χ p hp hpD)

/-- For an actual quadratic character the inverse orientation of the original Hecke cosets gives precisely the original quadratic prime value. -/
theorem finitePlaceDirichletDeterminant_hecke_quadratic {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hχ : χ.IsQuadratic) (N p : ℕ) [NeZero N] [NeZero p]
    (hp : p.Prime) (hpN : p.Coprime N) (hpD : p.Coprime D) (i : Option (ZMod p)) :
    finitePlaceDirichletDeterminant χ (rationalPrimePlace p hp)
      (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p hp))
        ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
          (finiteAdelicHeckeDiagonal p)⁻¹)) = χ (p : ZMod D) := by
  rw [finitePlaceDirichletDeterminant_hecke χ N p hp hpN hpD i]
  rcases hχ (p : ZMod D) with hz | ho | hm
  · rw [hz, _root_.inv_zero]
  · rw [ho, inv_one]
  · rw [hm, inv_neg, inv_one]

end
end Dubon2026

import Dubon2026.FinitePlaceRadialCoefficient
import Dubon2026.RadialHeckeFiniteSum
import Dubon2026.FinitePlaceHeckeSymmetric

/-! # Exact radial trace identities for the original intrinsic local Hecke operator -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (hpN : p.Coprime N)
variable (ρ : Representation ℂ (GeneralLinearGroup (Fin 2) (((rationalPrimePlace p (Fact.out : p.Prime))).adicCompletion ℚ)) V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hscalar : ∀ u z, ρ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (x y : V)
    (hx : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val x = x)
    (hy : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val y = y)

include hρ hscalar hx hy

/-- Translating the genuine p+1-term Hecke trace gives one preceding and p succeeding original radial coefficients. -/
theorem finitePlaceHeckeTrace_radial_successor (n : ℕ) :
    inner ℂ x (ρ ((GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime))) (finiteAdelicHeckeDiagonal p)) ^ (n + 1)) (@finitePlaceHeckeTrace V inferInstance inferInstance N p inferInstance inferInstance inferInstance hpN ρ y)) =
      @finitePlaceRadialCoefficient V inferInstance inferInstance p inferInstance inferInstance ρ x y n +
        (p : ℂ) * @finitePlaceRadialCoefficient V inferInstance inferInstance p inferInstance inferInstance ρ x y (n + 2) := by
  have hterm (i : Option (ZMod p)) :
      inner ℂ x (ρ ((GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime))) (finiteAdelicHeckeDiagonal p)) ^ (n + 1))
        (ρ (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
          ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
            (finiteAdelicHeckeDiagonal p)⁻¹)) y)) =
      inner ℂ x (ρ (finitePlaceHeckeRadialMatrix N p hpN (rationalPrimePlace p (Fact.out : p.Prime)) (n + 1) i) y) := by
    simp only [finitePlaceHeckeRadialMatrix, finitePlaceHeckeGamma, map_mul, map_inv,
      Module.End.mul_apply, hscalar]
  calc
    _ = ∑ i : Option (ZMod p),
        inner ℂ x (ρ (finitePlaceHeckeRadialMatrix N p hpN (rationalPrimePlace p (Fact.out : p.Prime)) (n + 1) i) y) := by
      simp only [finitePlaceHeckeTrace, LinearMap.sum_apply, map_sum, inner_sum]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = _ := hecke_option_sum_one_backward p _ _ _
      (finitePlaceHeckeRadialMatrix_backward_coefficient N p hpN ρ x y hscalar n)
      (finitePlaceHeckeRadialMatrix_forward_coefficient N p hpN ρ hρ x y hx hy (n + 1) none
        (by simp))
      (fun a ha => finitePlaceHeckeRadialMatrix_forward_coefficient N p hpN ρ hρ x y hx hy
        (n + 1) (some a) (by simpa using ha))

/-- At the original generator radius the genuine Hecke trace has exactly p+1 equal spherical coefficients. -/
theorem finitePlaceHeckeTrace_radial_zero :
    inner ℂ x (@finitePlaceHeckeTrace V inferInstance inferInstance N p inferInstance inferInstance inferInstance hpN ρ y) =
      ((p : ℂ) + 1) * @finitePlaceRadialCoefficient V inferInstance inferInstance p inferInstance inferInstance ρ x y 1 := by
  rw [← finitePlaceHeckeTrace_symmetric N p hpN ρ hρ hscalar x y hx hy]
  have he := unitary_coset_trace_inner_left ρ hρ
    (fun i => GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
      (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val)
    (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime))) (finiteAdelicHeckeDiagonal p)) x y (fun i => hy
      (finiteAdelicLevelAt N (rationalPrimePlace p (Fact.out : p.Prime)) (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i))))
  simpa only [finitePlaceHeckeTrace, LinearMap.sum_apply, map_mul, map_inv,
    Fintype.card_option, ZMod.card, Nat.cast_add, Nat.cast_one,
    finitePlaceRadialCoefficient, pow_one] using he

end
end Dubon2026

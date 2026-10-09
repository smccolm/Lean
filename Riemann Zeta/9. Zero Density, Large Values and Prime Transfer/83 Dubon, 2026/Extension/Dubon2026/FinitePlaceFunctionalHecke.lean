import Dubon2026.FinitePlaceFunctionalRadial
import Dubon2026.RadialHeckeFiniteSum
import Dubon2026.FinitePlaceHeckeSwap

/-! # Genuine spherical Hecke recurrence without an assumed unitary model -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (ℓ : V →ₗ[ℂ] ℂ) (y : V)
    (hℓ : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)),
      ∀ x : V, ℓ (ρ k.val x) = ℓ x)
    (hy : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ k.val y = y)
    (hc : ∀ u x, ρ (GeneralLinearGroup.scalar (Fin 2) u) x = x)

include hℓ hy hc

/-- The original inverse Hecke diagonal has the same genuine spherical functional value as the original positive diagonal. -/
theorem finitePlaceFunctionalRadial_inverse :
    ℓ (ρ (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
      (finiteAdelicHeckeDiagonal p))⁻¹ y) = finitePlaceFunctionalRadial p ρ ℓ y 1 := by
  let v := rationalPrimePlace p (Fact.out : p.Prime)
  let k : finitePlaceGL2Gamma0 1 v := ⟨gl2CoordinateSwap, finitePlace_coordinateSwap_integral v⟩
  rw [finitePlaceHeckeDiagonal_inverse_swap]
  simpa only [finitePlaceFunctionalRadial, pow_one] using
    sphericalFunctional_scalar_double_coset ρ _ ℓ hℓ y hy _ _ (hc _) k k⁻¹

/-- The actual intrinsic Hecke trace at radius zero is precisely p+1 copies of the original first spherical functional value. -/
theorem finitePlaceFunctionalHecke_zero :
    ℓ (finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ y) =
      ((p : ℂ) + 1) * finitePlaceFunctionalRadial p ρ ℓ y 1 := by
  let v := rationalPrimePlace p (Fact.out : p.Prime)
  have hterm (i : Option (ZMod p)) :
      ℓ (ρ (GeneralLinearGroup.map (finiteAdelePlace v)
        ((integralGamma0FiniteGL2Hom 1 (heckeUpperRepresentative p 1 (Nat.coprime_one_right p) i)).val⁻¹ *
          (finiteAdelicHeckeDiagonal p)⁻¹)) y) = finitePlaceFunctionalRadial p ρ ℓ y 1 := by
    let γ := finiteAdelicLevelAt 1 v
      (integralGamma0FiniteGL2Hom 1 (heckeUpperRepresentative p 1 (Nat.coprime_one_right p) i))
    have he : GeneralLinearGroup.map (finiteAdelePlace v)
        ((integralGamma0FiniteGL2Hom 1 (heckeUpperRepresentative p 1 (Nat.coprime_one_right p) i)).val⁻¹ *
          (finiteAdelicHeckeDiagonal p)⁻¹) = (γ⁻¹).val *
          (GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p))⁻¹ := by
      rw [map_mul, map_inv, map_inv]
      rfl
    rw [he, map_mul, Module.End.mul_apply, hℓ γ⁻¹]
    exact finitePlaceFunctionalRadial_inverse p ρ ℓ y hℓ hy hc
  calc
    _ = ∑ i : Option (ZMod p),
        ℓ (ρ (GeneralLinearGroup.map (finiteAdelePlace v)
          ((integralGamma0FiniteGL2Hom 1 (heckeUpperRepresentative p 1 (Nat.coprime_one_right p) i)).val⁻¹ *
            (finiteAdelicHeckeDiagonal p)⁻¹)) y) := by
      simp only [finitePlaceHeckeTrace, LinearMap.sum_apply, map_sum]
      rfl
    _ = ∑ _i : Option (ZMod p), finitePlaceFunctionalRadial p ρ ℓ y 1 :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_option, ZMod.card,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- Every actual translated intrinsic Hecke sum has one preceding and p succeeding original spherical functional coefficients. -/
theorem finitePlaceFunctionalHecke_successor (n : ℕ) :
    ℓ (ρ ((GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
      (finiteAdelicHeckeDiagonal p)) ^ (n + 1))
      (finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ y)) =
    finitePlaceFunctionalRadial p ρ ℓ y n +
      (p : ℂ) * finitePlaceFunctionalRadial p ρ ℓ y (n + 2) := by
  let v := rationalPrimePlace p (Fact.out : p.Prime)
  have hterm (i : Option (ZMod p)) :
      ℓ (ρ ((GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p)) ^ (n + 1))
        (ρ (GeneralLinearGroup.map (finiteAdelePlace v)
          ((integralGamma0FiniteGL2Hom 1 (heckeUpperRepresentative p 1 (Nat.coprime_one_right p) i)).val⁻¹ *
            (finiteAdelicHeckeDiagonal p)⁻¹)) y)) =
      ℓ (ρ (finitePlaceHeckeRadialMatrix 1 p (Nat.coprime_one_right p) v (n + 1) i) y) := by
    simp only [finitePlaceHeckeRadialMatrix, finitePlaceHeckeGamma, map_mul, map_inv,
      Module.End.mul_apply, hc]
  calc
    _ = ∑ i : Option (ZMod p),
        ℓ (ρ (finitePlaceHeckeRadialMatrix 1 p (Nat.coprime_one_right p) v (n + 1) i) y) := by
      simp only [finitePlaceHeckeTrace, LinearMap.sum_apply, map_sum]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = _ := hecke_option_sum_one_backward p _ _ _
      (finitePlaceFunctionalRadial_backward p ρ ℓ y hc n)
      (finitePlaceFunctionalRadial_forward p ρ ℓ y hℓ hy (n + 1) none (by simp))
      (fun a ha => finitePlaceFunctionalRadial_forward p ρ ℓ y hℓ hy
        (n + 1) (some a) (by simpa using ha))

/-- An actual Hecke eigenvector yields the complete original radial recurrence through a genuine compact-invariant functional, without a unitary premise. -/
theorem finitePlaceFunctionalHecke_eigen_recurrence (μ : ℂ)
    (heigen : finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ y = μ • y) :
    μ * finitePlaceFunctionalRadial p ρ ℓ y 0 =
      ((p : ℂ) + 1) * finitePlaceFunctionalRadial p ρ ℓ y 1 ∧
    ∀ n, μ * finitePlaceFunctionalRadial p ρ ℓ y (n + 1) =
      finitePlaceFunctionalRadial p ρ ℓ y n +
        (p : ℂ) * finitePlaceFunctionalRadial p ρ ℓ y (n + 2) := by
  constructor
  · have he := finitePlaceFunctionalHecke_zero p ρ ℓ y hℓ hy hc
    rw [heigen, map_smul, smul_eq_mul] at he
    simpa only [finitePlaceFunctionalRadial, pow_zero, map_one, Module.End.one_apply] using he
  · intro n
    have he := finitePlaceFunctionalHecke_successor p ρ ℓ y hℓ hy hc n
    rw [heigen, map_smul, map_smul, smul_eq_mul] at he
    exact he

end
end Dubon2026

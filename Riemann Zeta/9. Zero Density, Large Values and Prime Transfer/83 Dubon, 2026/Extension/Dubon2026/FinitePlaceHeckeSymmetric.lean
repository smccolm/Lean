import Dubon2026.FinitePlaceHeckeSwap
import Dubon2026.FinitePlaceHeckeTrace
import Dubon2026.UnitaryCosetTracePairing

/-! # Symmetry of the genuine intrinsic local Hecke trace on its original fixed space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The original local Hecke trace is symmetric on genuine local level-fixed vectors in every original unitary action with trivial scalar character. -/
theorem finitePlaceHeckeTrace_symmetric (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N)
    (ρ : Representation ℂ
      (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hscalar : ∀ u x, ρ (GeneralLinearGroup.scalar (Fin 2) u) x = x)
    (x y : V)
    (hx : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val x = x)
    (hy : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val y = y) :
    inner ℂ (finitePlaceHeckeTrace N p hpN ρ x) y =
      inner ℂ x (finitePlaceHeckeTrace N p hpN ρ y) := by
  let v := rationalPrimePlace p (Fact.out : p.Prime)
  let r := fun i => GeneralLinearGroup.map (finiteAdelePlace v)
    (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val
  let d := GeneralLinearGroup.map (finiteAdelePlace v) (finiteAdelicHeckeDiagonal p)
  let j : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) := gl2CoordinateSwap
  have hd (z : V) : ρ d⁻¹ z = ρ j (ρ d (ρ j⁻¹ z)) := by
    dsimp only [d, j]
    rw [finitePlaceHeckeDiagonal_inverse_swap]
    simp only [map_mul, Module.End.mul_apply, hscalar]
  have hxj : ρ j⁻¹ x = x := by
    rw [show j⁻¹ = j from gl2CoordinateSwap_inv]
    exact hx ⟨j, finitePlace_coordinateSwap_good N p (Fact.out : p.Prime) hpN⟩
  have hyj : ρ j⁻¹ y = y := by
    rw [show j⁻¹ = j from gl2CoordinateSwap_inv]
    exact hy ⟨j, finitePlace_coordinateSwap_good N p (Fact.out : p.Prime) hpN⟩
  have he := unitary_coset_trace_symmetric ρ hρ r d j hd x y
    (fun i => hx (finiteAdelicLevelAt N v (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i))))
    (fun i => hy (finiteAdelicLevelAt N v (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)))) hxj hyj
  simpa only [finitePlaceHeckeTrace, LinearMap.sum_apply, map_mul, map_inv, r, d] using he

/-- Multiplication by an original real scalar preserves the exact symmetry pairing. -/
theorem real_scaled_linear_symmetric (T : Module.End ℂ V)
    (x y : V) (h : inner ℂ (T x) y = inner ℂ x (T y)) (c : ℝ) :
    inner ℂ (((c : ℂ) • T) x) y = inner ℂ x (((c : ℂ) • T) y) := by
  simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal, h]

end
end Dubon2026

import Dubon2026.FinitePlaceHeckeRadialCosets
import Dubon2026.UnitaryDoubleCosetCoefficient
import Dubon2026.FinitePlaceSphericalLevel

/-! # Original spherical coefficients of the exact radial Hecke representatives -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The matrix coefficient at an actual power of the original local Hecke diagonal. -/
def finitePlaceRadialCoefficient (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ
      (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (x y : V) (n : ℕ) : ℂ :=
  inner ℂ x (ρ ((GeneralLinearGroup.map
    (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
      (finiteAdelicHeckeDiagonal p)) ^ n) y)

variable (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (hpN : p.Coprime N)
variable (ρ : Representation ℂ (GeneralLinearGroup (Fin 2) (((rationalPrimePlace p (Fact.out : p.Prime))).adicCompletion ℚ)) V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (x y : V)
    (hx : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val x = x)
    (hy : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val y = y)

include hpN hρ hx hy in
omit [NeZero N] in
/-- Genuine integral left and right factors leave the original fixed-vector coefficient unchanged. -/
theorem finitePlace_integral_double_coset_coefficient (n : ℕ)
    (l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime))) :
    inner ℂ x (ρ (l.val * (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime))) (finiteAdelicHeckeDiagonal p)) ^ n * r.val) y) = @finitePlaceRadialCoefficient V inferInstance inferInstance p inferInstance inferInstance ρ x y n := by
  have hl : l.val⁻¹ ∈ finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)) := by
    rw [finitePlaceGL2Gamma0_good_eq_one N p (Fact.out : p.Prime) hpN]
    exact (finitePlaceGL2Gamma0 1 _).inv_mem l.property
  have hr : r.val ∈ finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)) := by
    rw [finitePlaceGL2Gamma0_good_eq_one N p (Fact.out : p.Prime) hpN]
    exact r.property
  have he := @unitary_scalar_double_coset_coefficient _ V inferInstance inferInstance inferInstance ρ hρ 1 l.val ((GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime))) (finiteAdelicHeckeDiagonal p)) ^ n) r.val
    (fun z => by simp) x y (hx ⟨_, hl⟩) (hy ⟨_, hr⟩)
  simpa only [one_mul, finitePlaceRadialCoefficient] using he

include hpN hρ hx hy in
/-- Every original nonzero-residue or Bezout term gives the exact next radial coefficient. -/
theorem finitePlaceHeckeRadialMatrix_forward_coefficient (n : ℕ)
    (i : Option (ZMod p)) (hi : i ≠ some 0) :
    inner ℂ x (ρ (finitePlaceHeckeRadialMatrix N p hpN (rationalPrimePlace p (Fact.out : p.Prime)) n i) y) =
      @finitePlaceRadialCoefficient V inferInstance inferInstance p inferInstance inferInstance ρ x y (n + 1) := by
  have hcoset : ∃ l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)),
      finitePlaceHeckeRadialMatrix N p hpN (rationalPrimePlace p (Fact.out : p.Prime)) n i = l.val * (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime))) (finiteAdelicHeckeDiagonal p)) ^ (n + 1) * r.val := by
    cases i with
    | none => exact finitePlaceHeckeRadial_none_forward N p hpN n
    | some a => exact finitePlaceHeckeRadial_some_forward N p hpN n a (by simpa using hi)
  obtain ⟨l, r, he⟩ := hcoset
  rw [he]
  exact finitePlace_integral_double_coset_coefficient N p hpN ρ hρ x y hx hy (n + 1) l r

/-- The genuine zero-residue term gives exactly the preceding radial coefficient when scalars act trivially. -/
theorem finitePlaceHeckeRadialMatrix_backward_coefficient
    (hscalar : ∀ u z, ρ (GeneralLinearGroup.scalar (Fin 2) u) z = z) (n : ℕ) :
    inner ℂ x (ρ (finitePlaceHeckeRadialMatrix N p hpN (rationalPrimePlace p (Fact.out : p.Prime)) (n + 1) (some 0)) y) =
      @finitePlaceRadialCoefficient V inferInstance inferInstance p inferInstance inferInstance ρ x y n := by
  rw [finitePlaceHeckeRadial_some_zero]
  simp only [map_mul, Module.End.mul_apply, hscalar, finitePlaceRadialCoefficient]

end
end Dubon2026

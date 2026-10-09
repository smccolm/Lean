import Dubon2026.SphericalRadialFormula
import Dubon2026.FinitePlaceRadialEigenRecurrence
import Dubon2026.FinitePlaceGL2Cartan

/-! # Exact spherical functions of genuine unitary local Hecke eigenvectors -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hscalar : ∀ u z, ρ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (v : V) (hv : inner ℂ v v = 1)
    (hfixed : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val v = v)
    (z : ℂ) (heigen : @finitePlaceHeckeTrace V inferInstance inferInstance 1 p
      inferInstance inferInstance inferInstance (Nat.coprime_one_right p) ρ v = ((Real.sqrt p : ℂ) * z) • v)

include hρ hscalar hv hfixed heigen

/-- The actual intrinsic local Hecke equation determines every radial coefficient of a genuine unit spherical vector. -/
theorem finitePlace_unit_spherical_radial_formula (n : ℕ) :
    @finitePlaceRadialCoefficient V inferInstance inferInstance p inferInstance inferInstance ρ v v n =
      sphericalChebyshevCoefficient p (Real.sqrt p) z n := by
  obtain ⟨hb, hc⟩ := finitePlaceHecke_radial_eigen_recurrence 1 p (Nat.coprime_one_right p)
    ρ hρ hscalar v v hfixed hfixed _ heigen
  have hr : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < p by exact_mod_cast (Fact.out : p.Prime).pos)).ne'
  have hs : (Real.sqrt p : ℂ) ^ 2 = (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ p by positivity)
  have he := radial_recurrence_chebyshev_formula p (Real.sqrt p) z hr hs _ hb hc n
  simpa only [finitePlaceRadialCoefficient, pow_zero, map_one, Module.End.one_apply, hv, one_mul] using he

/-- On every literal central-integral Cartan factorization, the genuine spherical coefficient is the exact same normalized radial expression. -/
theorem finitePlace_unit_spherical_cartan_formula
    (u : ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)ˣ) (n : ℕ)
    (l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime))) :
    inner ℂ v (ρ (GeneralLinearGroup.scalar (Fin 2) u * l.val *
      (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
        (finiteAdelicHeckeDiagonal p)) ^ n * r.val) v) =
      sphericalChebyshevCoefficient p (Real.sqrt p) z n := by
  have he := unitary_scalar_double_coset_coefficient ρ hρ
    (GeneralLinearGroup.scalar (Fin 2) u) l.val
    ((GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
      (finiteAdelicHeckeDiagonal p)) ^ n) r.val (hscalar u) v v
    (hfixed l⁻¹) (hfixed r)
  exact he.trans (finitePlace_unit_spherical_radial_formula p ρ hρ hscalar v hv hfixed z heigen n)

end
end Dubon2026

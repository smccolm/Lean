import Dubon2026.FinitePlaceHeckeRadialTrace

/-! # The original good-prime local Hecke trace is independent of the global level representatives -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- A genuine local intertwiner commutes with the literal finite Hecke coset sum. -/
theorem finitePlaceHeckeTrace_intertwines {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N)
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (σ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) W)
    (T : V →ₗ[ℂ] W) (hT : ∀ g x, T (ρ g x) = σ g (T x)) (x : V) :
    T (finitePlaceHeckeTrace N p hpN ρ x) = finitePlaceHeckeTrace N p hpN σ (T x) := by
  simp only [finitePlaceHeckeTrace, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl (fun i _ => hT _ x)

/-- At a good prime, the actual local coset trace formed from the original level equals the level-one intrinsic trace on every genuine integral-fixed vector. -/
theorem finitePlaceHeckeTrace_good_eq_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (hpN : p.Coprime N)
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hscalar : ∀ u z, ρ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (y : V) (hy : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val y = y) :
    finitePlaceHeckeTrace N p hpN ρ y = finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ y := by
  have hK := finitePlaceGL2Gamma0_good_eq_one N p (Fact.out : p.Prime) hpN
  have hyN : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val y = y := by
    intro g
    exact hy ⟨g.val, hK ▸ g.property⟩
  have hNy (g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime))) :
      ρ g.val (finitePlaceHeckeTrace N p hpN ρ y) = finitePlaceHeckeTrace N p hpN ρ y :=
    finitePlaceHeckeTrace_level_fixed N p hpN ρ y hyN ⟨g.val, hK.symm ▸ g.property⟩
  have h1y (g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime))) :
      ρ g.val (finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ y) =
        finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ y :=
    finitePlaceHeckeTrace_level_fixed 1 p (Nat.coprime_one_right p) ρ y hy g
  let z := finitePlaceHeckeTrace N p hpN ρ y - finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ y
  have hz1 : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val z = z := by
    intro g
    dsimp only [z]
    rw [map_sub, hNy, h1y]
  have hzN : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val z = z := by
    intro g
    exact hz1 ⟨g.val, hK ▸ g.property⟩
  have he := (finitePlaceHeckeTrace_radial_zero N p hpN ρ hρ hscalar z y hzN hyN).trans
    (finitePlaceHeckeTrace_radial_zero 1 p (Nat.coprime_one_right p) ρ hρ hscalar z y hz1 hy).symm
  have hz : inner ℂ z z = 0 := by
    change inner ℂ z (finitePlaceHeckeTrace N p hpN ρ y - finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ y) = 0
    rw [inner_sub_right, he, sub_self]
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp hz)

end
end Dubon2026

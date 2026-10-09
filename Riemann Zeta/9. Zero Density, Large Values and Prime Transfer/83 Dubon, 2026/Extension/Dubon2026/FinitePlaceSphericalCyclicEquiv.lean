import Dubon2026.FinitePlaceSphericalUniqueness
import Dubon2026.GramDenseFamilyEquiv

/-! # Genuine completed cyclic spherical representation uniqueness -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (σ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) W)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hσ : ∀ g x y, inner ℂ (σ g x) (σ g y) = inner ℂ x y)
    (hcρ : ∀ u z, ρ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (hcσ : ∀ u z, σ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (v : V) (w : W) (hv : inner ℂ v v = 1) (hw : inner ℂ w w = 1)
    (hvK : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val v = v)
    (hwK : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), σ g.val w = w)
    (z : ℂ)
    (hzv : @finitePlaceHeckeTrace V inferInstance inferInstance 1 p inferInstance inferInstance
      inferInstance (Nat.coprime_one_right p) ρ v = ((Real.sqrt p : ℂ) * z) • v)
    (hzw : @finitePlaceHeckeTrace W inferInstance inferInstance 1 p inferInstance inferInstance
      inferInstance (Nat.coprime_one_right p) σ w = ((Real.sqrt p : ℂ) * z) • w)

include hρ hσ hcρ hcσ hv hw hvK hwK hzv hzw

/-- The actual dense cyclic spherical representations with the same genuine normalized Hecke eigenvalue are related by the completed original Gram isometry. -/
def finitePlaceSphericalCyclicEquiv
    (hvcyclic : (Submodule.span ℂ (Set.range (fun g => ρ g v))).topologicalClosure = ⊤)
    (hwcyclic : (Submodule.span ℂ (Set.range (fun g => σ g w))).topologicalClosure = ⊤) : V ≃ₗᵢ[ℂ] W :=
  gramDenseFamilyEquiv (fun g => ρ g v) (fun g => σ g w)
    (finitePlace_unit_spherical_orbit_gram p ρ σ hρ hσ hcρ hcσ v w hv hw hvK hwK z hzv hzw)
    hvcyclic hwcyclic

/-- The completed actual spherical equivalence sends every original group-orbit vector to its prescribed original counterpart. -/
theorem finitePlaceSphericalCyclicEquiv_orbit
    (hvcyclic : (Submodule.span ℂ (Set.range (fun g => ρ g v))).topologicalClosure = ⊤)
    (hwcyclic : (Submodule.span ℂ (Set.range (fun g => σ g w))).topologicalClosure = ⊤)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    finitePlaceSphericalCyclicEquiv p ρ σ hρ hσ hcρ hcσ v w hv hw hvK hwK z hzv hzw hvcyclic hwcyclic (ρ g v) = σ g w :=
  gramDenseFamilyEquiv_family _ _ _ hvcyclic hwcyclic g

/-- The completed original spherical equivalence intertwines every genuine local group operator on every vector of the original Hilbert space. -/
theorem finitePlaceSphericalCyclicEquiv_intertwines
    (hvcyclic : (Submodule.span ℂ (Set.range (fun g => ρ g v))).topologicalClosure = ⊤)
    (hwcyclic : (Submodule.span ℂ (Set.range (fun g => σ g w))).topologicalClosure = ⊤)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) (x : V) :
    finitePlaceSphericalCyclicEquiv p ρ σ hρ hσ hcρ hcσ v w hv hw hvK hwK z hzv hzw hvcyclic hwcyclic (ρ g x) =
      σ g (finitePlaceSphericalCyclicEquiv p ρ σ hρ hσ hcρ hcσ v w hv hw hvK hwK z hzv hzw hvcyclic hwcyclic x) := by
  exact gramDenseFamilyEquiv_intertwines (fun a => ρ a v) (fun a => σ a w)
    (finitePlace_unit_spherical_orbit_gram p ρ σ hρ hσ hcρ hcσ v w hv hw hvK hwK z hzv hzw)
    hvcyclic hwcyclic ((ρ g).isometryOfInner (hρ g)).toContinuousLinearMap
    ((σ g).isometryOfInner (hσ g)).toContinuousLinearMap (fun a => g * a)
    (fun a => by change ρ g (ρ a v) = ρ (g * a) v; rw [map_mul, Module.End.mul_apply])
    (fun a => by change σ g (σ a w) = σ (g * a) w; rw [map_mul, Module.End.mul_apply]) x

end
end Dubon2026

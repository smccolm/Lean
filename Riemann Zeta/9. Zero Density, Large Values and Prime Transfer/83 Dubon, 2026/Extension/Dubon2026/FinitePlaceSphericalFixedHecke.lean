import Dubon2026.FinitePlaceHeckeLevelIndependence
import Mathlib.LinearAlgebra.Trace

/-! # The actual Hecke endomorphism of the genuine local spherical fixed space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)

/-- The literal integral-fixed vectors in the original local representation. -/
def finitePlaceSphericalFixedSpace : Submodule ℂ V :=
  Representation.invariants (ρ.comp (finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime))).subtype)

/-- The genuine level-one coset trace restricted to its actual invariant spherical fixed space. -/
def finitePlaceSphericalFixedHecke : Module.End ℂ (finitePlaceSphericalFixedSpace p ρ) :=
  (finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ).restrict (by
    intro x hx
    exact finitePlaceHeckeTrace_level_fixed 1 p (Nat.coprime_one_right p) ρ x hx)

/-- The normalized trace of the actual local spherical Hecke endomorphism; applications must establish the dimension of its actual fixed space. -/
def finitePlaceNormalizedSphericalTrace : ℂ :=
  LinearMap.trace ℂ (finitePlaceSphericalFixedSpace p ρ) (finitePlaceSphericalFixedHecke p ρ) / (Real.sqrt p : ℂ)

/-- The actual fixed-space endomorphism retains the literal original local coset sum. -/
theorem finitePlaceSphericalFixedHecke_val (x : finitePlaceSphericalFixedSpace p ρ) :
    (finitePlaceSphericalFixedHecke p ρ x).val =
      finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ x.val := rfl

/-- The trace on the original fixed space is invariant under every genuine linear equivariant identification of fixed spaces. -/
theorem finitePlaceSphericalFixedHecke_trace_conj {W : Type*} [AddCommGroup W] [Module ℂ W]
    (e : finitePlaceSphericalFixedSpace p ρ ≃ₗ[ℂ] W) :
    LinearMap.trace ℂ W (e.conj (finitePlaceSphericalFixedHecke p ρ)) =
      LinearMap.trace ℂ (finitePlaceSphericalFixedSpace p ρ) (finitePlaceSphericalFixedHecke p ρ) :=
  LinearMap.trace_conj' _ _

end
end Dubon2026

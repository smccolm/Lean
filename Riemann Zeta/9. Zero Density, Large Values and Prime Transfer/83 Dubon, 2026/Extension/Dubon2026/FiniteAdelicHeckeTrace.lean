import Dubon2026.FiniteAdelicHeckeConjugation
import Dubon2026.RepresentationCosetTrace

/-! # Actual finite-adelic Hecke traces from the proved original coset representatives -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix
open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The literal finite sum of original finite-adelic right operators over the proved classical Hecke representatives. -/
def finiteAdelicHeckeTrace
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) V)
    (N p : ℕ) [NeZero N] [NeZero p] (hpN : p.Coprime N) : Module.End ℂ V :=
  ∑ i : Option (ZMod p), ρ ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
    (finiteAdelicHeckeDiagonal p)⁻¹)

/-- The genuine Hecke conjugation identity makes the original diagonal translate fixed by the actual Hecke upper subgroup. -/
theorem finiteAdelicHecke_diagonal_fixed
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) V)
    (N p : ℕ) [NeZero p] [Fact p.Prime] (v : V)
    (hv : ∀ g : finiteAdeleGL2Gamma0 N, ρ g.val v = v)
    (h : finiteAdeleGL2Gamma0 N) (hh : h ∈ finiteAdelicHeckeUpper N p) :
    ρ h.val (ρ (finiteAdelicHeckeDiagonal p)⁻¹ v) = ρ (finiteAdelicHeckeDiagonal p)⁻¹ v := by
  have hm := finiteAdelicHeckeUpper_conjugate_mem N p h hh
  have he := congrArg (ρ (finiteAdelicHeckeDiagonal p)⁻¹) (hv ⟨_, hm⟩)
  rw [← Module.End.mul_apply, ← map_mul] at he
  have hg : (finiteAdelicHeckeDiagonal p)⁻¹ *
      (finiteAdelicHeckeDiagonal p * h.val * (finiteAdelicHeckeDiagonal p)⁻¹) =
      h.val * (finiteAdelicHeckeDiagonal p)⁻¹ := by group
  rw [hg, map_mul, Module.End.mul_apply] at he
  exact he

/-- Summing over the proved full finite-adelic coset quotient makes the actual original Hecke trace fixed by the entire original level subgroup. -/
theorem finiteAdelicHeckeTrace_level_fixed
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) V)
    (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (hpN : p.Coprime N) (v : V)
    (hv : ∀ g : finiteAdeleGL2Gamma0 N, ρ g.val v = v) (g : finiteAdeleGL2Gamma0 N) :
    ρ g.val (finiteAdelicHeckeTrace ρ N p hpN v) = finiteAdelicHeckeTrace ρ N p hpN v := by
  have h := representation_coset_trace_invariant (ρ.comp (finiteAdeleGL2Gamma0 N).subtype)
    (finiteAdelicHeckeUpper N p) (ρ (finiteAdelicHeckeDiagonal p)⁻¹ v)
    (finiteAdelicHecke_diagonal_fixed ρ N p v hv)
    (fun i => (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i))⁻¹)
    (finiteAdelicHeckeUpperCosetEquiv N p hpN) (fun _ => rfl) g
  change ρ g.val (∑ i : Option (ZMod p),
      ρ (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹
        (ρ (finiteAdelicHeckeDiagonal p)⁻¹ v)) =
    ∑ i : Option (ZMod p),
      ρ (integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹
        (ρ (finiteAdelicHeckeDiagonal p)⁻¹ v) at h
  simp_rw [← Module.End.mul_apply, ← map_mul] at h
  simpa only [finiteAdelicHeckeTrace, LinearMap.sum_apply] using h

/-- Every genuine intertwiner of the original finite-adelic representation commutes with its actual finite Hecke trace. -/
theorem finiteAdelicHeckeTrace_intertwiner
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) V)
    (N p : ℕ) [NeZero N] [NeZero p] (hpN : p.Coprime N) (A : Module.End ℂ V)
    (hA : ∀ g v, A (ρ g v) = ρ g (A v)) (v : V) :
    A (finiteAdelicHeckeTrace ρ N p hpN v) = finiteAdelicHeckeTrace ρ N p hpN (A v) := by
  simp only [finiteAdelicHeckeTrace, LinearMap.sum_apply, map_sum, hA]

/-- Every actual equivariant linear map intertwines the same original finite-adelic Hecke trace on its source and target representations. -/
theorem finiteAdelicHeckeTrace_intertwines {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) V)
    (σ : Representation ℂ (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) W)
    (N p : ℕ) [NeZero N] [NeZero p] (hpN : p.Coprime N) (E : V →ₗ[ℂ] W)
    (hE : ∀ g v, E (ρ g v) = σ g (E v)) (v : V) :
    E (finiteAdelicHeckeTrace ρ N p hpN v) = finiteAdelicHeckeTrace σ N p hpN (E v) := by
  simp only [finiteAdelicHeckeTrace, LinearMap.sum_apply, map_sum, hE]

end
end Dubon2026

import Dubon2026.SourceCurveFiniteRankTraceLinear

/-! DUB-17/18 -> reverse modular genus inequality -> canonical degree -> global
residues -> residue/trace compatibility. This is the actual projected
commutator used for the Tate residue. Its finite rank is derived from the two
principal-part images, the local pole-space input to be supplied next. -/

noncomputable section

namespace Dubon2026.SourceCurve.ResidueTrace

open LinearMap Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The projected multiplication commutator whose trace defines the local residue. -/
def tateComm (p φ ψ : V →ₗ[K] V) : V →ₗ[K] V :=
  p ∘ₗ φ ∘ₗ p ∘ₗ ψ - p ∘ₗ ψ ∘ₗ p ∘ₗ φ

/-- The projected commutator takes values in the projector's image. -/
theorem tateComm_mem_range (p φ ψ : V →ₗ[K] V) (x : V) :
    tateComm p φ ψ x ∈ LinearMap.range p :=
  sub_mem (mem_range_self p _) (mem_range_self p _)

/-- The same commutator as an endomorphism of the projector's image. -/
def tateCommRestrict (p φ ψ : V →ₗ[K] V) :
    LinearMap.range p →ₗ[K] LinearMap.range p :=
  (tateComm p φ ψ).restrict (fun x _ => tateComm_mem_range p φ ψ x)

/-- Evaluation of the restricted commutator retains its literal value. -/
theorem tateCommRestrict_apply (p φ ψ : V →ₗ[K] V) (x : LinearMap.range p) :
    (tateCommRestrict p φ ψ x : V) = tateComm p φ ψ x := rfl

/-- Commuting multiplications factor the commutator through principal parts. -/
theorem tateComm_eq_of_commute {p φ ψ : V →ₗ[K] V}
    (hcomm : φ ∘ₗ ψ = ψ ∘ₗ φ) (x : V) :
    tateComm p φ ψ x = p (ψ (φ x - p (φ x))) - p (φ (ψ x - p (ψ x))) := by
  have h : φ (ψ x) = ψ (φ x) := DFunLike.congr_fun hcomm x
  simp only [tateComm, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, h]
  abel

/-- The trace is taken on the actual finite-dimensional commutator image. -/
def tateCommTrace (p φ ψ : V →ₗ[K] V) : K :=
  finrankTrace (tateCommRestrict p φ ψ)

/-- Finite principal-part images imply finite rank of the actual projected commutator. -/
theorem finite_range_tateCommRestrict (p φ ψ : V →ₗ[K] V)
    (hcomm : φ ∘ₗ ψ = ψ ∘ₗ φ)
    [FiniteDimensional K
      (LinearMap.range ((LinearMap.id - p) ∘ₗ φ ∘ₗ (LinearMap.range p).subtype))]
    [FiniteDimensional K
      (LinearMap.range ((LinearMap.id - p) ∘ₗ ψ ∘ₗ (LinearMap.range p).subtype))] :
    FiniteDimensional K (LinearMap.range (tateCommRestrict p φ ψ)) := by
  let Rφ := LinearMap.range ((LinearMap.id - p) ∘ₗ φ ∘ₗ (LinearMap.range p).subtype)
  let Rψ := LinearMap.range ((LinearMap.id - p) ∘ₗ ψ ∘ₗ (LinearMap.range p).subtype)
  let S : Submodule K V := Rφ.map (p ∘ₗ ψ) ⊔ Rψ.map (p ∘ₗ φ)
  haveI : FiniteDimensional K (Rφ.map (p ∘ₗ ψ)) := Module.Finite.map _ _
  haveI : FiniteDimensional K (Rψ.map (p ∘ₗ φ)) := Module.Finite.map _ _
  haveI : FiniteDimensional K S := Submodule.finiteDimensional_sup _ _
  have hS : S ≤ LinearMap.range p := by
    refine sup_le ?_ ?_ <;> rintro y ⟨x, _, rfl⟩ <;> exact mem_range_self p _
  haveI : FiniteDimensional K (S.comap (LinearMap.range p).subtype) :=
    FiniteDimensional.of_injective (Submodule.comapSubtypeEquivOfLe hS).toLinearMap
      (Submodule.comapSubtypeEquivOfLe hS).injective
  refine Submodule.finiteDimensional_of_le (S₂ := S.comap (LinearMap.range p).subtype) ?_
  rintro y ⟨x, rfl⟩
  rw [Submodule.mem_comap, Submodule.subtype_apply, tateCommRestrict_apply,
    tateComm_eq_of_commute hcomm]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · exact ⟨φ x - p (φ x), ⟨x, rfl⟩, rfl⟩
  · exact ⟨ψ x - p (ψ x), ⟨x, rfl⟩, rfl⟩

end Dubon2026.SourceCurve.ResidueTrace

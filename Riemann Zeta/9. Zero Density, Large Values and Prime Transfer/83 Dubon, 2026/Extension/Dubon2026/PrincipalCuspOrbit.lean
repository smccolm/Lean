import Dubon2026.PrincipalCuspAction
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Finite-dimensional actual slash orbits at principal level -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

attribute [local instance] principalNormal

/-- The actual span of the finite congruence-group orbit of a principal-level cusp form. -/
def principalCuspOrbit (N : ℕ) (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    Submodule ℂ (CuspForm ((Gamma N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ (Set.range fun g => principalCuspRepresentation N k g f)

/-- The starting cusp form belongs to its genuine slash-orbit span. -/
theorem mem_principalCuspOrbit (N : ℕ) (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) : f ∈ principalCuspOrbit N k f := by
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

/-- Positive level makes this actual orbit span finite dimensional, without a dimension formula. -/
instance principalCuspOrbit_finiteDimensional (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    FiniteDimensional ℂ (principalCuspOrbit N k f) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/-- Every congruence-group operator preserves the actual orbit span. -/
theorem principalCuspOrbit_stable (N : ℕ) (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (g : SL(2, ℤ) ⧸ Gamma N) :
    principalCuspOrbit N k f ≤
      (principalCuspOrbit N k f).comap (principalCuspRepresentation N k g) := by
  apply Submodule.span_le.mpr
  rintro u ⟨h, rfl⟩
  change principalCuspRepresentation N k g (principalCuspRepresentation N k h f) ∈
    principalCuspOrbit N k f
  rw [← Module.End.mul_apply, ← map_mul]
  exact Submodule.subset_span ⟨g * h, rfl⟩

/-- Restrict the real slash representation to the finite-dimensional orbit of a given form. -/
def principalCuspOrbitRepresentation (N : ℕ) (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) :
    Representation ℂ (SL(2, ℤ) ⧸ Gamma N) (principalCuspOrbit N k f) :=
  (principalCuspRepresentation N k).subrepresentation (principalCuspOrbit N k f)
    (principalCuspOrbit_stable N k f)

/-- The restricted action still evaluates as the original slash action on the upper half-plane. -/
theorem principalCuspOrbitRepresentation_apply (N : ℕ) (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (γ : SL(2, ℤ))
    (v : principalCuspOrbit N k f) :
    ⇑(principalCuspOrbitRepresentation N k f (QuotientGroup.mk γ) v).val =
      ⇑v.val ∣[k] mapGL ℝ γ⁻¹ := rfl

/-- A Gamma0 form is an actual principal-level form by subgroup restriction. -/
def cuspGamma0ToPrincipal (N : ℕ) (k : ℤ) :
    CuspForm ((Gamma0 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma N).map (mapGL ℝ)) k where
  toFun := cuspRestrictSubgroup (Subgroup.map_mono (fun _ h => (Gamma_mem.mp h).2.2.1))
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- The principal-level inclusion keeps exactly the same analytic function. -/
theorem cuspGamma0ToPrincipal_apply (N : ℕ) (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) : ⇑(cuspGamma0ToPrincipal N k f) = f := rfl

/-- Ordinary restriction from Gamma0 to principal level is injective. -/
theorem cuspGamma0ToPrincipal_injective (N : ℕ) (k : ℤ) :
    Function.Injective (cuspGamma0ToPrincipal N k) := by
  intro f g h
  ext τ
  exact DFunLike.congr_fun h τ

end
end Dubon2026

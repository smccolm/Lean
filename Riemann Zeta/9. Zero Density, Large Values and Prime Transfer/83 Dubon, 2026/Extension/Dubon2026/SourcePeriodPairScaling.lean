import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> elliptic ramification and numerical genus -> analytic
j separates modular orbits. Only the actual period pairs (tau,1) and
their nonzero scalar multiples are needed for the lattice identity.
The independence proofs are explicit; no elliptic-curve uniformization
or torsion structure is imported from the external definition package.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_PeriodPair_Uniformization.
-/
namespace Dubon2026.SourceFunctionField.PeriodLattice
noncomputable section
open UpperHalfPlane
variable (L : PeriodPair)

theorem linearIndependent_coe_upperHalfPlane_one (τ : ℍ) :
    LinearIndependent ℝ ![(τ : ℂ), (1 : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  have him : (a • (τ : ℂ) + b • (1 : ℂ)).im = 0 := by rw [h]; simp
  simp only [Complex.add_im, Complex.smul_im, Complex.one_im, smul_zero, add_zero] at him
  have ha : a = 0 := (mul_eq_zero.mp him).resolve_right (ne_of_gt τ.im_pos)
  subst ha
  simp only [zero_smul, zero_add, smul_eq_zero, one_ne_zero, or_false] at h
  exact ⟨rfl, h⟩

/-- The actual period pair consisting of an upper-half-plane point and one. -/
def ofTau (τ : ℍ) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := linearIndependent_coe_upperHalfPlane_one τ

theorem ofTau_ω₁ (τ : ℍ) : (ofTau τ).ω₁ = (τ : ℂ) := rfl
theorem ofTau_ω₂ (τ : ℍ) : (ofTau τ).ω₂ = 1 := rfl

theorem ofTau_lattice (τ : ℍ) :
    (ofTau τ).lattice = Submodule.span ℤ {(τ : ℂ), 1} := rfl

section Scale

variable (α : ℂˣ)

theorem scale_indep : LinearIndependent ℝ ![(α : ℂ) * L.ω₁, (α : ℂ) * L.ω₂] := by
  have h : ![(α : ℂ) * L.ω₁, (α : ℂ) * L.ω₂] = (LinearMap.mulLeft ℝ (α : ℂ)) ∘ ![L.ω₁, L.ω₂] := by
    funext i; fin_cases i <;> simp
  rw [h]
  exact L.indep.map' (LinearMap.mulLeft ℝ (α : ℂ))
    (LinearMap.ker_eq_bot_of_injective (mul_right_injective₀ α.ne_zero))

/-- Multiply both genuine periods by the given nonzero complex scalar. -/
def scale : PeriodPair where
  ω₁ := (α : ℂ) * L.ω₁
  ω₂ := (α : ℂ) * L.ω₂
  indep := scale_indep L α

theorem scale_ω₁ : (scale L α).ω₁ = (α : ℂ) * L.ω₁ := rfl
theorem scale_ω₂ : (scale L α).ω₂ = (α : ℂ) * L.ω₂ := rfl

end Scale
end
end Dubon2026.SourceFunctionField.PeriodLattice

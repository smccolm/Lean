import Dubon2026.FiniteArithmeticCongruenceTrivial
import Mathlib.Tactic.Group

/-! # Actual smallness from a large residue-prime congruence level

This is the direct finite-stabilizer route for DUB-17's unitary auxiliary
modules. Definiteness and compactness provide the finite arithmetic
groups. Their faithful local congruence images and the original number-
field matrix dimension prove triviality without an assumed torsion-free
local subgroup. No assertion about all local torsion is needed here.
-/

namespace Dubon2026

noncomputable section

open Matrix IsLocalRing

/-- Large residue-prime congruence and finite arithmetic stabilizers imply actual smallness. -/
theorem smallLevel_of_large_residue_congruence
    {K R L ι A G : Type*} [Field K] [NumberField K]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing L]
    [Fintype ι] [DecidableEq ι] [Group A] [Group G]
    (p : ℕ) (hp : p.Prime) [CharP (ResidueField R) p]
    (hlarge : Fintype.card ι * Module.finrank ℚ K < p - 1)
    (φ : R →+* L) (hφ : Function.Injective φ)
    (ρ : A →* GeneralLinearGroup ι K) (hρ : Function.Injective ρ)
    (f : A →* G) (U : Subgroup G) (π : G →* GeneralLinearGroup ι L)
    (hfaithful : Function.Injective (π.comp f))
    (hfinite : ∀ g : G, Finite (U.comap ((MulAut.conj g⁻¹).toMonoidHom.comp f)))
    (hlevel : U.map π ≤ (MatrixCongruenceKernel (ι := ι) (maximalIdeal R)).map
      (GeneralLinearGroup.map φ)) :
    ∀ (g : G) (u : U), g * u.val * g⁻¹ ∈ f.range → u = 1 := by
  intro g u hu
  obtain ⟨a, ha⟩ := hu
  let H := U.comap ((MulAut.conj g⁻¹).toMonoidHom.comp f)
  letI : Finite H := hfinite g
  let τ : H →* GeneralLinearGroup ι L :=
    (MulAut.conj (π g)⁻¹).toMonoidHom.comp ((π.comp f).comp H.subtype)
  have hτ : Function.Injective τ := by
    intro x y h
    apply Subtype.ext
    exact hfaithful ((MulAut.conj (π g)⁻¹).injective h)
  have hτlevel : τ.range ≤ (MatrixCongruenceKernel (ι := ι) (maximalIdeal R)).map
      (GeneralLinearGroup.map φ) := by
    rintro _ ⟨x, rfl⟩
    apply hlevel
    refine ⟨(MulAut.conj g⁻¹) (f x.val), x.property, ?_⟩
    change π (g⁻¹ * f x.val * (g⁻¹)⁻¹) = (π g)⁻¹ * π (f x.val) * ((π g)⁻¹)⁻¹
    simp only [map_mul, map_inv]
  have htrivial := finiteArithmeticCongruence_trivial p hp hlarge φ hφ
    (ρ.comp H.subtype) (hρ.comp Subtype.val_injective) τ hτ hτlevel
  have hconj : g⁻¹ * f a * g = u.val := by rw [ha]; group
  have haH : a ∈ H := by
    change g⁻¹ * f a * (g⁻¹)⁻¹ ∈ U
    simpa only [inv_inv, hconj] using u.property
  have haone : a = 1 := congrArg Subtype.val (htrivial ⟨a, haH⟩)
  apply Subtype.ext
  change u.val = 1
  rw [← hconj, haone, map_one]
  group

end
end Dubon2026

import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The H2 annihilator after an actual finite effacement

For an effaced H2 class, the original H1-to-H2 connecting map gives a lift.
H1 duality and the dual H0-to-H1 exact sequence then force that lift to come
from the middle module. This is the remaining local H0/H2 endpoint required
in DUB-17's global-duality/Selmer chain, without a higher-degree hypothesis.
-/

namespace Dubon2026
noncomputable section

variable {k A₂ AD₀ B₁ BD₁ C₁ CD₁ : Type} [Field k]
  [AddCommGroup A₂] [Module k A₂] [AddCommGroup AD₀] [Module k AD₀]
  [AddCommGroup B₁] [Module k B₁] [AddCommGroup BD₁] [Module k BD₁]
  [AddCommGroup C₁] [Module k C₁] [AddCommGroup CD₁] [Module k CD₁]
  (P : A₂ →ₗ[k] AD₀ →ₗ[k] k) (Q : B₁ →ₗ[k] BD₁ →ₗ[k] k)
  (R : C₁ →ₗ[k] CD₁ →ₗ[k] k)
  (j : B₁ →ₗ[k] C₁) (δ : C₁ →ₗ[k] A₂)
  (jD : CD₁ →ₗ[k] BD₁) (δD : AD₀ →ₗ[k] CD₁)
  (hex : LinearMap.range j = LinearMap.ker δ)
  (hexD : LinearMap.range δD = LinearMap.ker jD)
  (hnat : ∀ b z, Q b (jD z) = R (j b) z)
  (hadj : ∀ u w, P (δ u) w = R u (δD w))
  (hQ : Function.Surjective Q) (hR : Function.Injective R)

include hex hexD hnat hadj hQ hR in
/-- An effaced original H2 class in the left annihilator vanishes, by the
two actual exact pieces and the genuine H1 pairing identities. -/
theorem lowDegreeH2_connecting_left_zero (u : C₁) (hu : ∀ w, P (δ u) w = 0) :
    δ u = 0 := by
  have hℓ : R u ∈ LinearMap.range jD.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    apply (Submodule.mem_dualAnnihilator (R u)).mpr
    intro z hz
    rw [← hexD] at hz
    obtain ⟨w, rfl⟩ := hz
    exact (hadj u w).symm.trans (hu w)
  obtain ⟨ℓ, hℓ⟩ := hℓ
  obtain ⟨b, rfl⟩ := hQ ℓ
  have hb : j b = u := by
    apply hR
    apply LinearMap.ext
    intro z
    exact (hnat b z).symm.trans (DFunLike.congr_fun hℓ z)
  have hz : j b ∈ LinearMap.ker δ := by
    rw [← hex]
    exact LinearMap.mem_range_self j b
  rw [hb] at hz
  exact hz

end
end Dubon2026

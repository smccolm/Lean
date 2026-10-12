import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # The low-degree annihilator argument for local H1 duality

The three exact pieces are H0(B) to H0(C) to H1(A), H0(C) to
H1(A) to H1(B), and dual H1(A) to dual H2(C) to dual H2(B).
Naturality and the signed connecting-map identity descend the induced H1
annihilator using only surjectivity of the quotient endpoint. These inputs
will be supplied by original continuous cohomology in DUB-17's local-duality
chain; no higher-degree vanishing is required for this deduction.
-/

namespace Dubon2026
noncomputable section

variable {k A₁ AD₁ B₁ BD₁ B₀ C₀ CD₂ BD₂ : Type} [Field k]
  [AddCommGroup A₁] [Module k A₁] [AddCommGroup AD₁] [Module k AD₁]
  [AddCommGroup B₁] [Module k B₁] [AddCommGroup BD₁] [Module k BD₁]
  [AddCommGroup B₀] [Module k B₀] [AddCommGroup C₀] [Module k C₀]
  [AddCommGroup CD₂] [Module k CD₂] [AddCommGroup BD₂] [Module k BD₂]
  (P : A₁ →ₗ[k] AD₁ →ₗ[k] k) (Q : B₁ →ₗ[k] BD₁ →ₗ[k] k)
  (R : CD₂ →ₗ[k] C₀ →ₗ[k] k) (T : BD₂ →ₗ[k] B₀ →ₗ[k] k)
  (i : A₁ →ₗ[k] B₁) (iD : BD₁ →ₗ[k] AD₁)
  (δ : C₀ →ₗ[k] A₁) (j : B₀ →ₗ[k] C₀)
  (δD : AD₁ →ₗ[k] CD₂) (jD : CD₂ →ₗ[k] BD₂)
  (hex₁ : LinearMap.range δ = LinearMap.ker i)
  (hex₀ : LinearMap.range j = LinearMap.ker δ)
  (hexD : LinearMap.range δD = LinearMap.ker jD)
  (hnat : ∀ x y, Q (i x) y = P x (iD y))
  (hend : ∀ z b, T (jD z) b = R z (j b))
  (hadj : ∀ y w, R (δD y) w = -P (δ w) y)
  (hQ : Function.Injective Q) (hT : Function.Injective T)
  (hR : Function.Surjective R)

include hex₁ hex₀ hexD hnat hend hadj hQ hT hR in
/-- The exact low-degree diagram has zero left H1 annihilator. Every
functional vanishing on the invariant image is represented by a quotient
dual H2 class, then lifted through the actual dual connecting map. -/
theorem lowDegreeDuality_left_zero (x : A₁) (hx : ∀ y, P x y = 0) : x = 0 := by
  have hi : i x = 0 := by
    apply hQ
    apply LinearMap.ext
    intro y
    exact (hnat x y).trans ((hx _).trans (DFunLike.congr_fun (map_zero Q) y).symm)
  have hr : x ∈ LinearMap.range δ := by
    rw [hex₁]
    exact hi
  obtain ⟨w, rfl⟩ := hr
  have hw : w ∈ LinearMap.range j := by
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range j) w).mp
    intro ℓ hℓ
    obtain ⟨z, rfl⟩ := hR ℓ
    have hz : jD z = 0 := by
      apply hT
      apply LinearMap.ext
      intro b
      have hb : R z (j b) = 0 := (Submodule.mem_dualAnnihilator (R z)).mp hℓ (j b) (LinearMap.mem_range_self j b)
      exact (hend z b).trans (hb.trans (DFunLike.congr_fun (map_zero T) b).symm)
    have hzrange : z ∈ LinearMap.range δD := by
      rw [hexD]
      exact hz
    obtain ⟨y, rfl⟩ := hzrange
    exact (hadj y w).trans ((congrArg Neg.neg (hx y)).trans neg_zero)
  rw [hex₀] at hw
  exact hw

include hex₁ hex₀ hexD hnat hend hadj hQ hT hR in
/-- The same exact low-degree diagram makes the original H1 pairing map
injective, without an H3 or higher-degree hypothesis. -/
theorem lowDegreeDuality_left_injective : Function.Injective P := by
  intro x y h
  apply sub_eq_zero.mp
  apply lowDegreeDuality_left_zero P Q R T i iD δ j δD jD hex₁ hex₀ hexD hnat hend hadj hQ hT hR
  intro z
  rw [map_sub, LinearMap.sub_apply]
  exact sub_eq_zero.mpr (DFunLike.congr_fun h z)

end
end Dubon2026

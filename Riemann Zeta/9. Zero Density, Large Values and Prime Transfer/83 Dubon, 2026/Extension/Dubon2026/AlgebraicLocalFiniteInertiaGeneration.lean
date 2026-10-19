import Dubon2026.FiniteEmbeddedGaloisKernelOpen
import Dubon2026.AlgebraicLocalInertiaCyclicity

/-! # Original inertia and Frobenius generate the whole finite local quotient

This upgrades the two tame matrix equations to the whole original finite
local representation used by auxiliary deformation conditions for
Dubon Theorem 2.6. Openness is derived from the original embedding square.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] algebraicLocalIntegerAction algebraicLocalIntegerBaseAlgebra

/-- Actual inertia and the same arithmetic Frobenius generate the original
finite quotient obtained from a number-field embedding and restriction. -/
theorem algebraicLocal_finite_inertia_frobenius_generate
    {K L F : Type} [NontriviallyNormedField K] [NormedField L]
    [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
    [IsGalois K L] [Finite (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))]
    [Field F] [NumberField F]
    (e : F →+* L) (r : Gal(L/K) →* Gal(F/ℚ)) (he : ∀ g x, e (r g x) = g (e x))
    (φ : Gal(L/K))
    (hφ : ∀ x : algebraicLocalIntegerRing L,
      IsLocalRing.residue _ (φ • x) = (IsLocalRing.residue _ x) ^
        Nat.card (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))) :
    (algebraicLocalInertia K L).map (QuotientGroup.mk' r.ker) ⊔
      Subgroup.zpowers (QuotientGroup.mk' r.ker φ) = ⊤ := by
  let U : OpenNormalSubgroup Gal(L/K) := {
    toOpenSubgroup := ⟨r.ker, finiteEmbeddedGalois_kernel_isOpen e r he⟩
    isNormal' := inferInstance }
  let I := algebraicLocalInertia K L
  let N := I ⊔ U.toSubgroup
  let π := QuotientGroup.mk' r.ker
  let H := I.map π ⊔ Subgroup.zpowers (π φ)
  have hNH : N ≤ H.comap π := by
    apply sup_le
    · intro g hg
      exact Subgroup.mem_sup_left (Subgroup.mem_map_of_mem π hg)
    · intro g hg
      change π g ∈ H
      have hz : π g = 1 := (QuotientGroup.eq_one_iff _).mpr hg
      rw [hz]
      exact H.one_mem
  apply top_unique
  intro x _
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective r.ker x
  have hgen := algebraicLocal_frobenius_generates_inertia_quotient K L φ hφ U
    (QuotientGroup.mk' N g)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgen
  change (QuotientGroup.mk' N φ) ^ n = QuotientGroup.mk' N g at hn
  have hm : g * (φ ^ n)⁻¹ ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' N) (g * (φ ^ n)⁻¹) = 1
    rw [map_mul, map_inv, map_zpow, hn, mul_inv_cancel]
  have hgH : π (g * (φ ^ n)⁻¹) ∈ H := hNH hm
  have hφn : π (φ ^ n) ∈ H := by
    rw [map_zpow]
    exact Subgroup.mem_sup_right ((Subgroup.zpowers (π φ)).zpow_mem (Subgroup.mem_zpowers _) n)
  simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one] using H.mul_mem hgH hφn

end
end Dubon2026

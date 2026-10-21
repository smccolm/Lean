import Dubon2026.CosetTransitionCoordinates
import Mathlib.GroupTheory.Transfer
import Mathlib.Tactic

/-! DUB-17/18 -> residual Galois association -> finite-order weight-two
Hecke eigenvalues. The actual native coset sum is identified with Mathlib's
transfer, so its proved orbit formula applies without rebuilding orbit
decomposition or introducing a second cohomology model.
-/

namespace Dubon2026
noncomputable section
open Subgroup Subgroup.leftTransversals

variable {G C : Type} [Group G] [CommGroup C]
    (K : Subgroup G) [K.FiniteIndex] [Fintype (G ⧸ K)]

/-- Mathlib transfer is the product over the original coset-transition
coordinates used by the native degree-one correspondence. -/
theorem sourceTransfer_eq_coset_product (φ : K →* C) (g : G) :
    MonoidHom.transfer φ g = ∏ q : G ⧸ K, φ (cosetTransition K g q) := by
  classical
  let S : K.LeftTransversal :=
    ⟨Set.range (fun q : G ⧸ K => q.out),
      isComplement_range_left (fun q : G ⧸ K => Quotient.out_eq' q)⟩
  have hS (q : G ⧸ K) : ((S.2.leftQuotientEquiv q) : G) = q.out :=
    IsComplement.leftQuotientEquiv_apply (fun q : G ⧸ K => Quotient.out_eq' q) q
  rw [MonoidHom.transfer_def φ S g]
  unfold diff
  simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul, hS, smul_eq_mul]
  refine Finset.prod_bij (fun q _ => g⁻¹ • q) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro a _ b _ hab
    simpa only [smul_inv_smul] using congrArg (fun q => g • q) hab
  · intro q _
    exact ⟨g • q, by simp only [Finset.mem_univ], inv_smul_smul g q⟩
  · intro q _
    apply congrArg φ
    apply Subtype.ext
    change q.out⁻¹ * (g * (g⁻¹ • q).out) =
      (g • (g⁻¹ • q)).out⁻¹ * (g * (g⁻¹ • q).out)
    rw [smul_inv_smul]

/-- Transfer of the restriction of an actual global homomorphism is its
index power, using the same original coset coordinates. -/
theorem sourceTransfer_restriction_eq_pow (φ : G →* C) (g : G) :
    MonoidHom.transfer (φ.comp K.subtype) g = φ g ^ K.index := by
  rw [sourceTransfer_eq_coset_product]
  change (∏ q : G ⧸ K, φ ((g • q).out⁻¹ * (g * q.out))) = _
  simp only [map_mul, map_inv]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_mul_distrib,
    Finset.prod_const]
  have he : (∏ q : G ⧸ K, φ (g • q).out) = ∏ q : G ⧸ K, φ q.out :=
    Equiv.prod_comp (MulAction.toPerm g : Equiv.Perm (G ⧸ K))
      (fun q : G ⧸ K => φ q.out)
  rw [he, Subgroup.index_eq_card, Nat.card_eq_fintype_card, Finset.card_univ]
  simp [mul_comm]

end
end Dubon2026

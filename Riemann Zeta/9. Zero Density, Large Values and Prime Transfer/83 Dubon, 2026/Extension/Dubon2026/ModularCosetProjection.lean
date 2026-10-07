import Dubon2026.ModularProjectiveDomain
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # The exact integer-to-projective coset identification for Gamma0 -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- A homomorphism sends actual subgroup cosets to cosets of the image subgroup. -/
def subgroupCosetMap {G H : Type*} [Group G] [Group H] (φ : G →* H) (K : Subgroup G) :
    G ⧸ K → H ⧸ K.map φ :=
  Quotient.map φ (by
    intro a b hab
    change (QuotientGroup.leftRel K).r a b at hab
    change (QuotientGroup.leftRel (K.map φ)).r (φ a) (φ b)
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact ⟨a⁻¹ * b, hab, by simp⟩)

/-- The coset map is injective when the source subgroup contains the kernel. -/
theorem subgroupCosetMap_injective {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (K : Subgroup G) (hker : φ.ker ≤ K) :
    Function.Injective (subgroupCosetMap φ K) := by
  intro x y hxy
  induction x using Quotient.inductionOn with | h a => ?_
  induction y using Quotient.inductionOn with | h b => ?_
  apply QuotientGroup.eq.mpr
  have hm : φ (a⁻¹ * b) ∈ K.map φ := by
    simpa only [map_mul, map_inv] using QuotientGroup.eq.mp hxy
  change a⁻¹ * b ∈ (K.map φ).comap φ at hm
  rwa [Subgroup.comap_map_eq_self hker] at hm

/-- A surjective homomorphism induces a surjection on these actual cosets. -/
theorem subgroupCosetMap_surjective {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (K : Subgroup G) (hφ : Function.Surjective φ) :
    Function.Surjective (subgroupCosetMap φ K) := by
  intro q
  induction q using Quotient.inductionOn with | h b => ?_
  obtain ⟨a, rfl⟩ := hφ b
  exact ⟨QuotientGroup.mk a, rfl⟩

/-- The actual bijection of subgroup cosets under a surjection with absorbed kernel. -/
def subgroupCosetEquiv {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (K : Subgroup G) (hφ : Function.Surjective φ) (hker : φ.ker ≤ K) :
    G ⧸ K ≃ H ⧸ K.map φ :=
  Equiv.ofBijective (subgroupCosetMap φ K)
    ⟨subgroupCosetMap_injective φ K hker, subgroupCosetMap_surjective φ K hφ⟩

/-- Every central integer special linear matrix belongs to every Gamma0. -/
theorem center_SL_le_Gamma0 (Q : ℕ) : Subgroup.center SL(2, ℤ) ≤ Gamma0 Q := by
  intro γ hγ
  obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hγ
  rw [Gamma0_mem]
  have he : γ 1 0 = 0 := by
    have h := congrFun (congrFun hr 1) 0
    simpa [Matrix.scalar] using h.symm
  simp [he]

/-- The genuine projective image of Gamma0. -/
def projectiveGamma0 (Q : ℕ) : Subgroup PSL(2, ℤ) :=
  (Gamma0 Q).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

/-- Integer and projective Gamma0 cosets agree exactly, without a multiplicity factor. -/
def gamma0CosetEquiv (Q : ℕ) : SL(2, ℤ) ⧸ Gamma0 Q ≃ PSL(2, ℤ) ⧸ projectiveGamma0 Q :=
  subgroupCosetEquiv (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) (Gamma0 Q)
    (QuotientGroup.mk'_surjective _) (by
      simpa only [QuotientGroup.ker_mk'] using center_SL_le_Gamma0 Q)

/-- This coset equivalence uses the actual projected matrix representative. -/
theorem gamma0CosetEquiv_out (Q : ℕ) (q : SL(2, ℤ) ⧸ Gamma0 Q) :
    gamma0CosetEquiv Q q = QuotientGroup.mk (QuotientGroup.mk q.out : PSL(2, ℤ)) := by
  conv_lhs => rw [← q.out_eq]
  rfl

end
end Dubon2026

import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Tactic.Group

/-! # Unique right coordinates at a level with trivial arithmetic stabilizers

This is the group-theoretic step of CHT Lemma 3.3.1 used by BLGG Section 3.6
for the auxiliary automorphic modules in DUB-17. Arithmetic finiteness and
smallness still have to be proved for the source unitary group.
-/

namespace Dubon2026

noncomputable section

variable {G : Type*} [Group G] (Γ U : Subgroup G)

/-- The right factor in an actual double-coset decomposition exists. -/
theorem doubleCoset_right_factor_exists (g : G) :
    ∃ u : U, ∃ γ : Γ,
      g = γ * (DoubleCoset.mk Γ U g : DoubleCoset.Quotient Γ U).out * u := by
  obtain ⟨γ, hγ, u, hu, he⟩ :=
    (DoubleCoset.eq Γ U (DoubleCoset.mk Γ U g).out g).mp
      (DoubleCoset.out_eq' Γ U _)
  exact ⟨⟨u, hu⟩, ⟨γ, hγ⟩, he⟩

/-- Choose a right factor, retaining the actual double-coset representative. -/
def smallLevelRightFactor (g : G) : U :=
  (doubleCoset_right_factor_exists Γ U g).choose

/-- The chosen coordinate is realized by an element of the arithmetic subgroup. -/
theorem smallLevelRightFactor_spec (g : G) :
    ∃ γ : Γ, g = γ * (DoubleCoset.mk Γ U g : DoubleCoset.Quotient Γ U).out *
      smallLevelRightFactor Γ U g :=
  (doubleCoset_right_factor_exists Γ U g).choose_spec

/-- Trivial arithmetic stabilizers force uniqueness of the right factor. -/
theorem smallLevel_right_factor_unique
    (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1)
    (s : G) (γ δ : Γ) (u v : U)
    (he : (γ : G) * s * u = δ * s * v) : u = v := by
  have hm : s * ((u * v⁻¹ : U) : G) * s⁻¹ ∈ Γ := by
    have h : s * ((u * v⁻¹ : U) : G) * s⁻¹ = (γ : G)⁻¹ * δ := by
      change s * ((u : G) * (v : G)⁻¹) * s⁻¹ = (γ : G)⁻¹ * δ
      calc
        _ = (γ : G)⁻¹ * ((γ : G) * s * u) * (s * v)⁻¹ := by group
        _ = (γ : G)⁻¹ * ((δ : G) * s * v) * (s * v)⁻¹ := by rw [he]
        _ = _ := by group
    rw [h]
    exact Γ.mul_mem (Γ.inv_mem γ.property) δ.property
  exact mul_inv_eq_one.mp (hsmall s (u * v⁻¹) hm)

/-- Multiplication on the arithmetic side preserves the double coset. -/
theorem smallLevel_doubleCoset_left (γ : Γ) (g : G) :
    DoubleCoset.mk Γ U ((γ : G) * g) = DoubleCoset.mk Γ U g := by
  apply Eq.symm
  exact (DoubleCoset.eq Γ U g ((γ : G) * g)).mpr
    ⟨γ, γ.property, 1, U.one_mem, by simp⟩

/-- Multiplication on the level side preserves the double coset. -/
theorem smallLevel_doubleCoset_right (g : G) (u : U) :
    DoubleCoset.mk Γ U (g * u) = DoubleCoset.mk Γ U g := by
  apply Eq.symm
  exact (DoubleCoset.eq Γ U g (g * u)).mpr
    ⟨1, Γ.one_mem, u, u.property, by simp⟩

/-- The right coordinate is unchanged by the arithmetic subgroup. -/
theorem smallLevelRightFactor_left
    (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1)
    (γ : Γ) (g : G) :
    smallLevelRightFactor Γ U ((γ : G) * g) = smallLevelRightFactor Γ U g := by
  obtain ⟨δ, hδ⟩ := smallLevelRightFactor_spec Γ U ((γ : G) * g)
  obtain ⟨ε, hε⟩ := smallLevelRightFactor_spec Γ U g
  rw [smallLevel_doubleCoset_left] at hδ
  apply smallLevel_right_factor_unique Γ U hsmall _ δ (γ * ε)
  refine hδ.symm.trans ?_
  simpa only [Subgroup.coe_mul, mul_assoc] using congrArg (fun x : G => (γ : G) * x) hε

/-- Right multiplication multiplies the right coordinate. -/
theorem smallLevelRightFactor_right
    (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1)
    (g : G) (u : U) :
    smallLevelRightFactor Γ U (g * u) = smallLevelRightFactor Γ U g * u := by
  obtain ⟨δ, hδ⟩ := smallLevelRightFactor_spec Γ U (g * u)
  obtain ⟨ε, hε⟩ := smallLevelRightFactor_spec Γ U g
  rw [smallLevel_doubleCoset_right] at hδ
  apply smallLevel_right_factor_unique Γ U hsmall _ δ ε
  refine hδ.symm.trans ?_
  simpa only [Subgroup.coe_mul, mul_assoc] using congrArg (fun x : G => x * (u : G)) hε

/-- The chosen representative has right coordinate one. -/
theorem smallLevelRightFactor_out
    (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1)
    (q : DoubleCoset.Quotient Γ U) : smallLevelRightFactor Γ U q.out = 1 := by
  obtain ⟨γ, hγ⟩ := smallLevelRightFactor_spec Γ U q.out
  rw [DoubleCoset.out_eq'] at hγ
  apply smallLevel_right_factor_unique Γ U hsmall q.out γ 1
  simpa using hγ.symm

end
end Dubon2026

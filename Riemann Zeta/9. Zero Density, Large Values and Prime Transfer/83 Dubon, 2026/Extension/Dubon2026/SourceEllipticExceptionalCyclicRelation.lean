import Dubon2026.SourceEllipticExceptionalSubgroupOrbits
import Dubon2026.SourceCyclicSubgroupPermutation

/-! DUB-17/18 -> exceptional modular-place census. The literal source
relation on actual cyclic subgroups is exactly equality up to the two
or three powers of the exceptional automorphism. Every stabilizer is
covered, and each listed power is an actual stabilizing coordinate change. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticStabilizer
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

theorem quartic_cyclic_relation (A : K) (hA : A ≠ 0)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (u : Kˣ) (hu : (u : K) ^ 2 = -1)
    (N : ℕ) (hN : N ≠ 0)
    (S T : {H : AddSubgroup (EA A).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    cyclicStabilizerRelated (EA A) S.val T.val ↔ T = S ∨
      T = cyclicSubgroupEquiv N
        (stabilizerPointEquiv (EA A) ⟨u, 0, 0, 0⟩ (quartic_change_fixes u hu A)) S := by
  rw [cyclicStabilizerRelated_iff_map_eq (EA A) N hN]
  constructor
  · rintro ⟨C, hC, hm⟩
    rcases quartic_stabilizer_subgroup_orbit A hA h2 h3 u hu C hC S.val with h | h
    · exact Or.inl (Subtype.ext (hm.symm.trans h))
    · exact Or.inr (Subtype.ext (hm.symm.trans h))
  · rintro (rfl | rfl)
    · have h1 : (⟨1, 0, 0, 0⟩ : VariableChange K) • EA A = EA A := one_smul _ _
      refine ⟨⟨1, 0, 0, 0⟩, h1, ?_⟩
      have hid : (stabilizerPointEquiv (EA A) ⟨1, 0, 0, 0⟩ h1).toAddMonoidHom =
          AddMonoidHom.id _ := AddMonoidHom.ext (pure_scaling_one_point (EA A) h1)
      rw [hid, AddSubgroup.map_id]
    · exact ⟨⟨u, 0, 0, 0⟩, quartic_change_fixes u hu A, rfl⟩

theorem cubic_cyclic_relation (B : K) (hB : B ≠ 0)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (u : Kˣ) (hu : (u : K) ^ 3 = 1) (hu1 : (u : K) ≠ 1)
    (N : ℕ) (hN : N ≠ 0)
    (S T : {H : AddSubgroup (EB B).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    let τ := cyclicSubgroupEquiv N
      (stabilizerPointEquiv (EB B) ⟨u, 0, 0, 0⟩ (cubic_change_fixes u hu B))
    cyclicStabilizerRelated (EB B) S.val T.val ↔ T = S ∨ T = τ S ∨ T = τ (τ S) := by
  dsimp only
  rw [cyclicStabilizerRelated_iff_map_eq (EB B) N hN]
  constructor
  · rintro ⟨C, hC, hm⟩
    rcases cubic_stabilizer_subgroup_orbit B hB h2 h3 u hu hu1 C hC S.val with h | h | h
    · exact Or.inl (Subtype.ext (hm.symm.trans h))
    · exact Or.inr (Or.inl (Subtype.ext (hm.symm.trans h)))
    · exact Or.inr (Or.inr (Subtype.ext (hm.symm.trans h)))
  · rintro (rfl | rfl | rfl)
    · have h1 : (⟨1, 0, 0, 0⟩ : VariableChange K) • EB B = EB B := one_smul _ _
      refine ⟨⟨1, 0, 0, 0⟩, h1, ?_⟩
      have hid : (stabilizerPointEquiv (EB B) ⟨1, 0, 0, 0⟩ h1).toAddMonoidHom =
          AddMonoidHom.id _ := AddMonoidHom.ext (pure_scaling_one_point (EB B) h1)
      rw [hid, AddSubgroup.map_id]
    · exact ⟨⟨u, 0, 0, 0⟩, cubic_change_fixes u hu B, rfl⟩
    · have hu2 : ((u ^ 2 : Kˣ) : K) ^ 3 = 1 := by
        rw [Units.val_pow_eq_pow_val, ← pow_mul, Nat.mul_comm 2 3, pow_mul, hu, one_pow]
      refine ⟨⟨u ^ 2, 0, 0, 0⟩, cubic_change_fixes (u ^ 2) hu2 B, ?_⟩
      exact pure_scaling_subgroup_square (EB B) u (cubic_change_fixes u hu B)
        (cubic_change_fixes (u ^ 2) hu2 B) S.val

end
end Dubon2026.SourceEllipticExceptional

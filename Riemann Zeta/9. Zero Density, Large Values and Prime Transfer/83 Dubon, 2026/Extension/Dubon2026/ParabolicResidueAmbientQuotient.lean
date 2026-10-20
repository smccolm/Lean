import Dubon2026.ParabolicResidueLevel

/-! # The source U1 as an actual subgroup of the local general linear group

The auxiliary automorphic comparison takes two subgroups of one ambient
group. This realizes U1 in that group, proves the exact row congruences
and normality inside U0, and identifies their quotient with residue units.
-/

namespace Dubon2026

noncomputable section

open IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- U1, realized in the same original integral general linear group as U0. -/
def parabolicResidueLevelOneAmbient (a : ι) : Subgroup (Matrix ι ι R)ˣ :=
  (parabolicResidueLevelOne R a).map (parabolicResidueLevelZero R a).subtype

/-- The original U1 is contained in the original U0. -/
theorem parabolicResidueLevelOneAmbient_le (a : ι) :
    parabolicResidueLevelOneAmbient R a ≤ parabolicResidueLevelZero R a :=
  Subgroup.map_subtype_le _

/-- The ambient U1 condition is exactly the printed last-row congruence. -/
theorem parabolicResidueLevelOneAmbient_mem_iff (a : ι) (M : (Matrix ι ι R)ˣ) :
    M ∈ parabolicResidueLevelOneAmbient R a ↔
      (∀ j, j ≠ a → residue R (M.val a j) = 0) ∧ residue R (M.val a a) = 1 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(parabolicResidueLevelZero_mem_iff R a u.val).mp u.property,
      (parabolicResidueLevelOne_mem_iff R a u).mp hu⟩
  · rintro ⟨h0, h1⟩
    let u : parabolicResidueLevelZero R a :=
      ⟨M, (parabolicResidueLevelZero_mem_iff R a M).mpr h0⟩
    exact ⟨u, (parabolicResidueLevelOne_mem_iff R a u).mpr h1, rfl⟩

/-- Restriction back to U0 recovers exactly the proved character kernel. -/
theorem parabolicResidueLevelOneAmbient_subgroupOf (a : ι) :
    (parabolicResidueLevelOneAmbient R a).subgroupOf (parabolicResidueLevelZero R a) =
      parabolicResidueLevelOne R a :=
  (parabolicResidueLevelOne R a).comap_map_eq_self_of_injective Subtype.val_injective

/-- Normality of the original U1 inside U0 follows from its proved character-kernel identity. -/
instance parabolicResidueLevelOneAmbient_normal (a : ι) :
    ((parabolicResidueLevelOneAmbient R a).subgroupOf (parabolicResidueLevelZero R a)).Normal := by
  rw [parabolicResidueLevelOneAmbient_subgroupOf]
  infer_instance

/-- The quotient used by the original automorphic modules is exactly one residue-unit factor. -/
def parabolicResidueAmbientQuotientEquiv (a : ι) :
    parabolicResidueLevelZero R a ⧸
      (parabolicResidueLevelOneAmbient R a).subgroupOf (parabolicResidueLevelZero R a) ≃*
        (ResidueField R)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (parabolicResidueLevelOneAmbient_subgroupOf R a)).trans
    (parabolicResidueQuotientEquiv R a)

/-- The actual auxiliary quotient is finite whenever the original local residue field is finite. -/
theorem parabolicResidueAmbientQuotient_finite (a : ι) [Finite (ResidueField R)] :
    Finite (parabolicResidueLevelZero R a ⧸
      (parabolicResidueLevelOneAmbient R a).subgroupOf (parabolicResidueLevelZero R a)) :=
  Finite.of_equiv (ResidueField R)ˣ (parabolicResidueAmbientQuotientEquiv R a).symm.toEquiv

end
end Dubon2026

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.Algebra.Group.MinimalAxioms
import Dubon2026.CoinducedCohomologyTrace

/-! Native H2 vanishing for the free subgroup needed by original weight reduction.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> surjective native H1 coefficient map -> Gamma0 H2 vanishing
after inverting six -> its free subgroup of index dividing 48.

The cocycle-extension argument is adapted from
anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_TW12CD1Dock_subsingleton_H2_gamma0.lean.txt (Apache-2.0;
retained LICENSE and NOTICE). The existing local native coinduced
cohomology trace replaces that source's finite-index trace construction.
-/

namespace Dubon2026
noncomputable section
open groupCohomology CategoryTheory

variable {R G : Type} [CommRing R] [Group G] {A : Rep R G}

@[ext] private structure CocycleExtension (c : cocycles₂ A) where
  a : A
  g : G

namespace CocycleExtension

variable (c : cocycles₂ A)

private instance : Mul (CocycleExtension c) :=
  ⟨fun x y => ⟨x.a + A.ρ x.g y.a + c (x.g, y.g), x.g * y.g⟩⟩
private instance : One (CocycleExtension c) := ⟨⟨-c (1, 1), 1⟩⟩
private instance : Inv (CocycleExtension c) :=
  ⟨fun x => ⟨-c (1, 1) - A.ρ x.g⁻¹ x.a - c (x.g⁻¹, x.g), x.g⁻¹⟩⟩

private theorem mul_def (x y : CocycleExtension c) :
    x * y = ⟨x.a + A.ρ x.g y.a + c (x.g, y.g), x.g * y.g⟩ := rfl
private theorem one_def : (1 : CocycleExtension c) = ⟨-c (1, 1), 1⟩ := rfl
private theorem inv_def (x : CocycleExtension c) :
    x⁻¹ = ⟨-c (1, 1) - A.ρ x.g⁻¹ x.a - c (x.g⁻¹, x.g), x.g⁻¹⟩ := rfl

private instance : Group (CocycleExtension c) := Group.ofLeftAxioms
  (fun x y z => by
    ext
    · have hc := (mem_cocycles₂_iff (c : G × G → A)).mp c.property x.g y.g z.g
      simp only [mul_def, map_add, map_mul, Module.End.mul_apply]
      rw [eq_sub_of_add_eq hc]
      abel
    · simp only [mul_def, mul_assoc])
  (fun x => by
    ext
    · simp only [mul_def, one_def, map_one, Module.End.one_apply, cocycles₂_map_one_fst c x.g]
      abel
    · simp only [mul_def, one_def, one_mul])
  (fun x => by
    ext
    · simp only [mul_def, inv_def, one_def]
      abel
    · simp only [mul_def, inv_def, one_def, inv_mul_cancel])

private def projection : CocycleExtension c →* G where
  toFun x := x.g
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem coboundary_of_section (s : G →* CocycleExtension c) (hs : ∀ g, (s g).g = g) :
    (c : G × G → A) ∈ coboundaries₂ A := by
  refine ⟨fun g => -(s g).a, funext fun gh => ?_⟩
  obtain ⟨g, h⟩ := gh
  have he := congrArg CocycleExtension.a (s.map_mul g h)
  simp only [mul_def, hs] at he
  rw [d₁₂_hom_apply]
  simp only [map_neg, he]
  abel

end CocycleExtension

/-- Every native two-cocycle on a free group is an actual coboundary,
obtained by splitting its genuine cocycle extension on the free generators. -/
theorem sourceFreeGroupH2_coboundary [IsFreeGroup G] (c : cocycles₂ A) :
    (c : G × G → A) ∈ coboundaries₂ A := by
  let s : G →* CocycleExtension c := IsFreeGroup.lift fun x => ⟨0, IsFreeGroup.of x⟩
  have hs : (CocycleExtension.projection c).comp s = MonoidHom.id G :=
    IsFreeGroup.ext_hom fun x => by
      simp only [MonoidHom.comp_apply, s, IsFreeGroup.lift_of]
      rfl
  exact CocycleExtension.coboundary_of_section c s (fun g => DFunLike.congr_fun hs g)

/-- Full native second cohomology of a free group vanishes for every actual coefficient action. -/
theorem sourceFreeGroupH2_subsingleton [IsFreeGroup G] (A : Rep R G) :
    Subsingleton (H2 A) := by
  refine ⟨fun x y => ?_⟩
  induction x using H2_induction_on with
  | h x =>
    induction y using H2_induction_on with
    | h y => exact (H2π_eq_iff x y).mpr (sourceFreeGroupH2_coboundary (x - y))

/-- The existing native finite-index trace carries free-subgroup H2
vanishing to the original group whenever its actual index is invertible. -/
theorem sourceFreeFiniteIndexH2_subsingleton (S : Subgroup G) [S.FiniteIndex] [IsFreeGroup S]
    (hS : IsUnit (S.index : R)) (A : Rep R G) :
    Subsingleton (groupCohomology A 2) := by
  letI : Fintype (G ⧸ S) := S.fintypeQuotientOfFiniteIndex
  letI : Subsingleton (groupCohomology (Rep.res S.subtype A) 2) :=
    sourceFreeGroupH2_subsingleton (Rep.res S.subtype A)
  have hz (x : groupCohomology A 2) : x = 0 := by
    have h := subgroupCohomologyComparison_kernel_annihilated A S 2 x (Subsingleton.elim _ _)
    have hi : Fintype.card (G ⧸ S) = S.index := Nat.card_eq_fintype_card.symm
    rw [hi, ← Nat.cast_smul_eq_nsmul R] at h
    exact hS.smul_left_cancel.mp (h.trans (smul_zero _).symm)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end
end Dubon2026

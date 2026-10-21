import Dubon2026.SourceGamma0LevelIndex
import Dubon2026.SourceNativeH1RestrictionTrace
import Dubon2026.SourceIntegralCohomologyFinite

/-! Injective original binary H1 restriction at the residue prime.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> level raising from Q to Q*p. The original subgroup index is p+1, hence
one in characteristic p. The actual native restriction and finite trace
therefore preserve every nonzero original binary H1 class.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory

variable (F : Type) [Field F] (Q p n : ℕ)

/-- The original binary coefficient action restricts literally along the
actual level inclusion. -/
def sourceBinaryLevelMorphism :
    Rep.res (sourceGamma0LevelInclusion Q p) (sourceBinaryCoefficientRep F Q n) ⟶
      sourceBinaryCoefficientRep F (Q * p) n :=
  Rep.ofHom { toLinearMap := LinearMap.id, isIntertwining' := fun _ => rfl }

/-- The actual native binary H1 restriction from level Q to level Q*p. -/
def sourceBinaryLevelRestriction :
    groupCohomology.H1 (sourceBinaryCoefficientRep F Q n) →ₗ[F]
      groupCohomology.H1 (sourceBinaryCoefficientRep F (Q * p) n) :=
  (groupCohomology.map (sourceGamma0LevelInclusion Q p)
    (sourceBinaryLevelMorphism F Q p n) 1).hom

/-- The level restriction is represented by the literal restricted original cocycle. -/
theorem sourceBinaryLevelRestriction_cocycle
    (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep F Q n)) :
    sourceBinaryLevelRestriction F Q p n (groupCohomology.H1π _ c) =
      groupCohomology.H1π _ (groupCohomology.mapCocycles₁ (sourceGamma0LevelInclusion Q p)
        (sourceBinaryLevelMorphism F Q p n) c) :=
  groupCohomology.H1π_comp_map_apply _ _ c

/-- At a prime away from the level, the original binary H1 restriction is
injective in that characteristic. The exact p+1 index and original finite
trace discharge the nonvanishing obligation for level raising. -/
theorem sourceBinaryLevelRestriction_injective [CharP F p] (hp : p.Prime)
    (hpQ : Nat.Coprime p Q) :
    Function.Injective (sourceBinaryLevelRestriction F Q p n) := by
  let S := (Gamma0 (Q * p)).subgroupOf (Gamma0 Q)
  have hindex : S.index = p + 1 := sourceGamma0LevelSubgroup_index hp hpQ
  letI : S.FiniteIndex := ⟨by rw [hindex]; omega⟩
  letI : Fintype (Gamma0 Q ⧸ S) := S.fintypeQuotientOfFiniteIndex
  have hcard : (Fintype.card (Gamma0 Q ⧸ S) : F) = 1 := by
    have he : Fintype.card (Gamma0 Q ⧸ S) = p + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact hindex
    rw [he, Nat.cast_add, CharP.cast_eq_zero F p, Nat.cast_one, zero_add]
  have hinj := sourceH1SubgroupRestriction_injective (sourceBinaryCoefficientRep F Q n) S
    (hcard ▸ isUnit_one)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine groupCohomology.H1_induction_on x (fun c hc => ?_) hx
  rw [sourceBinaryLevelRestriction_cocycle] at hc
  obtain ⟨v, hv⟩ := (groupCohomology.H1π_eq_zero_iff _).mp hc
  apply hinj
  rw [map_zero, sourceH1SubgroupRestriction_cocycle]
  apply (groupCohomology.H1π_eq_zero_iff _).mpr
  refine ⟨v, ?_⟩
  funext s
  let e := Subgroup.subgroupOfEquivOfLe (Gamma0_le_of_dvd (dvd_mul_right Q p))
  exact congrFun hv (e s)

end
end Dubon2026

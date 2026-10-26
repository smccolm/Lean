import Dubon2026.CoinducedCosetTrace
import Dubon2026.OriginalCohomologyTraceNaturality

/-! DUB-17/18 -> original all-weight adic association -> Gamma1 geometric
realization -> surjective-transfer Hecke compatibility -> composition of
the literal native H1 traces. The existing Shapiro evaluation comparison
reduces that composition to actual nested coinduced functions and traces. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G]
  (A : Rep.{0} R G) (S T : Subgroup G) (hST : S ≤ T)

/-- Flatten the actual nested coinduced function by identity evaluation. -/
def sourceCoinducedTowerFlatten :
    Rep.coind T.subtype
      (Rep.coind (S.subgroupOf T).subtype
        (Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A))) ⟶
      Rep.coind S.subtype (Rep.res S.subtype A) :=
  Rep.ofHom {
    toLinearMap := {
      toFun := fun f => ⟨fun g => (f.val g).val 1, by
        intro s g
        let t : T := ⟨s.val, hST s.property⟩
        have hf := congrArg (fun z : Rep.coind (S.subgroupOf T).subtype
          (Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A)) => z.val 1)
          (f.property t g)
        change (f.val (s.val * g)).val 1 = (f.val g).val (1 * t) at hf
        rw [one_mul] at hf
        change (f.val (s.val * g)).val 1 = A.ρ s.val ((f.val g).val 1)
        rw [hf]
        simpa only [mul_one] using (f.val g).property
          ((Subgroup.subgroupOfEquivOfLe hST).symm s) 1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    isIntertwining' := by intro g; ext f x; rfl }

/-- The inverse keeps the genuine subgroup multiplication: its value at
an ambient element and a subgroup element is the original function at their product. -/
def sourceCoinducedTowerUnflatten :
    Rep.coind S.subtype (Rep.res S.subtype A) ⟶
      Rep.coind T.subtype
        (Rep.coind (S.subgroupOf T).subtype
          (Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A))) :=
  Rep.ofHom {
    toLinearMap := {
      toFun := fun f => ⟨fun g => ⟨fun t => f.val (t.val * g), by
        intro s t
        change f.val ((s.val.val * t.val) * g) = A.ρ s.val.val (f.val (t.val * g))
        rw [mul_assoc]
        exact f.property ((Subgroup.subgroupOfEquivOfLe hST) s) (t.val * g)⟩, by
          intro t g
          ext s
          change f.val (s.val * (t.val * g)) = f.val ((s.val * t.val) * g)
          rw [mul_assoc]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    isIntertwining' := by
      intro g
      ext f x t
      change f.val ((t.val * x) * g) = f.val (t.val * (x * g))
      rw [mul_assoc] }

/-- The two actual function maps form an isomorphism of the original
coinduced representations, with no transitivity axiom. -/
def sourceCoinducedTowerIso :
    Rep.coind T.subtype
      (Rep.coind (S.subgroupOf T).subtype
        (Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A))) ≅
      Rep.coind S.subtype (Rep.res S.subtype A) where
  hom := sourceCoinducedTowerFlatten A S T hST
  inv := sourceCoinducedTowerUnflatten A S T hST
  hom_inv_id := by
    apply Rep.hom_ext
    ext f g t
    change (f.val (t.val * g)).val 1 = (f.val g).val t
    have hf := congrArg (fun z : Rep.coind (S.subgroupOf T).subtype
      (Rep.res (S.subgroupOf T).subtype (Rep.res T.subtype A)) => z.val 1)
      (f.property t g)
    change (f.val (t.val * g)).val 1 = (f.val g).val (1 * t) at hf
    simpa only [one_mul] using hf
  inv_hom_id := by
    apply Rep.hom_ext
    ext f g
    change f.val (1 * g) = f.val g
    rw [one_mul]

end
end Dubon2026

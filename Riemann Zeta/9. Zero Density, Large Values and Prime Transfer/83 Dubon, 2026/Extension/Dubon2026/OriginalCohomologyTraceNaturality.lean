import Dubon2026.OriginalCohomologyRestrictionTrace

/-! # Coefficient naturality of the original subgroup trace

The actual idele-to-class projection must commute with corestriction before
the canonical class invariant can be evaluated on a local fundamental class.
The existing Shapiro restriction/evaluation identity supplies this bridge.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped BigOperators

variable {k G : Type} [CommRing k] [Group G] (S : Subgroup G)

/-- Shapiro's actual cohomology map commutes with the given coefficient morphism. -/
theorem originalShapiro_coefficient_naturality {A B : Rep k S} (f : A ⟶ B) (n : ℕ) :
    (groupCohomology.functor k G n).map ((Rep.coindFunctor k S.subtype).map f) ≫
      (groupCohomology.coindIso B n).hom =
    (groupCohomology.coindIso A n).hom ≫ (groupCohomology.functor k S n).map f := by
  let evA : Rep.res S.subtype (Rep.coind S.subtype A) ⟶ A :=
    (Rep.resCoindHomEquiv S.subtype (Rep.coind S.subtype A) A).symm (𝟙 _)
  let evB : Rep.res S.subtype (Rep.coind S.subtype B) ⟶ B :=
    (Rep.resCoindHomEquiv S.subtype (Rep.coind S.subtype B) B).symm (𝟙 _)
  have hA := OriginalShapiroRestriction.originalShapiroIso_eq_restriction_eval
    A n evA (fun _ => rfl)
  have hB := OriginalShapiroRestriction.originalShapiroIso_eq_restriction_eval
    B n evB (fun _ => rfl)
  change groupCohomology.map (MonoidHom.id G) ((Rep.coindFunctor k S.subtype).map f) n ≫
    (groupCohomology.coindIso B n).hom =
    (groupCohomology.coindIso A n).hom ≫ groupCohomology.map (MonoidHom.id S) f n
  rw [hA, hB]
  simp only [← groupCohomology.map_comp]
  congr 1

variable {A B : Rep k G} (f : A ⟶ B)

/-- Postcomposing a coinduced coefficient function commutes with each untwisted coset value. -/
theorem originalCoinducedCosetValues_coefficient_naturality
    (x : Rep.coind S.subtype (Rep.res S.subtype A)) (q : G ⧸ S) :
    coinducedCosetValues B S
        (((Rep.coindFunctor k S.subtype).map ((Rep.resFunctor S.subtype).map f)).hom x) q =
      f.hom (coinducedCosetValues A S x q) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    change B.ρ g (f.hom (x.val g⁻¹)) = f.hom (A.ρ g (x.val g⁻¹))
    exact (Rep.hom_comm_apply f g (x.val g⁻¹)).symm

variable [Fintype (G ⧸ S)]

/-- The genuine finite coset trace commutes with coefficient projection. -/
theorem originalCoinducedCosetTrace_coefficient_naturality :
    (Rep.coindFunctor k S.subtype).map ((Rep.resFunctor S.subtype).map f) ≫
      coinducedCosetTrace B S = coinducedCosetTrace A S ≫ f := by
  apply Rep.hom_ext
  ext x
  change (∑ q : G ⧸ S, coinducedCosetValues B S
    (((Rep.coindFunctor k S.subtype).map ((Rep.resFunctor S.subtype).map f)).hom x) q) =
      f.hom (∑ q : G ⧸ S, coinducedCosetValues A S x q)
  rw [map_sum]
  exact Finset.sum_congr rfl (fun q _ => originalCoinducedCosetValues_coefficient_naturality S f x q)

/-- The original subgroup cohomology trace commutes with the actual coefficient map in every degree. -/
theorem originalCohomologyTrace_coefficient_naturality (n : ℕ) :
    (groupCohomology.functor k S n).map ((Rep.resFunctor S.subtype).map f) ≫
      subgroupCohomologyTrace B S n =
    subgroupCohomologyTrace A S n ≫ (groupCohomology.functor k G n).map f := by
  have h := originalShapiro_coefficient_naturality S ((Rep.resFunctor S.subtype).map f) n
  apply (cancel_epi (groupCohomology.coindIso (Rep.res S.subtype A) n).hom).1
  unfold subgroupCohomologyTrace
  simp only [Category.assoc]
  erw [← Category.assoc, ← h]
  erw [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  erw [← Functor.map_comp, ← Functor.map_comp,
    originalCoinducedCosetTrace_coefficient_naturality]
  rfl

omit [Fintype (G ⧸ S)] in
/-- A coefficient-level identity-evaluation section gives an actual Shapiro lift section on cohomology. -/
theorem originalShapiro_lift_section {C : Rep k S} {B : Rep k G}
    (F : Rep.coind S.subtype C ⟶ B) (ev : Rep.res S.subtype B ⟶ C)
    (hev : ∀ x : Rep.coind S.subtype C, ev.hom (F.hom x) = x.val 1) (n : ℕ) :
    ((groupCohomology.coindIso C n).inv ≫ (groupCohomology.functor k G n).map F) ≫
      groupCohomology.map S.subtype ev n = 𝟙 (groupCohomology C n) := by
  let evC := (Rep.resFunctor S.subtype).map F ≫ ev
  have hsh := OriginalShapiroRestriction.originalShapiroIso_eq_restriction_eval
    C n evC hev
  rw [← groupCohomology.map_comp] at hsh
  change (groupCohomology.coindIso C n).hom = groupCohomology.map S.subtype evC n at hsh
  have hmap : (groupCohomology.functor k G n).map F ≫ groupCohomology.map S.subtype ev n =
      groupCohomology.map S.subtype evC n :=
    (groupCohomology.map_comp (A := Rep.coind S.subtype C) (B := B) (C := C)
      (MonoidHom.id G) S.subtype F ev n).symm
  calc
    _ = (groupCohomology.coindIso C n).inv ≫
        ((groupCohomology.functor k G n).map F ≫ groupCohomology.map S.subtype ev n) :=
      Category.assoc _ _ _
    _ = (groupCohomology.coindIso C n).inv ≫ (groupCohomology.coindIso C n).hom :=
      congrArg (fun f => (groupCohomology.coindIso C n).inv ≫ f) (hmap.trans hsh.symm)
    _ = _ := Iso.inv_hom_id _

/-- A coinduced coefficient lift followed by coset trace is the genuine cohomology trace of the original subgroup coefficient map. -/
theorem originalCohomologyTrace_coinduced_lift {C : Rep k S} {B : Rep k G}
    (j : C ⟶ Rep.res S.subtype B) (n : ℕ) :
    (groupCohomology.coindIso C n).inv ≫ (groupCohomology.functor k G n).map
      ((Rep.coindFunctor k S.subtype).map j ≫ coinducedCosetTrace B S) =
    (groupCohomology.functor k S n).map j ≫ subgroupCohomologyTrace B S n := by
  have h := originalShapiro_coefficient_naturality S j n
  apply (cancel_epi (groupCohomology.coindIso C n).hom).1
  unfold subgroupCohomologyTrace
  erw [Iso.hom_inv_id_assoc, Functor.map_comp]
  erw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_assoc]
  rfl


end
end Dubon2026

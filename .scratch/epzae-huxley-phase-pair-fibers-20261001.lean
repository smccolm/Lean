import TaoTrudgianYang2025.HuxleyLinearForms

open Set TaoTrudgianYang2025 TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical ContDiff
namespace HuxleyPhasePairFibersScratch

private theorem actual_phase_pair_forget_card
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) (ya yb : ℝ) :
    let Fiber := P.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    let embed := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      (((ya,ij.1.1),ij.1.2),((yb,ij.2.1),ij.2.2))
    (Fiber.image forget).card=Fiber.card ∧
      ∀ ij, ij∈Fiber.image forget ↔ embed ij∈P := by
  classical
  intro Fiber forget embed
  have hback ij (hij : ij∈Fiber) : embed (forget ij)=ij := by
    rcases ij with ⟨⟨⟨a,n⟩,ip⟩,⟨⟨b,m⟩,jp⟩⟩
    have he := (Finset.mem_filter.mp hij).2
    dsimp only at he
    rcases he with ⟨rfl,rfl⟩
    rfl
  constructor
  · apply Finset.card_image_of_injOn
    intro ij hij kl hkl he
    exact (hback ij hij).symm.trans ((congrArg embed he).trans (hback kl hkl))
  · intro ij
    constructor
    · intro hij
      obtain ⟨kl,hkl,rfl⟩ := Finset.mem_image.mp hij
      rw [hback kl hkl]
      exact (Finset.mem_filter.mp hkl).1
    · intro hij
      exact Finset.mem_image.mpr ⟨embed ij,Finset.mem_filter.mpr ⟨hij,by constructor <;> rfl⟩,rfl⟩

private theorem actual_phase_pair_sum_card
    (S : Finset (ℝ × ℤ))
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
    (hP : ∀ ij∈P, ij.1.1∈S ∧ ij.2.1∈S) :
    let Y := S.image Prod.fst
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    (P.card:ℝ)=∑ ab∈Y ×ˢ Y,
      (((P.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget).card:ℝ) := by
  classical
  intro Y forget
  let phase := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
    (ij.1.1.1,ij.2.1.1)
  have hmaps : Set.MapsTo phase (P : Set _) (Y ×ˢ Y : Finset _) := by
    intro ij hij
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem Prod.fst (hP ij hij).1,
       Finset.mem_image_of_mem Prod.fst (hP ij hij).2⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have heq ab : (P.filter (fun ij => phase ij=ab)).card=
      ((P.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget).card := by
    rw [(actual_phase_pair_forget_card P ab.1 ab.2).1]
    congr 1
    rcases ab with ⟨ya,yb⟩
    ext ij
    simp only [Finset.mem_filter,phase,Prod.mk.injEq]
  rw [Finset.sum_congr rfl (fun ab _ => heq ab)] at hcard
  exact_mod_cast hcard


example
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) (ya yb : ℝ) :
    let Fiber := P.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    let embed := fun ij : (ℤ × Fin 2) × (ℤ × Fin 2) =>
      (((ya,ij.1.1),ij.1.2),((yb,ij.2.1),ij.2.2))
    (Fiber.image forget).card=Fiber.card ∧
      ∀ ij, ij∈Fiber.image forget ↔ embed ij∈P :=
  HuxleyPhasePairFibersScratch.actual_phase_pair_forget_card P ya yb

example
    (S : Finset (ℝ × ℤ))
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
    (hP : ∀ ij∈P, ij.1.1∈S ∧ ij.2.1∈S) :
    let Y := S.image Prod.fst
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    (P.card:ℝ)=∑ ab∈Y ×ˢ Y,
      (((P.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget).card:ℝ) :=
  HuxleyPhasePairFibersScratch.actual_phase_pair_sum_card S P hP


private theorem actual_type_one_phase_pair_partition
    (S : Finset (ℝ × ℤ))
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
    (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
    (small : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Prop)
    [DecidablePred small]
    (hP : ∀ ij∈P, ij.1.1∈S ∧ ij.2.1∈S) :
    let TypeOne := P.filter small
    let Rest := P.filter (fun ij => ¬small ij)
    let Upper := Rest.filter (fun ij => Mat ij 2=0)
    let NonUpper := Rest.filter (fun ij => Mat ij 2≠0)
    let Lower := NonUpper.filter (fun ij => Mat ij 1=0)
    let Large := NonUpper.filter (fun ij => Mat ij 1≠0)
    let Y := S.image Prod.fst
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    let phaseFiber := fun (E : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) ab =>
      (E.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget
    (P.card:ℝ)=(TypeOne.card:ℝ)+∑ ab∈Y ×ˢ Y,
      (((phaseFiber Upper ab).card:ℝ)+((phaseFiber Lower ab).card:ℝ)+
        ((phaseFiber Large ab).card:ℝ)) := by
  classical
  intro TypeOne Rest Upper NonUpper Lower Large Y forget phaseFiber
  have hfirst : TypeOne.card+Rest.card=P.card :=
    Finset.card_filter_add_card_filter_not small
  have hsecond : Upper.card+NonUpper.card=Rest.card :=
    Finset.card_filter_add_card_filter_not (fun ij => Mat ij 2=0)
  have hthird : Lower.card+Large.card=NonUpper.card :=
    Finset.card_filter_add_card_filter_not (fun ij => Mat ij 1=0)
  have hsum : (P.card:ℝ)=(TypeOne.card:ℝ)+
      ((Upper.card:ℝ)+(Lower.card:ℝ)+(Large.card:ℝ)) := by
    exact_mod_cast (by omega : P.card=TypeOne.card+(Upper.card+Lower.card+Large.card))
  have hUpper := actual_phase_pair_sum_card S Upper (fun ij hij =>
    hP ij (Finset.mem_filter.mp (Finset.mem_filter.mp hij).1).1)
  have hLower := actual_phase_pair_sum_card S Lower (fun ij hij =>
    hP ij (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hij).1).1).1)
  have hLarge := actual_phase_pair_sum_card S Large (fun ij hij =>
    hP ij (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hij).1).1).1)
  rw [hsum,hUpper,hLower,hLarge]
  simp only [Finset.sum_add_distrib]
  rfl


example
    (S : Finset (ℝ × ℤ))
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
    (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
    (small : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Prop)
    [DecidablePred small]
    (hP : ∀ ij∈P, ij.1.1∈S ∧ ij.2.1∈S) :
    let TypeOne := P.filter small
    let Rest := P.filter (fun ij => ¬small ij)
    let Upper := Rest.filter (fun ij => Mat ij 2=0)
    let NonUpper := Rest.filter (fun ij => Mat ij 2≠0)
    let Lower := NonUpper.filter (fun ij => Mat ij 1=0)
    let Large := NonUpper.filter (fun ij => Mat ij 1≠0)
    let Y := S.image Prod.fst
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    let phaseFiber := fun (E : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2))) ab =>
      (E.filter (fun ij => ij.1.1.1=ab.1 ∧ ij.2.1.1=ab.2)).image forget
    (P.card:ℝ)=(TypeOne.card:ℝ)+∑ ab∈Y ×ˢ Y,
      (((phaseFiber Upper ab).card:ℝ)+((phaseFiber Lower ab).card:ℝ)+
        ((phaseFiber Large ab).card:ℝ)) :=
  HuxleyPhasePairFibersScratch.actual_type_one_phase_pair_partition S P Mat small hP


#print axioms actual_phase_pair_forget_card
#print axioms actual_phase_pair_sum_card
#print axioms actual_type_one_phase_pair_partition

end HuxleyPhasePairFibersScratch

import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Set
open scoped BigOperators Classical
namespace HuxleyResidualPhaseFiberScratch

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


private theorem actual_residual_phase_fiber_partition
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
    (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
    (ya yb : ℝ) :
    let Upper := P.filter (fun ij => Mat ij 2=0)
    let NonUpper := P.filter (fun ij => Mat ij 2≠0)
    let Lower := NonUpper.filter (fun ij => Mat ij 1=0)
    let Large := NonUpper.filter (fun ij => Mat ij 1≠0)
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    let phaseFiber := fun E : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) =>
      (E.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).image forget
    ((phaseFiber Upper).card:ℝ)+((phaseFiber Lower).card:ℝ)+((phaseFiber Large).card:ℝ)=
      ((phaseFiber P).card:ℝ) := by
  classical
  intro Upper NonUpper Lower Large forget phaseFiber
  change (((Upper.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).image forget).card:ℝ)+
    (((Lower.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).image forget).card:ℝ)+
    (((Large.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).image forget).card:ℝ)=
    (((P.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).image forget).card:ℝ)
  rw [(actual_phase_pair_forget_card Upper ya yb).1,
    (actual_phase_pair_forget_card Lower ya yb).1,
    (actual_phase_pair_forget_card Large ya yb).1,
    (actual_phase_pair_forget_card P ya yb).1]
  let Φ := P.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)
  have hu : (Φ.filter (fun ij => Mat ij 2=0)).card+
      (Φ.filter (fun ij => Mat ij 2≠0)).card=Φ.card :=
    Finset.card_filter_add_card_filter_not (fun ij => Mat ij 2=0)
  have hl : ((Φ.filter (fun ij => Mat ij 2≠0)).filter (fun ij => Mat ij 1=0)).card+
      ((Φ.filter (fun ij => Mat ij 2≠0)).filter (fun ij => Mat ij 1≠0)).card=
      (Φ.filter (fun ij => Mat ij 2≠0)).card :=
    Finset.card_filter_add_card_filter_not (fun ij => Mat ij 1=0)
  have hU : Φ.filter (fun ij => Mat ij 2=0)=
      Upper.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb) := by
    ext ij
    simp only [Φ,Upper,Finset.mem_filter]
    tauto
  have hL : (Φ.filter (fun ij => Mat ij 2≠0)).filter (fun ij => Mat ij 1=0)=
      Lower.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb) := by
    ext ij
    simp only [Φ,Lower,NonUpper,Finset.mem_filter]
    tauto
  have hH : (Φ.filter (fun ij => Mat ij 2≠0)).filter (fun ij => Mat ij 1≠0)=
      Large.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb) := by
    ext ij
    simp only [Φ,Large,NonUpper,Finset.mem_filter]
    tauto
  rw [hU] at hu
  rw [hL,hH] at hl
  exact_mod_cast (by omega :
    (Upper.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).card+
    (Lower.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).card+
    (Large.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).card=Φ.card)


example
    (P : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)))
    (Mat : (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) → Fin 4 → ℤ)
    (ya yb : ℝ) :
    let Upper := P.filter (fun ij => Mat ij 2=0)
    let NonUpper := P.filter (fun ij => Mat ij 2≠0)
    let Lower := NonUpper.filter (fun ij => Mat ij 1=0)
    let Large := NonUpper.filter (fun ij => Mat ij 1≠0)
    let forget := fun ij : ((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2) =>
      ((ij.1.1.2,ij.1.2),(ij.2.1.2,ij.2.2))
    let phaseFiber := fun E : Finset (((ℝ × ℤ) × Fin 2) × ((ℝ × ℤ) × Fin 2)) =>
      (E.filter (fun ij => ij.1.1.1=ya ∧ ij.2.1.1=yb)).image forget
    ((phaseFiber Upper).card:ℝ)+((phaseFiber Lower).card:ℝ)+((phaseFiber Large).card:ℝ)=
      ((phaseFiber P).card:ℝ) :=
  HuxleyResidualPhaseFiberScratch.actual_residual_phase_fiber_partition P Mat ya yb


#print axioms actual_phase_pair_forget_card
#print axioms actual_residual_phase_fiber_partition

end HuxleyResidualPhaseFiberScratch

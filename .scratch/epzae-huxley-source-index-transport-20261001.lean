import TaoTrudgianYang2025.HuxleyLinearForms
open Set TaoTrudgianYang2025.HuxleyRationalPhase
open scoped BigOperators Classical
namespace HuxleySourceIndexTransportScratch
private theorem actual_source_index_transport
    (S : Finset ((ℝ × (ℝ × ℝ)) × ℤ))
    (hinj : Set.InjOn (fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)) (S : Set _)) :
    let tag := fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)
    let P := S.image tag
    ∃ pull : ℝ × ℤ → (ℝ × (ℝ × ℝ)) × ℤ,
      (∀ p∈P, pull p∈S ∧ tag (pull p)=p) ∧
      (∀ i∈S, pull (tag i)=i) ∧
      P.card=S.card ∧
      (∀ w : (ℝ × (ℝ × ℝ)) × ℤ → ℝ,
        (∑ p∈P,w (pull p))=∑ i∈S,w i) ∧
      ∀ w : ((ℝ × (ℝ × ℝ)) × ℤ) × Fin 2 → ℝ,
        (∑ ip∈P ×ˢ (Finset.univ : Finset (Fin 2)),w (pull ip.1,ip.2))=
          ∑ i∈S, ∑ p : Fin 2,w (i,p) := by
  classical
  intro tag P
  let pull := Function.invFunOn tag (S : Set _)
  have himage p (hp : p∈P) : p∈tag '' (S : Set _) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨i,hi,rfl⟩
  have hright p (hp : p∈P) : pull p∈S ∧ tag (pull p)=p :=
    ⟨Function.invFunOn_mem (himage p hp),Function.invFunOn_eq (himage p hp)⟩
  have hleft i (hi : i∈S) : pull (tag i)=i := by
    have hh := hright (tag i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    exact hinj hh.1 hi hh.2
  refine ⟨pull,hright,hleft,Finset.card_image_of_injOn hinj,?_,?_⟩
  · intro w
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl (fun i hi => congrArg w (hleft i hi))
  · intro w
    rw [Finset.sum_product,Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro i hi
    change (∑ p : Fin 2,w (pull (tag i),p))=∑ p : Fin 2,w (i,p)
    rw [hleft i hi]

example
    (S : Finset ((ℝ × (ℝ × ℝ)) × ℤ))
    (hinj : Set.InjOn (fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)) (S : Set _)) :
    let tag := fun i : (ℝ × (ℝ × ℝ)) × ℤ => (i.1.1,i.2)
    let P := S.image tag
    ∃ pull : ℝ × ℤ → (ℝ × (ℝ × ℝ)) × ℤ,
      (∀ p∈P, pull p∈S ∧ tag (pull p)=p) ∧
      (∀ i∈S, pull (tag i)=i) ∧
      P.card=S.card ∧
      (∀ w : (ℝ × (ℝ × ℝ)) × ℤ → ℝ,
        (∑ p∈P,w (pull p))=∑ i∈S,w i) ∧
      ∀ w : ((ℝ × (ℝ × ℝ)) × ℤ) × Fin 2 → ℝ,
        (∑ ip∈P ×ˢ (Finset.univ : Finset (Fin 2)),w (pull ip.1,ip.2))=
          ∑ i∈S, ∑ p : Fin 2,w (i,p) :=
  HuxleySourceIndexTransportScratch.actual_source_index_transport S hinj


#print axioms actual_source_index_transport
end HuxleySourceIndexTransportScratch

import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! DUB-17/18 -> auxiliary point division -> cover Abel comparison -> compactness.
Finite constant-cardinality fibers exhaust nearby disjoint open sheets. This
proves closedness without assuming compactness of the source. The proper-map
criterion then transfers compactness from the already compact original curve.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Set Topology
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]

theorem isClosedMap_of_open_constant_finite_fibers (f : X → Y)
    (hf : IsOpenMap f) (hfin : ∀ y, (f ⁻¹' {y}).Finite)
    (hcard : ∀ y z, Nat.card (f ⁻¹' {y}) = Nat.card (f ⁻¹' {z})) :
    IsClosedMap f := by
  classical
  intro A hA
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro y hy
  obtain ⟨V, hV, hdisj⟩ := (hfin y).t2_separation
  let U (e : f ⁻¹' {y}) := V e ∩ Aᶜ
  have hopen (e : f ⁻¹' {y}) : IsOpen (U e) := (hV e).2.inter hA.isOpen_compl
  have hmem (e : f ⁻¹' {y}) : (e : X) ∈ U e := by
    refine ⟨(hV e).1, ?_⟩
    intro he
    exact hy ⟨e, he, e.2⟩
  letI : Finite (f ⁻¹' {y}) := hfin y
  let W := ⋂ e : f ⁻¹' {y}, f '' U e
  have hW : IsOpen W := isOpen_iInter_of_finite fun e => hf _ (hopen e)
  refine ⟨W, ?_, hW, mem_iInter.mpr fun e => ⟨e, hmem e, e.2⟩⟩
  intro z hz hzA
  have hex (e : f ⁻¹' {y}) : ∃ a : X, a ∈ U e ∧ f a = z := mem_iInter.mp hz e
  choose a ha hfa using hex
  let g : (f ⁻¹' {y}) → (f ⁻¹' {z}) := fun e => ⟨a e, hfa e⟩
  have hinj : Function.Injective g := by
    intro e e' he
    by_contra hne
    have hd := hdisj e.2 e'.2 (show (e : X) ≠ e' from fun h => hne (Subtype.ext h))
    have heq : a e = a e' := congrArg Subtype.val he
    exact Set.disjoint_left.mp hd (ha e).1 (heq.symm ▸ (ha e').1)
  letI : Fintype (f ⁻¹' {y}) := Fintype.ofFinite _
  letI : Finite (f ⁻¹' {z}) := hfin z
  letI : Fintype (f ⁻¹' {z}) := Fintype.ofFinite _
  have hsurj : Function.Surjective g := by
    by_contra h
    have hlt := Fintype.card_lt_of_injective_not_surjective g hinj h
    have heq := hcard y z
    simp only [Nat.card_eq_fintype_card] at heq
    omega
  obtain ⟨b, hbA, hbz⟩ := hzA
  obtain ⟨e, he⟩ := hsurj ⟨b, hbz⟩
  have heq : a e = b := congrArg Subtype.val he
  exact (ha e).2 (heq.symm ▸ hbA)

theorem compactSpace_of_open_constant_finite_fibers [CompactSpace Y]
    (f : X → Y) (hc : Continuous f) (ho : IsOpenMap f)
    (hfin : ∀ y, (f ⁻¹' {y}).Finite)
    (hcard : ∀ y z, Nat.card (f ⁻¹' {y}) = Nat.card (f ⁻¹' {z})) :
    CompactSpace X := by
  have hp : IsProperMap f := isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨hc, isClosedMap_of_open_constant_finite_fibers f ho hfin hcard,
      fun y => (hfin y).isCompact⟩
  exact ⟨by simpa only [preimage_univ] using hp.isCompact_preimage isCompact_univ⟩

end
end Dubon2026.SourceCurve

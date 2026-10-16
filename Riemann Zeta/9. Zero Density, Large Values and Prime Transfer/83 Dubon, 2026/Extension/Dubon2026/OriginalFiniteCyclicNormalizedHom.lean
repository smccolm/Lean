import Dubon2026.OriginalFiniteCyclicInvariant
import Dubon2026.OriginalClassH2InvariantFromGenerator

/-! # A prescribed normalized invariant on an actual cyclic group

Use the existing invariant construction and generation by the specified
element to identify a prescribed additive map. This proves injectivity
and the exact image for DUB-17's descended original-idele total, without
replacing it by an unrelated cyclic invariant.
-/
namespace Dubon2026
noncomputable section

/-- A prescribed additive map with reciprocal-order value on an actual generator has the same injection and exact image as the existing normalized cyclic invariant. -/
theorem originalFiniteCyclic_normalized_hom
    {A : Type*} [AddCommGroup A] (u : A) (n : ℕ) (hn : 0 < n)
    (hu : addOrderOf u = n) (hgen : ∀ x : A, x ∈ AddSubgroup.zmultiples u)
    (f : A →+ AddCircle (1 : ℚ)) (hf : f u = ↑((1 : ℚ) / n)) :
    Function.Injective f ∧ (∀ t : AddCircle (1 : ℚ), t ∈ f.range ↔ n • t = 0) := by
  obtain ⟨g, hi, hr, hg⟩ := originalFiniteCyclic_exists_invariant u n hn hu hgen
  have hgu : g u = f u := by
    have h : g u = ↑((1 : ℚ) / n) := by
      simpa only [one_zsmul, Int.cast_one] using hg 1
    exact h.trans hf.symm
  have he : g = f := by
    apply AddMonoidHom.ext
    intro x
    obtain ⟨j, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen x)
    rw [map_zsmul, map_zsmul, hgu]
  exact he ▸ ⟨hi, hr⟩

/-- A full-order original class witness upgrades its actual idele-total descent to an injective invariant with exactly the degree-annihilator image. -/
theorem originalIdeleClass_normalized_invariant_of_witness
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hn : 0 < n) (hdegree : Module.finrank K L = n)
    (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (h : ∃ f : groupCohomology (originalIdeleClassRep K L) 2 →+ AddCircle (1 : ℚ),
      ∃ u : groupCohomology (originalIdeleClassRep K L) 2,
        (∀ x : groupCohomology (originalFullIdeleRep K L) 2,
          f ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) = total x) ∧
        f u = ↑((1 : ℚ) / n) ∧ addOrderOf u = n) :
    ∃ f : groupCohomology (originalIdeleClassRep K L) 2 →+ AddCircle (1 : ℚ),
      Function.Injective f ∧ (∀ t : AddCircle (1 : ℚ), t ∈ f.range ↔ n • t = 0) ∧
      ∀ x : groupCohomology (originalFullIdeleRep K L) 2,
        f ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) = total x := by
  obtain ⟨f, u, ht, hf, hu⟩ := h
  have hg := originalIdeleClass_full_order_generates K L u (hu.trans hdegree.symm)
  obtain ⟨hi, hr⟩ := originalFiniteCyclic_normalized_hom u n hn hu hg f hf
  exact ⟨f, hi, hr, ht⟩

end
end Dubon2026

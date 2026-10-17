import Dubon2026.OriginalFundamentalClassKilling
import Mathlib.SetTheory.Cardinal.Finite

/-! # The two-degree vanishing deduction for a finite class extension

The actual long exact sequence, a killed H2 generator and the exact H1/H2
cardinalities force the middle coefficient's H1 and H2 to vanish. The
augmentation ideal calculations remain explicit inputs here; they are
separate obligations on DUB-17's fundamental-class extension route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G]

/-- A killed generator of the original second cohomology makes the actual connecting map surjective. -/
theorem originalFiniteSplitting_connecting_surjective
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (u : groupCohomology X.X₁ 2) (hgen : Submodule.span k {u} = ⊤)
    (hkill : (groupCohomology.map (MonoidHom.id G) X.f 2).hom u = 0) :
    Function.Surjective (groupCohomology.δ hX 1 2 rfl).hom := by
  have he : LinearMap.range (groupCohomology.δ hX 1 2 rfl).hom =
      LinearMap.ker (groupCohomology.map (MonoidHom.id G) X.f 2).hom :=
    (groupCohomology.mapShortComplex₁_exact hX (rfl : 1 + 1 = 2)).moduleCat_range_eq_ker
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hgen, Submodule.span_le,
    Set.singleton_subset_iff, SetLike.mem_coe, he]
  exact hkill

/-- Exactness and equal finite orders turn the killed fundamental generator into H1/H2 vanishing of the actual middle coefficient. -/
theorem originalFiniteSplitting_first_second_zero
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (hC1 : Limits.IsZero (groupCohomology X.X₁ 1))
    (n : ℕ) (hn : n ≠ 0)
    (hC2 : Nat.card (groupCohomology X.X₁ 2) = n)
    (u : groupCohomology X.X₁ 2) (hgen : Submodule.span k {u} = ⊤)
    (hkill : (groupCohomology.map (MonoidHom.id G) X.f 2).hom u = 0)
    (hI1 : Nat.card (groupCohomology X.X₃ 1) = n)
    (hI2 : Limits.IsZero (groupCohomology X.X₃ 2)) :
    Limits.IsZero (groupCohomology X.X₂ 1) ∧
      Limits.IsZero (groupCohomology X.X₂ 2) := by
  have e1 : LinearMap.range (groupCohomology.map (MonoidHom.id G) X.f 1).hom =
      LinearMap.ker (groupCohomology.map (MonoidHom.id G) X.g 1).hom :=
    (groupCohomology.mapShortComplex₂_exact hX 1).moduleCat_range_eq_ker
  have e2 : LinearMap.range (groupCohomology.map (MonoidHom.id G) X.g 1).hom =
      LinearMap.ker (groupCohomology.δ hX 1 2 rfl).hom :=
    (groupCohomology.mapShortComplex₃_exact hX (rfl : 1 + 1 = 2)).moduleCat_range_eq_ker
  have e3 : LinearMap.range (groupCohomology.δ hX 1 2 rfl).hom =
      LinearMap.ker (groupCohomology.map (MonoidHom.id G) X.f 2).hom :=
    (groupCohomology.mapShortComplex₁_exact hX (rfl : 1 + 1 = 2)).moduleCat_range_eq_ker
  have e4 : LinearMap.range (groupCohomology.map (MonoidHom.id G) X.f 2).hom =
      LinearMap.ker (groupCohomology.map (MonoidHom.id G) X.g 2).hom :=
    (groupCohomology.mapShortComplex₂_exact hX 2).moduleCat_range_eq_ker
  have zC : ∀ c : groupCohomology X.X₁ 1, c = 0 := fun c => by
    simpa using congrArg (fun φ => φ.hom c) (hC1.eq_of_src (𝟙 _) 0)
  have zI : ∀ c : groupCohomology X.X₃ 2, c = 0 := fun c => by
    simpa using congrArg (fun φ => φ.hom c) (hI2.eq_of_src (𝟙 _) 0)
  have hsurj := originalFiniteSplitting_connecting_surjective hX u hgen hkill
  haveI : Finite (groupCohomology X.X₃ 1) := Nat.finite_of_card_ne_zero (hI1.trans_ne hn)
  have hbij : Function.Bijective (groupCohomology.δ hX 1 2 rfl).hom :=
    hsurj.bijective_of_nat_card_le (by rw [hI1, hC2])
  constructor
  · have hz : ∀ y : groupCohomology X.X₂ 1, y = 0 := by
      intro y
      have hy : (groupCohomology.map (MonoidHom.id G) X.g 1).hom y = 0 := by
        apply hbij.1
        rw [map_zero]
        have hy' : (groupCohomology.map (MonoidHom.id G) X.g 1).hom y ∈
            LinearMap.ker (groupCohomology.δ hX 1 2 rfl).hom := by
          rw [← e2]
          exact LinearMap.mem_range_self _ _
        exact hy'
      have hy' : y ∈ LinearMap.range (groupCohomology.map (MonoidHom.id G) X.f 1).hom := by
        rw [e1]
        exact hy
      obtain ⟨c, rfl⟩ := hy'
      rw [zC c, map_zero]
    letI : Subsingleton (groupCohomology X.X₂ 1) := ⟨fun a b => (hz a).trans (hz b).symm⟩
    exact ModuleCat.isZero_of_subsingleton _
  · have hz : ∀ y : groupCohomology X.X₂ 2, y = 0 := by
      intro y
      have hy : y ∈ LinearMap.range (groupCohomology.map (MonoidHom.id G) X.f 2).hom := by
        rw [e4, LinearMap.mem_ker]
        exact zI _
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨w, rfl⟩ := hsurj c
      have hw : (groupCohomology.δ hX 1 2 rfl).hom w ∈
          LinearMap.ker (groupCohomology.map (MonoidHom.id G) X.f 2).hom := by
        rw [← e3]
        exact LinearMap.mem_range_self _ _
      exact hw
    letI : Subsingleton (groupCohomology X.X₂ 2) := ⟨fun a b => (hz a).trans (hz b).symm⟩
    exact ModuleCat.isZero_of_subsingleton _

end
end Dubon2026

import Dubon2026.OriginalCoefficientConnectingNaturality
import Dubon2026.OriginalCoinducedExtensionDiagram
import Dubon2026.OriginalFundamentalDoubleConnecting

/-! # The actual H2 map forces the twice-shifted divisibility test

Naturality through two genuine coefficient diagrams turns vanishing
of the original H2 map into the exact double connecting kernel.
The original fundamental class's full order therefore gives the
integral invariant divisibility required on DUB-17's norm route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
variable {G : Type} [Group G]

/-- The actual H0 map to the trivial integer coefficient evaluates the same original invariant vector. -/
theorem originalH0Map_to_integer (A : Rep.{0} ℤ G) (f : A ⟶ Rep.trivial ℤ G ℤ)
    (z : A.ρ.invariants) :
    (groupCohomology.map (MonoidHom.id G) f 0) ((groupCohomology.H0Iso A).inv z) =
      (groupCohomology.H0IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv (f.hom z) := by
  apply (groupCohomology.H0Iso (Rep.trivial ℤ G ℤ)).toLinearEquiv.injective
  have hn := congrArg (fun t : groupCohomology A 0 ⟶
      ModuleCat.of ℤ (Rep.trivial ℤ G ℤ).ρ.invariants =>
        t ((groupCohomology.H0Iso A).inv z))
    (groupCohomology.map_id_comp_H0Iso_hom f)
  have hz := (groupCohomology.H0Iso A).toLinearEquiv.apply_symm_apply z
  have ht := (groupCohomology.H0Iso (Rep.trivial ℤ G ℤ)).toLinearEquiv.apply_symm_apply
    (⟨f.hom z, fun _ => rfl⟩ : (Rep.trivial ℤ G ℤ).ρ.invariants)
  exact hn.trans ((congrArg (fun v => ((Rep.invariantsFunctor ℤ G).map f) v) hz).trans ht.symm)

/-- Two genuine shift diagrams carry a zero original H2 map to exact group-order divisibility on the original twice-shifted invariants. -/
theorem originalDoubleShift_invariant_divisibility [Fintype G]
    (M C : Rep.{0} ℤ G) (φ : groupCohomology.cocycles₂ C)
    (ho : addOrderOf (groupCohomology.H2π C φ) = Fintype.card G)
    (d : originalCoinducedShortComplex M ⟶ originalFundamentalSplittingShortComplex C φ)
    (e : originalCoinducedShortComplex (originalCoinducedQuotient M) ⟶
      originalAugmentationShortComplex ℤ G)
    (he : e.τ₁ = d.τ₃)
    (hf : (groupCohomology.functor ℤ G 2).map d.τ₁ = 0)
    (z : (originalCoinducedQuotient (originalCoinducedQuotient M)).ρ.invariants) :
    (Fintype.card G : ℤ) ∣ e.τ₃.hom z.val := by
  let z₀ := (groupCohomology.H0Iso (originalCoinducedQuotient (originalCoinducedQuotient M))).inv z
  let y := (groupCohomology.δ (originalCoinducedShortComplex_shortExact
    (originalCoinducedQuotient M)) 0 1 rfl) z₀
  have hn₁ := congrArg (fun t : groupCohomology (originalCoinducedQuotient M) 1 ⟶
      groupCohomology C 2 => t y)
    (originalCoefficient_delta_naturality d (originalCoinducedShortComplex_shortExact M)
      (originalFundamentalSplittingShortComplex_shortExact C φ) 1 2 rfl)
  have hn₂ := congrArg (fun t :
      groupCohomology (originalCoinducedQuotient (originalCoinducedQuotient M)) 0 ⟶
      groupCohomology (originalAugmentationIdeal ℤ G) 1 => t z₀)
    (originalCoefficient_delta_naturality e
      (originalCoinducedShortComplex_shortExact (originalCoinducedQuotient M))
      (originalAugmentationShortComplex_shortExact ℤ G) 0 1 rfl)
  have h₁ : (groupCohomology.δ (originalFundamentalSplittingShortComplex_shortExact C φ) 1 2 rfl)
      ((groupCohomology.map (MonoidHom.id G) d.τ₃ 1) y) = 0 :=
    hn₁.symm.trans (congrArg (fun t : groupCohomology M 2 ⟶ groupCohomology C 2 =>
      t ((groupCohomology.δ (originalCoinducedShortComplex_shortExact M) 1 2 rfl) y)) hf)
  have h₂ : (groupCohomology.map (MonoidHom.id G) d.τ₃ 1) y =
      (groupCohomology.δ (originalAugmentationShortComplex_shortExact ℤ G) 0 1 rfl)
        ((groupCohomology.map (MonoidHom.id G) e.τ₃ 0) z₀) := by
    exact (congrArg (fun t => (groupCohomology.map (MonoidHom.id G) t 1) y) he).symm.trans hn₂
  apply (originalFundamentalDoubleConnectingMap_zero_iff C φ ho _).mp
  have h₀ := originalH0Map_to_integer (originalCoinducedQuotient (originalCoinducedQuotient M)) e.τ₃ z
  exact (congrArg (fun t : groupCohomology (Rep.trivial ℤ G ℤ) 0 =>
    (groupCohomology.δ (originalFundamentalSplittingShortComplex_shortExact C φ) 1 2 rfl)
      ((groupCohomology.δ (originalAugmentationShortComplex_shortExact ℤ G) 0 1 rfl) t)) h₀).symm.trans
    ((congrArg (fun t : groupCohomology (originalAugmentationIdeal ℤ G) 1 =>
      (groupCohomology.δ (originalFundamentalSplittingShortComplex_shortExact C φ) 1 2 rfl) t) h₂).symm.trans h₁)

end
end Dubon2026

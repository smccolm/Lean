import Dubon2026.GaloisTowerKernelCohomology
import Dubon2026.OriginalClassQuotientSubgroupCohomology

/-! # Literal quotient norm roots on the original restriction kernel

Reuse the proved kernel-to-relative-Galois equivalence. Its automorphisms
act identically on the actual outside-unit quotient, so reindexing the
finite action sum transports invariant norm roots without changing the
coefficient. This is the normal-subgroup norm input needed by DUB-17's
relation-extension argument at the constructed arithmetic tower.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module
variable (K E L : Type) [Field K] [Field E] [Field L] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L] [Normal K E]
  [FiniteDimensional K L] [FiniteDimensional E L]
  (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)

omit [FiniteDimensional E L] in
/-- Prime divisibility of the actual restriction kernel's order and
invariant roots of its literal quotient norm. This proposition only
states the required arithmetic condition; it asserts no construction. -/
def OriginalRestrictionKernelNormCondition (p : ℕ) : Prop :=
  let H := (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker
  letI : Fintype H := Fintype.ofFinite H
  p ∣ Nat.card H ∧
    ∀ c : originalIdeleClassesModOutsideRep K L T hT,
      ∃ d : originalIdeleClassesModOutsideRep K L T hT,
        (∀ g : H, (originalIdeleClassesModOutsideRep K L T hT).ρ g.val d = d) ∧
        (∑ g : H, (originalIdeleClassesModOutsideRep K L T hT).ρ g.val c) = p • d

/-- Relative invariant roots of literal quotient norms are precisely
invariant roots for the actual normal restriction kernel's action sum. -/
theorem originalClassQuotient_kernel_invariant_norm_roots (p : ℕ)
    (hnorm : ∀ c : originalIdeleClassesModOutsideRep E L T
        (fun σ v => hT (σ.restrictScalars K) v),
      ∃ d : originalIdeleClassesModOutsideRep E L T
        (fun σ v => hT (σ.restrictScalars K) v),
        (∀ g, (originalIdeleClassesModOutsideRep E L T
          (fun σ v => hT (σ.restrictScalars K) v)).ρ g d = d) ∧
        (∑ g : Gal(L/E), (originalIdeleClassesModOutsideRep E L T
          (fun σ v => hT (σ.restrictScalars K) v)).ρ g c) = p • d) :
    let H := (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker
    letI : Fintype H := Fintype.ofFinite H
    ∀ c : originalIdeleClassesModOutsideRep K L T hT,
      ∃ d : originalIdeleClassesModOutsideRep K L T hT,
        (∀ g : H, (originalIdeleClassesModOutsideRep K L T hT).ρ g.val d = d) ∧
        (∑ g : H, (originalIdeleClassesModOutsideRep K L T hT).ρ g.val c) = p • d := by
  intro H
  letI : Fintype H := Fintype.ofFinite H
  intro c
  obtain ⟨d, hd, hn⟩ := hnorm c
  let e := galoisTowerKernelEquiv K E L
  refine ⟨d, fun g => hd (e g), ?_⟩
  calc
    (∑ g : H, (originalIdeleClassesModOutsideRep K L T hT).ρ g.val c) =
        ∑ g : Gal(L/E), (originalIdeleClassesModOutsideRep E L T
          (fun σ v => hT (σ.restrictScalars K) v)).ρ g c :=
      Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)
    _ = p • d := hn

end
end Dubon2026

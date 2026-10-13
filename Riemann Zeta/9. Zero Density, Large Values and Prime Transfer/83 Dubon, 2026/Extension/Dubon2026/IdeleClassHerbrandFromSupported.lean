import Dubon2026.SupportedIdeleCohomologySequence
import Dubon2026.OriginalSUnitHerbrand

/-! # The original idele-class Herbrand formula from the supported-idele factor

The actual supported-idele short exact sequence and proved original
S-unit formula derive finite idele-class H1/H2 and their exact ratio.
Only finiteness and the cohomological orbit factor of the original
supported ideles remain as explicit upstream inputs. This isolates the
remaining local calculation needed for DUB-17's norm-index lower bound.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual supported-idele factor and original S-unit formula derive original idele-class finiteness and the group-order Herbrand ratio. -/
theorem original_ideleClass_herbrand_of_supported
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (hsurj : Function.Surjective (numberFieldSupportedIdeleClassMap L S))
    [Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 1)]
    [Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 2)]
    (hfactor : letI := sUnitLogPlaceAction K L S hS
      Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) 2) =
        Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) 1) *
          ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
            Nat.card (MulAction.stabilizer Gal(L/K) ω.out)) :
    Finite (groupCohomology (originalIdeleClassRep K L) 1) ∧
      Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) =
        Nat.card (groupCohomology (originalIdeleClassRep K L) 1) * Nat.card Gal(L/K) := by
  letI := sUnitLogPlaceAction K L S hS
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI : IsCyclic Gal(L/K) := ⟨⟨σ, hgen⟩⟩
  letI := IsCyclic.commGroup (α := Gal(L/K))
  let X := originalSupportedIdeleShortComplex K L S hS
  have hX := originalSupportedIdeleShortComplex_shortExact K L S hS hsurj
  have hu := original_sUnit_herbrand_cardinality K L S hS σ hgen
  letI : Finite (groupCohomology X.X₁ 1) := hu.1
  letI : Finite (groupCohomology X.X₁ 2) := hu.2.1
  letI : Finite (groupCohomology X.X₁ 3) := cyclic_cohomology_positive_finite X.X₁ σ hgen 2
  letI : Finite (groupCohomology X.X₂ 1) :=
    inferInstanceAs (Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 1))
  letI : Finite (groupCohomology X.X₂ 2) :=
    inferInstanceAs (Finite (groupCohomology (originalSupportedIdeleRep K L S hS) 2))
  have hfinite (n : ℕ) [Finite (groupCohomology X.X₂ n)]
      [Finite (groupCohomology X.X₁ (n + 1))] : Finite (groupCohomology X.X₃ n) :=
    finite_exact_module_middle
      (A := groupCohomology X.X₂ n) (B := groupCohomology X.X₃ n)
      (C := groupCohomology X.X₁ (n + 1))
      ((groupCohomology.functor ℤ Gal(L/K) n).map X.g).hom
      (groupCohomology.δ hX n (n + 1) rfl).hom
      (groupCohomology.mapShortComplex₃_exact hX rfl).moduleCat_range_eq_ker
  letI := hfinite 1
  letI := hfinite 2
  refine ⟨inferInstanceAs (Finite (groupCohomology X.X₃ 1)),
    inferInstanceAs (Finite (groupCohomology X.X₃ 2)), ?_⟩
  change Nat.card (groupCohomology X.X₃ 2) =
    Nat.card (groupCohomology X.X₃ 1) * Nat.card Gal(L/K)
  have hm := (cyclic_cohomology_herbrand_cardinality X hX σ hgen).2.2
  have he : Nat.card (groupCohomology X.X₂ 2) * Nat.card (groupCohomology X.X₁ 1) =
      Nat.card (groupCohomology X.X₂ 1) * Nat.card (groupCohomology X.X₁ 2) * Nat.card Gal(L/K) := by
    change Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) 2) *
        Nat.card (groupCohomology (sUnitOriginalRep K L S hS) 1) = _
    rw [hfactor]
    calc
      _ = Nat.card (groupCohomology X.X₂ 1) *
        (Nat.card (groupCohomology X.X₁ 1) *
          ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
            Nat.card (MulAction.stabilizer Gal(L/K) ω.out)) := by
              change (_ * _) * Nat.card (groupCohomology X.X₁ 1) = _
              ac_rfl
      _ = Nat.card (groupCohomology X.X₂ 1) *
          (Nat.card (groupCohomology X.X₁ 2) * Nat.card Gal(L/K)) :=
            congrArg (fun n => Nat.card (groupCohomology X.X₂ 1) * n) hu.2.2.symm
      _ = _ := by ac_rfl
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (Nat.card_pos (α := groupCohomology X.X₂ 1))
      (Nat.card_pos (α := groupCohomology X.X₁ 2)))
  calc
    (Nat.card (groupCohomology X.X₂ 1) * Nat.card (groupCohomology X.X₁ 2)) *
        Nat.card (groupCohomology X.X₃ 2) =
      (Nat.card (groupCohomology X.X₂ 2) * Nat.card (groupCohomology X.X₁ 1)) *
        Nat.card (groupCohomology X.X₃ 1) := hm.symm
    _ = (Nat.card (groupCohomology X.X₂ 1) * Nat.card (groupCohomology X.X₁ 2) *
        Nat.card Gal(L/K)) * Nat.card (groupCohomology X.X₃ 1) := by rw [he]
    _ = _ := by ac_rfl

end
end Dubon2026

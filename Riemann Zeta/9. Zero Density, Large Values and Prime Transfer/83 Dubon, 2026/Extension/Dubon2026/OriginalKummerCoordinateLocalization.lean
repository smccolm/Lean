/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the retained upstream LICENSE.
The coordinate fixed-field argument is adapted from ClassFieldTheory
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/SUnitKummerPrimeSelection/Conclusion.lean.
The local-power bridge uses the original native completion and prime action.
-/
import Dubon2026.OriginalLocalKummerFixedRoot
import Dubon2026.OriginalCoordinatePrimeSet

/-! # The original coordinate local-power kernel

At the selected original primes, local power conditions fix exactly the
coordinate generators. Their proved span fixes exactly the original
restriction kernel, hence places the original Kummer root in the prescribed
subextension. This identifies the kernel needed to calculate the S-unit
local-unit power-map image on DUB-17's principal/class index chain. It does
not yet identify the different principal S-union-T local-power subgroup.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The selected original coordinate local-power conditions cut out precisely
the fixed field of the original subgroup spanned by those coordinates. -/
theorem originalLocalKummer_coordinates_iff_fixed
    (p : ℕ) (hp : 0 < p) (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (r : ℕ) (H : Subgroup Gal(L/K))
    (e : H ≃* (Fin r → Multiplicative (ZMod p)))
    (w : Fin r → HeightOneSpectrum (𝓞 L))
    (hD : ∀ i, OriginalFiniteDecompositionGroup K L (w i) =
      Subgroup.zpowers (primeCoordinateGenerator e i).val)
    (a : Kˣ) (β : Lˣ) (hβ : (β : L) ^ p = algebraMap K L (a : K)) :
    (∀ i, Units.map (algebraMap K ((originalFinitePrimeBelow K L (w i)).adicCompletion K)).toMonoidHom a ∈
      (powMonoidHom p : ((originalFinitePrimeBelow K L (w i)).adicCompletion K)ˣ →*
        ((originalFinitePrimeBelow K L (w i)).adicCompletion K)ˣ).range) ↔
    (β : L) ∈ IntermediateField.fixedField H := by
  letI : NeZero p := ⟨hp.ne'⟩
  have hLocal (i : Fin r) := by
    letI : (w i).asIdeal.LiesOver (originalFinitePrimeBelow K L (w i)).asIdeal :=
      originalFinitePrimeBelow_liesOver K L (w i)
    exact originalLocalKummer_power_iff_fixed K L (originalFinitePrimeBelow K L (w i))
      (w i) p hp ζ hζ a β hβ
  constructor
  · intro h
    let Fix : Subgroup H := MulAction.stabilizer H (β : L)
    have hGenerator (i : Fin r) : primeCoordinateGenerator e i ∈ Fix := by
      have hi := (hLocal i).mp (h i)
      rw [hD i, IntermediateField.mem_fixedField_iff] at hi
      exact hi (primeCoordinateGenerator e i).val (Subgroup.mem_zpowers _)
    have hSpan : (⨆ i : Fin r, Subgroup.zpowers (primeCoordinateGenerator e i)) ≤ Fix := by
      exact iSup_le fun i => Subgroup.zpowers_le.mpr (hGenerator i)
    rw [primeCoordinateGenerator_iSup] at hSpan
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    exact hSpan (Subgroup.mem_top (⟨σ, hσ⟩ : H))
  · intro h i
    apply (hLocal i).mpr
    rw [hD i, IntermediateField.mem_fixedField_iff]
    rw [IntermediateField.mem_fixedField_iff] at h
    intro σ hσ
    exact h σ ((Subgroup.zpowers_le.mpr (primeCoordinateGenerator e i).property) hσ)

/-- For coordinates of the actual restriction kernel, the selected original
local-power conditions hold exactly when the original root belongs to the
prescribed original subextension. -/
theorem originalLocalKummer_coordinates_iff_mem_subextension
    (E : IntermediateField K L) [IsGalois K E]
    (p : ℕ) (hp : 0 < p) (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (r : ℕ) (e : (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker ≃*
      (Fin r → Multiplicative (ZMod p)))
    (w : Fin r → HeightOneSpectrum (𝓞 L))
    (hD : ∀ i, OriginalFiniteDecompositionGroup K L (w i) =
      Subgroup.zpowers (primeCoordinateGenerator e i).val)
    (a : Kˣ) (β : Lˣ) (hβ : (β : L) ^ p = algebraMap K L (a : K)) :
    (∀ i, Units.map (algebraMap K ((originalFinitePrimeBelow K L (w i)).adicCompletion K)).toMonoidHom a ∈
      (powMonoidHom p : ((originalFinitePrimeBelow K L (w i)).adicCompletion K)ˣ →*
        ((originalFinitePrimeBelow K L (w i)).adicCompletion K)ˣ).range) ↔ (β : L) ∈ E := by
  rw [originalLocalKummer_coordinates_iff_fixed K L p hp ζ hζ r _ e w hD a β hβ,
    IntermediateField.restrictNormalHom_ker, IsGalois.fixedField_fixingSubgroup]

end
end Dubon2026

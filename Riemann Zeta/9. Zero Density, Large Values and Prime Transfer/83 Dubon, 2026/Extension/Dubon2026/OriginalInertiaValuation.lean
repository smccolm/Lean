import Dubon2026.NumberFieldGaloisValuation
import Mathlib.RingTheory.Ideal.Pointwise

/-! # Original inertia fixes residues of all valuation integers

Pinned integer approximation and the original Galois valuation transport
extend the original inertia congruence from global integers to every
original field element integral at the prime. Applied to a unit Kummer
generator, this places its inertia ratio in the principal units. Unit-
exponent residue injectivity then kills inertia, supplying the required
unramifiedness in DUB-17's principal localization norm argument.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Pointwise
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField L] in
/-- Actual inertia fixes the actual original prime under its original
Galois place action. -/
theorem originalInertia_fixes_prime
    (w : HeightOneSpectrum (𝓞 L)) (σ : Gal(L/K))
    (hσ : σ ∈ w.asIdeal.inertia Gal(L/K)) :
    numberFieldGaloisPlaceEquiv K L σ w = w := by
  apply HeightOneSpectrum.ext
  rw [numberFieldGaloisPlaceEquiv_asIdeal]
  have h := (Ideal.inertia_le_stabilizer w.asIdeal) hσ
  change σ • w.asIdeal = w.asIdeal at h
  rw [Ideal.pointwise_smul_def] at h
  have he : MulSemiringAction.toRingHom Gal(L/K) (𝓞 L) σ =
      (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingHom := by
    ext a
    rfl
  rw [he] at h
  exact h

/-- Every original valuation integer is fixed modulo the actual prime by
original inertia; no integrality over the global integer ring is required. -/
theorem originalInertia_valuation_sub_lt_one
    (w : HeightOneSpectrum (𝓞 L)) (σ : Gal(L/K))
    (hσ : σ ∈ w.asIdeal.inertia Gal(L/K))
    (x : L) (hx : w.valuation L x ≤ 1) :
    w.valuation L (σ x - x) < 1 := by
  have hVal (y : L) : w.valuation L (σ y) = w.valuation L y := by
    have h := numberFieldGaloisPlace_valuation K L σ w y
    rw [originalInertia_fixes_prime K L w σ hσ] at h
    exact h
  obtain ⟨a, ha⟩ := w.exists_valuation_sub_lt_of_integer hx 1
  have hInt : w.valuation L (σ (a : L) - (a : L)) < 1 := by
    have h := (w.valuation_lt_one_iff_mem (K := L) (σ • a - a)).mpr (hσ a)
    exact h
  have hFirst : w.valuation L (σ x - σ (a : L)) < 1 := by
    rw [← map_sub, hVal, Valuation.map_sub_swap]
    exact ha
  have h := (w.valuation L).map_add_lt ((w.valuation L).map_add_lt hFirst hInt) ha
  have he : σ x - x = ((σ x - σ (a : L)) + (σ (a : L) - (a : L))) + ((a : L) - x) := by ring
  rw [he]
  exact h

end
end Dubon2026

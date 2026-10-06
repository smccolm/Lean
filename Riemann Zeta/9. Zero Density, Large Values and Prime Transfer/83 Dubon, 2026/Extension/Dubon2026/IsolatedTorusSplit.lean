import Dubon2026.IsolatedBohrDecomposition
import Dubon2026.SteinhausPhases
import Dubon2026.JessenMean

/-! # The actual product-Haar split and the conditioned Bohr polynomial -/

namespace Dubon2026

open MeasureTheory

noncomputable section

/-- The prime coordinates complementary to the selected isolated primes. -/
abbrev ComplementaryPrimeCoordinates {N : ℕ} (S : Finset (PrimeCoordinate N)) :=
  {p : PrimeCoordinate N // p ∉ S}

/-- The measurable split into the selected and complementary circle coordinates. -/
def primeTorusSplit (N : ℕ) (S : Finset (PrimeCoordinate N)) :
    PrimeTorus N ≃ᵐ ((↥S → UnitAddCircle) × (ComplementaryPrimeCoordinates S → UnitAddCircle)) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : PrimeCoordinate N => UnitAddCircle) (fun p => p ∈ S)

theorem measurePreserving_primeTorusSplit (N : ℕ) (S : Finset (PrimeCoordinate N)) :
    MeasurePreserving (primeTorusSplit N S) (torusHaar N)
      ((steinhausHaar ↥S).prod (steinhausHaar (ComplementaryPrimeCoordinates S))) := by
  unfold primeTorusSplit torusHaar steinhausHaar
  have h := measurePreserving_piEquivPiSubtypeProd
    (fun _ : PrimeCoordinate N => (AddCircle.haarAddCircle : Measure UnitAddCircle)) (fun p => p ∈ S)
  have hi : (Subtype.fintype (fun p : PrimeCoordinate N => p ∈ S)) = Finset.Subtype.fintype S :=
    Subsingleton.elim _ _
  rw [hi] at h
  exact h

theorem measurePreserving_primeTorusSplit_symm (N : ℕ) (S : Finset (PrimeCoordinate N)) :
    MeasurePreserving (primeTorusSplit N S).symm
      ((steinhausHaar ↥S).prod (steinhausHaar (ComplementaryPrimeCoordinates S))) (torusHaar N) :=
  MeasurePreserving.symm (primeTorusSplit N S) (measurePreserving_primeTorusSplit N S)

theorem primeTorusSplit_symm_apply {N : ℕ} (S : Finset (PrimeCoordinate N))
    (z : ↥S → UnitAddCircle) (w : ComplementaryPrimeCoordinates S → UnitAddCircle)
    (p : PrimeCoordinate N) :
    (primeTorusSplit N S).symm (z, w) p = if hp : p ∈ S then z ⟨p, hp⟩ else w ⟨p, hp⟩ := rfl

/-- The literal Bohr remainder with the selected complex coordinates set to zero. -/
def isolatedBohrRemainder (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (S : Finset (PrimeCoordinate N))
    (w : ComplementaryPrimeCoordinates S → UnitAddCircle) : ℂ :=
  bohrLift a N σ (fun p => if hp : p ∈ S then 0 else fourier 1 (w ⟨p, hp⟩))

theorem bohrOnTorus_conditioned (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    (S : Finset (PrimeCoordinate N)) (hS : ∀ p ∈ S, N < 2 * p.val)
    (z : ↥S → UnitAddCircle) (w : ComplementaryPrimeCoordinates S → UnitAddCircle) :
    bohrOnTorus a N σ ((primeTorusSplit N S).symm (z, w)) =
      isolatedBohrRemainder a N σ S w +
        ∑ p : ↥S, a p.val.val * (p.val.val : ℂ) ^ (-(σ : ℂ)) * fourier 1 (z p) := by
  change bohrLift a N σ _ = _
  rw [isolatedBohr_decomposition a N σ S hS]
  congr 1
  · unfold isolatedBohrRemainder
    congr 1
    ext p
    unfold erasePrimeCoordinates
    by_cases hp : p ∈ S
    · simp [hp]
    · simp [hp, primeTorusSplit_symm_apply]
  · rw [← Finset.sum_coe_sort S]
    apply Finset.sum_congr rfl
    intro p _
    rw [primeTorusSplit_symm_apply, dif_pos p.property]

theorem integrable_split_bohr_log (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    (S : Finset (PrimeCoordinate N)) :
    Integrable (fun p => Real.log ‖bohrOnTorus a N σ ((primeTorusSplit N S).symm p)‖)
      ((steinhausHaar ↥S).prod (steinhausHaar (ComplementaryPrimeCoordinates S))) :=
  (measurePreserving_primeTorusSplit_symm N S).integrable_comp_of_integrable
    (integrable_bohrOnTorus_log a N σ)

theorem integral_split_bohr_log (a : ℕ → ℂ) (N : ℕ) (σ : ℝ)
    (S : Finset (PrimeCoordinate N)) :
    (∫ p, Real.log ‖bohrOnTorus a N σ ((primeTorusSplit N S).symm p)‖
      ∂(steinhausHaar ↥S).prod (steinhausHaar (ComplementaryPrimeCoordinates S))) =
        ∫ z, Real.log ‖bohrOnTorus a N σ z‖ ∂torusHaar N :=
  (measurePreserving_primeTorusSplit_symm N S).integral_comp
    (primeTorusSplit N S).symm.measurableEmbedding (fun z : PrimeTorus N => Real.log ‖bohrOnTorus a N σ z‖)

end

end Dubon2026

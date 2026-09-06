import GafniTao.SignedReflectedWideEnergy

/-!
# The complete two-sign reflected-wide energy reduction

The Poisson reflection supplies one of two signs independently at every
ordinate.  This module first colours all four coordinates of the additive
energy by those signs and then performs the bounded-shift dyadic extraction
inside every resulting self family.  Both losses remain literal.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Data produced after fixing all four reflection signs and performing all
four bounded-shift dyadic extractions. -/
structure ReflectedWideEnergyOutput
    (W : Finset Real) (H S R : Real) (k : Nat) (a : Nat → Complex) where
  sign : Fin 4 → Fin 2
  Ws : Fin 4 → Finset Real
  hSubset : ∀ i : Fin 4, Ws i ⊆ W
  hSeparated : ∀ i : Fin 4, IsSeparated 1 (Ws i)
  hCommonSign : ∀ i : Fin 4, ∀ t, t ∈ Ws i →
    (sign i = 0 →
      ∃ s : Real, |(-t) - s| ≤ H ∧ (-R ≤ s ∧ s ≤ R) ∧
        S ≤ ‖wideDirichletPoly 1 k a s‖) ∧
    (sign i = 1 →
      ∃ s : Real, |t - s| ≤ H ∧ (-R ≤ s ∧ s ≤ R) ∧
        S ≤ ‖wideDirichletPoly 1 k a s‖)
  hSignEnergy :
    4 * (ApproxAddEnergy 1 W : Real) ≤
      16 * (doubleFloorDefectWindow 1).card *
        ((ApproxAddEnergy 1 (Ws 0) : Real) +
          (ApproxAddEnergy 1 (Ws 1) : Real) +
          (ApproxAddEnergy 1 (Ws 2) : Real) +
          (ApproxAddEnergy 1 (Ws 3) : Real))
  label : Fin 4 → Fin 4 → Fin k
  U : Fin 4 → Fin 4 → Finset Real
  hDyadicSeparated : ∀ i j : Fin 4, IsSeparated 1 (U i j)
  hDyadicRange : ∀ i j : Fin 4, ∀ t, t ∈ U i j →
    -R ≤ t ∧ t ≤ R
  hDyadicLarge : ∀ i j : Fin 4, ∀ t, t ∈ U i j →
    S / k ≤ ‖dirichletPoly (2 ^ ((label i j : Fin k) : Nat)) a t‖
  hDyadicEnergy : ∀ i : Fin 4,
    4 * (ApproxAddEnergy 1 (Ws i) : Real) ≤
      ((2 * k : Nat) : Real) ^ 4 *
        ((2 * ⌈H + 1⌉₊ + 1 : Nat) : Real) ^ 4 *
        (doubleFloorDefectWindow (1 + 4 * (H + 1))).card *
        ((ApproxAddEnergy 1 (U i 0) : Real) +
          (ApproxAddEnergy 1 (U i 1) : Real) +
          (ApproxAddEnergy 1 (U i 2) : Real) +
          (ApproxAddEnergy 1 (U i 3) : Real))

/-- Exact finite composition of the four-coordinate sign split with the
four-coordinate bounded-shift dyadic extractor. -/
theorem reflected_wide_energy_to_dyadic_self
    (W : Finset Real) (hW : IsSeparated 1 W)
    (H S R : Real) (k : Nat) (hk : 0 < k) (a : Nat → Complex)
    (negative positive : Real → Prop)
    (hAlternative : ∀ t, t ∈ W → negative t ∨ positive t)
    (hNegative : ∀ t, t ∈ W → negative t →
      ∃ s : Real, |(-t) - s| ≤ H ∧ (-R ≤ s ∧ s ≤ R) ∧
        S ≤ ‖wideDirichletPoly 1 k a s‖)
    (hPositive : ∀ t, t ∈ W → positive t →
      ∃ s : Real, |t - s| ≤ H ∧ (-R ≤ s ∧ s ≤ R) ∧
        S ≤ ‖wideDirichletPoly 1 k a s‖) :
    Nonempty (ReflectedWideEnergyOutput W H S R k a) := by
  classical
  obtain ⟨sign, Ws, hSub, hSep, hSign, hSignEnergy⟩ :=
    reflection_sign_energy_split W hW negative positive hAlternative
  have hCommon : ∀ i : Fin 4, ∀ t, t ∈ Ws i →
      (sign i = 0 →
        ∃ s : Real, |(-t) - s| ≤ H ∧ (-R ≤ s ∧ s ≤ R) ∧
          S ≤ ‖wideDirichletPoly 1 k a s‖) ∧
      (sign i = 1 →
        ∃ s : Real, |t - s| ≤ H ∧ (-R ≤ s ∧ s ≤ R) ∧
          S ≤ ‖wideDirichletPoly 1 k a s‖) := by
    intro i t ht
    constructor
    · intro hi
      exact hNegative t (hSub i ht) ((hSign i t ht).1 hi)
    · intro hi
      exact hPositive t (hSub i ht) ((hSign i t ht).2 hi)
  have hEach : ∀ i : Fin 4,
      ∃ r : Fin 4 → Fin k, ∃ U : Fin 4 → Finset Real,
        (∀ j : Fin 4, IsSeparated 1 (U j)) ∧
        (∀ j : Fin 4, ∀ t, t ∈ U j → -R ≤ t ∧ t ≤ R) ∧
        (∀ j : Fin 4, ∀ t, t ∈ U j →
          S / k ≤ ‖dirichletPoly (2 ^ (r j : Nat)) a t‖) ∧
        4 * (ApproxAddEnergy 1 (Ws i) : Real) ≤
          ((2 * k : Nat) : Real) ^ 4 *
            ((2 * ⌈H + 1⌉₊ + 1 : Nat) : Real) ^ 4 *
            (doubleFloorDefectWindow (1 + 4 * (H + 1))).card *
            ((ApproxAddEnergy 1 (U 0) : Real) +
              (ApproxAddEnergy 1 (U 1) : Real) +
              (ApproxAddEnergy 1 (U 2) : Real) +
              (ApproxAddEnergy 1 (U 3) : Real)) := by
    intro i
    apply signed_reflected_wide_energy_to_dyadic_self
      (sign i) (Ws i) (hSep i) H S R k hk a
    intro t ht
    by_cases hs : sign i = 0
    · simp only [if_pos hs]
      exact (hCommon i t ht).1 hs
    · have hsOne : sign i = 1 := by
        apply Fin.eq_of_val_eq
        have hlt := (sign i).isLt
        have hne : (sign i).val ≠ 0 := by
          intro hz
          apply hs
          apply Fin.eq_of_val_eq
          simpa using hz
        omega
      simp only [if_neg hs]
      exact (hCommon i t ht).2 hsOne
  choose label U hSepU hRangeU hLargeU hEnergyU using hEach
  exact ⟨⟨sign, Ws, hSub, hSep, hCommon, hSignEnergy,
    label, U, hSepU, hRangeU, hLargeU, hEnergyU⟩⟩

#print axioms ReflectedWideEnergyOutput
#print axioms reflected_wide_energy_to_dyadic_self

end

end GafniTao

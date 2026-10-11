import Dubon2026.MatrixIdealQuotientHopfModels

/-! # Original coefficient maps induce faithful maps from their actual comap quotients -/

namespace Dubon2026
noncomputable section
open Matrix

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The original coefficient map induces the genuine quotient map from the inverse image of the original target ideal. -/
def coefficientComapQuotientMap (f : A →+* B) (J : Ideal B) :
    (A ⧸ J.comap f) →+* (B ⧸ J) :=
  Ideal.Quotient.lift (J.comap f) ((Ideal.Quotient.mk J).comp f)
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr ha)

/-- Evaluation retains the original coefficient and its actual target quotient class. -/
theorem coefficientComapQuotientMap_mk (f : A →+* B) (J : Ideal B) (a : A) :
    coefficientComapQuotientMap f J (Ideal.Quotient.mk (J.comap f) a) =
      Ideal.Quotient.mk J (f a) := by
  rfl

/-- The original comap ideal is precisely what makes the actual induced quotient map injective. -/
theorem coefficientComapQuotientMap_injective (f : A →+* B) (J : Ideal B) :
    Function.Injective (coefficientComapQuotientMap f J) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      intro h
      apply Ideal.Quotient.eq.mpr
      change f (a - b) ∈ J
      rw [map_sub]
      exact Ideal.Quotient.eq.mp h

variable {G ι : Type*} [Group G] [Fintype ι] [DecidableEq ι]

/-- The faithful original comap quotient map intertwines the entire original reduced matrix representation with the actual reduction after coefficient change. -/
theorem matrixIdealQuotientRepresentation_comap (f : A →+* B) (J : Ideal B)
    (ρ : G →* GeneralLinearGroup ι A) :
    (GeneralLinearGroup.map (coefficientComapQuotientMap f J)).comp
      (matrixIdealQuotientRepresentation (J.comap f) ρ) =
    matrixIdealQuotientRepresentation J ((GeneralLinearGroup.map f).comp ρ) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  ext i j
  rfl

end
end Dubon2026

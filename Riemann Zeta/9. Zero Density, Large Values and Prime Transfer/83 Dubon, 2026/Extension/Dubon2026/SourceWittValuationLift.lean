import Dubon2026.SourceWittResidueLift
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Valuation.LocalSubring

/-! A characteristic-zero valuation model for a perfect field, using native
local domination of the Witt ring inside the algebraic closure of its fraction
field. This is the coefficient realization needed by the residue quotient
product. The archived FLT power-series and transcendental conditions are not
needed after the general characteristic-zero product theorem. -/

namespace Dubon2026.SourceWittLift
open IsLocalRing
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [PerfectRing K p]

/-- The algebraic closure of the Witt fraction field has characteristic zero. -/
theorem fractionClosure_charZero :
    CharZero (AlgebraicClosure (FractionRing (WittVector p K))) := by
  letI := witt_charZero p K
  letI : CharZero (FractionRing (WittVector p K)) := IsFractionRing.charZero (WittVector p K)
  exact charZero_of_injective_algebraMap
    (algebraMap (FractionRing (WittVector p K))
      (AlgebraicClosure (FractionRing (WittVector p K)))).injective

/-- A local valuation lift with literal Teichmuller residue compatibility exists. -/
theorem exists_valuation_lift :
    ∃ (A : ValuationSubring (AlgebraicClosure (FractionRing (WittVector p K))))
      (f : WittVector p K →+* A) (ι : K →+* ResidueField A),
      ∀ a : K, residue A (f (WittVector.teichmuller p a)) = ι a := by
  let φ := (algebraMap (FractionRing (WittVector p K))
    (AlgebraicClosure (FractionRing (WittVector p K)))).comp
    (algebraMap (WittVector p K) (FractionRing (WittVector p K)))
  obtain ⟨A, hA, hf⟩ := IsLocalRing.exists_factor_valuationRing φ
  let f : WittVector p K →+* A := φ.codRestrict A.toSubring hA
  letI : IsLocalHom f := hf
  exact ⟨A, f, residueMap p K f, fun a => (residueMap_teichmuller p K f a).symm⟩

end
end Dubon2026.SourceWittLift

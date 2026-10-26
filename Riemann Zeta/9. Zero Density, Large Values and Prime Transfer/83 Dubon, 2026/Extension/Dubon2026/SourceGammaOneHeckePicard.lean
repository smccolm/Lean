import Dubon2026.SourceGammaOneHeckeFieldFinite
import Dubon2026.SourceGammaOneResidues
import Dubon2026.SourceCurvePicardCorrespondence

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> genuine Picard Hecke correspondence. Existing actual divisor
pullback/pushforward and norm/degree theorems consume the proved finite maps
and closed residue fields. No norm, degree or finite-map certificate remains.
Comparison with the finite H1 operator, diamonds and arithmetic Galois action
remain required. Reuse SourceOriginalHeckePicard's construction on the actual
Gamma1 fields; no new divisor or Picard foundations are introduced. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve
variable (L : Type*) [Field L] [Algebra ℚ L] [CharZero L] [IsAlgClosed L]
variable (M d : ℕ) [NeZero M] [NeZero d]

/-- The actual Gamma1 divisor Hecke operator: beta pullback followed by alpha pushforward. -/
def heckeDivisor :
    Divisor L (laurentBaseChange L (x1FunctionField M)) →+
      Divisor L (laurentBaseChange L (x1FunctionField M)) :=
  Divisor.geometricCorrespondence (heckeBeta L M d) (heckeAlpha L M d)
    (heckeBeta_finite L M d) (heckeAlpha_finite L M d)

theorem heckeDivisor_mem_degZero
    {D : Divisor L (laurentBaseChange L (x1FunctionField M))}
    (hD : D ∈ Divisor.degZero) : heckeDivisor L M d D ∈ Divisor.degZero :=
  Divisor.geometricCorrespondence_mem_degZero _ _ _ _
    (gamma1_place_residue_bijective L M)
    (gamma1_hecke_place_residue_bijective L M (d * M)) hD

theorem isPrincipal_heckeDivisor
    {D : Divisor L (laurentBaseChange L (x1FunctionField M))}
    (hD : Divisor.IsPrincipal D) : Divisor.IsPrincipal (heckeDivisor L M d D) :=
  Divisor.isPrincipal_geometricCorrespondence _ _ _ _
    (gamma1_place_residue_bijective L M)
    (gamma1_hecke_place_residue_bijective L M (d * M)) hD

/-- The actual Gamma1 Hecke endomorphism of degree-zero divisor classes. -/
def heckePicard :
    Pic0 L (laurentBaseChange L (x1FunctionField M)) →+
      Pic0 L (laurentBaseChange L (x1FunctionField M)) :=
  Pic0.geometricCorrespondence (heckeBeta L M d) (heckeAlpha L M d)
    (heckeBeta_finite L M d) (heckeAlpha_finite L M d)
    (gamma1_place_residue_bijective L M)
    (gamma1_hecke_place_residue_bijective L M (d * M))

theorem heckePicard_mk
    (D : Divisor.degZero (K := L) (F := laurentBaseChange L (x1FunctionField M))) :
    heckePicard L M d (Pic0.mk D) =
      Pic0.mk ⟨heckeDivisor L M d D.val, heckeDivisor_mem_degZero L M d D.2⟩ :=
  Pic0.geometricCorrespondence_mk _ _ _ _ _ _ D

end
end Dubon2026.SourceFunctionField.GammaOne

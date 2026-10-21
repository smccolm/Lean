import Dubon2026.SourceAffineFunctionFlag
import Dubon2026.SourceAffineFunctionHecke

/-! Native coefficient representations for the actual affine function flag.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> lifting a character eigenclass through this explicit quotient.
All group actions, leading characters and coefficient maps are the original
matrix and function constructions; the quotient is proved surjective.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] [CharP F p] (hpQ : p ∣ Q)
    (j : Fin p)

/-- The actual function flag is a native subrepresentation of the affine action. -/
def sourceAffineFlagSubrepresentation :
    Subrepresentation (sourceAffineFunctionRep p Q F hpQ).ρ where
  toSubmodule := sourceFiniteFunctionFlag F p j.val
  apply_mem_toSubmodule g _ hf := sourceAffineFunction_flag_stable F p Q hpQ j.isLt g hf

/-- The native representation of the actual finite-function flag. -/
def sourceAffineFlagRep : Rep F (Gamma0 Q) :=
  Rep.of (sourceAffineFlagSubrepresentation F p Q hpQ j).toRepresentation

/-- The original Hecke argument rescaling restricted to the actual function flag. -/
def sourceAffineFlagDiagonal (ell : ℕ) : Module.End F (sourceFiniteFunctionFlag F p j.val) :=
  (sourceAffineFunctionDiagonal p F ell).restrict
    (fun _ hf => sourceAffineFunctionDiagonal_flag_stable F p ell hf)

/-- The original leading coordinate gives an equivariant surjection to the exact character. -/
def sourceAffineFlagQuotientMap :
    sourceAffineFlagRep F p Q hpQ j ⟶ sourceBinaryFlagQuotientRep F p Q hpQ (2 * j.val) 0 :=
  Rep.ofHom {
    toLinearMap := (sourceFiniteFunctionCoordinate F p j).comp
      (sourceFiniteFunctionFlag F p j.val).subtype
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro f
      change sourceFiniteFunctionCoordinate F p j ((sourceAffineFunctionRep p Q F hpQ).ρ g f.val) =
        sourceBinaryFlagCharacter F p Q hpQ (2 * j.val) 0 g *
          sourceFiniteFunctionCoordinate F p j f.val
      simpa [sourceBinaryFlagCharacter, sourceAffineD] using
        sourceAffineFunctionCoordinate_action F p Q hpQ j g f.property }

/-- Every original character coefficient is reached by its explicit top monomial. -/
theorem sourceAffineFlagQuotientMap_surjective :
    Function.Surjective (sourceAffineFlagQuotientMap F p Q hpQ j) := by
  intro x
  change F at x
  refine ⟨⟨x • sourceFiniteFunctionMonomial F p j.val,
    Submodule.smul_mem _ x
      (sourceFiniteFunctionMonomial_mem_flag F p (le_refl j.val) j.isLt)⟩, ?_⟩
  change sourceFiniteFunctionCoordinate F p j (x • sourceFiniteFunctionMonomial F p j.val) = x
  rw [map_smul, sourceFiniteFunctionCoordinate_monomial F p j j.isLt,
    if_pos rfl, smul_eq_mul, mul_one]

private local instance affineFlagPrimeNeZero (ell : sourceBinaryHeckePrime Q) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

/-- The restricted affine coefficient map retains the exact original conjugation compatibility. -/
theorem sourceAffineFlagDiagonal_intertwine (ell : sourceBinaryHeckePrime Q)
    (u : heckeUpperSubgroup Q ell.val) :
    (sourceAffineFlagDiagonal F p j ell.val).comp
        ((sourceAffineFlagRep F p Q hpQ j).ρ (sourceHeckeConjugation ell.property.1 u)) =
      ((sourceAffineFlagRep F p Q hpQ j).ρ u.val).comp
        (sourceAffineFlagDiagonal F p j ell.val) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact LinearMap.congr_fun (sourceAffineFunctionDiagonal_intertwine F p Q hpQ ell u) f.val

/-- The original argument rescalings commute on every actual function-flag step. -/
theorem sourceAffineFlagDiagonal_commute (a b : ℕ) :
    (sourceAffineFlagDiagonal F p j a).comp (sourceAffineFlagDiagonal F p j b) =
      (sourceAffineFlagDiagonal F p j b).comp (sourceAffineFlagDiagonal F p j a) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact LinearMap.congr_fun (sourceAffineFunctionDiagonal_commute p F a b) f.val

/-- The complete original good-prime Hecke family on native H1 of the actual function flag. -/
def sourceAffineFlagHeckeOperators :
    sourceBinaryHeckePrime Q → Module.End F
      (groupCohomology.H1 (sourceAffineFlagRep F p Q hpQ j)) :=
  fun ell => sourcePrimeHeckeH1 ell.property.1 (sourceAffineFlagRep F p Q hpQ j)
    (sourceAffineFlagDiagonal F p j ell.val)
    (sourceAffineFlagDiagonal_intertwine F p Q hpQ j ell)

/-- Every pair of original good-prime function-flag H1 operators commutes. -/
theorem sourceAffineFlagHeckeOperators_commute (a b : sourceBinaryHeckePrime Q) :
    Commute (sourceAffineFlagHeckeOperators F p Q hpQ j a)
      (sourceAffineFlagHeckeOperators F p Q hpQ j b) := by
  by_cases he : a.val = b.val
  · have hab : a = b := Subtype.ext he
    subst b
    exact Commute.refl _
  · exact sourcePrimeHeckeH1_commute a.property.1 (sourceAffineFlagRep F p Q hpQ j)
      (sourceAffineFlagDiagonal F p j a.val)
      (sourceAffineFlagDiagonal_intertwine F p Q hpQ j a)
      b.property.1 a.property.2 b.property.2 he
      (sourceAffineFlagDiagonal F p j b.val)
      (sourceAffineFlagDiagonal_intertwine F p Q hpQ j b)
      (sourceAffineFlagDiagonal_commute F p j a.val b.val)

end
end Dubon2026

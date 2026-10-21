import Dubon2026.SourceAffineFunctionFlag
import Dubon2026.SourceFiniteFunctionDifference
import Dubon2026.SourceAffineDiagonalUnits
import Dubon2026.HeckeUpperCosets

/-! The actual invariant quotient controlling the weight-two Eisenstein exception.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> survival of the function-flag eigenclass -> its exact exceptional
invariant monomial and exponent. The already proved translation and actual
diagonal-unit witnesses supply both necessary conclusions.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] [CharP F p] (hpQ : p ∣ Q)

omit [CharP F p] in
/-- The original integral translation acts by the actual prime-field shift. -/
theorem sourceAffineFunction_translation (f : ZMod p → F) :
    sourceAffineFunctionAction p Q F (heckeUpperTranslation Q (-1)) f =
      sourceFiniteFunctionShift F p f := by
  funext u
  simp [sourceAffineFunctionAction, sourceAffineD, sourceAffineB,
    heckeUpperTranslation, sourceFiniteFunctionShift]

/-- Every invariant modulo the original degree-k function flag is represented
by a scalar multiple of the next actual monomial. -/
theorem sourceAffineFunction_invariant_quotient {k : ℕ} (hk : k + 1 < p)
    {f : ZMod p → F}
    (hf : ∀ g : Gamma0 Q, sourceAffineFunctionAction p Q F g f - f ∈
      sourceFiniteFunctionFlag F p k) :
    ∃ r : F, f - r • sourceFiniteFunctionMonomial F p (k + 1) ∈
      sourceFiniteFunctionFlag F p k := by
  apply sourceFiniteFunctionDifference_degree F p hk
  rw [← sourceAffineFunction_translation F p Q]
  exact hf _

include hpQ in
/-- If the next original monomial is invariant modulo the flag, its exact
lower-diagonal exponent is divisible by p minus one. -/
theorem sourceAffineFunction_invariant_exponent [NeZero Q] {k : ℕ} (hk : k + 1 < p)
    (hinv : ∀ g : Gamma0 Q,
      sourceAffineFunctionAction p Q F g (sourceFiniteFunctionMonomial F p (k + 1)) -
        sourceFiniteFunctionMonomial F p (k + 1) ∈ sourceFiniteFunctionFlag F p k) :
    (p - 1) ∣ 2 * (k + 1) := by
  apply sourceAffine_diagonal_exponent_dvd p Q
  intro g
  let j : Fin p := ⟨k + 1, hk⟩
  have hzero := sourceFiniteFunctionCoordinate_zero F p (k := j)
    (Nat.lt_succ_self k) (hinv g)
  have ha := sourceAffineFunctionCoordinate_action F p Q hpQ j g
    (sourceFiniteFunctionMonomial_mem_flag F p (le_refl (k + 1)) hk)
  change sourceFiniteFunctionCoordinate F p j (sourceAffineFunctionAction p Q F g _) = _ at ha
  rw [map_sub, ha,
    sourceFiniteFunctionCoordinate_monomial F p j hk, if_pos rfl,
    mul_one, sub_eq_zero, ← map_pow] at hzero
  exact (ZMod.castHom (dvd_refl p) F).injective (hzero.trans (map_one _).symm)

end
end Dubon2026

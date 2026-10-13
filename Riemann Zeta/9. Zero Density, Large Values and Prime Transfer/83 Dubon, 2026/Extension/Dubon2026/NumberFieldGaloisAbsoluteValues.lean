/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Absolute-value transport adapted from NYLL ClassFieldTheory, commit
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/GaloisAction.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.NumberFieldGaloisValuation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-! # Original absolute values under simultaneous Galois transport

The actual residue-ring quotient equivalence preserves the prime norm.
Together with the proved valuation transport, this preserves the actual
normalized finite absolute values. Infinite multiplicities are preserved
by the pinned original place action. These are the precise normalization
inputs for DUB-17's equivariant S-unit logarithmic lattice.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- Transporting an original prime by the original automorphism preserves its actual absolute norm. -/
theorem numberFieldGaloisPlace_absNorm (σ : Gal(L/K)) (v : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm (numberFieldGaloisPlaceEquiv K L σ v).asIdeal = Ideal.absNorm v.asIdeal := by
  rw [numberFieldGaloisPlaceEquiv_asIdeal, Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal _
    (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv rfl).toEquiv.symm

private theorem normalizedValue_congr {e f : NNReal} (he : e ≠ 0) (hf : f ≠ 0)
    (hef : e = f) (q : WithZero (Multiplicative ℤ)) :
    ((WithZeroMulInt.toNNReal he q : NNReal) : ℝ) =
      ((WithZeroMulInt.toNNReal hf q : NNReal) : ℝ) := by
  subst f
  rfl

/-- The normalized original finite absolute value is invariant under simultaneous original transport. -/
theorem numberFieldGaloisPlace_adicAbv (σ : Gal(L/K))
    (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    NumberField.HeightOneSpectrum.adicAbv L (numberFieldGaloisPlaceEquiv K L σ v) (σ x) =
      NumberField.HeightOneSpectrum.adicAbv L v x := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, NumberField.HeightOneSpectrum.adicAbv_def,
    numberFieldGaloisPlace_valuation]
  exact normalizedValue_congr _ _
    (congrArg (fun n : ℕ => (n : NNReal)) (numberFieldGaloisPlace_absNorm K L σ v)) _

omit [NumberField L] in
/-- The multiplicity of an actual infinite place is preserved by the actual Galois action. -/
theorem numberFieldGaloisInfinitePlace_mult (σ : Gal(L/K)) (w : NumberField.InfinitePlace L) :
    (σ • w).mult = w.mult := by
  unfold NumberField.InfinitePlace.mult
  rw [NumberField.InfinitePlace.isReal_smul_iff]

end
end Dubon2026

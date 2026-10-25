import Dubon2026.SourceOriginalHeckeNormEmbeddings
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17/18 -> actual degeneracy norm product -> complete embedding list.
The existing twisted-series injectivity distinguishes the prime conjugates.
Evaluating each candidate at the original second j coordinate transfers
this distinction to field embeddings; the proved inclusion degree makes
the list exhaustive. The exact Atkin equations remain explicit here. -/
namespace Dubon2026.SourceFunctionField.HeckeNorm
noncomputable section
open IntermediateField PrimeDegreeAux
variable (L : Type*) [Field L] [Algebra ℚ L]
variable (N p : ℕ) [hp : Fact p.Prime]
local notation "FF" => modularFunctionFieldOver N L
local notation "GG" => modularFunctionFieldOver (N * p) L
local notation "EE" => AlgebraicClosure (LaurentSeries L)
attribute [local instance] alphaAlgebra

theorem primeConjugates_injective (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p) :
    Function.Injective (PhiGen.conj p ζ) := by
  intro i
  refine Fin.cases ?_ (fun a => ?_) i
  · intro j
    refine Fin.cases (fun _ => rfl) (fun b h => ?_) j
    rw [conj_zero_eq, conj_succ_eq] at h
    have he := (TS_injective h).1
    have hp2 := hp.out.two_le
    exfalso
    nlinarith
  · intro j
    refine Fin.cases (fun h => ?_) (fun b h => ?_) j
    · rw [conj_succ_eq, conj_zero_eq] at h
      have he := (TS_injective h).1
      have hp2 := hp.out.two_le
      exfalso
      nlinarith
    · rw [conj_succ_eq, conj_succ_eq] at h
      have hu := (TS_injective h).2
      have hζu : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.mp hζ
      exact congrArg Fin.succ (Fin.ext (hζu.pow_inj a.2 b.2 hu))

theorem embedding_injective (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p)
    (w : GG ≃ₐ[L] GG)
    (hforward : ∀ x, w (originalHeckeAlpha L N p x) = originalHeckeBeta L N p x)
    (hback : ∀ x, w (originalHeckeBeta L N p x) = originalHeckeAlpha L N p x) :
    Function.Injective (embedding L N p ζ hζ w hforward) := by
  intro i j hij
  apply primeConjugates_injective L p ζ hζ
  apply (algebraMap (LaurentSeries L) EE).injective
  rw [← embedding_jBeta L N p ζ hζ w hforward hback i,
    ← embedding_jBeta L N p ζ hζ w hforward hback j, hij]

theorem embedding_bijective [NeZero N] (hpN : ¬ p ∣ N)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) p)
    (w : GG ≃ₐ[L] GG)
    (hforward : ∀ x, w (originalHeckeAlpha L N p x) = originalHeckeBeta L N p x)
    (hback : ∀ x, w (originalHeckeBeta L N p x) = originalHeckeAlpha L N p x) :
    Function.Bijective (embedding L N p ζ hζ w hforward) := by
  classical
  letI := targetAlgebra L N p
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : CharZero FF :=
    charZero_of_injective_algebraMap (algebraMap L FF).injective
  haveI : FiniteDimensional FF GG := Module.finite_of_finrank_pos (by
    rw [originalHeckeAlpha_finrank L N p hpN]
    exact Nat.succ_pos p)
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨embedding_injective L N p ζ hζ w hforward hback, ?_⟩
  rw [Fintype.card_fin, AlgHom.card, originalHeckeAlpha_finrank L N p hpN]

end
end Dubon2026.SourceFunctionField.HeckeNorm

import Dubon2026.SourceReductionCompletionBasePrime
import Dubon2026.OriginalAdicLocalFieldStructures

/-! DUB-17/18 -> prescribed coefficient reduction -> give the actual
completion at the reduction kernel its Tate-prime scalar map. Compose
the native rational p-adic completion equivalence with the existing
completed original field embedding, preserving rational values. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable (F : Type) [Field F] [NumberField F]
variable {k : Type*} [Field k] (ell : ℕ) (hell : ell.Prime) [Fact ell.Prime] [CharP k ell]
variable (φ : 𝓞 F →+* k)
local notation "w" => sourceReductionPrime F ell hell φ
local notation "v" => Equiv.symm (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (Subtype.mk ell hell)
private local instance : (w).asIdeal.LiesOver (v).asIdeal :=
  sourceReductionPrime_liesOver_rational F ell hell φ

/-- The original Tate-prime field map into the completion chosen by the reduction kernel. -/
def sourceReductionCompletionPadicMap : ℚ_[ell] →+* (w).adicCompletion F :=
  (originalAdicBaseChangeMap ℚ F v w).comp
    (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨ell, hell⟩).toRingHom

theorem sourceReductionCompletionPadicMap_continuous :
    Continuous (sourceReductionCompletionPadicMap F ell hell φ) :=
  (originalAdicBaseChangeMap_continuous ℚ F v w).comp
    (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨ell, hell⟩).continuous

theorem sourceReductionCompletionPadicMap_rational (x : ℚ) :
    sourceReductionCompletionPadicMap F ell hell φ (algebraMap ℚ ℚ_[ell] x) =
      algebraMap ℚ ((w).adicCompletion F) x := by
  change originalAdicBaseChangeMap ℚ F v w
    ((Padic.adicCompletionEquiv (𝓞 ℚ) ⟨ell, hell⟩) (algebraMap ℚ ℚ_[ell] x)) = _
  have he : (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨ell, hell⟩)
      (algebraMap ℚ ℚ_[ell] x) = algebraMap ℚ ((v).adicCompletion ℚ) x :=
    (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨ell, hell⟩).commutes x
  rw [he, originalAdicBaseChangeMap_algebraMap]
  exact (IsScalarTower.algebraMap_apply ℚ F ((w).adicCompletion F) x).symm

end
end Dubon2026

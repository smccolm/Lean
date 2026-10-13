import Dubon2026.OriginalFiniteRamification
import Dubon2026.SupportedIdeleCohomologySequence

/-! # One original support supplies both class surjectivity and unramified outside places

The existing finite stable class-surjective enlargement is applied to
the prescribed support together with the proved finite absolute
ramification set. This discharges the joint support-choice assumption
in DUB-17's actual global idele Herbrand formula.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- A single constructed original finite stable support surjects onto the actual idele classes and contains all absolutely ramified places. -/
theorem original_exists_unramified_galoisStable_idele_support
    (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      (∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) ∧
        Function.Surjective (numberFieldSupportedIdeleClassMap L S) ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal := by
  let T := (original_finite_absolutely_ramified_places L).toFinset
  obtain ⟨S, hsub, hS, hsurj⟩ := numberField_exists_galoisStable_idele_support K L (S₀ ∪ T)
  refine ⟨S, Finset.subset_union_left.trans hsub, hS, hsurj, ?_⟩
  intro w hw
  by_contra hram
  apply hw
  apply hsub
  apply Finset.mem_union_right
  exact (Set.Finite.mem_toFinset _).mpr hram

end
end Dubon2026

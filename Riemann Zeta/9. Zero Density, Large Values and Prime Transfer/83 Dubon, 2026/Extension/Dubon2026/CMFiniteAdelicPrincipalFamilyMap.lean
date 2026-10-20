import Dubon2026.CMFiniteAdelicPrincipalIntegralMap
import Dubon2026.CMFiniteAdelicSplitFamilySurjective
import Dubon2026.CMFiniteAdelicParabolicFamilyLevels

/-! # Original auxiliary evaluation preserves the small principal level

The supported original unitary lift is one at the separate principal
place. It therefore realizes every original local matrix tuple inside
the already constructed smallness level, rather than losing the
principal-congruence condition. This is the exact DUB-17 auxiliary
family realization needed by the automorphic comparison.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {S : Type*} (v : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)

/-- Original simultaneous local evaluation on the actual principal unitary level. -/
def cmFiniteAdelicPrincipalFamilyMap
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (w : HeightOneSpectrum (𝓞 K)) :
    cmFiniteAdelicPrincipalLevel K H w →*
      (∀ s, (Matrix (Fin (n + 1)) (Fin (n + 1)) (Valued.integer ((v s).adicCompletion K)))ˣ) :=
  (cmFiniteAdelicIntegralLocalFamilyMap K v n H).comp (cmFiniteAdelicPrincipalIntegralMap K H w)

/-- Original auxiliary evaluation on the original principal unitary level is continuous. -/
theorem cmFiniteAdelicPrincipalFamilyMap_continuous
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (w : HeightOneSpectrum (𝓞 K)) :
    Continuous (cmFiniteAdelicPrincipalFamilyMap K v n H w) :=
  continuous_pi fun s => (cmFiniteAdelicIntegralLocalMap_continuous K H (v s)).comp
    (cmFiniteAdelicPrincipalIntegralMap_continuous K H w)

/-- The actual principal unitary level surjects onto the original finite auxiliary local family, preserving the separate smallness place. -/
theorem cmFiniteAdelicPrincipalFamilyMap_surjective [Fintype S]
    (H : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ) (hH : star H = H)
    (hv : ∀ s, v s ≠ cmFinitePlaceConjugation K (v s))
    (hlocal : ∀ s, cmFiniteAdelicFormIntegralAtConjugate K H (v s))
    (hsep : Pairwise fun s t => v s ≠ v t ∧ v s ≠ cmFinitePlaceConjugation K (v t))
    (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ s, w ≠ v s ∧ w ≠ cmFinitePlaceConjugation K (v s)) :
    Function.Surjective (cmFiniteAdelicPrincipalFamilyMap K v n H.val w) := by
  intro g
  obtain ⟨M, hM, hMs⟩ := cmFiniteAdelicIntegralLocalFamily_exists_support K H hH v hv hlocal hsep g
  have hP := cmFiniteAdelicIntegral_mem_principal_of_local_one K H.val w M (hMs w hw)
  exact ⟨⟨M.val, hP⟩, hM⟩

end
end Dubon2026

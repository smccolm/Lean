import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.DedekindDomain.SInteger

/-! # Supported original number-field ideles and principal S-units

Ideles are the units of the pinned original adele ring, as in the existing
rational automorphic construction. Local components and principal ideles
use its actual maps. The principal preimage of supported ideles is proved
to be the existing original S-unit group. This is the kernel input for
the supported-idele exact sequence in DUB-17's global norm-index route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- The actual diagonal principal-idele homomorphism of the original number field. -/
def numberFieldPrincipalIdele : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom

/-- The actual principal-idele homomorphism retains the original global unit. -/
theorem numberFieldPrincipalIdele_injective : Function.Injective (numberFieldPrincipalIdele K) :=
  Units.map_injective (AdeleRing.algebraMap_injective (𝓞 K) K)

/-- The original finite-place component of an original full idele. -/
def numberFieldIdeleFiniteComponent (v : HeightOneSpectrum (𝓞 K)) :
    (AdeleRing (𝓞 K) K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (((RestrictedProduct.evalRingHom
    (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) v).comp
      (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))).toMonoidHom)

/-- Original ideles integral and invertible at each original finite place outside S. -/
def numberFieldSupportedIdeles (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (AdeleRing (𝓞 K) K)ˣ :=
  ⨅ v : HeightOneSpectrum (𝓞 K), ⨅ (_ : v ∉ S),
    ((v.adicCompletionIntegers K).units).comap (numberFieldIdeleFiniteComponent K v)

/-- A principal original idele is supported on S exactly when its original unit is an S-unit. -/
theorem numberFieldPrincipalIdele_mem_supported_iff
    (S : Set (HeightOneSpectrum (𝓞 K))) (x : Kˣ) :
    numberFieldPrincipalIdele K x ∈ numberFieldSupportedIdeles K S ↔ x ∈ S.unit K := by
  simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
  change (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    Valued.v (algebraMap K (v.adicCompletion K) x.val) = 1) ↔ _
  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, Valued.valuedCompletion_apply]
  rfl

end
end Dubon2026

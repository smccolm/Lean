import Dubon2026.OriginalInfiniteKernelLocalClassChoice
import Dubon2026.OriginalUniversalLocalRestrictions
import Dubon2026.OriginalNormalizedLocalClassChoice

/-! # One global class compatible with every normalized local choice

Keep the constructed global class and the existence of normalized local
classes. The actual local-image comparison then identifies its restrictions
with every supplied normalized local class, as required by DUB-17's local
fundamental-class compatibility clause.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

/-- The constructed common global class is compatible with every supplied normalized local class, by injectivity of the canonical class invariant on actual local images. -/
theorem originalIdeleClass_universal_local_restrictions_of_infinite_kernel
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (localInvariant : IsDedekindDomain.HeightOneSpectrum (𝓞 L) →
      groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (hc : OriginalInfiniteKernelClassInvariantTraceSystem K L total)
    (hf : OriginalLocalTraceTotalFormula K L localInvariant total)
    (hn : OriginalNormalizedLocalRestrictions K L localInvariant) :
    OriginalUniversalNormalizedLocalRestrictions K L localInvariant := by
  obtain ⟨u, hu, hl⟩ := hn
  refine ⟨u, hu, fun w => ?_⟩
  letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  obtain ⟨y, hy, hres⟩ := hl w
  refine ⟨⟨y, hy⟩, fun z hz => ?_⟩
  exact hres.trans (originalIdeleClass_local_image_eq_of_invariant_of_infinite_kernel
    K L localInvariant total hc hf w y z (hy.trans hz.symm))

end
end Dubon2026

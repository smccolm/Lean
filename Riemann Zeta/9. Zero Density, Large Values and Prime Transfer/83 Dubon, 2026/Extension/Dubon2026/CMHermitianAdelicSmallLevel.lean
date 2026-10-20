import Dubon2026.CMHermitianArithmeticSmallLevel
import Dubon2026.SmallLevelSubgroupRestriction

/-! # Smallness inside the specified finite-adelic unitary realization

The source form and its finite-adelic group are retained explicitly.
Definiteness, compactness and the one-place local level condition now
derive the arithmetic smallness required by the DUB-17 auxiliary modules.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder

variable {K ι : Type*} [Field K] [NumberField K] [IsCMField K]
variable [Fintype ι] [DecidableEq ι]

/-- Derive the actual arithmetic smallness in the supplied adelic subgroup, retaining the source form. -/
theorem cmHermitianAdelic_smallLevel
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (S : Subgroup (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ)
    (hS : ∀ a, cmHermitianFiniteAdeleHom H a ∈ S)
    (U : Subgroup S) (hU : IsCompact (U : Set S))
    (v : HeightOneSpectrum (𝓞 K))
    [IsMulTorsionFree ((U.map S.subtype).map (numberFieldFiniteAdelicMatrixProjection K ι v))] :
    ∀ (g : S) (u : U),
      g * u.val * g⁻¹ ∈ ((cmHermitianFiniteAdeleHom H).codRestrict S hS).range → u = 1 := by
  apply smallLevel_restrict_to_subgroup (cmHermitianFiniteAdeleHom H) S hS U
  apply cmHermitian_smallLevel_of_local_torsionFree H hH (U.map S.subtype) _ v
  exact hU.image continuous_subtype_val

end
end Dubon2026

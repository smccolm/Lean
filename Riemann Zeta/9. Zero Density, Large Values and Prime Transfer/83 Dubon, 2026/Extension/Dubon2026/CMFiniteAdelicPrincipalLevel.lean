import Dubon2026.CMFiniteAdelicIntegralLevel
import Dubon2026.NumberFieldPrincipalMatrixLevel

/-! # An actual compact open small level in the CM unitary group

The original principal congruence condition is imposed on the constructed
finite-adelic unitary group. Compactness, openness and arithmetic smallness
are proved, removing those supplied level certificates from DUB-17's
auxiliary-module comparison. The source field and form choices, suitable
prime selection, finite double cosets and Hecke realization remain separate.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual one-place principal level in the original finite-adelic unitary group. -/
def cmFiniteAdelicPrincipalLevel (H : Matrix ι ι K) (v : HeightOneSpectrum (𝓞 K)) :
    Subgroup (cmFiniteAdelicUnitaryGroup K H) :=
  (numberFieldPrincipalMatrixLevel K ι v).subgroupOf (cmFiniteAdelicUnitaryGroup K H)

/-- The original principal unitary level is open. -/
theorem cmFiniteAdelicPrincipalLevel_isOpen (H : Matrix ι ι K)
    (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen (cmFiniteAdelicPrincipalLevel K H v : Set (cmFiniteAdelicUnitaryGroup K H)) :=
  (numberFieldPrincipalMatrixLevel_isOpen K ι v).preimage continuous_subtype_val

/-- The original principal unitary level is compact. -/
theorem cmFiniteAdelicPrincipalLevel_isCompact (H : Matrix ι ι K)
    (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact (cmFiniteAdelicPrincipalLevel K H v : Set (cmFiniteAdelicUnitaryGroup K H)) :=
  (cmFiniteAdelicUnitaryGroup_isClosed K H).isClosedEmbedding_subtypeVal.isCompact_preimage
    (numberFieldPrincipalMatrixLevel_isCompact K ι v)

/-- The constructed unitary level satisfies the original local principal condition. -/
theorem cmFiniteAdelicPrincipalLevel_projection (H : Matrix ι ι K)
    (v : HeightOneSpectrum (𝓞 K)) :
    ((cmFiniteAdelicPrincipalLevel K H v).map (cmFiniteAdelicUnitaryGroup K H).subtype).map
      (numberFieldFiniteAdelicMatrixProjection K ι v) ≤
        finitePlacePrincipalCongruenceImage K ι v := by
  apply le_trans _ (numberFieldPrincipalMatrixLevel_projection K ι v)
  apply Subgroup.map_mono
  rintro _ ⟨a, ha, rfl⟩
  exact ha

/-- Every open refinement has finite index in the constructed original principal level. -/
theorem cmFiniteAdelicPrincipalLevel_quotient_finite (H : Matrix ι ι K)
    (v : HeightOneSpectrum (𝓞 K)) (V : Subgroup (cmFiniteAdelicUnitaryGroup K H))
    (hV : IsOpen (V : Set (cmFiniteAdelicUnitaryGroup K H))) :
    Finite (cmFiniteAdelicPrincipalLevel K H v ⧸ V.subgroupOf (cmFiniteAdelicPrincipalLevel K H v)) := by
  letI : CompactSpace (cmFiniteAdelicPrincipalLevel K H v) :=
    isCompact_iff_compactSpace.mp (cmFiniteAdelicPrincipalLevel_isCompact K H v)
  exact (V.subgroupOf (cmFiniteAdelicPrincipalLevel K H v)).quotient_finite_of_isOpen
    (hV.preimage continuous_subtype_val)

/-- Every original conjugate arithmetic stabilizer of this level is trivial at a large prime. -/
theorem cmFiniteAdelicPrincipalLevel_small (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime)
    [CharP (Valued.ResidueField (v.adicCompletion K)) p]
    (hlarge : Fintype.card ι * Module.finrank ℚ K < p - 1) :
    ∀ (g : cmFiniteAdelicUnitaryGroup K H) (u : cmFiniteAdelicPrincipalLevel K H v),
      g * u.val * g⁻¹ ∈ ((cmHermitianFiniteAdeleHom H).codRestrict
        (cmFiniteAdelicUnitaryGroup K H) (cmFiniteAdelicUnitaryGroup_principal K H)).range →
          u = 1 :=
  cmHermitianAdelic_smallLevel_of_large_congruence H hH (cmFiniteAdelicUnitaryGroup K H)
    (cmFiniteAdelicUnitaryGroup_principal K H) (cmFiniteAdelicPrincipalLevel K H v)
    (cmFiniteAdelicPrincipalLevel_isCompact K H v) v p hp hlarge
    (cmFiniteAdelicPrincipalLevel_projection K H v)

end
end Dubon2026

import Dubon2026.OriginalAdicUnitCohomology

/-! # Literal global-unit localization at an original finite prime

These maps use the original prime decomposition group and the literal
field-to-completion embedding. Their cocycle formula is the common
input for comparison with finite-support local detection and normalized
completion invariants, required to apply DUB-17's constructed cyclotomic
stage to the actual global H2 class.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))

/-- The literal original completion embedding, equivariant for the original decomposition group. -/
def originalGlobalAdicUnitRepHom :
    Rep.res (OriginalFiniteDecompositionGroup K L w).subtype (Rep.ofAlgebraAutOnUnits K L) ⟶
      originalAdicUnitRep K L w :=
  Rep.ofHom ⟨(Units.map (algebraMap L (w.adicCompletion L)).toMonoidHom).toAdditive.toIntLinearMap, by
    intro σ
    apply LinearMap.ext
    intro x
    apply congrArg Additive.ofMul
    apply Units.ext
    exact (numberFieldGaloisLocalTransport_algebraMap K L σ.val w w σ.property x.toMul.val).symm⟩

/-- Actual localization of the original global two-cocycle. -/
def originalGlobalAdicTwoCocycle :
    groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L) →
      groupCohomology.cocycles₂ (originalAdicUnitRep K L w) :=
  groupCohomology.mapCocycles₂ (OriginalFiniteDecompositionGroup K L w).subtype
    (originalGlobalAdicUnitRepHom K L w)

/-- The localized cocycle is exactly subgroup restriction followed by the same original completion embedding. -/
theorem originalGlobalAdicTwoCocycle_apply
    (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
    (g h : OriginalFiniteDecompositionGroup K L w) :
    originalGlobalAdicTwoCocycle K L w c (g, h) =
      Additive.ofMul (Units.map (algebraMap L (w.adicCompletion L)).toMonoidHom
        (c (g.val, h.val)).toMul) := rfl

/-- Actual original global-to-finite-local H2, without a choice of finite support or orbit representative. -/
def originalGlobalAdicH2 :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ⟶
      groupCohomology (originalAdicUnitRep K L w) 2 :=
  groupCohomology.map (OriginalFiniteDecompositionGroup K L w).subtype
    (originalGlobalAdicUnitRepHom K L w) 2

/-- The actual localization map takes the class of the original cocycle to the class of its literal localized cocycle. -/
theorem originalGlobalAdicH2_cocycle
    (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L)) :
    originalGlobalAdicH2 K L w (groupCohomology.H2π _ c) =
      groupCohomology.H2π _ (originalGlobalAdicTwoCocycle K L w c) :=
  groupCohomology.H2π_comp_map_apply _ _ c

end
end Dubon2026

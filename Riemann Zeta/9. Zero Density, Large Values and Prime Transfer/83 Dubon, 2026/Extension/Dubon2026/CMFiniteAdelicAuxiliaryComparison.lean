import Dubon2026.CMHermitianCongruenceSmallLevel
import Dubon2026.CMFiniteAdelicUnitaryGroup
import Dubon2026.SmallLevelAuxiliaryModuleComparison

/-! # The auxiliary comparison in the actual finite-adelic CM unitary group

The ambient unitary group and principal arithmetic inclusion are now
constructed from the original CM involution and the specified form.
The finite free auxiliary module and exact unnormalized trace comparison
therefore use those actual groups. DUB-17 still requires the source field
and local form choices, finite double cosets, highest-weight lattice and
nonzero localized Hecke realization.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder BigOperators

/-- A large original congruence prime supplies finite freeness and the exact auxiliary trace. -/
theorem cmFiniteAdelicAuxiliaryModule_comparison
    {K : Type} {ι R W : Type*} [Field K] [NumberField K] [IsCMField K]
    [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup W] [Module R W]
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (U V : Subgroup (cmFiniteAdelicUnitaryGroup K H))
    (hU : IsCompact (U : Set (cmFiniteAdelicUnitaryGroup K H))) (hVU : V ≤ U)
    (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime)
    [CharP (Valued.ResidueField (v.adicCompletion K)) p]
    (hlarge : Fintype.card ι * Module.finrank ℚ K < p - 1)
    (hlevel : (U.map (cmFiniteAdelicUnitaryGroup K H).subtype).map (numberFieldFiniteAdelicMatrixProjection K ι v) ≤
      finitePlacePrincipalCongruenceImage K ι v)
    (ρ : Representation R U W) [(V.subgroupOf U).Normal]
    [Finite (DoubleCoset.Quotient (G := cmFiniteAdelicUnitaryGroup K H)
      ((cmHermitianFiniteAdeleHom H).codRestrict (cmFiniteAdelicUnitaryGroup K H) (cmFiniteAdelicUnitaryGroup_principal K H)).range U)]
    [Fintype (U ⧸ V.subgroupOf U)] [Module.Finite R W] [Module.Free R W] :
    let Γ := ((cmHermitianFiniteAdeleHom H).codRestrict (cmFiniteAdelicUnitaryGroup K H) (cmFiniteAdelicUnitaryGroup_principal K H)).range
    let hs := cmHermitianAdelic_smallLevel_of_large_congruence H hH (cmFiniteAdelicUnitaryGroup K H)
      (cmFiniteAdelicUnitaryGroup_principal K H) U hU v p hp hlarge hlevel
    Module.Free (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hs).asModule ∧
    Module.Finite (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hs).asModule ∧
    ∃ e : (auxiliaryAutomorphicAction Γ U V hVU ρ hs).Coinvariants ≃ₗ[R]
        algebraicAutomorphicForms Γ U ρ,
      ∀ (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU))) (g : cmFiniteAdelicUnitaryGroup K H),
        (e (Representation.Coinvariants.mk
          (auxiliaryAutomorphicAction Γ U V hVU ρ hs) f)).val g =
          ∑ d : U ⧸ V.subgroupOf U, ρ d.out (f.val (g * (d.out : cmFiniteAdelicUnitaryGroup K H))) :=
  smallLevelAuxiliaryModule_comparison _ U V hVU ρ
    (cmHermitianAdelic_smallLevel_of_large_congruence H hH (cmFiniteAdelicUnitaryGroup K H)
      (cmFiniteAdelicUnitaryGroup_principal K H) U hU v p hp hlarge hlevel)

end
end Dubon2026

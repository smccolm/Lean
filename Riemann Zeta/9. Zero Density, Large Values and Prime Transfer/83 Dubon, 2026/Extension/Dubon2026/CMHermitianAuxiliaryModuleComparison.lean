import Dubon2026.CMHermitianAdelicSmallLevel
import Dubon2026.SmallLevelAuxiliaryModuleComparison

/-! # The auxiliary comparison with actual Hermitian arithmetic smallness derived

DUB-17 uses CHT Lemma 3.3.1 inside the source's finite-adelic unitary group.
This consumer retains that subgroup and the original definite CM form.
Compactness and a torsion-free one-place level derive the formerly assumed
smallness. Finite actual double cosets, the weight lattice and the source
Hecke localization remain separate inputs and obligations.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder BigOperators

/-- Actual Hermitian arithmetic smallness supplies finite freeness and the exact auxiliary trace. -/
theorem cmHermitianAuxiliaryModule_comparison
    {K ι R W : Type*} [Field K] [NumberField K] [IsCMField K]
    [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup W] [Module R W]
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (S : Subgroup (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ)
    (hS : ∀ a, cmHermitianFiniteAdeleHom H a ∈ S)
    (U V : Subgroup S) (hU : IsCompact (U : Set S)) (hVU : V ≤ U)
    (v : HeightOneSpectrum (𝓞 K))
    [IsMulTorsionFree ((U.map S.subtype).map (numberFieldFiniteAdelicMatrixProjection K ι v))]
    (ρ : Representation R U W) [(V.subgroupOf U).Normal]
    [Finite (DoubleCoset.Quotient (G := S)
      ((cmHermitianFiniteAdeleHom H).codRestrict S hS).range U)]
    [Fintype (U ⧸ V.subgroupOf U)] [Module.Finite R W] [Module.Free R W] :
    let Γ := ((cmHermitianFiniteAdeleHom H).codRestrict S hS).range
    let hs := cmHermitianAdelic_smallLevel H hH S hS U hU v
    Module.Free (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hs).asModule ∧
    Module.Finite (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hs).asModule ∧
    ∃ e : (auxiliaryAutomorphicAction Γ U V hVU ρ hs).Coinvariants ≃ₗ[R]
        algebraicAutomorphicForms Γ U ρ,
      ∀ (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU))) (g : S),
        (e (Representation.Coinvariants.mk
          (auxiliaryAutomorphicAction Γ U V hVU ρ hs) f)).val g =
          ∑ d : U ⧸ V.subgroupOf U, ρ d.out (f.val (g * (d.out : S))) :=
  smallLevelAuxiliaryModule_comparison _ U V hVU ρ
    (cmHermitianAdelic_smallLevel H hH S hS U hU v)

end
end Dubon2026

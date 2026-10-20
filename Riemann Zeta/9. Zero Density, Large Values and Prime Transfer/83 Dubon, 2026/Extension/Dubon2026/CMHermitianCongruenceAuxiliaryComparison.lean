import Dubon2026.CMHermitianCongruenceSmallLevel
import Dubon2026.SmallLevelAuxiliaryModuleComparison

/-! # The actual auxiliary comparison with large-prime arithmetic smallness

DUB-17 uses CHT Lemma 3.3.1 inside the source finite-adelic unitary group.
The same original definite form, level, weight and quotient are retained.
Actual congruence reduction and the cyclotomic rank bound now derive
arithmetic smallness; no torsion-free local-group certificate is supplied.
The source global level, finite double cosets and localized Hecke module
remain separate obligations.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder BigOperators

/-- A large original congruence prime supplies finite freeness and the exact auxiliary trace. -/
theorem cmHermitianCongruenceAuxiliaryModule_comparison
    {K ι R W : Type*} [Field K] [NumberField K] [IsCMField K]
    [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup W] [Module R W]
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (S : Subgroup (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))ˣ)
    (hS : ∀ a, cmHermitianFiniteAdeleHom H a ∈ S)
    (U V : Subgroup S) (hU : IsCompact (U : Set S)) (hVU : V ≤ U)
    (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime)
    [CharP (Valued.ResidueField (v.adicCompletion K)) p]
    (hlarge : Fintype.card ι * Module.finrank ℚ K < p - 1)
    (hlevel : (U.map S.subtype).map (numberFieldFiniteAdelicMatrixProjection K ι v) ≤
      finitePlacePrincipalCongruenceImage K ι v)
    (ρ : Representation R U W) [(V.subgroupOf U).Normal]
    [Finite (DoubleCoset.Quotient (G := S)
      ((cmHermitianFiniteAdeleHom H).codRestrict S hS).range U)]
    [Fintype (U ⧸ V.subgroupOf U)] [Module.Finite R W] [Module.Free R W] :
    let Γ := ((cmHermitianFiniteAdeleHom H).codRestrict S hS).range
    let hs := cmHermitianAdelic_smallLevel_of_large_congruence H hH S hS U hU v p hp hlarge hlevel
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
    (cmHermitianAdelic_smallLevel_of_large_congruence H hH S hS U hU v p hp hlarge hlevel)

end
end Dubon2026

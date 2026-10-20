import Dubon2026.CMFiniteAdelicClassFiniteness
import Dubon2026.CMFiniteAdelicAuxiliaryComparison

/-! # Original auxiliary-module comparison with arithmetic class finiteness proved

For the actual definite CM unitary group and an original compact open
level, arithmetic double-coset finiteness is now derived from the
specified form and the original open subgroup. The established large
congruence-prime smallness theorem therefore gives finite freeness and
the exact unnormalized trace without that additional hypothesis.

The remaining DUB-17 source chain still requires the prescribed source
field and form choices, permitted auxiliary primes and local refinements,
the original highest-weight lattice and nonzero localized Hecke
realization, crystalline and Selmer dimension comparisons, and the
original automorphy continuation. No acceptance gate is closed here.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder BigOperators

/-- Original compact open unitary levels have the exact finite free auxiliary comparison with arithmetic class finiteness discharged. -/
theorem cmFiniteAdelicOpenAuxiliaryModule_comparison
    {K : Type} {ι R W : Type*} [Field K] [NumberField K] [IsCMField K]
    [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup W] [Module R W]
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (U V : Subgroup (cmFiniteAdelicUnitaryGroup K H))
    (hU : IsCompact (U : Set (cmFiniteAdelicUnitaryGroup K H)))
    (hUopen : IsOpen (U : Set (cmFiniteAdelicUnitaryGroup K H))) (hVU : V ≤ U)
    (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime)
    [CharP (Valued.ResidueField (v.adicCompletion K)) p]
    (hlarge : Fintype.card ι * Module.finrank ℚ K < p - 1)
    (hlevel : (U.map (cmFiniteAdelicUnitaryGroup K H).subtype).map
      (numberFieldFiniteAdelicMatrixProjection K ι v) ≤ finitePlacePrincipalCongruenceImage K ι v)
    (ρ : Representation R U W) [(V.subgroupOf U).Normal]
    [Fintype (U ⧸ V.subgroupOf U)] [Module.Finite R W] [Module.Free R W] :
    let Γ := ((cmHermitianFiniteAdeleHom H).codRestrict (cmFiniteAdelicUnitaryGroup K H)
      (cmFiniteAdelicUnitaryGroup_principal K H)).range
    let hs := cmHermitianAdelic_smallLevel_of_large_congruence H hH (cmFiniteAdelicUnitaryGroup K H)
      (cmFiniteAdelicUnitaryGroup_principal K H) U hU v p hp hlarge hlevel
    Module.Free (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hs).asModule ∧
    Module.Finite (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hs).asModule ∧
    ∃ e : (auxiliaryAutomorphicAction Γ U V hVU ρ hs).Coinvariants ≃ₗ[R]
        algebraicAutomorphicForms Γ U ρ,
      ∀ (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU)))
        (g : cmFiniteAdelicUnitaryGroup K H),
        (e (Representation.Coinvariants.mk
          (auxiliaryAutomorphicAction Γ U V hVU ρ hs) f)).val g =
          ∑ a : U ⧸ V.subgroupOf U, ρ a.out (f.val (g * (a.out : cmFiniteAdelicUnitaryGroup K H))) := by
  letI := cmFiniteAdelicDoubleCoset_finite K H hH U hUopen
  exact cmFiniteAdelicAuxiliaryModule_comparison H hH U V hU hVU v p hp hlarge hlevel ρ

end
end Dubon2026

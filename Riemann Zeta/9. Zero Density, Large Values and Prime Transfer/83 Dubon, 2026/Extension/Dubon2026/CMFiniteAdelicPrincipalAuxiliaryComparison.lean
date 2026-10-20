import Dubon2026.CMFiniteAdelicPrincipalLevel
import Dubon2026.SmallLevelAuxiliaryModuleComparison

/-! # The auxiliary comparison at the constructed principal unitary level

The original unitary group, its principal arithmetic inclusion and its
compact open principal level are constructed. At a sufficiently large
original residue prime, the arithmetic stabilizers are proved trivial.
The actual weighted function module is therefore finite free over its
level quotient, with the exact unnormalized coinvariant trace. DUB-17
still requires the source field and form choices, auxiliary local level
refinements, finite double cosets, weight lattice and Hecke realization.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder BigOperators

/-- A large original congruence prime supplies finite freeness and the exact auxiliary trace. -/
theorem cmFiniteAdelicPrincipalAuxiliaryModule_comparison
    {K : Type} {ι R W : Type*} [Field K] [NumberField K] [IsCMField K]
    [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup W] [Module R W]
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime)
    [CharP (Valued.ResidueField (v.adicCompletion K)) p]
    (hlarge : Fintype.card ι * Module.finrank ℚ K < p - 1)
    (V : Subgroup (cmFiniteAdelicUnitaryGroup K H))
    (hV : IsOpen (V : Set (cmFiniteAdelicUnitaryGroup K H)))
    (hVU : V ≤ (cmFiniteAdelicPrincipalLevel K H v))
    (ρ : Representation R (cmFiniteAdelicPrincipalLevel K H v) W) [(V.subgroupOf (cmFiniteAdelicPrincipalLevel K H v)).Normal]
    [Finite (DoubleCoset.Quotient (G := cmFiniteAdelicUnitaryGroup K H)
      ((cmHermitianFiniteAdeleHom H).codRestrict (cmFiniteAdelicUnitaryGroup K H) (cmFiniteAdelicUnitaryGroup_principal K H)).range (cmFiniteAdelicPrincipalLevel K H v))]
    [Module.Finite R W] [Module.Free R W] :
    letI := cmFiniteAdelicPrincipalLevel_quotient_finite K H v V hV
    letI := Fintype.ofFinite
      ((cmFiniteAdelicPrincipalLevel K H v) ⧸ V.subgroupOf (cmFiniteAdelicPrincipalLevel K H v))
    let Γ := ((cmHermitianFiniteAdeleHom H).codRestrict (cmFiniteAdelicUnitaryGroup K H) (cmFiniteAdelicUnitaryGroup_principal K H)).range
    let hs := cmFiniteAdelicPrincipalLevel_small K H hH v p hp hlarge
    Module.Free (MonoidAlgebra R ((cmFiniteAdelicPrincipalLevel K H v) ⧸ V.subgroupOf (cmFiniteAdelicPrincipalLevel K H v)))
      (auxiliaryAutomorphicAction Γ (cmFiniteAdelicPrincipalLevel K H v) V hVU ρ hs).asModule ∧
    Module.Finite (MonoidAlgebra R ((cmFiniteAdelicPrincipalLevel K H v) ⧸ V.subgroupOf (cmFiniteAdelicPrincipalLevel K H v)))
      (auxiliaryAutomorphicAction Γ (cmFiniteAdelicPrincipalLevel K H v) V hVU ρ hs).asModule ∧
    ∃ e : (auxiliaryAutomorphicAction Γ (cmFiniteAdelicPrincipalLevel K H v) V hVU ρ hs).Coinvariants ≃ₗ[R]
        algebraicAutomorphicForms Γ (cmFiniteAdelicPrincipalLevel K H v) ρ,
      ∀ (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU))) (g : cmFiniteAdelicUnitaryGroup K H),
        (e (Representation.Coinvariants.mk
          (auxiliaryAutomorphicAction Γ (cmFiniteAdelicPrincipalLevel K H v) V hVU ρ hs) f)).val g =
          ∑ d : (cmFiniteAdelicPrincipalLevel K H v) ⧸ V.subgroupOf (cmFiniteAdelicPrincipalLevel K H v), ρ d.out (f.val (g * (d.out : cmFiniteAdelicUnitaryGroup K H))) := by
  letI := cmFiniteAdelicPrincipalLevel_quotient_finite K H v V hV
  letI := Fintype.ofFinite
    ((cmFiniteAdelicPrincipalLevel K H v) ⧸ V.subgroupOf (cmFiniteAdelicPrincipalLevel K H v))
  exact smallLevelAuxiliaryModule_comparison _ (cmFiniteAdelicPrincipalLevel K H v) V hVU ρ
    (cmFiniteAdelicPrincipalLevel_small K H hH v p hp hlarge)

end
end Dubon2026

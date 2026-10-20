import Dubon2026.CMFiniteAdelicSmallPrimaryTopology
import Dubon2026.CMHermitianPositiveUnitStar
import Dubon2026.CMFiniteAdelicOpenAuxiliaryComparison

/-! # The actual source primary auxiliary automorphic comparison

The original CM unitary group, positive form, finite split auxiliary
family, and separate large principal prime produce the actual compact
open levels and the actual maximal-primary quotient. Their original
automorphic module is finite free over its actual quotient group ring;
coinvariants recover the upper-level forms by the exact unnormalized
weighted trace. Level topology, smallness, class finiteness, quotient
finiteness, and the source parabolic realization are all discharged.

DUB-17 still requires the prescribed source fields and form choices,
the original integral highest-weight coefficient representation and
its nonzero localized Hecke realization, crystalline/Selmer dimension
comparisons, and the source automorphy continuation. This theorem takes
an explicit finite free coefficient representation; it does not supply
those remaining source objects or close the acceptance gate.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder BigOperators

/-- The actual principal-refined source primary auxiliary levels have the exact finite free automorphic comparison and original weighted trace. -/
theorem cmFiniteAdelicSmallPrimaryAuxiliaryModule_comparison
    {K : Type} {R W S : Type*} [Field K] [NumberField K] [IsCMField K]
    [CommRing R] [AddCommGroup W] [Module R W] [Fintype S]
    (v : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (H : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ)
    (hpos : ∀ φ : K →+* ℂ, (φ.mapMatrix H.val).PosDef)
    (hv : ∀ s, v s ≠ cmFinitePlaceConjugation K (v s))
    (hlocal : ∀ s, cmFiniteAdelicFormIntegralAtConjugate K H (v s))
    (hsep : Pairwise fun s t => v s ≠ v t ∧ v s ≠ cmFinitePlaceConjugation K (v t))
    (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ s, w ≠ v s ∧ w ≠ cmFinitePlaceConjugation K (v s))
    (p : ℕ) (hp : p.Prime) [CharP (Valued.ResidueField (w.adicCompletion K)) p]
    (hlarge : Fintype.card (Fin (n + 1)) * Module.finrank ℚ K < p - 1) (q : ℕ)
    (ρ : Representation R (cmFiniteAdelicSmallParabolicZero K v n H.val w) W)
    [Module.Finite R W] [Module.Free R W] :
    let hH := cmHermitianPositiveUnit_star K H hpos
    let U := cmFiniteAdelicSmallParabolicZero K v n H.val w
    let V := cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q
    let hVU := cmFiniteAdelicSmallPrimaryLevel_le K v n H hH hv hlocal hsep w hw q
    letI : Finite (U ⧸ V.subgroupOf U) :=
      cmFiniteAdelicSmallPrimaryQuotient_finite K v n H hH hv hlocal hsep w hw q
    letI : Fintype (U ⧸ V.subgroupOf U) := Fintype.ofFinite _
    let Γ := ((cmHermitianFiniteAdeleHom H.val).codRestrict (cmFiniteAdelicUnitaryGroup K H.val)
      (cmFiniteAdelicUnitaryGroup_principal K H.val)).range
    let hs := cmHermitianAdelic_smallLevel_of_large_congruence H.val hpos (cmFiniteAdelicUnitaryGroup K H.val)
      (cmFiniteAdelicUnitaryGroup_principal K H.val) U
      (cmFiniteAdelicSmallParabolicZero_isCompact K v n H.val w) w p hp hlarge
      (cmFiniteAdelicSmallParabolicZero_projection K v n H.val w)
    Module.Free (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hs).asModule ∧
    Module.Finite (MonoidAlgebra R (U ⧸ V.subgroupOf U))
      (auxiliaryAutomorphicAction Γ U V hVU ρ hs).asModule ∧
    ∃ e : (auxiliaryAutomorphicAction Γ U V hVU ρ hs).Coinvariants ≃ₗ[R]
        algebraicAutomorphicForms Γ U ρ,
      ∀ (f : algebraicAutomorphicForms Γ V (ρ.comp (V.inclusion hVU)))
        (g : cmFiniteAdelicUnitaryGroup K H.val),
        (e (Representation.Coinvariants.mk
          (auxiliaryAutomorphicAction Γ U V hVU ρ hs) f)).val g =
          ∑ a : U ⧸ V.subgroupOf U, ρ a.out (f.val (g * (a.out : cmFiniteAdelicUnitaryGroup K H.val))) := by
  let hH := cmHermitianPositiveUnit_star K H hpos
  letI := cmFiniteAdelicSmallPrimaryQuotient_finite K v n H hH hv hlocal hsep w hw q
  letI : Fintype (cmFiniteAdelicSmallParabolicZero K v n H.val w ⧸
      (cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q).subgroupOf
        (cmFiniteAdelicSmallParabolicZero K v n H.val w)) := Fintype.ofFinite _
  exact cmFiniteAdelicOpenAuxiliaryModule_comparison H.val hpos
    (cmFiniteAdelicSmallParabolicZero K v n H.val w)
    (cmFiniteAdelicSmallPrimaryLevel K v n H hH hv hlocal hsep w hw q)
    (cmFiniteAdelicSmallParabolicZero_isCompact K v n H.val w)
    (cmFiniteAdelicSmallParabolicZero_isOpen K v n H.val w)
    (cmFiniteAdelicSmallPrimaryLevel_le K v n H hH hv hlocal hsep w hw q)
    w p hp hlarge (cmFiniteAdelicSmallParabolicZero_projection K v n H.val w) ρ

end
end Dubon2026

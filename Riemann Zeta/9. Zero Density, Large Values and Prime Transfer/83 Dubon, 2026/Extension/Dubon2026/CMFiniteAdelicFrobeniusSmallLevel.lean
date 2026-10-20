import Dubon2026.SourceSmallnessFrobeniusPrime
import Dubon2026.CMFiniteAdelicClassFiniteness
import Dubon2026.CMFiniteAdelicPrincipalLevel

/-! # Actual unitary small levels at the prescribed auxiliary Frobenius

The specified original CM form now has a principal compact open level
with trivial arithmetic stabilizers and finitely many arithmetic classes
at a prime satisfying the simultaneous Frobenius and cyclotomic-degree
conditions. This discharges the prime choice for the source smallness
construction once its actual residual and cyclotomic maps and their
kernel noncontainment are supplied. These source representation inputs,
the field and local-form choices, and the weight/Hecke construction are
still required for DUB-17; no automorphy or acceptance gate is asserted.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder

/-- The actual definite CM unitary group has finite arithmetic classes and trivial stabilizers at a compact open principal level whose prime realizes the prescribed source Frobenius separation. -/
theorem cmFiniteAdelic_exists_frobenius_small_level
    (K : Type) [Field K] [NumberField K] [IsCMField K]
    {ι Ω A C : Type*} [Fintype ι] [DecidableEq ι]
    [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    [Group A] [TopologicalSpace A] [DiscreteTopology A]
    [Group C] [TopologicalSpace C] [DiscreteTopology C]
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (ρ : Gal(Ω/K) →ₜ* A) (χ : Gal(Ω/K) →ₜ* C)
    (hker : ¬ ρ.toMonoidHom.ker ≤ χ.toMonoidHom.ker) :
    ∃ F : FiniteGaloisIntermediateField K Ω, ∃ ψ : Gal(F/K) →* A × C,
      (∀ g : Gal(Ω/K), ψ (AlgEquiv.restrictNormalHom F g) = (ρ g, χ g)) ∧
      (letI : NumberField F := NumberField.of_module_finite K F
       ∀ S : Finset (Ideal (𝓞 K)),
         ∃ (v : HeightOneSpectrum (𝓞 K)) (p : ℕ),
           v.asIdeal ∉ S ∧ p.Prime ∧ Fintype.card ι * Module.finrank ℚ K < p - 1 ∧
           CharP (Valued.ResidueField (v.adicCompletion K)) p ∧
           Algebra.IsUnramifiedAt ℤ v.asIdeal ∧
           Chebotarev.UnramifiedIn K F v.asIdeal ∧
           (ψ (Chebotarev.frobeniusClass K F v.asIdeal).out).1 = 1 ∧
           (ψ (Chebotarev.frobeniusClass K F v.asIdeal).out).2 ≠ 1 ∧
           Fintype.card ι < Module.finrank K (CyclotomicField p K) ∧
           IsOpen (cmFiniteAdelicPrincipalLevel K H v : Set (cmFiniteAdelicUnitaryGroup K H)) ∧
           IsCompact (cmFiniteAdelicPrincipalLevel K H v : Set (cmFiniteAdelicUnitaryGroup K H)) ∧
           Finite (DoubleCoset.Quotient (G := cmFiniteAdelicUnitaryGroup K H)
             ((cmHermitianFiniteAdeleHom H).codRestrict (cmFiniteAdelicUnitaryGroup K H)
               (cmFiniteAdelicUnitaryGroup_principal K H)).range (cmFiniteAdelicPrincipalLevel K H v)) ∧
           ∀ (g : cmFiniteAdelicUnitaryGroup K H) (u : cmFiniteAdelicPrincipalLevel K H v),
             g * u.val * g⁻¹ ∈ ((cmHermitianFiniteAdeleHom H).codRestrict
               (cmFiniteAdelicUnitaryGroup K H) (cmFiniteAdelicUnitaryGroup_principal K H)).range →
                 u = 1) := by
  obtain ⟨F, ψ, hψ, hF⟩ := continuous_galois_exists_smallness_frobenius_prime ρ χ hker
  refine ⟨F, ψ, hψ, ?_⟩
  letI : NumberField F := NumberField.of_module_finite K F
  intro S
  obtain ⟨v, p, hv, hp, hlarge, hchar, habs, hur, hρ, hχ, hdeg⟩ := hF S (Fintype.card ι)
  letI := hchar
  have hopen := cmFiniteAdelicPrincipalLevel_isOpen K H v
  exact ⟨v, p, hv, hp, hlarge, hchar, habs, hur, hρ, hχ, hdeg, hopen,
    cmFiniteAdelicPrincipalLevel_isCompact K H v,
    cmFiniteAdelicDoubleCoset_finite K H hH (cmFiniteAdelicPrincipalLevel K H v) hopen,
    cmFiniteAdelicPrincipalLevel_small K H hH v p hp hlarge⟩

end
end Dubon2026

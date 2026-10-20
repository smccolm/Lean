import Dubon2026.CMFiniteAdelicFrobeniusSmallLevel
import Dubon2026.PrimitiveRootCyclotomicContinuity

/-! # Source root noncontainment and the genuine cyclotomic smallness prime

The second Frobenius map is constructed from the actual primitive root.
Its continuity is reused from the existing Krull-topology proof. The
source hypothesis that this root is outside the field fixed by the
residual adjoint kernel discharges the kernel-separation premise. This
advances DUB-17's BLGG 3.6.1 auxiliary prime construction without an
independently supplied cyclotomic character.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder

/-- Source noncontainment of the actual primitive root implies the exact cyclotomic kernel separation. -/
theorem primitiveRoot_not_mem_fixedField_kernel_separation
    {K Ω A : Type} [Field K] [Field Ω] [Algebra K Ω]
    [Group A] (ρ : Gal(Ω/K) →* A) {l : ℕ} [NeZero l]
    {z : Ω} (hz : IsPrimitiveRoot z l)
    (hnot : z ∉ IntermediateField.fixedField ρ.ker) :
    ¬ ρ.ker ≤ (hz.autToPow K).ker := by
  intro hle
  apply hnot
  rw [IntermediateField.mem_fixedField_iff]
  intro g hg
  have he : hz.autToPow K g = hz.autToPow K 1 :=
    (show hz.autToPow K g = 1 from hle hg).trans (map_one _).symm
  rw [← hz.autToPow_spec K g, he, hz.autToPow_spec K 1]
  rfl

/-- The source root-noncontainment hypothesis constructs the genuine cyclotomic character and a corresponding actual compact open unitary small level. -/
theorem cmFiniteAdelic_exists_cyclotomic_small_level
    (K : Type) [Field K] [NumberField K] [IsCMField K]
    {ι : Type*} {Ω A : Type} [Fintype ι] [DecidableEq ι]
    [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    [Group A] [TopologicalSpace A] [DiscreteTopology A]
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (ρ : Gal(Ω/K) →ₜ* A) {l : ℕ} [NeZero l] {z : Ω}
    (hz : IsPrimitiveRoot z l)
    (hnot : z ∉ IntermediateField.fixedField ρ.toMonoidHom.ker) :
    ∃ F : FiniteGaloisIntermediateField K Ω, ∃ ψ : Gal(F/K) →* A × (ZMod l)ˣ,
      (∀ g : Gal(Ω/K), ψ (AlgEquiv.restrictNormalHom F g) = (ρ g, hz.autToPow K g)) ∧
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
  let χ : Gal(Ω/K) →ₜ* (ZMod l)ˣ :=
    ⟨hz.autToPow K, primitiveRootCyclotomicCharacter_continuous hz⟩
  exact cmFiniteAdelic_exists_frobenius_small_level K H hH ρ χ
    (primitiveRoot_not_mem_fixedField_kernel_separation ρ.toMonoidHom hz hnot)

end
end Dubon2026

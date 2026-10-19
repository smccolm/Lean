import Dubon2026.ArithmeticTorusPrimaryDescent
import Dubon2026.LocalAdicQuotientResidue
import Dubon2026.AdicPowerQuotientTopology
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! The fixed auxiliary inertia quotient acts on the original Noetherian
adic coefficient ring. Artinian reductions and Krull intersection remove
the Artinian coefficient restriction without choosing compatible bases.
This supplies the actual universal-ring action on the Dubon Theorem 2.6
arithmetic patching dependency chain. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField

attribute [local instance] rationalArithmeticOriginalFiniteGalois rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

private theorem localMatrix_eq_one_of_power_reductions
    {A ι : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Fintype ι] [DecidableEq ι] (M : GeneralLinearGroup ι A)
    (h : ∀ n : ℕ, GeneralLinearGroup.map
      (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) M = 1) : M = 1 := by
  apply Units.ext
  ext i j
  apply (IsHausdorff.eq_iff_smodEq (I := maximalIdeal A)).mpr
  intro n
  cases n with
  | zero => simp [SModEq.sub_mem]
  | succ n =>
    rw [SModEq.sub_mem]
    change _ ∈ (maximalIdeal A ^ (n + 1) • (⊤ : Ideal A))
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    apply Ideal.Quotient.eq.mp
    simpa [Matrix.one_apply] using congrArg (fun X : GeneralLinearGroup ι
      (A ⧸ maximalIdeal A ^ (n + 1)) => X.val i j) (h n)

private theorem subgroup_unique_factor
    {G H D : Type*} [Group G] [Group H] [Group D]
    (ρ : G →* H) (π : G →* D) (I : Subgroup G)
    (hs : Function.Surjective (π.comp I.subtype))
    (hk : (π.comp I.subtype).ker ≤ (ρ.comp I.subtype).ker) :
    ∃! η : D →* H, ∀ g ∈ I, η (π g) = ρ g := by
  let πI := π.comp I.subtype
  let ρI := ρ.comp I.subtype
  let η := πI.liftOfSurjective hs ⟨ρI, hk⟩
  have hc : η.comp πI = ρI := πI.liftOfRightInverse_comp _ _ _
  refine ⟨η, ?_, ?_⟩
  · intro g hg
    exact DFunLike.congr_fun hc ⟨g, hg⟩
  · intro η' hη'
    apply MonoidHom.ext
    intro d
    obtain ⟨g, rfl⟩ := hs d
    exact (hη' g.val g.property).trans (DFunLike.congr_fun hc g).symm

private theorem adicPrimary_kernel_powerReduction
    (a b : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime] (hlevel : 0 < level)
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes) [NeZero p.val]
    (hgood : RationalArithmeticTorusAuxiliaryPrime a q degree level R p)
    (hpb : (p.val : 𝓞 ℚ) ∣ b)
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [WithIdeal A]
    (hA : (WithIdeal.i : Ideal A) = maximalIdeal A)
    (eA : ResidueField A ≃+* ZMod q)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) A)
    (hτ : Continuous τ)
    (hred : ∀ g, GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g))
    (g : Gal(rationalPrimeLocalClosure p.val p.property / rationalPrimeLocalField p.val p.property))
    (hg : g ∈ rationalPrimeNormInertia p.val p.property)
    (hπ : QuotientGroup.mk' (rationalPrimeTameCoefficientKernel p.val q)
      (rationalPrimeCyclotomicCharacter p.val p.property p.val g) = 1) (n : ℕ) :
    GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) = 1 := by
  letI : Finite (ResidueField A) := Finite.of_injective eA eA.injective
  let J := maximalIdeal A ^ (n + 1)
  let B := A ⧸ J
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
    (Ideal.pow_le_self (Nat.succ_ne_zero n))
  letI : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hJ
  letI : IsLocalRing B := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  letI : Finite B := finite_quotient_iff.mpr ⟨n + 1, le_rfl⟩
  letI : DiscreteTopology B := by
    change DiscreteTopology (A ⧸ maximalIdeal A ^ (n + 1))
    rw [← hA]
    exact adicPowerQuotient_discrete (n + 1)
  let eB := (localQuotientResidueAlgEquiv (O := A) J).symm.toRingEquiv.trans eA
  let τB := (GeneralLinearGroup.map (n := Fin (degree + 1)) (Ideal.Quotient.mk J)).comp τ
  have hc : Continuous τB := by
    change Continuous ((GeneralLinearGroup.map (n := Fin (degree + 1)) (Ideal.Quotient.mk J)) ∘ τ)
    apply Continuous.comp ?_ hτ
    change Continuous (GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))))
    rw [← hA]
    exact adicMatrixPowerReduction_continuous (n + 1)
  have he : (eB.toRingHom.comp (residue B)).comp (Ideal.Quotient.mk J) =
      eA.toRingHom.comp (residue A) := by
    ext x
    change eA ((localQuotientResidueAlgEquiv (O := A) J).symm
      (residue B (Ideal.Quotient.mk J x))) = eA (residue A x)
    rw [← localQuotientResidueAlgEquiv_residue (O := A) J x, AlgEquiv.symm_apply_apply]
  have hr : ∀ x, GeneralLinearGroup.map (eB.toRingHom.comp (residue B))
      (τB (rationalPrimeArithmeticRestriction b p.val p.property x)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property x) := by
    intro x
    change ((GeneralLinearGroup.map (eB.toRingHom.comp (residue B))).comp
      (GeneralLinearGroup.map (Ideal.Quotient.mk J)))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property x)) = _
    rw [← GeneralLinearGroup.map_comp, he]
    exact hred x
  obtain ⟨η, hη, _⟩ := rationalArithmetic_torus_global_primary_descent
    a b q degree level hlevel R p hgood hpb eB τB hc hr
  have h := hη g hg
  rw [hπ, map_one] at h
  exact h.symm

/-- The same selected prime and actual global adic lift determine the
unique action of the fixed coefficient-primary quotient on original
inertia. The coefficient ring need not be Artinian or complete. -/
theorem rationalArithmetic_torus_global_adic_primary_descent
    (a b : 𝓞 ℚ) (q degree level : ℕ) [Fact q.Prime] (hlevel : 0 < level)
    (R : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ZMod q))
    (p : Nat.Primes) [NeZero p.val]
    (hgood : RationalArithmeticTorusAuxiliaryPrime a q degree level R p)
    (hpb : (p.val : 𝓞 ℚ) ∣ b)
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [WithIdeal A]
    (hA : (WithIdeal.i : Ideal A) = maximalIdeal A)
    (eA : ResidueField A ≃+* ZMod q)
    (τ : rationalArithmeticGaloisGroup b →* GeneralLinearGroup (Fin (degree + 1)) A)
    (hτ : Continuous τ)
    (hred : ∀ g, GeneralLinearGroup.map (eA.toRingHom.comp (residue A))
      (τ (rationalPrimeArithmeticRestriction b p.val p.property g)) =
        R (rationalPrimeArithmeticRestriction a p.val p.property g)) :
    ∃! η : RationalPrimeTameCoefficientQuotient p.val q →* GeneralLinearGroup (Fin (degree + 1)) A,
      ∀ g ∈ rationalPrimeNormInertia p.val p.property,
        η (QuotientGroup.mk' (rationalPrimeTameCoefficientKernel p.val q)
          (rationalPrimeCyclotomicCharacter p.val p.property p.val g)) =
            τ (rationalPrimeArithmeticRestriction b p.val p.property g) := by
  letI : Finite (ResidueField A) := Finite.of_injective eA eA.injective
  let I := rationalPrimeNormInertia p.val p.property
  let π := (QuotientGroup.mk' (rationalPrimeTameCoefficientKernel p.val q)).comp
    (rationalPrimeCyclotomicCharacter p.val p.property p.val).toMonoidHom
  let πI := π.comp I.subtype
  let ρI := (τ.comp (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom).comp I.subtype
  have hp2 : p.val ≠ 2 := by
    have hm := hgood.2.1.of_dvd (dvd_pow_self q (Nat.ne_of_gt hlevel))
    have hpone : (p.val : ZMod q) = 1 := by
      simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff p.val 1 q).mpr hm
    intro h
    have he : (1 : ZMod q) + 1 = 1 + 0 := by simpa only [h, Nat.cast_ofNat, one_add_one_eq_two, add_zero] using hpone
    exact one_ne_zero (add_left_cancel he)
  have hs : Function.Surjective πI := by
    intro d
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (rationalPrimeTameCoefficientKernel p.val q) d
    obtain ⟨g, hg, hv⟩ := rationalPrimeCyclotomicCharacter_inertia_surjective p.val p.property hp2 v
    exact ⟨⟨g, hg⟩, congrArg (QuotientGroup.mk' _) hv⟩
  have hk : πI.ker ≤ ρI.ker := by
    intro g hg
    exact localMatrix_eq_one_of_power_reductions (ρI g) (fun n =>
      adicPrimary_kernel_powerReduction a b q degree level hlevel R p hgood hpb hA eA τ hτ hred
        g.val g.property hg n)
  exact subgroup_unique_factor
    (τ.comp (rationalPrimeArithmeticRestriction b p.val p.property).toMonoidHom) π I hs hk

end
end Dubon2026

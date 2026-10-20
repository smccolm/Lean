import Dubon2026.CMAdelicPairingClosure

/-! # Recovering the original lattice from its integral pairings

The actual unitary equation and a fixed integral multiple of the inverse
Hermitian matrix turn integral pairings into inverse-matrix integrality.
Together with the trace-dual denominator this will give the uniform
dual-lattice containment for DUB-17's finite Gram-class argument.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain Matrix
attribute [local instance] cmFiniteAdeleStarRing

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A fixed integral inverse-matrix multiple turns original integral pairings into membership in the actual lattice. -/
theorem cmAdelicPairing_scaled_dual_mem (H J : Matrix ι ι K) (hHJ : H * J = 1)
    (k : ℤ) (hJ : ∀ i j, IsIntegral ℤ (k • J i j)) (n : ℤ)
    (g : cmFiniteAdelicUnitaryGroup K H) (x : ι → K)
    (hx : ∀ y : numberFieldAdelicLattice K ι g.val,
      IsIntegral ℤ (n • dotProduct (star x) (H.mulVec y.val))) :
    (k * n) • x ∈ numberFieldAdelicLattice K ι g.val := by
  let A := (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix H
  let B := (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix J
  let px := numberFieldAdelicVectorMap K ι x
  let u := (g.val⁻¹).val.mulVec px
  have hAB : A * B = 1 := by
    rw [← map_mul, hHJ, map_one]
  have hr (i : ι) : (n • (star u ᵥ* A)) i ∈ numberFieldIntegralFiniteAdeles K := by
    let e : ι → FiniteAdeleRing (𝓞 K) K := Pi.single i 1
    have he (j : ι) : e j ∈ numberFieldIntegralFiniteAdeles K := by
      dsimp [e]
      by_cases h : j = i
      · subst j
        simp only [Pi.single_eq_same]
        exact (numberFieldIntegralFiniteAdeles K).one_mem
      · rw [Pi.single_eq_of_ne h]
        exact (numberFieldIntegralFiniteAdeles K).zero_mem
    have hregion : g.val.val.mulVec e ∈ numberFieldAdelicLatticeRegion K ι g.val := by
      change ∀ j, (g.val⁻¹).val.mulVec (g.val.val.mulVec e) j ∈ _
      rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
      exact he
    have hi := cmAdelicPairing_integral_on_region K H n g x hx _ hregion
    have hp := cmFiniteAdelicPairing_preserved K H g u e
    have hu : g.val.val.mulVec u = px := by
      dsimp [u]
      rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    rw [hu] at hp
    change n • dotProduct (star px) (A.mulVec (g.val.val.mulVec e)) ∈ _ at hi
    change dotProduct (star px) (A.mulVec (g.val.val.mulVec e)) =
      dotProduct (star u) (A.mulVec e) at hp
    rw [hp, dotProduct_mulVec] at hi
    simpa only [e, dotProduct_single_one, Pi.smul_apply] using hi
  have hB (i j : ι) : (k • B) i j ∈ numberFieldIntegralFiniteAdeles K := by
    change k • algebraMap K (FiniteAdeleRing (𝓞 K) K) (J i j) ∈ _
    simpa only [zsmul_eq_mul, map_mul, map_intCast] using
      (numberFieldFiniteAdele_integral_iff K _).mpr (hJ i j)
  have hrow (i : ι) : ((n • (star u ᵥ* A)) ᵥ* (k • B)) i ∈
      numberFieldIntegralFiniteAdeles K := by
    apply (numberFieldIntegralFiniteAdeles K).sum_mem
    intro j _
    exact (numberFieldIntegralFiniteAdeles K).mul_mem (hr j) (hB j i)
  rw [vecMul_smul, smul_vecMul, vecMul_vecMul, hAB, vecMul_one, smul_smul] at hrow
  have hu (i : ι) : ((k * n) • u) i ∈ numberFieldIntegralFiniteAdeles K := by
    have hs := cmFiniteAdele_star_integral K (hrow i)
    simpa only [Pi.smul_apply, Pi.star_apply, star_smul, star_trivial, star_star] using hs
  apply (numberFieldAdelicLattice_mem_iff K ι g.val _).mpr
  have he : numberFieldAdelicVectorMap K ι ((k * n) • x) = (k * n) • px := by
    funext i
    change algebraMap K (FiniteAdeleRing (𝓞 K) K) ((k * n) • x i) =
      (k * n) • algebraMap K (FiniteAdeleRing (𝓞 K) K) (x i)
    simp only [zsmul_eq_mul, map_mul, map_intCast]
  change ∀ i, (g.val⁻¹).val.mulVec (numberFieldAdelicVectorMap K ι ((k * n) • x)) i ∈ _
  rw [he, mulVec_smul]
  exact hu

end
end Dubon2026

import Tao2026.PolynomialEulerCoefficients

/-!
# Polynomiality of the literal root-multiset Kummer L-series

Finite Frobenius orbit Euler products identify every Newton coefficient with a
signed monic-polynomial character sum. Character orthogonality gives the degree
cutoff, hence the canonical characteristic recurrence without a recurrence premise.
-/

namespace Tao2026
open Finset Polynomial UniqueFactorizationMonoid
open scoped BigOperators
noncomputable section

theorem complexEulerDivisorSumNewton_eq_signed_coeff {ι : Type*} [Fintype ι]
    (l : ι → ℕ) (hl : ∀ i, l i ≠ 0) (b : ι → ℂ) (s : ℕ → ℂ) (m : ℕ)
    (hs : ∀ d, 0 < d → d ≤ m → s d =
      -(∑ i, if l i ∣ d then (l i : ℂ) * b i ^ (d / l i) else 0)) :
    complexNewtonElementary s m = (-1 : ℂ) ^ m *
      PowerSeries.coeff m (∏ i, complexEulerFactor (l i) (hl i) (b i)) := by
  let G (i : ι) := complexEulerFactor (l i) (hl i) (b i)
  let F : PowerSeries ℂ := ∏ i, G i
  let T : PowerSeries ℂ := ∑ i, PowerSeries.C (l i : ℂ) * (G i - 1)
  have hF : PowerSeries.constantCoeff F = 1 := by
    simp [F, G, complexEulerFactor_constantCoeff]
  have hT : PowerSeries.constantCoeff T = 0 := by
    simp [T, G, complexEulerFactor_constantCoeff]
  have hD : PowerSeries.X * PowerSeries.derivative ℂ F = F * T :=
    complexPowerSeries_prod_derivative univ G
      (fun i => PowerSeries.C (l i : ℂ) * (G i - 1))
      (fun i _ => complexEulerFactor_derivative (l i) (hl i) (b i))
  apply complexNewtonElementary_eq_signed_coeff s F T hF hT hD m
  intro d hd hdm
  rw [hs d hd hdm]
  congr 1
  simp only [T, map_sum, PowerSeries.coeff_C_mul, map_sub,
    G, complexEulerFactor_coeff, PowerSeries.coeff_one, if_neg (Nat.ne_of_gt hd),
    sub_zero, mul_ite, mul_zero]

theorem finitePermutationWeight_newton_eq_signed_coeff {α : Type*} [Fintype α]
    (σ : Equiv.Perm α) (w : ℕ → α → ℂ)
    (hinv : ∀ d x, (σ ^ d) x = x → w d (σ x) = w d x)
    (hmul : ∀ d k x, (σ ^ d) x = x → w (d * k) x = w d x ^ k)
    (s : ℕ → ℂ) (m : ℕ)
    (hs : letI : DecidableEq α := Classical.decEq _
      ∀ d, 0 < d → d ≤ m → s d =
        -(∑ x ∈ univ.filter (fun x => (σ ^ d) x = x), w d x)) :
    letI : Fintype (finitePermutationOrbits σ) := Fintype.ofFinite _
    complexNewtonElementary s m = (-1 : ℂ) ^ m * PowerSeries.coeff m
      (∏ o : finitePermutationOrbits σ,
        complexEulerFactor (finitePermutationOrbitLength σ o)
          (finitePermutationOrbitLength_pos σ o).ne'
          (w (finitePermutationOrbitLength σ o) o.out)) := by
  classical
  letI : Fintype (finitePermutationOrbits σ) := Fintype.ofFinite _
  apply complexEulerDivisorSumNewton_eq_signed_coeff
  intro d hd hdm
  rw [hs d hd hdm, finitePermutationWeight_fixed_sum σ w hinv hmul d]

theorem primeRootMultisetPolynomialWeight_prod
    {ι : Type*} (s : Finset ι) (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (P : ι → (ZMod p)[X]) (hmon : ∀ i ∈ s, (P i).Monic) :
    primeRootMultisetPolynomialWeight p χ R (∏ i ∈ s, P i) =
      ∏ i ∈ s, primeRootMultisetPolynomialWeight p χ R (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [primeRootMultisetPolynomialWeight_one]
  | @insert a s ha ih =>
      rw [prod_insert ha, prod_insert ha,
        primeRootMultisetPolynomialWeight_mul p χ R _ _ (hmon a (mem_insert_self _ _))
          (monic_prod_of_monic _ _ (fun i hi => hmon i (mem_insert_of_mem hi))),
        ih (fun i hi => hmon i (mem_insert_of_mem hi))]

theorem primeRootMultisetMonicLseriesCoefficient_eq_monic_sum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (m : ℕ) :
    letI : Fintype (degreeLT (ZMod p) m) :=
      Fintype.ofEquiv (Fin m → ZMod p) (degreeLTEquiv (ZMod p) m).symm.toEquiv
    letI : Fintype {Q : (ZMod p)[X] // Q.Monic ∧ Q.natDegree = m} :=
      Fintype.ofEquiv (degreeLT (ZMod p) m) (monicEquivDegreeLT m).symm
    primeRootMultisetMonicLseriesCoefficient p χ R m =
      ∑ Q : {Q : (ZMod p)[X] // Q.Monic ∧ Q.natDegree = m},
        primeRootMultisetPolynomialWeight p χ R Q.val := by
  classical
  letI : Fintype (degreeLT (ZMod p) m) :=
    Fintype.ofEquiv (Fin m → ZMod p) (degreeLTEquiv (ZMod p) m).symm.toEquiv
  letI : Fintype {Q : (ZMod p)[X] // Q.Monic ∧ Q.natDegree = m} :=
    Fintype.ofEquiv (degreeLT (ZMod p) m) (monicEquivDegreeLT m).symm
  exact Fintype.sum_equiv (monicEquivDegreeLT m).symm _ _ (fun _ => rfl)

def primeRootMultisetOrbitEulerProduct
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) : PowerSeries ℂ :=
  letI : Fintype (finitePermutationOrbits (primeFieldFrobeniusPerm p n)) := Fintype.ofFinite _
  ∏ o : finitePermutationOrbits (primeFieldFrobeniusPerm p n),
    complexEulerFactor (finitePermutationOrbitLength (primeFieldFrobeniusPerm p n) o)
      (finitePermutationOrbitLength_pos (primeFieldFrobeniusPerm p n) o).ne'
      (primeFieldFrobeniusWeight p n
        (finitePermutationOrbitLength (primeFieldFrobeniusPerm p n) o) χ R o.out)

theorem primeRootMultisetOrbitEulerProduct_coeff_eq_monic
    (p n m : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (hdegrees : ∀ d : ℕ, 0 < d → d ≤ m → d ∣ n) :
    PowerSeries.coeff m (primeRootMultisetOrbitEulerProduct p n χ R) =
      primeRootMultisetMonicLseriesCoefficient p χ R m := by
  classical
  letI : Fintype (finitePermutationOrbits (primeFieldFrobeniusPerm p n)) := Fintype.ofFinite _
  letI : Fintype (degreeLT (ZMod p) m) :=
    Fintype.ofEquiv (Fin m → ZMod p) (degreeLTEquiv (ZMod p) m).symm.toEquiv
  letI : Fintype {Q : (ZMod p)[X] // Q.Monic ∧ Q.natDegree = m} :=
    Fintype.ofEquiv (degreeLT (ZMod p) m) (monicEquivDegreeLT m).symm
  let P := primeFieldOrbitMinpoly p n
  have hcover : ∀ Q : (ZMod p)[X], Q.Monic → Irreducible Q → Q.natDegree ≤ m →
      ∃ o, P o = Q := by
    intro Q hmon hirr hdeg
    exact primeFieldOrbitMinpoly_exists_of_irreducible_degree_dvd p n Q hmon hirr
      (hdegrees Q.natDegree hirr.natDegree_pos hdeg)
  have hproduct : primeRootMultisetOrbitEulerProduct p n χ R =
      ∏ o, complexEulerFactor (P o).natDegree
        (primeFieldOrbitMinpoly_irreducible p n o).natDegree_pos.ne'
        (primeRootMultisetPolynomialWeight p χ R (P o)) := by
    unfold primeRootMultisetOrbitEulerProduct
    apply prod_congr rfl
    intro o _
    dsimp only [P]
    congr 1
    · exact (primeFieldOrbitMinpoly_natDegree p n o).symm
    · exact primeFieldFrobeniusWeight_eq_minpoly_weight p n χ R o.out
  rw [hproduct, monicIrreducibleFamily_eulerCoefficient P (primeFieldOrbitMinpoly_monic p n)
    (primeFieldOrbitMinpoly_irreducible p n) (primeFieldOrbitMinpoly_injective p n)
    (fun o => primeRootMultisetPolynomialWeight p χ R (P o)) m hcover,
    primeRootMultisetMonicLseriesCoefficient_eq_monic_sum]
  apply sum_congr rfl
  intro Q _
  have hprod := monicIrreducibleFamily_prod_count P (primeFieldOrbitMinpoly_injective p n)
    Q.val Q.property.1
    (monicIrreducibleFamily_covers_normalizedFactors P m hcover Q.val Q.property.1 Q.property.2.le)
  calc
    _ = primeRootMultisetPolynomialWeight p χ R
        (∏ o, P o ^ (normalizedFactors Q.val).count (P o)) := by
      rw [primeRootMultisetPolynomialWeight_prod univ p χ R _
        (fun o _ => (primeFieldOrbitMinpoly_monic p n o).pow _)]
      apply prod_congr rfl
      intro o _
      exact (primeRootMultisetPolynomialWeight_pow p χ R (P o)
        (primeFieldOrbitMinpoly_monic p n o) _).symm
    _ = _ := congrArg (primeRootMultisetPolynomialWeight p χ R) hprod

theorem primeRootMultisetNewtonElementary_eq_signed_monicCoefficient
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (m : ℕ) :
    primeRootMultisetNewtonElementary p χ R m =
      (-1 : ℂ) ^ m * primeRootMultisetMonicLseriesCoefficient p χ R m := by
  classical
  letI : NeZero m.factorial := ⟨Nat.factorial_ne_zero m⟩
  letI : Fintype (primeFieldExtension p m.factorial) := Fintype.ofFinite _
  have hNewton : primeRootMultisetNewtonElementary p χ R m = (-1 : ℂ) ^ m *
      PowerSeries.coeff m (primeRootMultisetOrbitEulerProduct p m.factorial χ R) := by
    apply finitePermutationWeight_newton_eq_signed_coeff
      (primeFieldFrobeniusPerm p m.factorial)
      (primeFieldFrobeniusWeight p m.factorial · χ R)
      (s := primeRootMultisetNewtonPowerSum p χ R) (m := m)
    · intro d x hx
      rw [primeFieldFrobeniusPerm_apply]
      exact primeFieldFrobeniusWeight_frob p m.factorial d χ R x
        (by simpa only [primeFieldFrobeniusPerm_pow_apply] using hx)
    · intro d k x hx
      exact primeFieldFrobeniusWeight_mul p m.factorial d k χ R x
        (by simpa only [primeFieldFrobeniusPerm_pow_apply] using hx)
    · intro d hd hdm
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
      rw [primeRootMultisetNewtonPowerSum]
      congr 1
      rw [primeRootMultisetExtensionCorrelation_eq_fixed_sum p m.factorial q
        (Nat.dvd_factorial (Nat.succ_pos q) hdm) χ R]
      simp only [primeFieldFrobeniusPerm_pow_apply, Nat.succ_eq_add_one]
  rw [hNewton, primeRootMultisetOrbitEulerProduct_coeff_eq_monic p m.factorial m χ R
    (fun d hd hdm => Nat.dvd_factorial hd hdm)]

theorem primeRootMultisetNewtonElementary_eq_zero_of_support_le
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (m : ℕ)
    (hm : R.toFinset.card ≤ m) (r₀ : ZMod p) (hr₀ : r₀ ∈ R)
    (hcount : R.count r₀ < orderOf χ) :
    primeRootMultisetNewtonElementary p χ R m = 0 := by
  rw [primeRootMultisetNewtonElementary_eq_signed_monicCoefficient,
    primeRootMultisetMonicLseriesCoefficient_eq_zero p χ R m hm r₀ hr₀ hcount,
    mul_zero]

theorem primeRootMultisetNewtonElementary_eq_canonical_esymm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (r₀ : ZMod p) (hr₀ : r₀ ∈ R) (hcount : R.count r₀ < orderOf χ) (j : ℕ) :
    primeRootMultisetNewtonElementary p χ R j =
      (primeRootMultisetCanonicalEigenvalues p χ R).esymm j := by
  by_cases hj : j ≤ primeRootMultisetSpectralRank R
  · exact (esymm_primeRootMultisetCanonicalEigenvalues_eq_newtonElementary p χ R j hj).symm
  · have hsupport : R.toFinset.card ≤ j := by
      unfold primeRootMultisetSpectralRank at hj
      omega
    rw [primeRootMultisetNewtonElementary_eq_zero_of_support_le p χ R j hsupport r₀ hr₀ hcount]
    have hcard : (primeRootMultisetCanonicalEigenvalues p χ R).card < j := by
      rw [card_primeRootMultisetCanonicalEigenvalues]
      omega
    simp [Multiset.esymm, Multiset.powersetCard_eq_empty j hcard]

theorem primeRootMultisetNewtonPowerSum_eq_canonical
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (r₀ : ZMod p) (hr₀ : r₀ ∈ R) (hcount : R.count r₀ < orderOf χ) (d : ℕ) :
    primeRootMultisetNewtonPowerSum p χ R d =
      ((primeRootMultisetCanonicalEigenvalues p χ R).map fun a => a ^ d).sum := by
  cases d with
  | zero =>
      simp [primeRootMultisetNewtonPowerSum, card_primeRootMultisetCanonicalEigenvalues]
  | succ d =>
      apply complexNewtonPowerSum_eq_of_elementary_eq
        (primeRootMultisetNewtonPowerSum p χ R)
        (fun k => ((primeRootMultisetCanonicalEigenvalues p χ R).map fun a => a ^ k).sum)
        (d + 1)
      · intro j _
        rw [complexNewtonElementary_powerSum_eq_esymm]
        exact primeRootMultisetNewtonElementary_eq_canonical_esymm p χ R r₀ hr₀ hcount j
      · exact le_rfl
      · omega

theorem primeRootMultisetNewtonPowerSum_characteristic_recurrence
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (r₀ : ZMod p) (hr₀ : r₀ ∈ R) (hcount : R.count r₀ < orderOf χ) :
    PolynomialPowerSumRecurrence
      (primeRootMultisetNewtonPolynomial p χ R)
      (primeRootMultisetSpectralRank R)
      (primeRootMultisetNewtonPowerSum p χ R) := by
  intro d
  simp_rw [primeRootMultisetNewtonPowerSum_eq_canonical p χ R r₀ hr₀ hcount]
  exact canonicalEigenvalues_powerSum_recurrence p χ R d

theorem primeRootMultisetNewtonLiteralConditions_of_extensionWeilBounds
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (r₀ : ZMod p) (hr₀ : r₀ ∈ R) (hcount : R.count r₀ < orderOf χ)
    (hweil : PrimeRootMultisetExtensionWeilBounds p χ R) :
    PrimeRootMultisetNewtonLiteralConditions p χ R :=
  ⟨primeRootMultisetNewtonCoefficientIntegrality p χ R, hweil,
    primeRootMultisetNewtonPowerSum_characteristic_recurrence p χ R r₀ hr₀ hcount⟩

end
end Tao2026

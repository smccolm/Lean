import Dubon2026.SourceHassePolynomialTransport
import Dubon2026.SourcePrimeJOrbitFactorization
import Dubon2026.SourceDiscriminantPrimeNorm

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime j nonmembership -> Hasse composition divisibility.
The actual prime orbit factorization and discriminant norm supply the two
identities needed to descend a Laurent identity to a polynomial divisibility.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_closure. Existing j transcendence and coefficient
formulas replace repeated principal-part proofs. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem hasse_polynomial_closure {K : Type*} [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) {M : ℕ} {G R : Polynomial K}
    (hstar : Polynomial.aeval (jqModC K) G *
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1)
    (hR : Polynomial.aeval (jqModC K) R = jqNModC K p)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    ∃ c : K, c ≠ 0 ∧ G.comp R ∣ Polynomial.C c * G ^ (p + 1) := by
  have hpress := (prime_j_orbit_factorization p ζ hζ hR).2.2
  have hnorm := deltaNorm p ζ hζ

  have hjp : jqNModC K p = qExpand K p (jqModC K) := rfl

  have F2 : ∀ α : K, algebraMap K (LaurentSeries K) (R.eval α) - jqNModC K p =
      ∏ b ∈ Finset.range p, (algebraMap K (LaurentSeries K) α - qTwist (ζ ^ b) (jqModC K)) := by
    intro α
    have h := congrArg (Polynomial.eval (algebraMap K (LaurentSeries K) α)) hpress
    rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Polynomial.eval_prod] at h
    simpa only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using h

  have F3 : Polynomial.aeval (jqNModC K p)
      ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) =
      ∏ b ∈ Finset.range p, (G.roots.map fun α =>
        algebraMap K (LaurentSeries K) α - qTwist (ζ ^ b) (jqModC K)).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    have h1 : (G.roots.map ((Polynomial.aeval (jqNModC K p)) ∘ fun α =>
        Polynomial.C (R.eval α) - Polynomial.X)) =
        G.roots.map fun α => ∏ b ∈ Finset.range p,
          (algebraMap K (LaurentSeries K) α - qTwist (ζ ^ b) (jqModC K)) := by
      refine Multiset.map_congr rfl fun α _ => ?_
      rw [Function.comp_apply, map_sub, Polynomial.aeval_C, Polynomial.aeval_X]
      exact F2 α
    rw [h1]
    simp only [Finset.prod_eq_multiset_prod]
    exact Multiset.prod_map_prod_map _ _

  have F4 : ∏ b ∈ Finset.range p, Polynomial.aeval (qTwist (ζ ^ b) (jqModC K)) G =
      (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
        Polynomial.aeval (jqNModC K p)
          ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) := by
    rw [F3, Finset.prod_congr rfl fun b _ => aeval_eq_prod_roots K G (qTwist (ζ ^ b) (jqModC K)),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

  have F5 : (∏ b ∈ Finset.range p, Polynomial.aeval (qTwist (ζ ^ b) (jqModC K)) G) *
      (∏ b ∈ Finset.range p, qTwist (ζ ^ b) (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) ^ M = 1 := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun b _ => ?_
    have h := congrArg (qTwist (ζ ^ b)) hstar
    rwa [map_mul, map_pow, (qTwist (ζ ^ b)).map_one, qTwist_aeval] at h

  have F6 : Polynomial.aeval (jqNModC K p) G * qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1 := by
    have h := congrArg (qExpand K p) hstar
    rwa [map_mul, map_pow, (qExpand K p).map_one, qExpand_aeval] at h
  have F7 : Polynomial.aeval (qExpand K (p * p) (jqModC K)) G * qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1 := by
    have h := congrArg (qExpand K (p * p)) hstar
    rwa [map_mul, map_pow, (qExpand K (p * p)).map_one, qExpand_aeval] at h

  have F54 : (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
      Polynomial.aeval (jqNModC K p)
        ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
      (∏ b ∈ Finset.range p, qTwist (ζ ^ b) (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) ^ M = 1 := by
    rw [← F4]; exact F5

  have key : Polynomial.aeval (jqNModC K p) G ^ (p + 1) =
      (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
        HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M *
        Polynomial.aeval (jqNModC K p)
          ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
        Polynomial.aeval (qExpand K (p * p) (jqModC K)) G := by
    calc Polynomial.aeval (jqNModC K p) G ^ (p + 1)
        = Polynomial.aeval (jqNModC K p) G ^ (p + 1) *
            (Polynomial.aeval (qExpand K (p * p) (jqModC K)) G * qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M) *
            ((algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
              Polynomial.aeval (jqNModC K p)
                ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
              (∏ b ∈ Finset.range p, qTwist (ζ ^ b) (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) ^ M) := by
          rw [F7, F54, mul_one, mul_one]
      _ = (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
            Polynomial.aeval (jqNModC K p)
              ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
            Polynomial.aeval (qExpand K (p * p) (jqModC K)) G *
            Polynomial.aeval (jqNModC K p) G ^ (p + 1) *
            ((∏ b ∈ Finset.range p, qTwist (ζ ^ b) (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) * qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) ^ M := by
          ring
      _ = (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
            Polynomial.aeval (jqNModC K p)
              ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
            Polynomial.aeval (qExpand K (p * p) (jqModC K)) G *
            Polynomial.aeval (jqNModC K p) G ^ (p + 1) *
            (HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
              qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ (p + 1)) ^ M := by
          rw [hnorm]
      _ = (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
            HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M *
            Polynomial.aeval (jqNModC K p)
              ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
            Polynomial.aeval (qExpand K (p * p) (jqModC K)) G *
            (Polynomial.aeval (jqNModC K p) G * qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M) ^ (p + 1) := by
          ring
      _ = (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
            HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M *
            Polynomial.aeval (jqNModC K p)
              ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
            Polynomial.aeval (qExpand K (p * p) (jqModC K)) G := by
          rw [F6, one_pow, mul_one]

  have hκL : algebraMap K (LaurentSeries K)
      ((G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
        (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M) =
      (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
        HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M := by
    rw [map_mul, map_pow, map_pow, map_mul, map_pow, map_neg, map_one,
      algebraMap_eq_C K (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K))]
  have hP1 : qExpand K p (Polynomial.aeval (jqModC K) (G ^ (p + 1))) =
      Polynomial.aeval (jqNModC K p) G ^ (p + 1) := by
    rw [map_pow, map_pow, qExpand_aeval, ← hjp]
  have hP2 : qExpand K p (Polynomial.aeval (jqModC K)
      (Polynomial.C ((G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
          (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M) *
        (G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod * G.comp R)) =
      (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
        HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M *
        Polynomial.aeval (jqNModC K p)
          ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
        Polynomial.aeval (qExpand K (p * p) (jqModC K)) G := by
    rw [map_mul, map_mul, map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_comp, hR, hjp, ← qExpand_aeval, qExpand_qExpand,
      algebraMap_eq_C, qExpand_C, ← algebraMap_eq_C, hκL, qExpand_aeval, qExpand_aeval]
  have hpoly : G ^ (p + 1) =
      Polynomial.C ((G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
          (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M) *
        (G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod * G.comp R :=
    aeval_jqModC_injective K (qExpand_injective (R := K) (N := p) (hP1.trans (key.trans hP2.symm)))
  exact ⟨1, one_ne_zero, Polynomial.C ((G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
      (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M) *
    (G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod,
    by rw [map_one, one_mul, hpoly]; ring⟩


end
end Dubon2026.SourceFunctionField

import Dubon2026.PadicIntegralSL2Density
import Dubon2026.PrincipalCongruenceQuotient
import Mathlib.Data.ZMod.QuotientRing

/-! # Simultaneous actual integral SL2 approximation at finitely many p-adic places -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups BigOperators

/-- The original integral SL2 group lifts every actual finite family of pairwise coprime congruence matrices simultaneously. -/
theorem integralSL2_simultaneous_congruence {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (hm0 : ∀ i, m i ≠ 0)
    (hm : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (g : ∀ i, SL(2, ZMod (m i))) :
    ∃ γ : SL(2, ℤ), ∀ t : ι, ∀ i j : Fin 2,
      (γ i j : ZMod (m t)) = g t i j := by
  letI : NeZero (∏ i, m i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => hm0 i)⟩
  let e := ZMod.prodEquivPi m hm
  let G : SL(2, (∀ i, ZMod (m i))) := ⟨fun i j t => g t i j, by
    funext t
    simpa only [Matrix.det_fin_two, Pi.sub_apply, Pi.mul_apply, Pi.one_apply] using (g t).property⟩
  obtain ⟨γ, hγ⟩ := SL2Reduction.SL2_reduction_surjective (∏ i, m i)
    ((sl2RingEquiv e).symm G)
  have hG : sl2RingEquiv e (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (∏ i, m i))) γ) = G := by
    rw [hγ]
    exact (sl2RingEquiv e).apply_symm_apply G
  refine ⟨γ, fun t i j => ?_⟩
  have he := congrArg (fun A : SL(2, (∀ t, ZMod (m t))) => A i j t) hG
  change e (γ i j : ZMod (∏ t, m t)) t = g t i j at he
  simpa using he

/-- A single genuine integral determinant-one matrix realizes arbitrary finite p-adic prime-power precisions. -/
theorem integralSL2_finite_padic_congruence {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hp : Function.Injective p)
    (g : ∀ i, SL(2, ℤ_[p i])) (n : ι → ℕ) :
    ∃ γ : SL(2, ℤ), ∀ t : ι, ∀ i j : Fin 2,
      PadicInt.toZModPow (n t) ((γ i j : ℤ) : ℤ_[p t]) =
        PadicInt.toZModPow (n t) (g t i j) := by
  have hc : Pairwise (fun i j => Nat.Coprime (p i ^ n i) (p j ^ n j)) := by
    intro i j hij
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Fact.out : (p i).Prime)
      (Fact.out : (p j).Prime)).mpr (hp.ne hij))
  obtain ⟨γ, hγ⟩ := integralSL2_simultaneous_congruence (fun i => p i ^ n i)
    (fun i => pow_ne_zero _ (Fact.out : (p i).Prime).ne_zero) hc
    (fun i => Matrix.SpecialLinearGroup.map (PadicInt.toZModPow (n i)) (g i))
  refine ⟨γ, fun t i j => ?_⟩
  simpa only [map_intCast] using hγ t i j

/-- The actual simultaneous integral matrix approximates every original p-adic entry by the requested local precision. -/
theorem integralSL2_finite_padic_approximation {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hp : Function.Injective p)
    (g : ∀ i, SL(2, ℤ_[p i])) (n : ι → ℕ) :
    ∃ γ : SL(2, ℤ), ∀ t : ι, ∀ i j : Fin 2,
      ‖g t i j - ((γ i j : ℤ) : ℤ_[p t])‖ ≤ (p t : ℝ) ^ (-(n t : ℤ)) := by
  obtain ⟨γ, hγ⟩ := integralSL2_finite_padic_congruence p hp g n
  refine ⟨γ, fun t i j => ?_⟩
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
    RingHom.mem_ker, map_sub, ← hγ t i j, sub_self]

end
end Dubon2026

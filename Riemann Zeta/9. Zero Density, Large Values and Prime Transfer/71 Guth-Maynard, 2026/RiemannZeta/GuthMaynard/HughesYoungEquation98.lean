import RiemannZeta.GuthMaynard.HughesYoungCFunctionalEquation

open Complex Finset
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

theorem hughesYoungEquation98_leftFactor
    (h : ℕ) (p : Nat.Primes) (alpha beta gamma delta s : ℂ) :
    hughesYoungLemma61LeftFactor h
        (1 - alpha + beta) (1 - gamma + delta)
        (alpha + gamma + 2 * s - 1) p =
      hughesYoungCPrimeFactor (h.factorization p) p
        alpha beta gamma delta s := by
  let P : ℂ := (p : ℂ)
  let A : ℂ := P ^ alpha
  let B : ℂ := P ^ (-beta)
  let G : ℂ := P ^ gamma
  let D : ℂ := P ^ (-delta)
  let S : ℂ := P ^ (-2 * s)
  have hP : P ≠ 0 := by
    dsimp only [P]
    exact_mod_cast p.2.ne_zero
  have hA : A ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hP)
  have hB : B ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hP)
  have hG : G ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hP)
  have hD : D ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hP)
  have hS : S ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hP)
  have hnegOne : P ^ (-1 : ℂ) = P⁻¹ := by
    simpa using Complex.cpow_neg P 1
  have hnegTwo : P ^ (-2 : ℂ) = P⁻¹ * P⁻¹ := by
    rw [show (-2 : ℂ) = (-1 : ℂ) + (-1) by ring]
    rw [Complex.cpow_add _ _ hP, hnegOne]
  have hAlphaNeg : P ^ (-alpha) = A⁻¹ := Complex.cpow_neg P alpha
  have hGammaNeg : P ^ (-gamma) = G⁻¹ := Complex.cpow_neg P gamma
  have hpb : P ^ (-(1 - gamma + delta)) = P⁻¹ * G * D := by
    rw [show -(1 - gamma + delta) = (-1 : ℂ) + gamma + (-delta) by ring]
    rw [Complex.cpow_add _ _ hP, Complex.cpow_add _ _ hP,
      hnegOne]
  have hpa : P ^ (-(1 - alpha + beta)) = P⁻¹ * A * B := by
    rw [show -(1 - alpha + beta) = (-1 : ℂ) + alpha + (-beta) by ring]
    rw [Complex.cpow_add _ _ hP, Complex.cpow_add _ _ hP,
      hnegOne]
  have hpabc :
      P ^ (-(1 - alpha + beta + (1 - gamma + delta) +
          (alpha + gamma + 2 * s - 1))) =
        P⁻¹ * B * D * S := by
    rw [show -(1 - alpha + beta + (1 - gamma + delta) +
          (alpha + gamma + 2 * s - 1)) =
        (-1 : ℂ) + (-beta) + (-delta) + (-2 * s) by ring]
    rw [Complex.cpow_add _ _ hP, Complex.cpow_add _ _ hP,
      Complex.cpow_add _ _ hP, hnegOne]
  have hpc : P ^ (-(alpha + gamma + 2 * s - 1)) =
      P * A⁻¹ * G⁻¹ * S := by
    rw [show -(alpha + gamma + 2 * s - 1) =
        (1 : ℂ) + (-alpha) + (-gamma) + (-2 * s) by ring]
    rw [Complex.cpow_add _ _ hP, Complex.cpow_add _ _ hP,
      Complex.cpow_add _ _ hP, Complex.cpow_one, hAlphaNeg, hGammaNeg]
  have hpbc : P ^ (-(1 - gamma + delta +
          (alpha + gamma + 2 * s - 1))) = A⁻¹ * D * S := by
    rw [show -(1 - gamma + delta +
          (alpha + gamma + 2 * s - 1)) =
        (-alpha) + (-delta) + (-2 * s) by ring]
    rw [Complex.cpow_add _ _ hP, Complex.cpow_add _ _ hP, hAlphaNeg]
  have hpab : P ^ (-(1 - alpha + beta + (1 - gamma + delta))) =
      P⁻¹ * P⁻¹ * A * B * G * D := by
    rw [show -(1 - alpha + beta + (1 - gamma + delta)) =
        (-1 : ℂ) + (-1) + alpha + (-beta) + gamma + (-delta) by ring]
    rw [Complex.cpow_add _ _ hP, Complex.cpow_add _ _ hP,
      Complex.cpow_add _ _ hP, Complex.cpow_add _ _ hP,
      Complex.cpow_add _ _ hP, hnegOne]
  have hgd : P ^ (gamma - delta) = G * D := by
    rw [show gamma - delta = gamma + (-delta) by ring]
    exact Complex.cpow_add _ _ hP
  have hab : P ^ (alpha - beta) = A * B := by
    rw [show alpha - beta = alpha + (-beta) by ring]
    exact Complex.cpow_add _ _ hP
  have hx : P ^ (-alpha - delta - 2 * s) = A⁻¹ * D * S := by
    rw [show -alpha - delta - 2 * s = (-alpha) + (-delta) + (-2 * s) by ring]
    rw [Complex.cpow_add _ _ hP, Complex.cpow_add _ _ hP, hAlphaNeg]
  have hreg : P ^ (-2 + alpha - beta + gamma - delta) =
      P⁻¹ * P⁻¹ * A * B * G * D := by
    rw [show -2 + alpha - beta + gamma - delta =
        (-1 : ℂ) + (-1) + alpha + (-beta) + gamma + (-delta) by ring]
    rw [Complex.cpow_add _ _ hP, Complex.cpow_add _ _ hP,
      Complex.cpow_add _ _ hP, Complex.cpow_add _ _ hP,
      Complex.cpow_add _ _ hP, hnegOne]
  have huv : P ^ (alpha - beta + gamma - delta) = A * B * G * D := by
    rw [show alpha - beta + gamma - delta =
        alpha + (-beta) + gamma + (-delta) by ring]
    rw [Complex.cpow_add _ _ hP, Complex.cpow_add _ _ hP,
      Complex.cpow_add _ _ hP]
  unfold hughesYoungLemma61LeftFactor hughesYoungCPrimeFactor
    hughesYoungCPrimeNumerator hughesYoungC0 hughesYoungC1 hughesYoungC2
  dsimp only
  change
    ((1 - P ^ (-(1 - gamma + delta))) *
          (1 - P ^ (-(1 - alpha + beta + (1 - gamma + delta) +
            (alpha + gamma + 2 * s - 1)))) +
        P ^ (-(1 - gamma + delta)) *
          (1 - P ^ (-(1 - alpha + beta))) *
          (1 - P ^ (-(alpha + gamma + 2 * s - 1))) *
          (P ^ (-(1 - gamma + delta +
            (alpha + gamma + 2 * s - 1)))) ^ h.factorization p) /
        ((1 - P ^ (-(1 - gamma + delta +
            (alpha + gamma + 2 * s - 1)))) *
          (1 - P ^ (-(1 - alpha + beta + (1 - gamma + delta))))) = _
  rw [hpb, hpabc, hpa, hpc, hpbc, hpab, hnegOne, hnegTwo,
    hgd, hab, huv, hx, hreg]
  congr 1
  · simp only [mul_pow, inv_pow]
    field_simp [hP, hA, hG]
    ring
  · ring

theorem hughesYoungLemma61RightFactor_eq_leftFactor
    (k : ℕ) (p : Nat.Primes) (a b c : ℂ) :
    hughesYoungLemma61RightFactor k a b c p =
      hughesYoungLemma61LeftFactor k b a c p := by
  unfold hughesYoungLemma61RightFactor hughesYoungLemma61LeftFactor
  rw [show b + a + c = a + b + c by ring,
    show b + a = a + b by ring]

theorem hughesYoungEquation98_rightFactor
    (k : ℕ) (p : Nat.Primes) (alpha beta gamma delta s : ℂ) :
    hughesYoungLemma61RightFactor k
        (1 - alpha + beta) (1 - gamma + delta)
        (alpha + gamma + 2 * s - 1) p =
      hughesYoungCPrimeFactor (k.factorization p) p
        gamma delta alpha beta s := by
  rw [hughesYoungLemma61RightFactor_eq_leftFactor]
  simpa only [add_comm, add_left_comm, add_assoc] using
    hughesYoungEquation98_leftFactor k p gamma delta alpha beta s

theorem hughesYoungEquation98
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : Nat.Coprime h k)
    {alpha beta gamma delta s : ℂ}
    (hAbsolute : 1 <
      ((1 - alpha + beta) + (1 - gamma + delta)).re)
    (hShift : 0 < (alpha + gamma + 2 * s - 1).re)
    (hhx : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-alpha - delta - 2 * s) ≠ 0)
    (hkx : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-gamma - beta - 2 * s) ≠ 0) :
    hughesYoungEquation96 h k
        (1 - alpha + beta) (1 - gamma + delta)
        (alpha + gamma + 2 * s) =
      (riemannZeta (alpha + gamma + 2 * s) *
          riemannZeta (1 + beta + delta + 2 * s) /
          riemannZeta (2 - alpha + beta - gamma + delta)) *
        (hughesYoungC h alpha beta gamma delta s *
          hughesYoungC k gamma delta alpha beta s) := by
  have hleft : ∀ p ∈ hughesYoungPrimeFactors h,
      1 - (p : ℂ) ^ (-((1 - gamma + delta) +
        (alpha + gamma + 2 * s - 1))) ≠ 0 := by
    intro p hp
    simpa only [show -((1 - gamma + delta) +
        (alpha + gamma + 2 * s - 1)) =
        -alpha - delta - 2 * s by ring] using hhx p hp
  have hright : ∀ p ∈ hughesYoungPrimeFactors k,
      1 - (p : ℂ) ^ (-((1 - alpha + beta) +
        (alpha + gamma + 2 * s - 1))) ≠ 0 := by
    intro p hp
    simpa only [show -((1 - alpha + beta) +
        (alpha + gamma + 2 * s - 1)) =
        -gamma - beta - 2 * s by ring] using hkx p hp
  have hsource := hughesYoungLemma61_source hh hk hhk hAbsolute hShift
    hleft hright
  rw [show (1 : ℂ) + (alpha + gamma + 2 * s - 1) =
      alpha + gamma + 2 * s by ring] at hsource
  rw [show (1 - alpha + beta) + (1 - gamma + delta) +
        (alpha + gamma + 2 * s - 1) =
      1 + beta + delta + 2 * s by ring] at hsource
  rw [show (1 - alpha + beta) + (1 - gamma + delta) =
      2 - alpha + beta - gamma + delta by ring] at hsource
  calc
    _ = riemannZeta (alpha + gamma + 2 * s) *
          (riemannZeta (1 + beta + delta + 2 * s) /
            riemannZeta (2 - alpha + beta - gamma + delta)) *
          ((∏ p ∈ hughesYoungPrimeFactors h,
              hughesYoungLemma61LeftFactor h
                (1 - alpha + beta) (1 - gamma + delta)
                (alpha + gamma + 2 * s - 1) p) *
            ∏ p ∈ hughesYoungPrimeFactors k,
              hughesYoungLemma61RightFactor k
                (1 - alpha + beta) (1 - gamma + delta)
                (alpha + gamma + 2 * s - 1) p) := hsource
    _ = _ := by
      rw [hughesYoungC, hughesYoungC]
      congr 1
      · ring
      · congr 1
        · apply Finset.prod_congr rfl
          intro p hp
          exact hughesYoungEquation98_leftFactor h p alpha beta gamma delta s
        · apply Finset.prod_congr rfl
          intro p hp
          exact hughesYoungEquation98_rightFactor k p alpha beta gamma delta s

end RiemannZeta.GuthMaynard

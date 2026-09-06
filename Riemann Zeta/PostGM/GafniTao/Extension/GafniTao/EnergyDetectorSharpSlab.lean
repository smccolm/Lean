import GafniTao.EnergyDetectorGMConsumer
import RiemannZeta.GuthMaynard.FiniteDensityEndpoint

/-!
# The sharp mollifier as a zero-energy detector on one positive slab

This file keeps the exact positive-slab scope of the frozen beta-removal
theorem.  It does not silently identify that slab with the symmetric zero
set used by `GafniTao.zeroAdditiveEnergyCount`.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Complex conjugation preserves the unit coefficient bound on the actual
dyadic interval. -/
theorem norm_conjugate_normalizedSharpMollifiedLineCoeff_le_one
    (A X N n : Nat) (sigma eta C : Real) (hN : 0 < N)
    (hsigma : 0 <= sigma) (heta : 0 <= eta) (hC : 0 < C)
    (hCoeff : forall m : Nat, 0 < m ->
      ‖sharpMollifiedCoeff A X m‖ <= C * (m : Real) ^ eta)
    (hn : n ∈ dyadicInterval N) :
    ‖conjugateCoeffs
        (normalizedSharpMollifiedLineCoeff A X N sigma eta C) n‖ <= 1 := by
  rw [norm_conjugateCoeffs]
  exact norm_normalizedSharpMollifiedLineCoeff_le_one
    A X N n sigma eta C hN hsigma heta hC hCoeff hn

/-- Every zero on one positive dyadic height slab yields an actual shifted
sharp-mollifier block, normalized to unit coefficients and written in the
positive-sign source convention required by the Guth--Maynard energy
theorems.  The literal `Nat.clog`, coefficient, and displacement losses are
retained. -/
theorem positiveSlab_sharpMollified_energy_witness
    (sigma delta eta : Real) (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 1) (hdelta : 0 < delta) (heta : 0 < eta) :
    exists C T0 : Real, 0 < C /\
      (forall (A X n : Nat), 0 < n ->
        ‖sharpMollifiedCoeff A X n‖ <= C * (n : Real) ^ eta) /\
      8 <= T0 /\
      forall (T : Real) (X : Nat), T0 <= T ->
        1 <= X -> X <= ⌊sharpZetaCutoff T⌋₊ -> (X : Real) <= T ->
        let A := ⌊sharpZetaCutoff T⌋₊
        let k := Nat.clog 2 A
        0 < k /\
        forall rho, rho ∈ zerosInRect sigma 1 T (2 * T) ->
          exists t : Real, |rho.im - t| <= T ^ delta /\
            (T - T ^ delta <= t /\ t <= 2 * T + T ^ delta) /\
            exists r : Fin k,
              let N := 2 ^ (r : Nat) * X
              (forall n, n ∈ dyadicInterval N ->
                ‖conjugateCoeffs
                  (normalizedSharpMollifiedLineCoeff A X N sigma eta C) n‖ <= 1) /\
              ((3 / 8) / (k : Real)) /
                    (C * (2 * N : Real) ^ eta * (N : Real) ^ (-sigma)) <=
                ‖sourceDirichletPoly N
                  (conjugateCoeffs
                    (normalizedSharpMollifiedLineCoeff A X N sigma eta C)) t‖ := by
  obtain ⟨Craw, hCraw, hCoeffRaw⟩ := sharpMollifiedCoeff_bound eta heta
  let C : Real := max 1 Craw
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hCoeff : forall (A X n : Nat), 0 < n ->
      ‖sharpMollifiedCoeff A X n‖ <= C * (n : Real) ^ eta := by
    intro A X n hn
    exact (hCoeffRaw A X n hn).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 Craw)
        (Real.rpow_nonneg (by positivity) _))
  obtain ⟨T0, hT0, hBeta⟩ :=
    sharpMollifiedTail_beta_removal_native sigma delta hsigma hsigmaUpper hdelta
  refine ⟨C, T0, hC, hCoeff, hT0, ?_⟩
  intro T X hT hX hXA hXT
  let A := ⌊sharpZetaCutoff T⌋₊
  let k := Nat.clog 2 A
  have hA : 1 < A := by
    have hTpos : 0 < T := by linarith [hT0.trans hT]
    have hCutNonneg : 0 <= sharpZetaCutoff T :=
      (mul_nonneg (by norm_num) hTpos.le).trans
        (four_mul_lt_sharpZetaCutoff T).le
    have hTwo : (2 : Real) <= sharpZetaCutoff T := by
      linarith [four_mul_lt_sharpZetaCutoff T, hT0.trans hT]
    have hTwoNat : 2 <= A := (Nat.le_floor_iff hCutNonneg).mpr hTwo
    omega
  have hk : 0 < k := Nat.clog_pos Nat.one_lt_two hA
  refine ⟨hk, ?_⟩
  intro rho hrho
  obtain ⟨t, htShift, htLarge⟩ := hBeta T rho X hT hrho hX hXA hXT
  have hRect := hrho
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    mem_ZeroRectangle] at hRect
  have htInterval : T - T ^ delta <= t /\ t <= 2 * T + T ^ delta := by
    rw [abs_le] at htShift
    constructor <;> linarith [hRect.1.2.1, hRect.1.2.2]
  obtain ⟨r, hr, hrLarge⟩ := exists_sharpMollified_large_dyadic_block
    A X sigma t (3 / 8) hA htLarge
  let rf : Fin k := ⟨r, by simpa [k] using hr⟩
  let N := 2 ^ (rf : Nat) * X
  have hN : 0 < N := Nat.mul_pos (pow_pos (by omega) _) (by omega)
  have hD : 0 < C * (2 * N : Real) ^ eta * (N : Real) ^ (-sigma) := by
    positivity
  refine ⟨t, ?_, htInterval, rf, ?_, ?_⟩
  · simpa [abs_sub_comm] using htShift
  · intro n hn
    exact norm_conjugate_normalizedSharpMollifiedLineCoeff_le_one
      A X N n sigma eta C hN (by linarith) heta.le hC
        (fun m hm => hCoeff A X m hm) hn
  · rw [norm_sourceDirichletPoly_conjugateCoeffs,
      dirichletPoly_normalizedSharpMollifiedLineCoeff, norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
    apply (div_le_div_iff_of_pos_right hD).2
    simpa only [N, rf, k, A] using hrLarge

/-- Zeros on the two signed dyadic slabs with absolute ordinate in
`[U,2U]`.  The overlap at endpoints is harmless because this is a finset
union. -/
noncomputable def absoluteDyadicZeroSlab (sigma U : Real) : Finset Complex :=
  zerosInRect sigma 1 (-2 * U) (-U) ∪ zerosInRect sigma 1 U (2 * U)

/-- Conjugation moves the negative dyadic slab to the positive slab while
preserving the real-part and zeta-zero conditions. -/
theorem conj_mem_positiveSlab_of_mem_negativeSlab
    {sigma U : Real} {rho : Complex}
    (hrho : rho ∈ zerosInRect sigma 1 (-2 * U) (-U)) :
    star rho ∈ zerosInRect sigma 1 U (2 * U) := by
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrho ⊢
  rcases hrho with ⟨hrect, hzero⟩
  rw [mem_ZeroRectangle] at hrect ⊢
  change riemannZeta rho = 0 at hzero
  have hrhoNe : rho ≠ 1 := by
    intro h
    subst rho
    exact riemannZeta_one_ne_zero hzero
  refine ⟨⟨by simpa using hrect.1, by simpa using hrect.2.1,
    by simp; linarith [hrect.2.2.1], by simp; linarith [hrect.2.2.2]⟩, ?_⟩
  change riemannZeta (star rho) = 0
  rw [riemannZeta_conj rho hrhoNe, hzero]
  simp

/-- The sign-labelled coefficient family used on the two signed slabs.
Label zero converts the negative-sign detector into the source convention by
coefficient conjugation; label one reverses the ordinate instead. -/
noncomputable def signedNormalizedSharpCoeff
    (A X : Nat) (N : Fin 2 -> Nat) (sigma eta C : Real)
    (sign : Fin 2) (n : Nat) : Complex :=
  if sign = 0 then
    conjugateCoeffs
      (normalizedSharpMollifiedLineCoeff A X (N sign) sigma eta C) n
  else
    normalizedSharpMollifiedLineCoeff A X (N sign) sigma eta C n

theorem signedNormalizedSharpCoeff_zero
    (A X : Nat) (N : Fin 2 -> Nat) (sigma eta C : Real) (n : Nat) :
    signedNormalizedSharpCoeff A X N sigma eta C 0 n =
      conjugateCoeffs
        (normalizedSharpMollifiedLineCoeff A X (N 0) sigma eta C) n := by
  simp [signedNormalizedSharpCoeff]

theorem signedNormalizedSharpCoeff_one
    (A X : Nat) (N : Fin 2 -> Nat) (sigma eta C : Real) (n : Nat) :
    signedNormalizedSharpCoeff A X N sigma eta C 1 n =
      normalizedSharpMollifiedLineCoeff A X (N 1) sigma eta C n := by
  simp [signedNormalizedSharpCoeff]

/-- Exact signed version of the sharp detector on one absolute dyadic height
shell.  No global symmetric-height inference is made here: the shell and its
two signs remain explicit in the theorem. -/
theorem absoluteSlab_sharpMollified_energy_witness
    (sigma delta eta : Real) (hsigma : 1 / 2 < sigma)
    (hsigmaUpper : sigma <= 1) (hdelta : 0 < delta) (heta : 0 < eta) :
    exists C T0 : Real, 0 < C /\
      (forall (A X n : Nat), 0 < n ->
        ‖sharpMollifiedCoeff A X n‖ <= C * (n : Real) ^ eta) /\
      8 <= T0 /\
      forall (U : Real) (X : Nat), T0 <= U ->
        1 <= X -> X <= ⌊sharpZetaCutoff U⌋₊ -> (X : Real) <= U ->
        let A := ⌊sharpZetaCutoff U⌋₊
        let k := Nat.clog 2 A
        0 < k /\
        forall rho, rho ∈ absoluteDyadicZeroSlab sigma U ->
          exists t : Real, |rho.im - t| <= U ^ delta /\
            (-(2 * U + U ^ delta) <= t /\ t <= 2 * U + U ^ delta) /\
            exists r : Fin k × Fin 2,
              let N := fun _sign : Fin 2 => 2 ^ (r.1 : Nat) * X
              (forall n, n ∈ dyadicInterval (N r.2) ->
                ‖signedNormalizedSharpCoeff A X N sigma eta C r.2 n‖ <= 1) /\
              ((3 / 8) / (k : Real)) /
                    (C * (2 * N r.2 : Real) ^ eta *
                      (N r.2 : Real) ^ (-sigma)) <=
                ‖sourceDirichletPoly (N r.2)
                  (signedNormalizedSharpCoeff A X N sigma eta C r.2) t‖ := by
  obtain ⟨C, T0, hC, hCoeff, hT0, hPositive⟩ :=
    positiveSlab_sharpMollified_energy_witness sigma delta eta
      hsigma hsigmaUpper hdelta heta
  refine ⟨C, T0, hC, hCoeff, hT0, ?_⟩
  intro U X hU hX hXA hXU
  let A := ⌊sharpZetaCutoff U⌋₊
  let k := Nat.clog 2 A
  obtain ⟨hk, hPos⟩ := hPositive U X hU hX hXA hXU
  refine ⟨hk, ?_⟩
  intro rho hrho
  rw [absoluteDyadicZeroSlab, Finset.mem_union] at hrho
  rcases hrho with hneg | hpos
  · have hconj := conj_mem_positiveSlab_of_mem_negativeSlab hneg
    obtain ⟨s, hsShift, hsInterval, r, hrUnit, hrLarge⟩ := hPos (star rho) hconj
    let pair : Fin k × Fin 2 := (r, 1)
    let N := fun _sign : Fin 2 => 2 ^ (r : Nat) * X
    refine ⟨-s, ?_, ?_, pair, ?_, ?_⟩
    · calc
        |rho.im - -s| = |-rho.im - s| := by
          rw [← abs_neg]
          congr 1
          ring
        _ = |(star rho).im - s| := by simp
        _ ≤ U ^ delta := hsShift
    · constructor <;> linarith [hsInterval.1, hsInterval.2]
    · intro n hn
      have hu := hrUnit n (by simpa only [N, pair] using hn)
      rw [norm_conjugateCoeffs] at hu
      change ‖normalizedSharpMollifiedLineCoeff A X
        (2 ^ (r : Nat) * X) sigma eta C n‖ <= 1
      simpa only [A, k] using hu
    · change ((3 / 8) / (k : Real)) /
          (C * (2 * N 1 : Real) ^ eta * (N 1 : Real) ^ (-sigma)) <=
        ‖sourceDirichletPoly (N 1)
          (signedNormalizedSharpCoeff A X N sigma eta C 1) (-s)‖
      rw [show signedNormalizedSharpCoeff A X N sigma eta C 1 =
          normalizedSharpMollifiedLineCoeff A X (N 1) sigma eta C from by
        funext n
        exact signedNormalizedSharpCoeff_one A X N sigma eta C n]
      dsimp only [N]
      calc
        _ <= ‖sourceDirichletPoly (2 ^ (r : Nat) * X)
            (conjugateCoeffs
              (normalizedSharpMollifiedLineCoeff A X
                (2 ^ (r : Nat) * X) sigma eta C)) s‖ := by
          simpa only [A, k] using hrLarge
        _ = ‖dirichletPoly (2 ^ (r : Nat) * X)
            (normalizedSharpMollifiedLineCoeff A X
              (2 ^ (r : Nat) * X) sigma eta C) s‖ :=
          norm_sourceDirichletPoly_conjugateCoeffs _ _ _
        _ = ‖sourceDirichletPoly (2 ^ (r : Nat) * X)
            (normalizedSharpMollifiedLineCoeff A X
              (2 ^ (r : Nat) * X) sigma eta C) (-s)‖ := by
          rw [← dirichletPoly_neg_eq_sourceDirichletPoly]
          simp
  · obtain ⟨t, htShift, htInterval, r, hrUnit, hrLarge⟩ := hPos rho hpos
    let pair : Fin k × Fin 2 := (r, 0)
    let N := fun _sign : Fin 2 => 2 ^ (r : Nat) * X
    refine ⟨t, htShift, ?_, pair, ?_, ?_⟩
    · constructor <;> linarith [htInterval.1, htInterval.2]
    · intro n hn
      change ‖conjugateCoeffs
        (normalizedSharpMollifiedLineCoeff A X
          (2 ^ (r : Nat) * X) sigma eta C) n‖ <= 1
      simpa only [N, A, k] using hrUnit n hn
    · change ((3 / 8) / (k : Real)) /
          (C * (2 * N 0 : Real) ^ eta * (N 0 : Real) ^ (-sigma)) <=
        ‖sourceDirichletPoly (N 0)
          (signedNormalizedSharpCoeff A X N sigma eta C 0) t‖
      rw [show signedNormalizedSharpCoeff A X N sigma eta C 0 =
          conjugateCoeffs
            (normalizedSharpMollifiedLineCoeff A X (N 0) sigma eta C) from by
        funext n
        exact signedNormalizedSharpCoeff_zero A X N sigma eta C n]
      dsimp only [N]
      simpa only [N, A, k] using hrLarge

#print axioms norm_conjugate_normalizedSharpMollifiedLineCoeff_le_one
#print axioms positiveSlab_sharpMollified_energy_witness
#print axioms conj_mem_positiveSlab_of_mem_negativeSlab
#print axioms signedNormalizedSharpCoeff_zero
#print axioms signedNormalizedSharpCoeff_one
#print axioms absoluteSlab_sharpMollified_energy_witness

end

end GafniTao

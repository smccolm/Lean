import GafniTao.HeathBrownLowerSourceScale
import GafniTao.SourceSmoothDyadicEnergySplit
import RiemannZeta.GuthMaynard.MediumTypeIEndpoint

/-!
# Threshold transfer for lower Type-I source cells

Both logarithmic denominators are retained literally.  Their product is
absorbed only after the sharp cutoff has been substituted, and the dyadic
comparison `P < 2Q` is used before passing to a powered threshold.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem eventually_lower_source_log_loss
    {sigma zeta : Real} (hzeta : 0 < zeta) :
    ∀ᶠ U : Real in atTop,
      (8 / 3 : Real) * 4 ^ sigma *
          ((Nat.clog 2 (Nat.floor (sharpZetaCutoff U)) + 1 : Nat) : Real) *
          (Nat.clog 2 (Nat.floor (sharpZetaCutoff U) + 1) : Real) <=
        U ^ zeta := by
  obtain ⟨C, hC, Tlog, _hTlog, hLogs⟩ :=
    eventually_source_selection_log_product_le (zeta / 2) (by positivity)
  let D : Real := (8 / 3 : Real) * 4 ^ sigma
  have hAbsorb := eventually_const_mul_rpow_le_rpow
    (D := D * C) (a := zeta / 2) (b := zeta) (by linarith)
  filter_upwards [hAbsorb, eventually_ge_atTop Tlog] with U hAbsorbU hTlogU
  have hLog := hLogs U hTlogU
  calc
    (8 / 3 : Real) * 4 ^ sigma *
          ((Nat.clog 2 (Nat.floor (sharpZetaCutoff U)) + 1 : Nat) : Real) *
          (Nat.clog 2 (Nat.floor (sharpZetaCutoff U) + 1) : Real) =
        D * (((Nat.clog 2 (Nat.floor (sharpZetaCutoff U)) + 1 : Nat) : Real) *
          (Nat.clog 2 (Nat.floor (sharpZetaCutoff U) + 1) : Real)) := by
            dsimp only [D]
            ring
    _ <= D * (C * U ^ (zeta / 2)) := by
      gcongr
    _ = (D * C) * U ^ (zeta / 2) := by ring
    _ <= U ^ zeta := hAbsorbU

theorem lower_source_dyadic_threshold
    {U u zeta sigma eta : Real} {A Q P : Nat}
    (hU : 0 < U) (hsigma : 0 <= sigma) (heta : 0 <= eta)
    (hA : 1 < A) (hP : 0 < P) (hPUpper : P < 2 * Q)
    (hLog :
      (8 / 3 : Real) * 4 ^ sigma *
          ((Nat.clog 2 A + 1 : Nat) : Real) *
          (Nat.clog 2 (A + 1) : Real) <= U ^ zeta) :
    U ^ (-(u + zeta)) * (P : Real) ^ (sigma - eta) <=
      ((((Q : Real) / 2) ^ sigma) *
        (((3 / 4 : Real) * (U ^ (-u) / 2)) /
          ((Nat.clog 2 A + 1 : Nat) : Real))) /
        (Nat.clog 2 (A + 1) : Real) := by
  have hPReal : (0 : Real) < P := by exact_mod_cast hP
  have hQ : 0 < Q := by omega
  have hQReal : (0 : Real) < Q := by exact_mod_cast hQ
  have hFirst : (0 : Real) < ((Nat.clog 2 A + 1 : Nat) : Real) := by positivity
  have hSecond : (0 : Real) < (Nat.clog 2 (A + 1) : Real) := by
    exact_mod_cast Nat.clog_pos Nat.one_lt_two (by omega : 1 < A + 1)
  have hUz : 0 < U ^ zeta := Real.rpow_pos_of_pos hU _
  have hUu : 0 < U ^ (-u) := Real.rpow_pos_of_pos hU _
  have hPQuarter : (P : Real) / 4 <= (Q : Real) / 2 := by
    have hCast : (P : Real) <= 2 * (Q : Real) := by exact_mod_cast hPUpper.le
    linarith
  have hPpow : (P : Real) ^ sigma <=
      4 ^ sigma * ((Q : Real) / 2) ^ sigma := by
    have hRaised := Real.rpow_le_rpow (by positivity) hPQuarter hsigma
    have hIdentity : (P : Real) ^ sigma =
        4 ^ sigma * ((P : Real) / 4) ^ sigma := by
      rw [Real.div_rpow hPReal.le (by norm_num : (0 : Real) <= 4)]
      field_simp [(Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 4)
        sigma).ne']
    rw [hIdentity]
    exact mul_le_mul_of_nonneg_left hRaised (Real.rpow_nonneg (by norm_num) _)
  have hEta : (P : Real) ^ (sigma - eta) <= (P : Real) ^ sigma :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hP) (by linarith)
  have hCore : U ^ (-zeta) * (P : Real) ^ (sigma - eta) <=
      (3 / 8 : Real) * ((Q : Real) / 2) ^ sigma /
        ((Nat.clog 2 A + 1 : Nat) : Real) /
        (Nat.clog 2 (A + 1) : Real) := by
    rw [Real.rpow_neg hU.le]
    field_simp [hUz.ne', hFirst.ne', hSecond.ne']
    have hPcombined : (P : Real) ^ (sigma - eta) <=
        4 ^ sigma * ((Q : Real) / 2) ^ sigma := hEta.trans hPpow
    calc
      (P : Real) ^ (sigma - eta) * 8 *
          ((Nat.clog 2 A + 1 : Nat) : Real) *
          (Nat.clog 2 (A + 1) : Real) <=
        (4 ^ sigma * ((Q : Real) / 2) ^ sigma) * 8 *
          ((Nat.clog 2 A + 1 : Nat) : Real) *
          (Nat.clog 2 (A + 1) : Real) := by gcongr
      _ = ((8 / 3 : Real) * 4 ^ sigma *
          ((Nat.clog 2 A + 1 : Nat) : Real) *
          (Nat.clog 2 (A + 1) : Real)) *
            (3 * ((Q : Real) / 2) ^ sigma) := by ring
      _ <= U ^ zeta * (3 * ((Q : Real) / 2) ^ sigma) := by
        gcongr
      _ = U ^ zeta * 3 * ((Q : Real) / 2) ^ sigma := by ring
  have hSplit : U ^ (-(u + zeta)) = U ^ (-u) * U ^ (-zeta) := by
    rw [← Real.rpow_add hU]
    congr 1
    ring
  rw [hSplit]
  calc
    (U ^ (-u) * U ^ (-zeta)) * (P : Real) ^ (sigma - eta) =
        U ^ (-u) * (U ^ (-zeta) * (P : Real) ^ (sigma - eta)) := by ring
    _ <= U ^ (-u) * ((3 / 8 : Real) * ((Q : Real) / 2) ^ sigma /
        ((Nat.clog 2 A + 1 : Nat) : Real) /
        (Nat.clog 2 (A + 1) : Real)) :=
      mul_le_mul_of_nonneg_left hCore hUu.le
    _ = ((((Q : Real) / 2) ^ sigma) *
        (((3 / 4 : Real) * (U ^ (-u) / 2)) /
          ((Nat.clog 2 A + 1 : Nat) : Real))) /
        (Nat.clog 2 (A + 1) : Real) := by ring

#print axioms eventually_lower_source_log_loss
#print axioms lower_source_dyadic_threshold

end

end GafniTao

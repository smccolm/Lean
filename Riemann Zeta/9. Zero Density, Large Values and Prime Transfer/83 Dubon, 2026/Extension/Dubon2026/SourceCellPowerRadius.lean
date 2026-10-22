import Dubon2026.SourceCellBoundaryGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Separation.Regular

/-! DUB-17/18 -> original Abel-Jacobi -> actual branch and pole cells.
The source power pullback retains the exact radial preimage, multiplicity,
arc laps and separated inverse branches needed for geometric pairing.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing radial periodicity and periodic argument evaluation are reused.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.PowPullback
noncomputable section
open scoped Real

theorem div_lt_div_aux {X Y E : ℝ} (hE : 0 < E) (h : X < Y) : X / E < Y / E := by
  have h1 : 0 < (Y - X) / E := div_pos (by linarith) hE
  rw [sub_div] at h1
  linarith

theorem div_le_div_aux {X Y E : ℝ} (hE : 0 < E) (h : X ≤ Y) : X / E ≤ Y / E := by
  have h1 : 0 ≤ (Y - X) / E := div_nonneg (by linarith) hE.le
  rw [sub_div] at h1
  linarith

theorem le_of_div_le {A E ψ : ℝ} (hE : 0 < E) (h : A / E ≤ ψ) : A ≤ E * ψ := by
  have h1 : A / E * E ≤ ψ * E := mul_le_mul_of_nonneg_right h hE.le
  rw [div_mul_cancel₀ _ hE.ne'] at h1
  linarith [mul_comm ψ E]

theorem div_le_of_le {B E ψ : ℝ} (hE : 0 < E) (h : ψ ≤ B / E) : E * ψ ≤ B := by
  have h1 : ψ * E ≤ B / E * E := mul_le_mul_of_nonneg_right h hE.le
  rw [div_mul_cancel₀ _ hE.ne'] at h1
  linarith [mul_comm ψ E]

theorem mul_div_self_aux {X E : ℝ} (hE : 0 < E) : E * (X / E) = X := by
  rw [mul_comm]
  exact div_mul_cancel₀ X hE.ne'

theorem natCast_pos_of_ne_zero {e : ℕ} (he : e ≠ 0) : (0 : ℝ) < e := by
  have he' : 0 < e := Nat.pos_of_ne_zero he
  exact_mod_cast he'

theorem image_shift_div_Icc (c : ℝ) {E : ℝ} (hE : 0 < E) (a b : ℝ) :
    (fun t : ℝ => (c + t) / E) '' Set.Icc a b = Set.Icc ((c + a) / E) ((c + b) / E) := by
  ext s
  constructor
  · rintro ⟨t, ⟨hta, htb⟩, rfl⟩
    exact ⟨div_le_div_aux hE (by linarith), div_le_div_aux hE (by linarith)⟩
  · rintro ⟨hs1, hs2⟩
    have h1 := le_of_div_le hE hs1
    have h2 := div_le_of_le hE hs2
    refine ⟨E * s - c, ⟨by linarith, by linarith⟩, ?_⟩
    show (c + (E * s - c)) / E = s
    rw [div_eq_iff hE.ne']
    ring

theorem lap_lt {e N j k : ℕ} (hj : j < e) (hk : k < N) : j * N + k < e * N :=
  calc j * N + k < j * N + N := Nat.add_lt_add_left hk _
    _ = Nat.succ j * N := (Nat.succ_mul j N).symm
    _ ≤ e * N := Nat.mul_le_mul_right N (Nat.succ_le_of_lt hj)

theorem lap_div {N j k : ℕ} (hk : k < N) : (j * N + k) / N = j := by
  have hN : 0 < N := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hk, Nat.zero_add]

theorem lap_mod {N j k : ℕ} (hk : k < N) : (j * N + k) % N = k := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]

/- As constructed below. -/
/-- The radial radius obtained by pulling a region back through a positive integer power. -/
def rootRadius (r : ℝ → ℝ) (e : ℕ) : ℝ → ℝ :=
  fun ψ => (r (e * ψ)) ^ ((e : ℝ)⁻¹)

theorem rootRadius_apply (r : ℝ → ℝ) (e : ℕ) (ψ : ℝ) :
    rootRadius r e ψ = (r (e * ψ)) ^ ((e : ℝ)⁻¹) := rfl

theorem rootRadius_continuous (r : ℝ → ℝ) (hcont : Continuous r) (hpos : ∀ φ, 0 < r φ)
    (e : ℕ) : Continuous (rootRadius r e) := by
  show Continuous (fun ψ : ℝ => (r (e * ψ)) ^ ((e : ℝ)⁻¹))
  exact (hcont.comp (continuous_const.mul continuous_id)).rpow_const
    (fun ψ => Or.inl (hpos _).ne')

theorem rootRadius_periodic (r : ℝ → ℝ) (hper : Function.Periodic r (2 * π)) (e : ℕ) :
    Function.Periodic (rootRadius r e) (2 * π) := by
  intro ψ
  show (r (e * (ψ + 2 * π))) ^ ((e : ℝ)⁻¹) = (r (e * ψ)) ^ ((e : ℝ)⁻¹)
  congr 1
  rw [show (e : ℝ) * (ψ + 2 * π) = e * ψ + e * (2 * π) by ring]
  exact (hper.nat_mul e) (e * ψ)

theorem rootRadius_pos (r : ℝ → ℝ) (hpos : ∀ φ, 0 < r φ) (e : ℕ) (ψ : ℝ) :
    0 < rootRadius r e ψ := by
  show 0 < (r (e * ψ)) ^ ((e : ℝ)⁻¹)
  exact Real.rpow_pos_of_pos (hpos _) _

theorem periodic_arg_pow {r : ℝ → ℝ} (hper : Function.Periodic r (2 * Real.pi))
    {e : ℕ} (he : e ≠ 0) (ζ : ℂ) :
    r (Complex.arg (ζ ^ e)) = r (e * Complex.arg ζ) := by
  rcases eq_or_ne ζ 0 with rfl | hζ
  · rw [zero_pow he, Complex.arg_zero, mul_zero]
  · have hpolar : ζ ^ e = ((‖ζ‖ ^ e : ℝ) : ℂ) *
        Complex.exp (((e * Complex.arg ζ : ℝ) : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ζ]
      rw [mul_pow, ← Complex.exp_nat_mul]
      push_cast
      rw [mul_assoc]
    rw [hpolar]
    exact periodic_apply_arg hper (pow_pos (norm_pos_iff.mpr hζ) e) _

theorem norm_le_rootRadius_iff {r : ℝ → ℝ} (hper : Function.Periodic r (2 * Real.pi))
    (hpos : ∀ φ, 0 < r φ) {e : ℕ} (he : e ≠ 0) (q ζ : ℂ) :
    ‖ζ‖ ≤ rootRadius r e (Complex.arg ζ)
      ↔ ‖(q + ζ ^ e) - q‖ ≤ r (Complex.arg ((q + ζ ^ e) - q)) := by
  rw [add_sub_cancel_left, norm_pow, periodic_arg_pow hper he, rootRadius_apply]
  constructor
  · intro h
    calc ‖ζ‖ ^ e ≤ ((r (e * Complex.arg ζ)) ^ ((e : ℝ)⁻¹)) ^ e :=
          pow_le_pow_left₀ (norm_nonneg ζ) h e
    _ = r (e * Complex.arg ζ) := Real.rpow_inv_natCast_pow (hpos _).le he
  · intro h
    calc ‖ζ‖ = ((‖ζ‖ ^ e : ℝ)) ^ ((e : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (norm_nonneg ζ) he).symm
    _ ≤ (r (e * Complex.arg ζ)) ^ ((e : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) h (by positivity)

theorem norm_lt_rootRadius_iff {r : ℝ → ℝ} (hper : Function.Periodic r (2 * Real.pi))
    (hpos : ∀ φ, 0 < r φ) {e : ℕ} (he : e ≠ 0) (q ζ : ℂ) :
    ‖ζ‖ < rootRadius r e (Complex.arg ζ)
      ↔ ‖(q + ζ ^ e) - q‖ < r (Complex.arg ((q + ζ ^ e) - q)) := by
  rw [add_sub_cancel_left, norm_pow, periodic_arg_pow hper he, rootRadius_apply]
  constructor
  · intro h
    calc ‖ζ‖ ^ e < ((r (e * Complex.arg ζ)) ^ ((e : ℝ)⁻¹)) ^ e :=
          pow_lt_pow_left₀ h (norm_nonneg ζ) he
    _ = r (e * Complex.arg ζ) := Real.rpow_inv_natCast_pow (hpos _).le he
  · intro h
    calc ‖ζ‖ = ((‖ζ‖ ^ e : ℝ)) ^ ((e : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (norm_nonneg ζ) he).symm
    _ < (r (e * Complex.arg ζ)) ^ ((e : ℝ)⁻¹) :=
          Real.rpow_lt_rpow (by positivity) h (by positivity)


end
end Dubon2026.SourceFunctionField.CellGeometry.PowPullback

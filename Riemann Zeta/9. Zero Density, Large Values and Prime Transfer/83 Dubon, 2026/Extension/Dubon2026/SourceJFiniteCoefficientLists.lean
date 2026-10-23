import Dubon2026.SourceJPositiveCoefficients

/-! Exact first seven coefficients of the actual integral j numerator.
These supply the finite coefficient comparison identifying the actual integral
prime-two modular polynomial, then its cyclic-quotient roots and finite inertia
census on the DUB-17 / DUB-18 good-reduction chain. Adapted from the selected
coeff_jNum_le_six proof, anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Reuse the existing proved eta-product
truncation; do not repeat its topological infinite-product argument. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open PowerSeries
namespace JCoeff

variable {R : Type*} [CommRing R]

/-- Agreement with a finite coefficient list. -/
def LowCoeffs (f : R⟦X⟧) (L : List R) : Prop :=
  ∀ i : ℕ, i < L.length → coeff i f = L.getD i 0

/-- Truncated convolution of two coefficient lists. -/
def conv (L M : List R) : List R :=
  (List.range (min L.length M.length)).map
    fun k => ((List.range (k + 1)).map fun i => L.getD i 0 * M.getD (k - i) 0).sum

theorem length_conv (L M : List R) : (conv L M).length = min L.length M.length := by
  simp [conv]

theorem finset_sum_range_eq_list_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

theorem getD_conv (L M : List R) {k : ℕ} (hk : k < min L.length M.length) :
    (conv L M).getD k 0 = ∑ i ∈ Finset.range (k + 1), L.getD i 0 * M.getD (k - i) 0 := by
  rw [conv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp [finset_sum_range_eq_list_sum]

theorem LowCoeffs.mul {f g : R⟦X⟧} {L M : List R} (hf : LowCoeffs f L) (hg : LowCoeffs g M) :
    LowCoeffs (f * g) (conv L M) := by
  intro k hk
  rw [length_conv] at hk
  rw [getD_conv L M hk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [hf i (by omega), hg (k - i) (by omega)]

theorem LowCoeffs.congr {f : R⟦X⟧} {L M : List R} (hf : LowCoeffs f L) (h : L = M) : LowCoeffs f M :=
  h ▸ hf

theorem LowCoeffs.one (n : ℕ) : LowCoeffs (1 : R⟦X⟧) (1 :: List.replicate n 0) := by
  intro i hi
  rcases i with _ | i
  · simp
  · simp only [List.length_cons, List.length_replicate] at hi
    rw [coeff_one, if_neg (Nat.succ_ne_zero i), List.getD_eq_getElem?_getD]
    simp [show i < n by omega]

theorem LowCoeffs.one_sub_X_pow (m n : ℕ) (hm : 0 < m) :
    LowCoeffs (1 - X ^ m : R⟦X⟧) ((List.range n).map fun i => if i = 0 then 1 else if i = m then -1 else 0) := by
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some, map_sub, coeff_one, coeff_X_pow]
  by_cases h0 : i = 0
  · subst h0; simp [hm.ne]
  · simp [h0]
    split_ifs <;> simp

theorem LowCoeffs.X_pow_dvd_sub {f g : R⟦X⟧} {L : List R} (hf : LowCoeffs f L) (hg : LowCoeffs g L) :
    (X : R⟦X⟧) ^ L.length ∣ f - g := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, hf m hm, hg m hm, sub_self]

theorem LowCoeffs.invOfUnit {u : R⟦X⟧} {L V : List R} (hu : LowCoeffs u L) (hV : V.length = L.length)
    (hc : constantCoeff u = 1) (hconv : conv L V = 1 :: List.replicate (L.length - 1) 0)
    (hpos : 0 < L.length) :
    LowCoeffs (u.invOfUnit 1) V := by
  set w := u.invOfUnit 1 with hw
  have huw : u * w = 1 := PowerSeries.mul_invOfUnit u 1 (by rw [hc]; rfl)

  set Vp : R⟦X⟧ := PowerSeries.mk fun i => V.getD i 0 with hVp
  have hVpL : LowCoeffs Vp V := fun i _ => by simp [hVp, coeff_mk]
  have h1 : LowCoeffs (u * Vp) (1 :: List.replicate (L.length - 1) 0) :=
    (hu.mul hVpL).congr (by rw [hconv])
  have h1' : LowCoeffs (1 : R⟦X⟧) (1 :: List.replicate (L.length - 1) 0) := LowCoeffs.one _
  have hdvd : (X : R⟦X⟧) ^ L.length ∣ u * Vp - 1 := by
    have := h1.X_pow_dvd_sub h1'
    simpa [Nat.sub_add_cancel hpos] using this
  have hdvd' : (X : R⟦X⟧) ^ L.length ∣ Vp - w := by
    have : Vp - w = w * (u * Vp - 1) := by
      calc Vp - w = (u * w) * Vp - w * 1 := by rw [huw, one_mul, mul_one]
        _ = w * (u * Vp - 1) := by ring
    rw [this]
    exact Dvd.dvd.mul_left hdvd w
  rw [X_pow_dvd_iff] at hdvd'
  intro i hi
  have := hdvd' i (by omega)
  rw [map_sub, sub_eq_zero] at this
  rw [← this]
  exact hVpL i hi

end JCoeff

end
end Dubon2026.SourceFunctionField

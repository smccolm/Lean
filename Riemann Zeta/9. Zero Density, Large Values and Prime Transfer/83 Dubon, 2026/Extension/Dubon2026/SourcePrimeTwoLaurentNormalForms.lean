import Dubon2026.SourceJSevenCoefficients
import Dubon2026.SourcePrimeTwoPolynomial
import Dubon2026.SourceLaurentRootTwist

/-! Finite Laurent coefficient comparison for the actual prime-two integral
modular polynomial. This identifies the explicit cubic used by the degree-two
quotient product, required for the actual cyclic-quotient root interpretation
and elliptic inertia census on the DUB-17 / DUB-18 good-reduction chain.
Adapted from the selected phi_eq_phiTwo proof, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Reuse the existing
coefficient-list operations; degree bounds come from actual Laurent poles,
without polynomial symmetry or abstract modular-polynomial data. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial PowerSeries JCoeff
open Dubon2026.SourcePrimeTwoPolynomial
namespace PhiTwoCalc
variable {R : Type*} [CommRing R]
theorem getD_map_intCast (l : List ℤ) (i : ℕ) : (l.map (Int.cast : ℤ → R)).getD i 0 = ((l.getD i 0 : ℤ) : R) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[i]? <;> simp

theorem conv_map_intCast (L M : List ℤ) :
    conv (L.map (Int.cast : ℤ → R)) (M.map (Int.cast : ℤ → R)) = (conv L M).map (Int.cast : ℤ → R) := by
  simp only [conv, List.length_map, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, getD_map_intCast]
  rw [Int.cast_list_sum, List.map_map]
  refine congrArg _ (List.map_congr_left fun i _ => ?_)
  simp [Function.comp_apply, Int.cast_mul]

/-- The native power-series embedding into rational Laurent series. -/
noncomputable abbrev ofPS (F : ℚ⟦X⟧) : LaurentSeries ℚ := HahnSeries.ofPowerSeries ℤ ℚ F

theorem coeff_ofPS (F : ℚ⟦X⟧) (m : ℤ) :
    (ofPS F).coeff m = if 0 ≤ m then PowerSeries.coeff m.toNat F else 0 := by
  split_ifs with h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [Int.toNat_natCast, HahnSeries.ofPowerSeries_apply_coeff]
  · exact ofPowerSeries_coeff_of_neg F (by omega)

theorem coeff_single_mul_ofPS (a : ℤ) (r : ℚ) (F : ℚ⟦X⟧) (m : ℤ) :
    (HahnSeries.single a r * ofPS F).coeff m = if a ≤ m then r * PowerSeries.coeff (m - a).toNat F else 0 := by
  rw [HahnSeries.coeff_single_mul, coeff_ofPS]
  by_cases h : a ≤ m
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h, mul_zero]

theorem eq_single_mul_ofPS (x : LaurentSeries ℚ) (a : ℤ) (hx : ∀ m < a, x.coeff m = 0) :
    x = HahnSeries.single a 1 * ofPS (PowerSeries.mk fun i => x.coeff (a + i)) := by
  ext m
  rw [coeff_single_mul_ofPS, one_mul]
  split_ifs with h
  · rw [PowerSeries.coeff_mk]; congr 1; omega
  · exact hx m (by omega)

/-- A Laurent series with a proved lower support bound and finite coefficient list. -/
def NF (x : LaurentSeries ℚ) (a : ℤ) (L : List ℤ) : Prop :=
  ∃ F : ℚ⟦X⟧, x = HahnSeries.single a 1 * ofPS F ∧ LowCoeffs F (L.map (Int.cast : ℤ → ℚ))

theorem NF.mul {x y : LaurentSeries ℚ} {a b : ℤ} {L M : List ℤ} (hx : NF x a L) (hy : NF y b M) :
    NF (x * y) (a + b) (conv L M) := by
  obtain ⟨F, rfl, hF⟩ := hx
  obtain ⟨G, rfl, hG⟩ := hy
  refine ⟨F * G, ?_, ?_⟩
  · rw [mul_mul_mul_comm, HahnSeries.single_mul_single, one_mul]
    congr 1
    exact (map_mul (HahnSeries.ofPowerSeries ℤ ℚ) F G).symm
  · rw [← conv_map_intCast]; exact hF.mul hG

theorem NF.congr {x : LaurentSeries ℚ} {a : ℤ} {L M : List ℤ} (hx : NF x a L) (h : L = M) : NF x a M := h ▸ hx

theorem NF.coeff {x : LaurentSeries ℚ} {a : ℤ} {L : List ℤ} (hx : NF x a L) (m : ℤ) (hm : (m - a).toNat < L.length) :
    x.coeff m = if a ≤ m then ((L.getD (m - a).toNat 0 : ℤ) : ℚ) else 0 := by
  obtain ⟨F, rfl, hF⟩ := hx
  rw [coeff_single_mul_ofPS, one_mul]
  split_ifs with h
  · rw [hF _ (by simpa using hm), getD_map_intCast]
  · rfl

theorem coeff_jq_eq (i : ℕ) : jq.coeff (-1 + (i : ℤ)) = ((PowerSeries.coeff i jNum : ℤ) : ℚ) := by
  rw [show jq = HahnSeries.single (-1 : ℤ) 1 * ofPS jNumQ from rfl, coeff_single_mul_ofPS, one_mul,
    if_pos (by omega), show (-1 + (i : ℤ) - -1).toNat = i by omega, jNumQ, PowerSeries.coeff_map]
  simp

/-- The seven exact integral j numerator coefficients. -/
def LJ : List ℤ := [1, 744, 196884, 21493760, 864299970, 20245856256, 333202640600]

theorem coeff_jNum_eq_LJ (i : ℕ) (hi : i < 7) : (PowerSeries.coeff i jNum : ℤ) = LJ.getD i 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := coeff_jNum_le_six
  interval_cases i <;> simp [LJ, h0, h1, h2, h3, h4, h5, h6]

theorem nf_jq : NF jq (-1) LJ := by
  refine ⟨PowerSeries.mk fun i => jq.coeff (-1 + i), eq_single_mul_ofPS jq (-1) (fun m hm => coeff_jq_of_lt hm), ?_⟩
  intro i hi
  simp only [List.length_map, LJ, List.length_cons, List.length_nil] at hi
  rw [PowerSeries.coeff_mk, coeff_jq_eq, coeff_jNum_eq_LJ i (by omega), getD_map_intCast]

/-- The seven coefficients after twisting by minus one. -/
def LC : List ℤ := [-1, 744, -196884, 21493760, -864299970, 20245856256, -333202640600]

theorem nf_qTwist_neg_one_jq : NF (qTwist (-1 : ℚˣ) jq) (-1) LC := by
  refine ⟨PowerSeries.mk fun i => (qTwist (-1 : ℚˣ) jq).coeff (-1 + i),
    eq_single_mul_ofPS _ (-1) (fun m hm => by rw [qTwist_coeff, coeff_jq_of_lt hm, mul_zero]), ?_⟩
  intro i hi
  simp only [List.length_map, LC, List.length_cons, List.length_nil] at hi
  rw [PowerSeries.coeff_mk, qTwist_coeff, coeff_jq_eq, coeff_jNum_eq_LJ i (by omega)]
  rw [getD_map_intCast]
  interval_cases i <;> simp [LJ, LC, Units.val_zpow_eq_zpow_val]

/-- The seven coefficients after substituting q to the fourth power. -/
def LA : List ℤ := [1, 0, 0, 0, 744, 0, 0]

theorem nf_qExpand_four_jq : NF (qExpand ℚ 4 jq) (-4) LA := by
  refine ⟨PowerSeries.mk fun i => (qExpand ℚ 4 jq).coeff (-4 + i), eq_single_mul_ofPS _ (-4) (fun m hm => ?_), ?_⟩
  · by_cases h : (4 : ℤ) ∣ m
    · obtain ⟨c, rfl⟩ := h
      have h4 := qExpand_coeff_mul (R := ℚ) 4 jq c
      rw [Nat.cast_ofNat] at h4
      rw [h4]
      exact coeff_jq_of_lt (by omega)
    · exact qExpand_coeff_of_not_dvd 4 jq (by exact_mod_cast h)
  · intro i hi
    simp only [List.length_map, LA, List.length_cons, List.length_nil] at hi
    rw [PowerSeries.coeff_mk]
    interval_cases i
    · rw [show (-4 : ℤ) + ((0 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) * (-1) by norm_num, qExpand_coeff_mul, coeff_jq_neg_one]; simp [LA]
    · rw [qExpand_coeff_of_not_dvd 4 jq (by decide)]; simp [LA]
    · rw [qExpand_coeff_of_not_dvd 4 jq (by decide)]; simp [LA]
    · rw [qExpand_coeff_of_not_dvd 4 jq (by decide)]; simp [LA]
    · rw [show (-4 : ℤ) + ((4 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) * 0 by norm_num, qExpand_coeff_mul,
        show (0 : ℤ) = -1 + ((1 : ℕ) : ℤ) by norm_num, coeff_jq_eq, coeff_jNum_eq_LJ 1 (by omega)]; simp [LA, LJ]
    · rw [qExpand_coeff_of_not_dvd 4 jq (by decide)]; simp [LA]
    · rw [qExpand_coeff_of_not_dvd 4 jq (by decide)]; simp [LA]

/-- The seven coefficients after substituting q to the second power. -/
def L2 : List ℤ := [1, 0, 744, 0, 196884, 0, 21493760]

theorem nf_qExpand_two_jq : NF (qExpand ℚ 2 jq) (-2) L2 := by
  refine ⟨PowerSeries.mk fun i => (qExpand ℚ 2 jq).coeff (-2 + i), eq_single_mul_ofPS _ (-2) (fun m hm => ?_), ?_⟩
  · by_cases h : (2 : ℤ) ∣ m
    · obtain ⟨c, rfl⟩ := h
      have h2 := qExpand_coeff_mul (R := ℚ) 2 jq c
      rw [Nat.cast_ofNat] at h2
      rw [h2]
      exact coeff_jq_of_lt (by omega)
    · exact qExpand_coeff_of_not_dvd 2 jq (by exact_mod_cast h)
  · intro i hi
    simp only [List.length_map, L2, List.length_cons, List.length_nil] at hi
    rw [PowerSeries.coeff_mk]
    interval_cases i
    · rw [show (-2 : ℤ) + ((0 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) * (-1) by norm_num, qExpand_coeff_mul, coeff_jq_neg_one]; simp [L2]
    · rw [qExpand_coeff_of_not_dvd 2 jq (by decide)]; simp [L2]
    · rw [show (-2 : ℤ) + ((2 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) * (-1 + ((1 : ℕ) : ℤ)) by norm_num, qExpand_coeff_mul,
        coeff_jq_eq, coeff_jNum_eq_LJ 1 (by omega)]; simp [L2, LJ]
    · rw [qExpand_coeff_of_not_dvd 2 jq (by decide)]; simp [L2]
    · rw [show (-2 : ℤ) + ((4 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) * (-1 + ((2 : ℕ) : ℤ)) by norm_num, qExpand_coeff_mul,
        coeff_jq_eq, coeff_jNum_eq_LJ 2 (by omega)]; simp [L2, LJ]
    · rw [qExpand_coeff_of_not_dvd 2 jq (by decide)]; simp [L2]
    · rw [show (-2 : ℤ) + ((6 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) * (-1 + ((3 : ℕ) : ℤ)) by norm_num, qExpand_coeff_mul,
        coeff_jq_eq, coeff_jNum_eq_LJ 3 (by omega)]; simp [L2, LJ]

end PhiTwoCalc
end
end Dubon2026.SourceFunctionField

import GafniTao.FordLemma34EventualData
import GafniTao.FordPrimePacketUniform

/-!
# Ford Lemma 3.4: a quantitative common scale

The asymptotic PNT argument used earlier leaves its endpoint hidden inside an
eventual quantifier.  That is harmless for fixed moment parameters but is not
uniform enough for Ford's later choice of a degree growing with the zeta
height.  Here the PNT is used only once, at the fixed relative width `1/100`.
The resulting global constant is combined with explicit polynomial powers of
`s` and `k`, producing a common physical `P` threshold for every index in the
Lemma 3.4 induction.
-/

namespace GafniTao

noncomputable section

/-- A base which simultaneously dominates Ford's degree and the uniform
prime-packet threshold. -/
def fordLemma34UniformBase (k : ℕ) : ℝ :=
  max (k : ℝ) (fordPrimePacketScaleThreshold k + 1 : ℕ)

/-- Explicit common real endpoint for all scale obligations in Lemma 3.4. -/
def fordLemma34ExplicitThreshold (s k : ℕ) : ℝ :=
  max ((4 * k ^ 4 + 2 : ℕ) : ℝ)
    (max (fordLemma34UniformBase k ^ (k + 1))
      (((64 * s ^ 2 + 1 : ℕ) : ℝ) ^ 10))

theorem fordLemma34UniformBase_one_le (k : ℕ) :
    1 ≤ fordLemma34UniformBase k := by
  unfold fordLemma34UniformBase
  have hnat : 1 ≤ fordPrimePacketScaleThreshold k + 1 := by omega
  have hreal : (1 : ℝ) ≤ ((fordPrimePacketScaleThreshold k + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hreal.trans (le_max_right _ _)

theorem fordLemma34ExplicitThreshold_one_le (s k : ℕ) :
    1 ≤ fordLemma34ExplicitThreshold s k := by
  unfold fordLemma34ExplicitThreshold
  have hnat : 1 ≤ 4 * k ^ 4 + 2 := by omega
  have hreal : (1 : ℝ) ≤ ((4 * k ^ 4 + 2 : ℕ) : ℝ) := by exact_mod_cast hnat
  exact hreal.trans (le_max_left _ _)

private theorem rpow_inv_succ_of_one_le {x : ℝ} (hx : 1 ≤ x) (k : ℕ) :
    (x ^ (k + 1)) ^ (1 / (((k + 1 : ℕ) : ℝ))) = x := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx0]
  have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hexp : (((k + 1 : ℕ) : ℝ)) *
      (1 / (((k + 1 : ℕ) : ℝ))) = 1 := by field_simp
  rw [hexp, Real.rpow_one]

private theorem rpow_one_tenth_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    (x ^ 10) ^ (1 / 10 : ℝ) = x := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx0]
  norm_num

/-- The explicit threshold supplies the two uniform powers and the floor
condition used in equation (3.9). -/
theorem fordLemma34ExplicitThreshold_powers
    {s k : ℕ} {P : ℝ} (hP : fordLemma34ExplicitThreshold s k ≤ P) :
    1 ≤ P ∧
    (k : ℝ) ≤ P ^ (1 / (((k + 1 : ℕ) : ℝ))) ∧
    (64 * (s : ℝ) ^ 2 + 1) ≤ P ^ (1 / 10 : ℝ) ∧
    4 * k ^ 4 < ⌊P⌋₊ := by
  have hPone : 1 ≤ P := (fordLemma34ExplicitThreshold_one_le s k).trans hP
  have hP' := hP
  change max ((4 * k ^ 4 + 2 : ℕ) : ℝ)
      (max (fordLemma34UniformBase k ^ (k + 1))
        (((64 * s ^ 2 + 1 : ℕ) : ℝ) ^ 10)) ≤ P at hP'
  have hbasePow : fordLemma34UniformBase k ^ (k + 1) ≤ P :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hP')
  have hsourcePow : (((64 * s ^ 2 + 1 : ℕ) : ℝ) ^ 10) ≤ P :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hP')
  have hbaseOne := fordLemma34UniformBase_one_le k
  have hsourceOne : (1 : ℝ) ≤ ((64 * s ^ 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 64 * s ^ 2 + 1 by omega)
  have hrootMono := Real.rpow_le_rpow
    (by positivity : 0 ≤ fordLemma34UniformBase k ^ (k + 1))
    hbasePow (by positivity : 0 ≤ (1 / (((k + 1 : ℕ) : ℝ))))
  have hsourceMono := Real.rpow_le_rpow
    (by positivity : 0 ≤ (((64 * s ^ 2 + 1 : ℕ) : ℝ) ^ 10))
    hsourcePow (by norm_num : (0 : ℝ) ≤ 1 / 10)
  have hfloorReal : ((4 * k ^ 4 + 1 : ℕ) : ℝ) < P := by
    have hfirst : ((4 * k ^ 4 + 2 : ℕ) : ℝ) ≤
        fordLemma34ExplicitThreshold s k := le_max_left _ _
    have hstep : ((4 * k ^ 4 + 1 : ℕ) : ℝ) <
        ((4 * k ^ 4 + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    exact hstep.trans_le (hfirst.trans hP)
  have hfloor : 4 * k ^ 4 + 1 ≤ ⌊P⌋₊ := by
    apply (Nat.le_floor_iff (show 0 ≤ P by positivity)).2
    exact hfloorReal.le
  refine ⟨hPone, ?_, ?_, by omega⟩
  · calc
      (k : ℝ) ≤ fordLemma34UniformBase k := le_max_left _ _
      _ = (fordLemma34UniformBase k ^ (k + 1)) ^
          (1 / (((k + 1 : ℕ) : ℝ))) :=
        (rpow_inv_succ_of_one_le hbaseOne k).symm
      _ ≤ P ^ (1 / (((k + 1 : ℕ) : ℝ))) := hrootMono
  · have hcast : ((64 * s ^ 2 + 1 : ℕ) : ℝ) =
        64 * (s : ℝ) ^ 2 + 1 := by norm_num
    rw [← hcast]
    calc
      ((64 * s ^ 2 + 1 : ℕ) : ℝ) =
          ((((64 * s ^ 2 + 1 : ℕ) : ℝ) ^ 10) ^ (1 / 10 : ℝ)) :=
        (rpow_one_tenth_of_one_le hsourceOne).symm
      _ ≤ P ^ (1 / 10 : ℝ) := hsourceMono

/-- Quantitative replacement for the earlier eventual source-data theorem.
It uses the canonical packet and a fixed `1/100` PNT window, which is strictly
inside Ford's `eta=53/50` window. -/
theorem ford_equation_3_10_inputs_explicit
    {s k r j : ℕ} {delta : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (hk : 26 ≤ k) (hr : 4 ≤ r) (hrk : r ≤ k)
    (hj : 2 ≤ j) (hjr : 10 * j ≤ 9 * r)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤
      2 * delta - (((k - r) * (k - r + 1) : ℕ) : ℝ))
    (hlower : ∀ i, 1 ≤ i → i ≤ j →
      1 / ((k + 1 : ℕ) : ℝ) ≤ Φ.phi i)
    {P : ℝ} (hthreshold : fordLemma34ExplicitThreshold s k ≤ P) :
      1 ≤ P ∧
      4 * k ^ 4 < ⌊P⌋₊ ∧
      (∀ i, 1 ≤ i → i ≤ j → (k : ℝ) ≤ fordMScale P Φ i) ∧
      (∀ i, i < j →
        (((32 * s ^ 2 * ⌈fordMScale P Φ (i + 1)⌉₊ + 1 : ℕ) : ℝ)) ≤
          fordQScale P Φ i) ∧
      (∀ i, 1 ≤ i → i ≤ j →
        ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ i⌋₊,
          (p : ℝ) ≤ (53 / 50 : ℝ) * fordMScale P Φ i) := by
  rcases fordLemma34ExplicitThreshold_powers hthreshold with
    ⟨hP, hbaseK, hbaseQ, hPfloor⟩
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hupper : ∀ i, 1 ≤ i → i ≤ j → Φ.phi i ≤ 1 / (r : ℝ) :=
    Φ.le_inv_r (show 1 ≤ k by omega) (show 1 ≤ r by omega)
      hrk hj h38 hlower
  have hMlarge : ∀ i, 1 ≤ i → i ≤ j →
      (k : ℝ) ≤ fordMScale P Φ i := by
    intro i hi hij
    exact hbaseK.trans (fordMScale_ge_uniform_base Φ hP (hlower i hi hij))
  have hQbox : ∀ i, i < j →
      (((32 * s ^ 2 * ⌈fordMScale P Φ (i + 1)⌉₊ + 1 : ℕ) : ℝ)) ≤
        fordQScale P Φ i := by
    intro i hij
    have hMone : 1 ≤ fordMScale P Φ (i + 1) := by
      exact (show (1 : ℝ) ≤ k by exact_mod_cast (show 1 ≤ k by omega)).trans
        (hMlarge (i + 1) (by omega) (by omega))
    exact ford_equation_3_9_rounded Φ hP (show 1 ≤ r by omega)
      (by omega) hupper (by omega) hMone hbaseQ
  have hpacket : ∀ i, 1 ≤ i → i ≤ j →
      ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ i⌋₊,
        (p : ℝ) ≤ (53 / 50 : ℝ) * fordMScale P Φ i := by
    intro i hi hij p hp
    have hthreshold' := hthreshold
    change max ((4 * k ^ 4 + 2 : ℕ) : ℝ)
        (max (fordLemma34UniformBase k ^ (k + 1))
          (((64 * s ^ 2 + 1 : ℕ) : ℝ) ^ 10)) ≤ P at hthreshold'
    have hbasePow : fordLemma34UniformBase k ^ (k + 1) ≤ P :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hthreshold')
    have hbaseRoot : fordLemma34UniformBase k ≤
        P ^ (1 / (((k + 1 : ℕ) : ℝ))) := by
      calc
        fordLemma34UniformBase k =
            (fordLemma34UniformBase k ^ (k + 1)) ^
              (1 / (((k + 1 : ℕ) : ℝ))) :=
          (rpow_inv_succ_of_one_le (fordLemma34UniformBase_one_le k) k).symm
        _ ≤ P ^ (1 / (((k + 1 : ℕ) : ℝ))) :=
          Real.rpow_le_rpow
            (pow_nonneg (zero_le_one.trans (fordLemma34UniformBase_one_le k)) _)
            hbasePow (div_nonneg zero_le_one (by positivity))
    have hbasePacket : ((fordPrimePacketScaleThreshold k + 1 : ℕ) : ℝ) ≤
        P ^ (1 / (((k + 1 : ℕ) : ℝ))) := by
      exact (le_max_right _ _).trans hbaseRoot
    have hscalePacket : (fordPrimePacketScaleThreshold k : ℝ) ≤
        fordMScale P Φ i := by
      have hpow := fordMScale_ge_uniform_base Φ hP (hlower i hi hij)
      have hstrict : (fordPrimePacketScaleThreshold k : ℝ) <
          P ^ (1 / (((k + 1 : ℕ) : ℝ))) := by
        have hs : (fordPrimePacketScaleThreshold k : ℝ) <
            ((fordPrimePacketScaleThreshold k + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.lt_succ_self (fordPrimePacketScaleThreshold k)
        exact hs.trans_le hbasePacket
      exact hstrict.le.trans hpow
    have hfloorScale : fordPrimePacketScaleThreshold k ≤
        ⌊fordMScale P Φ i⌋₊ :=
      (Nat.le_floor_iff (fordMScale_pos hP0 Φ i).le).2 hscalePacket
    have hpNat := fordPrimeSet_le_fixedWidth hfloorScale hp
    have hpReal : (p : ℝ) ≤
        (fordRelativePrimeBound fordUniformPrimeWidth
          ⌊fordMScale P Φ i⌋₊ : ℕ) := by exact_mod_cast hpNat
    have hboundFloor :
        ((fordRelativePrimeBound fordUniformPrimeWidth
          ⌊fordMScale P Φ i⌋₊ : ℕ) : ℝ) ≤
          (1 + fordUniformPrimeWidth) * fordMScale P Φ i := by
      calc
        ((fordRelativePrimeBound fordUniformPrimeWidth
            ⌊fordMScale P Φ i⌋₊ : ℕ) : ℝ) ≤
            (1 + fordUniformPrimeWidth) *
              (⌊fordMScale P Φ i⌋₊ : ℝ) := by
          unfold fordRelativePrimeBound
          exact Nat.floor_le (mul_nonneg
            (by norm_num [fordUniformPrimeWidth]) (Nat.cast_nonneg _))
        _ ≤ (1 + fordUniformPrimeWidth) * fordMScale P Φ i := by
          exact mul_le_mul_of_nonneg_left
            (Nat.floor_le (fordMScale_pos hP0 Φ i).le)
            (by norm_num [fordUniformPrimeWidth])
    calc
      (p : ℝ) ≤
          (fordRelativePrimeBound fordUniformPrimeWidth
            ⌊fordMScale P Φ i⌋₊ : ℕ) := hpReal
      _ ≤ (1 + fordUniformPrimeWidth) * fordMScale P Φ i := hboundFloor
      _ ≤ (53 / 50 : ℝ) * fordMScale P Φ i := by
        have hscale0 := (fordMScale_pos hP0 Φ i).le
        rw [fordUniformPrimeWidth]
        gcongr
        norm_num
  exact ⟨hP, hPfloor, hMlarge, hQbox, hpacket⟩

#print axioms fordLemma34ExplicitThreshold_powers
#print axioms ford_equation_3_10_inputs_explicit

end

end GafniTao

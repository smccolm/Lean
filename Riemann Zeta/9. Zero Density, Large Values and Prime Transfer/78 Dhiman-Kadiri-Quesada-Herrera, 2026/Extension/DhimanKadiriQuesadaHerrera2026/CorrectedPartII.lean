import DhimanKadiriQuesadaHerrera2026.PartIIShiftInputs
import DhimanKadiriQuesadaHerrera2026.PartIIHalfSource
import DhimanKadiriQuesadaHerrera2026.PoissonHalfDelta
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Topology.Order.MonotoneContinuity

namespace DhimanKadiriQuesadaHerrera2026

/-- A monotone derivative is continuous on the closed interval by Darboux, including both endpoints. -/
theorem continuousOn_deriv_of_monotone {F : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ F u)
    (hm : MonotoneOn (deriv F) (Set.Icc a b)) :
    ContinuousOn (deriv F) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · let φ : Set.Icc a b → Set.Icc (deriv F a) (deriv F b) := fun u =>
      ⟨deriv F u, hm (Set.left_mem_Icc.mpr hab) u.property u.property.1,
        hm u.property (Set.right_mem_Icc.mpr hab) u.property.2⟩
    have hφ : Monotone φ := fun u v huv => hm u.property v.property huv
    have hs : Function.Surjective φ := by
      intro z
      obtain ⟨u, hu, he⟩ := exists_hasDerivWithinAt_eq_of_ge_of_le hab
        (fun u hu => (hd u hu).hasDerivAt.hasDerivWithinAt) z.property.1 z.property.2
      exact ⟨⟨u, hu⟩, Subtype.ext he⟩
    have hc := continuous_subtype_val.comp (hφ.continuous_of_surjective hs)
    exact continuousOn_iff_continuous_restrict.mpr hc
  · rw [Set.Icc_eq_empty_of_lt (lt_of_not_ge hab)]
    exact continuousOn_empty _

/-- A nonincreasing derivative is continuous on the closed interval; no extra endpoint smoothness is assumed. -/
theorem continuousOn_deriv_of_antitone {F : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ F u)
    (hm : AntitoneOn (deriv F) (Set.Icc a b)) :
    ContinuousOn (deriv F) (Set.Icc a b) := by
  have hneg : MonotoneOn (deriv (fun u => -F u)) (Set.Icc a b) := by
    intro u hu v hv huv
    change deriv (-F) u ≤ deriv (-F) v
    rw [(hd u hu).hasDerivAt.neg.deriv, (hd v hv).hasDerivAt.neg.deriv]
    exact neg_le_neg (hm hu hv huv)
  have hc := (continuousOn_deriv_of_monotone (fun u hu => (hd u hu).neg) hneg).neg
  apply hc.congr
  intro u hu
  change deriv F u = -deriv (-F) u
  rw [(hd u hu).hasDerivAt.neg.deriv, neg_neg]

/-- Published strict derivative conditions and the accepted quotient repairs derive every general Part-II field. -/
theorem secondOrderRegularity_of_source {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hN : (N : ℝ) < deriv f b)
    (hfa : StrictAntiOn (deriv f) (Set.Icc a b))
    (hgd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ g u)
    (hgdc : ContinuousOn (deriv g) (Set.Icc a b))
    (hgp : ∀ u ∈ Set.Icc a b, 0 < g u) (hga : AntitoneOn g (Set.Icc a b))
    (hgda : AntitoneOn (fun u => |deriv g u|) (Set.Icc a b))
    (hgdq : AntitoneOn (fun u => |deriv g u| / (1 + deriv f u - N)) (Set.Icc a b))
    (hf2p : ∀ u ∈ Set.Icc a b, 0 < |deriv (deriv f) u|)
    (hf2a : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hg2p : ∀ u ∈ Set.Icc a b, 0 < deriv (deriv g) u)
    (hg2a : AntitoneOn (deriv (deriv g)) (Set.Icc a b))
    (hq : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv h u| /
        ((ν : ℝ) + deriv f u - N) ^ 2) (Set.Icc a b))
    (hc : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |h u * deriv (deriv f) u| /
        ((ν : ℝ) + deriv f u - N) ^ 3) (Set.Icc a b)) :
    SecondOrderRegularity (phaseShift f N) g a b := by
  have hfdd (u : ℝ) (hu : u ∈ Set.Icc a b) : DifferentiableAt ℝ (deriv f) u :=
    differentiableAt_of_deriv_ne_zero (abs_pos.mp (hf2p u hu))
  have hgdd (u : ℝ) (hu : u ∈ Set.Icc a b) : DifferentiableAt ℝ (deriv g) u :=
    differentiableAt_of_deriv_ne_zero (ne_of_gt (hg2p u hu))
  have hfn (u : ℝ) (hu : u ∈ Set.Icc a b) : deriv (deriv f) u ≤ 0 :=
    deriv_nonpos_of_antitone_Icc hab hfa.antitoneOn hu (hfdd u hu)
  have hm : MonotoneOn (deriv (deriv f)) (Set.Icc a b) := by
    intro u hu v hv huv
    have hh := hf2a hu hv huv
    dsimp only at hh
    rw [abs_of_nonpos (hfn u hu), abs_of_nonpos (hfn v hv)] at hh
    linarith
  apply secondOrderRegularity_shift_of_inputs
    (partIRegularityAt_of_source_hypotheses hab hfd hfc hN hfa hgd hgdc hgp hga hgda hgdq)
    hfdd (continuousOn_deriv_of_monotone hfdd hm)
    hgdd (continuousOn_deriv_of_antitone hgdd hg2a) hf2a
    (fun u hu => (hg2p u hu).le) hg2a
  · intro h hh n
    simpa only [Nat.cast_add, Nat.cast_one] using hq h hh (n + 1) (by omega)
  · intro h hh n
    simpa only [Nat.cast_add, Nat.cast_one] using hc h hh (n + 1) (by omega)

/-- The corrected general Part-II theorem exposes every published analytic input and accepted repair. -/
theorem corrected_poisson_partII {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hN : (N : ℝ) < deriv f b)
    (hfa : StrictAntiOn (deriv f) (Set.Icc a b))
    (hgd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ g u)
    (hgdc : ContinuousOn (deriv g) (Set.Icc a b))
    (hgp : ∀ u ∈ Set.Icc a b, 0 < g u) (hga : AntitoneOn g (Set.Icc a b))
    (hgda : AntitoneOn (fun u => |deriv g u|) (Set.Icc a b))
    (hgdq : AntitoneOn (fun u => |deriv g u| / (1 + deriv f u - N)) (Set.Icc a b))
    (hf2p : ∀ u ∈ Set.Icc a b, 0 < |deriv (deriv f) u|)
    (hf2a : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hg2p : ∀ u ∈ Set.Icc a b, 0 < deriv (deriv g) u)
    (hg2a : AntitoneOn (deriv (deriv g)) (Set.Icc a b))
    (hq : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv h u| /
        ((ν : ℝ) + deriv f u - N) ^ 2) (Set.Icc a b))
    (hc : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |h u * deriv (deriv f) u| /
        ((ν : ℝ) + deriv f u - N) ^ 3) (Set.Icc a b)) :
    let F := phaseShift f N
    let y := deriv f a - N
    let M := ⌊deriv f a⌋₊ - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, (g (n : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊, ∫ u in a..b, (g u : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (g b * poissonEndpointMajorant b y + g a * poissonEndpointMajorant a y) / (2 * Real.pi) +
      ‖poissonBoundary F g a b‖ +
      (secondH F g b * secondTailMajorant M b (deriv f b - N) +
        secondH F g a * secondTailMajorant M a y) / (4 * Real.pi ^ 2) +
      (secondH1 F g a * partIISquareTailEnvelope y +
        secondH F g a * |deriv (deriv f) a| * partIICubeCoefficient y) /
          (4 * Real.pi ^ 3 * y) := by
  have r := partIRegularityAt_of_source_hypotheses hab hfd hfc hN hfa hgd hgdc hgp hga hgda hgdq
  have rr := secondOrderRegularity_of_source hab hfd hfc hN hfa hgd hgdc hgp hga hgda hgdq hf2p hf2a hg2p hg2a hq hc
  have ha := Set.left_mem_Icc.mpr hab.le
  have hb := Set.right_mem_Icc.mpr hab.le
  have hd := deriv_phaseShift N (hfd a ha)
  have hdb := deriv_phaseShift N (hfd b hb)
  have hdd := deriv_deriv_phaseShift N
    (differentiableAt_of_deriv_ne_zero (abs_pos.mp (hf2p a ha)))
    (ne_of_gt ((Nat.cast_nonneg (α := ℝ) N).trans_lt (r.deriv_gt ha)))
  have ht := second_poisson_shifted_bound r rr
  rw [secondPoissonError_eq_envelope (rr.f_deriv_pos a ha)] at ht
  simpa only [weightedWave, hd, hdb, hdd, Nat.floor_sub_natCast] using ht

/-- The corrected weighted half-integer theorem preserves every positive gap and exposes its full endpoint factor. -/
theorem corrected_poisson_partII_half_integer {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hN : (N : ℝ) < deriv f b)
    (hfa : StrictAntiOn (deriv f) (Set.Icc a b))
    (hgd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ g u)
    (hgdc : ContinuousOn (deriv g) (Set.Icc a b))
    (hgp : ∀ u ∈ Set.Icc a b, 0 < g u) (hga : AntitoneOn g (Set.Icc a b))
    (hgda : AntitoneOn (fun u => |deriv g u|) (Set.Icc a b))
    (hgdq : AntitoneOn (fun u => |deriv g u| / (1 + deriv f u - N)) (Set.Icc a b))
    (hf2p : ∀ u ∈ Set.Icc a b, 0 < |deriv (deriv f) u|)
    (hf2a : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hg2p : ∀ u ∈ Set.Icc a b, 0 < deriv (deriv g) u)
    (hg2a : AntitoneOn (deriv (deriv g)) (Set.Icc a b))
    (hq : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv h u| /
        ((ν : ℝ) + deriv f u - N) ^ 2) (Set.Icc a b))
    (hc : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |h u * deriv (deriv f) u| /
        ((ν : ℝ) + deriv f u - N) ^ 3) (Set.Icc a b))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    let F := phaseShift f N
    let y := deriv f a - N
    let M := ⌊deriv f a⌋₊ - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, (g (n : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊, ∫ u in a..b, (g u : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / y) +
      secondH F g b / (4 * Real.pi ^ 2) * halfSecondEndpointDelta M (deriv f b - N) +
      secondH F g a / (4 * Real.pi ^ 2) * halfSecondEndpointDelta M y +
      (secondH1 F g a * partIISquareTailEnvelope y +
        secondH F g a * |deriv (deriv f) a| * partIICubeCoefficient y) /
          (4 * Real.pi ^ 3 * y) := by
  have r := partIRegularityAt_of_source_hypotheses hab hfd hfc hN hfa hgd hgdc hgp hga hgda hgdq
  have rr := secondOrderRegularity_of_source hab hfd hfc hN hfa hgd hgdc hgp hga hgda hgdq hf2p hf2a hg2p hg2a hq hc
  have ha := Set.left_mem_Icc.mpr hab.le
  have hb := Set.right_mem_Icc.mpr hab.le
  have hd := deriv_phaseShift N (hfd a ha)
  have hdb := deriv_phaseShift N (hfd b hb)
  have hdd := deriv_deriv_phaseShift N
    (differentiableAt_of_deriv_ne_zero (abs_pos.mp (hf2p a ha)))
    (ne_of_gt ((Nat.cast_nonneg (α := ℝ) N).trans_lt (r.deriv_gt ha)))
  have ht := second_poisson_shifted_delta r rr hah hbh
  dsimp only at ht ⊢
  have hy : 0 < deriv f a - N := sub_pos.mpr (r.deriv_gt ha)
  have hsq := squareBounds_eq_proposed_envelope hy
  have hcu := cubeBounds_eq_source_coefficient hy
  rw [Nat.floor_sub_natCast] at hsq hcu
  rw [hsq, hcu, hdd] at ht
  simp only [weightedWave] at ht
  apply ht.trans_eq
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Constant weight derives all regularity fields from explicit phase conditions, including endpoint continuity. -/
theorem constant_secondOrderRegularity_source {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hpos : 0 < deriv f b)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hfdd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hanti : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hq : ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv (deriv f) u| /
      ((ν : ℝ) + deriv f u) ^ 2) (Set.Icc a b))
    (hr : ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv f u * deriv (deriv f) u| /
      ((ν : ℝ) + deriv f u) ^ 3) (Set.Icc a b)) :
    SecondOrderRegularity f (fun _ => 1) a b := by
  have hn (u : ℝ) (hu : u ∈ Set.Icc a b) : deriv (deriv f) u ≤ 0 :=
    deriv_nonpos_of_antitone_Icc hab hfa hu (hfdd u hu)
  have hm : MonotoneOn (deriv (deriv f)) (Set.Icc a b) := by
    intro u hu v hv huv
    have hh := hanti hu hv huv
    dsimp only at hh
    rw [abs_of_nonpos (hn u hu), abs_of_nonpos (hn v hv)] at hh
    linarith
  apply constant_secondOrderRegularity hab hfd hfc hpos hfa hfdd
    (continuousOn_deriv_of_monotone hfdd hm) hanti
  · intro n
    simpa only [Nat.cast_add, Nat.cast_one] using hq (n + 1) (by omega)
  · intro n
    simpa only [Nat.cast_add, Nat.cast_one] using hr (n + 1) (by omega)

/-- The corrected constant-weight Corollary 0.1 consumes explicit phase inputs and retains the full finite head. -/
theorem corrected_corollary_zero_one_partII {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hpos : 0 < deriv f b)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hfdd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hanti : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hq : ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv (deriv f) u| /
      ((ν : ℝ) + deriv f u) ^ 2) (Set.Icc a b))
    (hr : ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv f u * deriv (deriv f) u| /
      ((ν : ℝ) + deriv f u) ^ 3) (Set.Icc a b))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    let y := deriv f a
    let M := ⌊y⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / y) / Real.pi +
      (deriv f b * halfSecondEndpointDelta M (deriv f b) + y * halfSecondEndpointDelta M y) /
        (2 * Real.pi) +
      |deriv (deriv f) a| / (2 * Real.pi ^ 2) *
        (partIISquareTailEnvelope y / y + partIICubeCoefficient y) := by
  have r := constant_secondOrderRegularity_source hab hfd hfc hpos hfa hfdd hanti hq hr
  have ht := constant_second_poisson_delta r hah hbh
  dsimp only at ht ⊢
  have hy := r.f_deriv_pos a (Set.left_mem_Icc.mpr hab.le)
  rw [squareBounds_eq_proposed_envelope hy, cubeBounds_eq_source_coefficient hy] at ht
  apply ht.trans_eq
  field_simp
  ring

/-- The corrected constant-weight Corollary 0.1 consumes explicit phase inputs and retains the full finite head. -/
theorem corrected_corollary_zero_one_partII_pi {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hpos : 0 < deriv f b)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hfdd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hanti : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hq : ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv (deriv f) u| /
      ((ν : ℝ) + deriv f u) ^ 2) (Set.Icc a b))
    (hr : ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv f u * deriv (deriv f) u| /
      ((ν : ℝ) + deriv f u) ^ 3) (Set.Icc a b))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ (⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a) :
    let y := deriv f a
    let M := ⌊y⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 M, ∫ u in a..b,
        Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      (Real.log 2 + 1 / y) / Real.pi +
      (deriv f b * halfSecondEndpointBound M (deriv f b) + y * halfSecondEndpointBound M y) /
        (2 * Real.pi) +
      |deriv (deriv f) a| / (2 * Real.pi ^ 2) *
        (partIISquareTailEnvelope y / y + partIICubeCoefficient y) := by
  have r := constant_secondOrderRegularity_source hab hfd hfc hpos hfa hfdd hanti hq hr
  have ht := constant_second_poisson_half r hah hbh hδ
  dsimp only at ht ⊢
  have hy := r.f_deriv_pos a (Set.left_mem_Icc.mpr hab.le)
  rw [squareBounds_eq_proposed_envelope hy, cubeBounds_eq_source_coefficient hy] at ht
  apply ht.trans_eq
  field_simp
  ring

/-- Corrected Corollary 8.1 at the exact half gap follows from the fully explicit accepted source inputs. -/
theorem corrected_corollary_eight_one {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hab : a < b) (hfd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hN : (N : ℝ) < deriv f b)
    (hfa : StrictAntiOn (deriv f) (Set.Icc a b))
    (hgd : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ g u)
    (hgdc : ContinuousOn (deriv g) (Set.Icc a b))
    (hgp : ∀ u ∈ Set.Icc a b, 0 < g u) (hga : AntitoneOn g (Set.Icc a b))
    (hgda : AntitoneOn (fun u => |deriv g u|) (Set.Icc a b))
    (hgdq : AntitoneOn (fun u => |deriv g u| / (1 + deriv f u - N)) (Set.Icc a b))
    (hf2p : ∀ u ∈ Set.Icc a b, 0 < |deriv (deriv f) u|)
    (hf2a : AntitoneOn (fun u => |deriv (deriv f) u|) (Set.Icc a b))
    (hg2p : ∀ u ∈ Set.Icc a b, 0 < deriv (deriv g) u)
    (hg2a : AntitoneOn (deriv (deriv g)) (Set.Icc a b))
    (hq : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |deriv h u| /
        ((ν : ℝ) + deriv f u - N) ^ 2) (Set.Icc a b))
    (hc : ∀ h : ℝ → ℝ, (h = deriv g ∨ h = fun u => g u * (deriv f u - N)) →
      ∀ ν : ℕ, 0 < ν → AntitoneOn (fun u => |h u * deriv (deriv f) u| /
        ((ν : ℝ) + deriv f u - N) ^ 3) (Set.Icc a b))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 - Int.fract (deriv f a) = 1 / 2) :
    let F := phaseShift f N
    let y := deriv f a - N
    let z := deriv f b - N
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ u in a..b, (g u : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f u - (ν : ℝ) * u : ℝ) : ℂ))‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / y) +
      secondH F g b / (4 * Real.pi ^ 2) *
        ((1 / z) * (Real.pi / 2 + 1 / (y + 1 / 2) + Real.log 2 + 3 / (2 * (z + 1)))) +
      secondH F g a / (4 * Real.pi ^ 2) *
        ((1 / y) * (Real.pi / 2 + 1 / (y + 1 / 2) + Real.log 2 + 3 / (2 * (y + 1)))) +
      secondH1 F g a / (4 * Real.pi ^ 3) *
        ((46 / 9) / y + (Real.log (y + 1) - Real.log (y + 1 / 2) + 1 / (y + 1 / 2) -
          2 * Real.log 2 - (1 + 2 * y) / (2 * (y + 1))) / y ^ 2) +
      (secondH F g a * |deriv (deriv F) a| / (4 * Real.pi ^ 3)) *
        ((230 / 27) / y - (14 / 3) / y ^ 2 +
          (Real.log (y + 1 / 2) + Real.log (y + 1) + 2 * Real.log 2 +
            2 * Real.eulerMascheroniConstant - 1 / (2 * (y + 1 / 2)) -
            (1 + 3 * y + 3 * y ^ 2) / (2 * (y + 1) ^ 2)) / y ^ 3) := by
  exact second_poisson_shifted_exact_half
    (partIRegularityAt_of_source_hypotheses hab hfd hfc hN hfa hgd hgdc hgp hga hgda hgdq)
    (secondOrderRegularity_of_source hab hfd hfc hN hfa hgd hgdc hgp hga hgda hgdq
      hf2p hf2a hg2p hg2a hq hc) hah hbh hδ

end DhimanKadiriQuesadaHerrera2026

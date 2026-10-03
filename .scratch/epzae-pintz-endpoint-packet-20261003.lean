import TaoTrudgianYang2025.LiteratureDensity

/-! Actual analytic consumers of the endpoint packet, not density endpoint proofs. -/
noncomputable section
open TaoTrudgianYang2025

example {n : ℕ} (hn : 6 ≤ n) {τ : ℝ}
    (hτlo : 2 ≤ τ) (hτhi : τ < 4*((n:ℝ)-1)/3) :
    zetaLargeValueExponent (1-1/(2*(n:ℝ)*((n:ℝ)-1))) τ = ⊥ :=
  zetaLargeValueExponent_eq_bot_pintz_tail_endpoint hn hτlo hτhi

example : zetaLargeValueExponent (59/60) 2 = ⊥ := by
  have hh := zetaLargeValueExponent_eq_bot_pintz_tail_endpoint
    (n:=6) (τ:=2) (by omega) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

example : zetaLargeValueExponent (59/60) 6 = ⊥ := by
  have hh := zetaLargeValueExponent_eq_bot_pintz_tail_endpoint
    (n:=6) (τ:=6) (by omega) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

example : zetaLargeValueExponent (83/84) 7 = ⊥ := by
  have hh := zetaLargeValueExponent_eq_bot_pintz_tail_endpoint
    (n:=7) (τ:=7) (by omega) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

example : zetaLargeValueExponent (111/112) 9 = ⊥ := by
  have hh := zetaLargeValueExponent_eq_bot_pintz_tail_endpoint
    (n:=8) (τ:=9) (by omega) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

example {τ : ℝ} (hτlo : 2 ≤ τ) (hτhi : τ < 21/4) :
    zetaLargeValueExponent (39/40) τ = ⊥ :=
  zetaLargeValueExponent_eq_bot_pintz_first_endpoint hτlo hτhi

example : zetaLargeValueExponent (39/40) 2 = ⊥ :=
  zetaLargeValueExponent_eq_bot_pintz_first_endpoint (by norm_num) (by norm_num)

example : zetaLargeValueExponent (39/40) 5 = ⊥ :=
  zetaLargeValueExponent_eq_bot_pintz_first_endpoint (by norm_num) (by norm_num)

example {τ : ℝ} (hτlo : 21/8 ≤ τ) (hτhi : τ < 17/5) :
    largeValueExponent (39/40) τ ≤ ((2*τ/105:ℝ):EReal) :=
  largeValueExponent_le_pintz_first_endpoint_lower hτlo hτhi

example : largeValueExponent (39/40) (21/8) ≤ ((1/20:ℝ):EReal) := by
  have hh := largeValueExponent_le_pintz_first_endpoint_lower
    (τ:=21/8) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

example : largeValueExponent (39/40) 3 ≤ ((2/35:ℝ):EReal) := by
  have hh := largeValueExponent_le_pintz_first_endpoint_lower
    (τ:=3) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

example {τ : ℝ} (hτlo : 170/63 ≤ τ) (hτhi : τ ≤ 85/21) :
    largeValueExponent (41/42) τ ≤ ((3*τ/170:ℝ):EReal) :=
  largeValueExponent_le_pintz_second_endpoint_general hτlo hτhi

example : largeValueExponent (41/42) (170/63) ≤ ((1/21:ℝ):EReal) := by
  have hh := largeValueExponent_le_pintz_second_endpoint_general
    (τ:=170/63) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

example : largeValueExponent (41/42) (169/42) ≤ ((169/2380:ℝ):EReal) := by
  have hh := largeValueExponent_le_pintz_second_endpoint_general
    (τ:=169/42) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

example : largeValueExponent (41/42) (85/21) ≤ ((1/14:ℝ):EReal) := by
  have hh := largeValueExponent_le_pintz_second_endpoint_general
    (τ:=85/21) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

example {τ : ℝ} (hτlo : 2 ≤ τ) (hτhi : τ < 37/7) :
    zetaLargeValueExponent (41/42) τ = ⊥ :=
  zetaLargeValueExponent_eq_bot_pintz_second_endpoint_lower hτlo hτhi

example : zetaLargeValueExponent (41/42) 2 = ⊥ :=
  zetaLargeValueExponent_eq_bot_pintz_second_endpoint_lower (by norm_num) (by norm_num)

example : zetaLargeValueExponent (41/42) 5 = ⊥ :=
  zetaLargeValueExponent_eq_bot_pintz_second_endpoint_lower (by norm_num) (by norm_num)

example {n : ℕ} (hn : 6 ≤ n) {τ : ℝ}
    (hτlo : 2*((n:ℝ)-1)/3 ≤ τ) (hτhi : τ < (n:ℝ)-2+2/(n:ℝ)) :
    largeValueExponent (1-1/(2*(n:ℝ)*((n:ℝ)-1))) τ ≤
      ((3*τ/(2*(n:ℝ)*((n:ℝ)-1)^2):ℝ):EReal) :=
  largeValueExponent_le_pintz_tail_endpoint_lower hn hτlo hτhi

example : largeValueExponent (59/60) (10/3) ≤ ((1/30:ℝ):EReal) := by
  have hh := largeValueExponent_le_pintz_tail_endpoint_lower
    (n:=6) (τ:=10/3) (by omega) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

example : largeValueExponent (59/60) 4 ≤ ((1/25:ℝ):EReal) := by
  have hh := largeValueExponent_le_pintz_tail_endpoint_lower
    (n:=6) (τ:=4) (by omega) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

example : largeValueExponent (83/84) 4 ≤ ((1/42:ℝ):EReal) := by
  have hh := largeValueExponent_le_pintz_tail_endpoint_lower
    (n:=7) (τ:=4) (by omega) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

example : largeValueExponent (111/112) 5 ≤ ((15/784:ℝ):EReal) := by
  have hh := largeValueExponent_le_pintz_tail_endpoint_lower
    (n:=8) (τ:=5) (by omega) (by norm_num) (by norm_num)
  norm_num at hh
  exact hh

example (P : LargeValuePattern) :
    PintzEndpointGram.alignedOffDiagonal P =
      let c := fun t => RiemannZeta.GuthMaynard.phaseAlign
        (∑ n ∈ P.indices,P.coeff n*dirichletPhase n t)
      ∑ t ∈ P.ordinates,∑ u ∈ P.ordinates,
        if t = u then 0 else
          star (c t)*c u*(∑ n ∈ P.indices,dirichletPhase n (u-t)) := rfl

example (P : LargeValuePattern) :
    ((P.ordinates.card:ℝ)*P.V)^2 ≤
      4*P.N^2*(P.ordinates.card:ℝ)+2*P.N*(PintzEndpointGram.alignedOffDiagonal P).re :=
  PintzEndpointGram.retained_gram P

example (P : ZetaLargeValuePattern) :
    ((P.ordinates.card:ℝ)*P.V)^2 ≤
      4*P.N^2*(P.ordinates.card:ℝ)+
        2*P.N*(PintzEndpointGram.alignedOffDiagonal P.toLargeValuePattern).re :=
  PintzEndpointGram.retained_gram P.toLargeValuePattern

#print axioms largeValueExponent_le_pintz_tail_endpoint_lower
#print axioms PintzEndpointGram.alignedOffDiagonal
#print axioms PintzEndpointGram.retained_gram
#print axioms zetaLargeValueExponent_eq_bot_pintz_tail_endpoint
#print axioms zetaLargeValueExponent_eq_bot_pintz_first_endpoint
#print axioms largeValueExponent_le_pintz_first_endpoint_lower
#print axioms largeValueExponent_le_pintz_second_endpoint_general
#print axioms zetaLargeValueExponent_eq_bot_pintz_second_endpoint_lower

import GafniTao.WooleyWeightedMean
#check ZMod.castHom
#check ZMod.castHom_surjective
#check AddMonoidHom.card_fiber_eq_of_mem_range
#check Fintype.card_congr
#check ZMod.cast_natCast
#check mul_le_mul_left
#check (mul_le_mul_left₀)
#check (mul_le_mul_left_iff_of_pos)
#check mul_le_mul_left'
#check (mul_le_mul_left_iff₀)
#check (mul_le_mul_left_iff_of_pos)
#check lt_of_mul_lt_mul_left
#check le_of_mul_le_mul_left
example {p a b n : ℕ} [NeZero p] (hab : a ≤ b) :
    ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) (n : ZMod (p ^ b)) =
      (n : ZMod (p ^ a)) := by simp
#check ZMod.card
#check Nat.card_zmod
#check pow_dvd_pow
#check Nat.pow_sub_mul_pow
#check Nat.pow_sub_mul_pow
#check Finset.card_filter
#check Fintype.card_congr
#check Fintype.card_congr
#check Fintype.card_congr
#check Fintype.card_eq_sum_card_fiberwise
#check Finset.card_eq_sum_card_fiberwise
#check Fintype.card_congr
#check Fintype.card_prod
#check Fintype.card_congr
#check Fintype.card_congr
#check Fintype.card_congr

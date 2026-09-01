opaque testOpaque : Nat := 3

#check testOpaque.eq_def
#check testOpaque

example : testOpaque = 3 := by
  rw [testOpaque.eq_def]

@[simp] theorem takeWhile_nil : [].takeWhile f = [] := rfl

@[simp] theorem transitive_le_succ : a <= b -> b <= b + 1 -> a <= b + 1 := by
    apply Nat.le_trans

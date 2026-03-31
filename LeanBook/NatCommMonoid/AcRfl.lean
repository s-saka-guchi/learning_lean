import LeanBook.NatCommMonoid.Simp

/-- 加算の交換法則 -/
theorem MyNat.add_comm (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    simp [MyNat.ctor_eq_zero]
  | succ n' ih =>
    simp [ih]

/-- 加算の結合法則 -/
-- l + m + nと書くと(l + m) + nと解釈されることに注意
theorem MyNat.add_assoc (l m n : MyNat) : l + m + n = l + (m + n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp [ih]

-- 交換法則と結合法則の利用例
example (l m n : MyNat) : l + m + n + 3 = m + (l + n) + 3 := calc
  _ = m + l + n + 3 := by rw [MyNat.add_comm l m]
  _ = m + (l + n) + 3 := by rw [MyNat.add_assoc m l n]

-- 使う定理と引数を明示的に指定しないといけない。これは手間。
-- 成り立つことがわかっていれば自動で適用することができるタクティクとして、ac_rflがある。

-- 演算が交換法則を満たすことを事前に登録する
instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := MyNat.add_comm

-- 演算が結合法則を満たすことを事前に登録する
instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := MyNat.add_assoc

-- ac_rflを使うと、交換法則と結合法則を自動で適用して証明できる
example (l m n : MyNat) : l + m + n + 3 = m + (l + n) + 3 := by
  ac_rfl

--practice 4.4.3
example (l m n : MyNat) : l + (1 + m) + n = m + (l + n) + 1 := by
  ac_rfl

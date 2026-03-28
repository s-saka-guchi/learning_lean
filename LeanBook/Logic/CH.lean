-- 3.6 カリー・ハワード同型対応
/-- 1 + 1 = 2 という命題の証明 -/
theorem one_add_one_eq_two : 1 + 1 = 2 := by
  rfl

#check one_add_one_eq_two
#check 1
#check 1.2
#check "hello"
#check (by rfl : 1 + 1 = 2)

-- hは「Pの証明項hpを受け取ってQの証明を返す関数」である
-- c.f. 関数f : A → Bがあって項a : Aがあれば、f a の型がBになるのと同様
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

-- タクティクの正体は、「与えられた型の項を構成するツール」である
/-- Nat上の恒等関数 -/
def idOnNat : Nat → Nat := by?
  intro n
  exact n

#eval idOnNat 5

/-- practice 3.6.4 -/
example (P Q : Prop) (hp : P) : Q → P :=
  fun _hq => hp

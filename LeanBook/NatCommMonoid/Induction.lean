import LeanBook.NatCommMonoid.TypeClass

-- MyNatに対して n + 0 = n を示す
example (n : MyNat) : n + 0 = n := by
  rfl

-- MyNatに対して 0 + n = n を示す
-- rfl では示すことができない
-- example (n : MyNat) : 0 + n = n := by
--   rfl

#reduce fun (n : MyNat) => n + 0

#reduce fun (n : MyNat) => 0 + n

-- rwタクティクの利用例
/-- 0を右から足しても変わらない -/
theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by
  rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [MyNat.add_zero]

/-- add_zeroの逆バージョン -/
theorem MyNat.add_zero_rev (n : MyNat) : n = n + 0 := by
  rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [← MyNat.add_zero_rev]

-- ローカルコンテクストの仮定を書き換える
example (m n : MyNat) (h : m + 0 = n) : n + m = m + n := by
  rw [MyNat.add_zero] at h

  rw [h]

/-- .succを外に出す -/
theorem MyNat.add_succ (m n : MyNat) : m + .succ n = .succ (m + n) := by
  rfl

-- 0 + n = nの証明は帰納法を用いる
-- infoviewにおける表示を制御する設定
set_option pp.fieldNotation.generalized false in

theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  -- nについての帰納法
  induction n with

  -- n = 0の場合
  | zero =>
    -- ゴールの形
    guard_target =ₛ 0 + MyNat.zero = MyNat.zero

    -- 変数がないのでrflで証明可能
    rfl

  -- n = succ n'の場合
  | succ n' ih =>
    -- ゴールの形
    guard_target =ₛ 0 + MyNat.succ n' = MyNat.succ n'

    -- 帰納法の仮定ihが手に入る
    guard_hyp ih : 0 + n' = n'

    rw [MyNat.add_succ]
    rw [ih]


-- infoviewの設定を再び変更
set_option pp.fieldNotation.generalized false in

/-- practice 4.2.6 -/
example (n : MyNat) : 1 + n = .succ n := by
  induction n with

  | zero =>
    guard_target =ₛ 1 + MyNat.zero = MyNat.succ MyNat.zero

    rfl

  | succ n' ih =>

    guard_target =ₛ 1 + MyNat.succ n' = MyNat.succ (MyNat.succ n')

    guard_hyp ih : 1 + n' = MyNat.succ n'

    rw [MyNat.add_succ]
    rw [ih]

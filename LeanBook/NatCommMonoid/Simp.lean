import LeanBook.NatCommMonoid.Induction

--式をより簡単な形に自動で変形する単純化をする
example (n : MyNat) : 0 + (n + 0) = n := by
  -- 最初はsimpで証明できない
  -- fail_if_success は、後続するタクティクが失敗することを検証する
  fail_if_success simp

  -- 明示的にrwで証明する
  rw [MyNat.add_zero, MyNat.zero_add]

-- 証明済の命題に[simp]属性をつけておくと、後で証明に使うことができる
attribute [simp] MyNat.add_zero MyNat.zero_add

example (n : MyNat) : 0 + (n + 0) = n := by
  simp

-- attribute [simp]を付与する以外にも、手動で命題をsimpタクティクに渡すことも可能
theorem MyNat.ctor_eq_zero : MyNat.zero = 0 := by
  rfl

example : MyNat.zero = 0 := by

  fail_if_success simp

  simp [MyNat.ctor_eq_zero]

-- 前節で証明したMyNat.add_succ も[simp]属性を与えておく
attribute [simp] MyNat.add_succ

-- simpを仮定に適用することもできる。at構文で指定する
example (m n : MyNat) (h : m + n + 0 = n + m) : m + n = n + m := by
  simp at h

  guard_hyp h : m + n = n + m

  rw [h]

-- ゴールと仮定の両方を同時に単純化することもできる
example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp at *

  guard_hyp h : m = n
  guard_target =ₛ m = n

  rw[h]

-- 全ての仮定とゴールをこれ以上単純化できなくなるまで単純化するsimp_allタクティク
example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by

  fail_if_success rfl

  simp_all

-- theoremで命題を証明した時点で、simpにより自動的に適用するように登録するタグ
@[simp] theorem MyNat.succ_add (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp [ih]

-- simpによる書き換えにおいて、何が使われたのかを明示的に確認したい場合はsimp?とする
example (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp? [ih]

-- calcによる途中経過表示
example (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n' ih => calc
    _ = (m.succ + n').succ := by rw [MyNat.add_succ]
    _ = (m + n').succ.succ := by rw [MyNat.succ_add]
    _ = (m + n'.succ).succ := by rw [MyNat.add_succ]
    -- つぎつぎに左辺を書き換える形でゴールを変更していき、最終的に左辺と右辺が同じになるようにする

-- calcによる途中経過表示の例その2
example (n : MyNat) : 1 + n = n + 1 := calc
  _ = .succ 0 + n := by rfl
  _ = .succ (0 + n) := by rw [MyNat.succ_add]
  _ = .succ n := by rw [MyNat.zero_add]
  _ = n + 1 := by rfl

-- practice 4.3.7
example (n : MyNat) : n + 2 = 2 + n := calc
  _ = n + .succ (.succ 0) := by rfl
  _ = (n + .succ 0).succ := by rw [MyNat.add_succ]
  _ = (n + 0).succ.succ := by rw [MyNat.add_succ]
  _ = (n).succ.succ := by rfl
  _ = (0 + n).succ.succ := by rw [MyNat.zero_add]
  _ = (.succ 0 + n).succ := by rw [MyNat.succ_add]
  _ = (1 + n).succ := by rfl
  _ = .succ 1 + n := by rw [MyNat.succ_add]
  _ = 2 + n := by rfl

-- practice 4.3.7
example (n : MyNat) : n + 2 = 2 + n := by
  induction n with
  | zero => rfl
  | succ n' ih => simp [ih]

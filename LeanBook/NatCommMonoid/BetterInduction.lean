import LeanBook.NatCommMonoid.AcRfl

-- 問題意識：帰納法で記法が崩れてしまう。
-- +記号や数値リテラルを使えるようにしたのに、inductionタクティクを実行した時点でMyNat.zeroやMyNat.succが現れてしまう

example (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    -- ゴールにMyNat.zeroが現れてしまう
    -- m + 0 = 0 + m の形になってほしい。（数値リテラルをつかえるようにしたのだから。）
    -- 途中でctor_eq_zeroを使ってMyNat.zeroを0に変換する必要も生じてしまっている。
    guard_target =ₛ m + MyNat.zero = MyNat.zero + m
    simp [MyNat.ctor_eq_zero]

  | succ n' ih =>
    -- ゴールにMyNat.succが現れてしまう
    -- m + (n' + 1) = (n' + 1) + m の形になってほしい。
    guard_target =ₛ m + MyNat.succ n' = MyNat.succ n' + m

    simp [ih]

-- MyNat.recとは、MyNat用の帰納法の原理を示す。
#check MyNat.rec

-- したがって、帰納法の原理を以下のように書き直せばよい。
/-- MyNatの帰納法の原理を書き直したもの -/
def MyNat.recAux.{u} (motive : MyNat → Sort u)
  (zero: motive 0)
  (succ : (n : MyNat) → motive n → motive (n + 1)) (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux motive zero succ n)

-- この.recAuxを.recの代わりにinductionタクティクに使用させる
attribute [induction_eliminator] MyNat.recAux

-- 改めて同じ証明を行う
example (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    guard_target =ₛ m + 0 = 0 + m
    simp

  | succ n' ih =>
    guard_target =ₛ m + (n' + 1) = (n' + 1) + m
    ac_rfl

-- practice 4.5.4
/-- 「ひとつ前」の自然数を返す関数。ゼロに対してはゼロを返すことに注意。-/
private def MyNat.pred (n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => n

example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  induction n with
  | zero =>
    guard_target =ₛ MyNat.pred (MyNat.pred 0 + 1) = MyNat.pred 0

    rfl
  | succ n' ih =>
    guard_target =ₛ MyNat.pred (MyNat.pred (n' + 1) + 1) = MyNat.pred (n' + 1)
    ac_rfl

private theorem MyNat.pred_add_one (n : MyNat) : MyNat.pred (n + 1) = n := by
  rfl

example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  rw [MyNat.pred_add_one]

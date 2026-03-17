/-- 自前で実装した自然数 -/
inductive MyNat where
  /-- 0-/
  | zero
  /-- 後続の自然数 -/
  | succ (n : MyNat)

#check MyNat.zero
#check MyNat.succ

#check MyNat.succ .zero

/-- 自前で定義した1 -/
def MyNat.one : MyNat := MyNat.succ .zero

/-- 自前で定義した2 -/
def MyNat.two : MyNat := MyNat.succ .one

/-- MyNat同士の加法 -/
def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | MyNat.zero => m
  | MyNat.succ n' => MyNat.succ (MyNat.add m n')

#check MyNat.add .one .one = .two

-- #reduce コマンドの結果表示をカスタマイズするための設定
set_option pp.fieldNotation.generalized false

#reduce MyNat.add .one .one
#reduce MyNat.two

/-- 1 + 1 = 2 のMyNatにおける照明 -/
example : MyNat.add .one .one = .two := by
  rfl

/-- 0を右から足しても値は変わらない -/
example (n : MyNat): MyNat.add n .zero = n := by
  rfl

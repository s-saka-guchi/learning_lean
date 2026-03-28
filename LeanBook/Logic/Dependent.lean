-- 3.7 依存型
#check Nat.add_zero
#check Nat.add_zero 0
#check Nat.add_zero 43
#check (Nat.add_zero : (n : Nat) → n + 0 = n)

-- exampleとは「命題に名前を付けずに証明する」コマンドである、としたが、
-- 実際には、証明に限らず「型の具体的な値かどうかを確認する」コマンドとして使える
example : (∀ n : Nat, n + 0 = n) = ((n : Nat) → n + 0 = n) := by
  rfl

-- ∀を依存型として表示させることができるオプション
set_option pp.foralls false in
#check (∀ n : Nat, n + 0 = n)

-- List
example : List Nat := [1, 2, 3]
example : List Nat := [0, 1]
example : List Nat := 1 :: 2 :: 3 :: []

/-- 依存型を使うと、「要素数の情報を含んだ連結リスト」を構成できる -/
inductive Vect (α : Type) : Nat → Type where
  /-- 空のベクトルは長さ0のベクトル -/
  | nil : Vect α 0
  /-- ベクトルv : Vect α nの先頭に要素a : αを追加することで新しいベクトルが得られる -/
  | cons {n : Nat} (a : α) (v : Vect α n) : Vect α (n + 1)

example : Vect Nat 0 := Vect.nil
example : Vect Nat 3 := Vect.cons 1 (Vect.cons 2 (Vect.cons 3 Vect.nil))
example : Vect Nat 1 := Vect.cons 42 Vect.nil

#check Vect.cons 1 (Vect.cons 2 (Vect.cons 3 Vect.nil))
#eval Vect.cons 1 (Vect.cons 2 (Vect.cons 3 Vect.nil))


-- 依存ペア（Dependent Pair）
-- (a, b) : A × Bと似ているが、「bの型がa」のように、bの型がaに依存してもよい
-- (α : Type) × α のよう型は「依存ペア型」と呼ばれる。
example : (α : Type) × α := ⟨Nat, 1⟩
example : (α : Type) × α := ⟨Bool, true⟩
example : (α : Type) × α := ⟨Prop, True⟩

example : List ((α : Type) × α) := [⟨Nat, 1⟩, ⟨Bool, true⟩, ⟨Prop, True⟩ ]

-- practice 3.7.4
example : List ((α : Type) × α ) := [⟨Nat, 42⟩, ⟨Bool, false⟩]
example : {α : Type} → {n : Nat} → (a : α) → (v : Vect α n) → Vect α (n + 1) :=
  fun a v => Vect.cons a v

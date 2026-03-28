-- 公理(axiom)：ほかの定理からは証明できない、真であると仮定する命題

-- 排中律はclassical.emという名前で定義されている
#check Classical.em

-- 依存する公理をすべて出力するコマンド：#print axioms
#print axioms Classical.em

#check Classical.choice

/-- 関数の全射性 -/
-- {}は暗黙引数を表し、関数を呼び出したときにほかの引数の値などの文脈からLeangが自動的に推論
def Surjective {X Y : Type} (f : X → Y) : Prop :=
  ∀ y : Y, ∃ x : X, f x = y

/-- Surjectiveを使用する例：恒等関数は全射である -/
example : Surjective (fun x : Nat => x) := by
  intro y
  exists y

-- fが全射の時、逆向きの対応付けを考えることができる。
-- 「関数f:X→Yをその右逆関数g:Y→Xに変換するような関数inverseが存在する」ことが言える

variable {X Y : Type}

/-- 全射であるような関数f: X → Yに対して、その右逆関数g: Y → Xを返すような高階関数 -/
noncomputable def inverse (f : X → Y) (hf : Surjective f) : Y → X := by
  -- y : Yが任意に与えられたとする
  intro y

  -- fは全射なので {x // f x = y} という集合は空でない
  -- {x // f x = y}という表記は「部分型」(subytype) と呼ばれ、
  --「ある型の要素のうちPという述語が成り立つもの」だけを集めたもの
  have : Nonempty {x // f x = y }:= by
    let ⟨x, hx⟩ := hf y
    exact ⟨⟨x, hx⟩⟩

  -- 選択原理を用いて、f x = y なるx : Xを構成する
  have x := Classical.choice this
  exact x.val

/-- 3.5.4 practice -/
/- 対偶が元の命題と同値であることを認めれば、排中律を使わずに二重否定の除去が導ける -/
theorem double_negation_of_contra_equiv (P : Prop)
  (contra_equiv : ∀ (P Q : Prop), (¬ P → ¬ Q) ↔ (Q → P)) : ¬¬ P → P := by

  have := contra_equiv P True
  rw [show ¬ True ↔ False from by simp] at this
  rw [show (True → P) ↔ P from by simp] at this
  rw [show (¬ P → False) ↔ ¬¬ P from by rfl] at this
  rw [this]
  simp

-- theorem double_negation_of_contra_equiv (P : Prop)
--   (contra_equiv : ∀ (P Q : Prop), (P → Q) ↔ (¬ Q → ¬ P)) : ¬¬ P → P := by

--   -- 対偶の同値性より、¬¬ P ↔ (¬ P → False) ↔ (False → P) ↔ P

--   have := contra_equiv True P
--   rw [show ¬ True ↔ False from by simp] at this
--   rw [show (True → P) ↔ P from by simp] at this
--   rw [show (¬ P → False) ↔ ¬¬ P from by rfl] at this
--   rw [← this]
--   simp

-- Classical.choiceに依存していないことを確認
#print axioms double_negation_of_contra_equiv

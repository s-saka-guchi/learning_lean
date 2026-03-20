-- 命題 (Proposition)
#check Prop

-- これは命題 (proposition) である
#check (1 + 1 = 3 : Prop)

-- これは命題ではなく、命題への関数 = 述語 (predicate) である
#check (fun n => n + 3 = 39 : Nat → Prop)

-- 真である、または偽である命題
#check True
#check False

-- Trueは無条件で証明できる命題
example : True := by
  trivial

-- h : P という前提から、Pを証明する命題
-- hはhypothesisの頭文字を取っている
example (P : Prop) (h : P) : P := by
  exact h

example (P : Prop) (h : P) : P := by
  assumption

/-- 矛盾からは任意の命題が導ける -/
example (h : False) : ∀ x y z n : Nat,
    n ≥ 3 → x ^ n + y ^ n = z ^ n → x * y * z = 0 := by
  trivial

/-- 含意(implication) -/
example (P Q R : Prop) : (P → Q → R) = (P → (Q → R)) := by
  rfl

#eval True → True
#eval True → False
#eval False → True
#eval False → False

/-- モーダスポネンス（三段論法））-/
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  -- P → Q が成り立つので、Qを示すにはPを示せばよい
  apply h

  -- Pが成り立つので、Pを示すことができる
  -- apply hp でも同じことができる
  exact hp

-- あるいは、hを直接適用しても同じことができる
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

/-- intro tactic -/
example (P Q : Prop) (hq : Q) : P → Q := by
  -- P → Q を示したいので、Pを仮定する
  intro hp

  -- Qはすでに仮定されているので、Qを示すことができる
  exact hq


-- 否定 ¬
#eval ¬ True
#eval ¬ False

/-- 否定は含意の特殊な場合 -/
example (P : Prop) : (¬ P) = (P → False) := by
  rfl

/-- Pと¬ Pを同時に仮定すると矛盾する -/
example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  -- ¬ P は P → False と等しいので、Pを示せばよい
  apply hnp
  -- 仮定Pがあるので、証明終了
  exact hp

/-- 対偶が元の命題と同値になることの、片側 -/
example (P Q : Prop) (h : P → ¬ Q) : Q → ¬ P := by
  -- Q → ¬ P を示したいので、Qを仮定する
  intro hq

  -- ¬ P は P → False と等しいので、Pをさらに仮定する
  intro hp

  -- 仮定Pがあるので、証明終了
  exact h hp hq

/-- contradiction tactic -/
-- 矛盾からは任意の命題を導くことができる
example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  contradiction

/-- exfolso tactic -/
-- 矛盾からはなんでも示せることを利用して、ゴールをFalseに変える
example (P Q : Prop) (hnp : ¬ P) (hp : P) : Q := by
  -- 矛盾を示せばよいというゴール設定
  exfalso
  -- 仮定に矛盾があるため証明完了に
  contradiction


-- 同値性 ↔
#eval True ↔ True
#eval True ↔ False
#eval False ↔ True
#eval False ↔ False

/-- constructor tactic -/
example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  -- P → Q を示す
  · exact h1
  -- Q → P を示す
  · exact h2

/-- constructor tactic with intro tactic -/
example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor
  -- まず左から右を示す
  case mp =>
    intro h
    exact h hq

  -- 次に右から左を示す
  case mpr =>
    intro hp hq
    exact hp

/-- using <;> tactic combinator -/
example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  -- <;> は、直前のタクティクで生成されたすべてのゴールに対して、後続のタクティクを適用する
  -- おそらく、mpとmprの両方のゴールに対して、前提となる部分をhとすることができるということ
  constructor <;> intro h

  -- まず左から右を示す
  case mp =>
    exact h hq

  -- 次に右から左を示す
  case mpr =>
    intro hp
    exact h

/-- rw tactic -/
example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  -- h : P ↔ Q なので、PとQは同値である。ゴールをPからQに書き換える
  rw [h]
  -- Qが成り立つので、Qを示すことができる
  exact hq

/-- rw tactic -/
example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  -- h : P ↔ Q なので、PとQは同値である。ゴールをQからPに書き換える
  rw [← h]
  -- Pが成り立つので、Pを示すことができる
  exact hp

/-- 命題外延性 (Propositional Extensionality) -/
example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  rw [h]

-- 論理積 ∧
#eval True ∧ True
#eval True ∧ False
#eval False ∧ True
#eval False ∧ False

/-- constructor tactic for ∧ -/
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  -- Pを示す
  · exact hp
  -- Qを示す
  · exact hq

/-- 無名コンストラクタ -/
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

/-- .left and .right for ∧ -/
example (P Q : Prop) (h : P ∧ Q) : P := by
  -- h : P ∧ Q なので、Pを示すために、hの左側を取り出す
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  -- h : P ∧ Q なので、Qを示すために、hの右側を取り出す
  exact h.right

-- 論理和 ∨
#eval True ∨ True
#eval True ∨ False
#eval False ∨ True
#eval False ∨ False

/-- left and right tactics for ∨ -/
example (P Q : Prop) (hp : P) : P ∨ Q := by
  -- h : P ∨ Q なので、Pを示すために、hの左側を取り出す
  left
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  -- h : P ∨ Q なので、Qを示すために、hの右側を取り出す
  right
  exact hq

/-- cases tactic for ∨ -/
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h with
  -- Pが成り立つ場合
  | inl hp =>
    -- P ∨ Q を示すために、Pを示す
    right
    exact hp
  -- Qが成り立つ場合
  | inr hq =>
    -- P ∨ Q を示すために、Qを示す
    left
    exact hq

/-- cases tactic for ∨ -/
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  -- Pが成り立つ場合
  case inl hp =>
    -- P ∨ Q を示すために、Pを示す
    right
    exact hp
  -- Qが成り立つ場合
  case inr hq =>
    -- P ∨ Q を示すために、Qを示す
    left
    exact hq

/-- practice 3.18 -/
example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro h hp
  cases h with
  -- ¬ Pが成り立つ場合
  | inl hnp =>
    -- Q を示すために、Falseを示す
    exfalso
    -- hnp : ¬ P と hp : P が同時に成り立つので、矛盾が生じる
    contradiction
  | inr hq =>
    -- Qが成り立つので、Qを示すことができる
    exact hq

example (P Q : Prop) : ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q) := by
  constructor
  -- ¬ (P ∨ Q) → (¬ P ∧ ¬ Q) を示す
  case mp =>
    intro h
    -- ¬ P ∧ ¬ Q を示す。¬ Pを示すのと ¬ Q を示すのを分けるためにconstructorで分解
    constructor
    -- ¬ P を示す
    · intro hp
      apply h
      left
      assumption
    -- ¬ Q を示す
    · intro hq
      apply h
      right
      assumption

  -- (¬ P ∧ ¬ Q) → ¬ (P ∨ Q) を示す
  case mpr =>
    intro h
    -- ¬ (P ∨ Q) を示すために、P ∨ Q を仮定して矛盾を導く
    intro hpq
    cases hpq with
    -- Pが成り立つ場合
    | inl hp =>
      -- h : ¬ P ∧ ¬ Q なので、h.left : ¬ P である。矛盾が生じる
      exact h.left hp
    -- Qが成り立つ場合
    | inr hq =>
      -- h : ¬ P ∧ ¬ Q なので、h.right : ¬ Q である。矛盾が生じる
      exact h.right hq

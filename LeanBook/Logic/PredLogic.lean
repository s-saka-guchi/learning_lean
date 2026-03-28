-- Predicate Logic (述語論理)

-- 全称量化
/-- (Leanの標準の)自然数上の述語論理 -/
def P (n : Nat) : Prop := n = n

example : ∀ a : Nat, P a := by
  -- x : Natが任意に与えられたとする
  intro x

  -- Pを展開すれば明らか
  dsimp [P]

/-- 全ての自然数xについてP xが成り立つならば、P 0も成り立つ -/
example (P : Nat → Prop) (h : ∀ x : Nat, P x) : P 0 := by
  -- hは、全ての自然数xについてP xが成り立つことを意味する
  -- したがって、hを0に適用すれば、P 0が成り立つことがわかる
  exact h 0

-- 存在量化
/-- 偶数であることを表す述語 -/
def even (n : Nat) : Prop := ∃ k : Nat, n = k + k

/-- 4は偶数である -/
example : even 4 := by
  -- 4は2 + 2であることを示せば十分である
  exists 2

/- obtainタクティクで、存在が主張されている命題から、存在する値を取り出す -/
example (t : Type) (P Q : t → Prop) (h : ∃ x : t, P x ∧ Q x)
    : ∃ x : t, Q x := by
  -- hから、存在する値を取り出す
  obtain ⟨y, hy⟩ := h

  -- このyが求めるものである
  exists y

  -- なぜなら、yはP y ∧ Q yを満たすからである
  exact hy.right

-- 複数の量化子 人間関係で記述
/-- 人間たちの集合-/
opaque Human : Type

/-- 愛の関係 -/
opaque Love : Human → Human → Prop

-- 専用の中値記法
@[inherit_doc] infix:50 " -♥→ " => Love

/-- 全ての人に愛されているアイドルが存在する -/
def IdolExists : Prop := ∃ idol : Human, ∀ y : Human, y -♥→ idol

/-- 誰にでも好きな人の一人くらいいる -/
def EveryoneLovesSomeone : Prop := ∀ x : Human, ∃ tgt : Human, x -♥→ tgt

/-- 全ての人を愛する博愛主義者が存在する -/
def PhilanExists : Prop := ∃ philan : Human, ∀ h : Human, philan -♥→ h

/-- どんな人も、誰かに愛されている -/
def EveryoneLoved : Prop := ∀ h : Human, ∃ lover : Human, lover -♥→ h

/-- 博愛主義者が存在するならば、すべての人はだれかに愛されている -/
example : PhilanExists → EveryoneLoved := by
  -- 博愛主義者が存在すると仮定する
  intro h

  -- hから、存在する値を取り出す
  obtain ⟨philan, hPhilan⟩ := h

  -- この時、EveryoneLovedを示したい
  -- 定義に沿って示せばよい
  dsimp [EveryoneLoved]

  -- 任意にhuman : Humanが与えられたと仮定する
  intro human

  -- ここで、lover = philanとすれば、philan -♥→ humanが成り立つことがわかる
  exists philan

  -- なぜなら、hPhilanは、任意のh : Humanに対してphilan -♥→ hが成り立つことを意味するからである
  exact hPhilan human

/-- 3.3.4 practice-/
example : IdolExists → EveryoneLovesSomeone := by
  -- IdolExistsを仮定する
  intro h

  -- hから、存在する値を取り出す
  obtain ⟨idol, hIdol⟩ := h

  -- この時、EveryoneLovesSomeoneを示したい
  -- 定義に沿って示せばよいので、定義を展開する
  dsimp [EveryoneLovesSomeone]

  -- 任意にx : Humanが与えられたと仮定する
  intro x

  -- ここで、tgt = idolとすれば、x -♥→ idolが成り立つことがわかる
  exists idol

  -- なぜなら、hIdolは、任意のy : Humanに対してy -♥→ idolが成り立つことを意味するからである
  exact hIdol x

/-- Leanで排中律をつかう 二重否定の除去-/
example (P : Prop) : ¬¬ P → P := by
  -- ¬¬ P と仮定する
  intro hnnp

  -- 排中律より、P ∨ ¬ Pが成り立つ
  by_cases h : P

  -- Pが成り立つ場合は、Pが成り立つので証明終了
  · exact h

  -- ¬ Pが成り立つ場合は、hnnpと矛盾する
  · contradiction

-- 3.4.3 practice
/-- 二重否定の除去 -/
example (P : Prop) : ¬¬ P → P := by
  -- ¬¬ P と仮定する
  intro hnnp

  -- 排中律より、P ∨ ¬ Pが成り立つ
  by_cases h : P

  -- Pが成り立つ場合は、Pが成り立つので証明終了
  · exact h

  -- ¬ Pが成り立つ場合は、hnnpと矛盾する
  · contradiction

/-- ドモルガンの法則 -/
example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor

  -- ¬ (P ∧ Q) → (¬ P ∨ ¬ Q) を示す
  · intro hnpq

    -- 排中律より、P ∨ ¬ Pが成り立つ
    by_cases hp : P
    · right
      intro hq
      exact hnpq ⟨hp, hq⟩
    · left
      exact hp

  -- (¬ P ∨ ¬ Q) → ¬ (P ∧ Q) を示す
  · intro hnp_or_hnq
    intro hpq

    cases hnp_or_hnq with
    | inl hnp =>
      have := hpq.left
      contradiction
    | inr hnq =>
      have := hpq.right
      contradiction

/-- 対偶が元の命題と同値であること -/
example (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  constructor

  -- (P → Q) → (¬ Q → ¬ P) を示す
  · intro hpq
    intro hnq
    intro hp
    have hq := hpq hp
    contradiction

  -- (¬ Q → ¬ P) → (P → Q) を示す
  · intro hnq_hnp
    intro hp
    by_cases hq : Q
    · exact hq
    · have hnp := hnq_hnp hq
      contradiction

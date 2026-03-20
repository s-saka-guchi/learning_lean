-- 3.2 証明を楽にするコツ

-- 3.2.1 haveタクティクでローカルに補題を示す

/-- 3重否定の簡略化 -/
example (P : Prop) : ¬¬¬P → ¬P := by
  -- ¬¬¬ P かつ P と仮定する
  intro hn3p hp

  -- ここで¬¬ Pが成り立つ
  have hn2p : ¬¬P := by
    -- なぜならば、¬Pを仮定したとき
    intro hnp
    -- 仮定のPと矛盾するから
    contradiction

  -- これで¬¬Pが成り立つことがわかったので、仮定の¬¬¬Pと矛盾する
  contradiction

/-- 3重否定の簡略化 2 -/
example (P : Prop) : ¬¬¬P → ¬P := by
  -- ¬¬¬ P かつ P と仮定する
  intro hn3p hp

  -- ここで¬¬ Pが成り立つ
  have : ¬¬P := by
    intro hnp
    contradiction

  -- this : ¬¬Pという仮定が得られている
  guard_hyp this : ¬¬P
  contradiction

-- 3.2.2 sufficesタクティクでゴールを変更する
-- 「～を示せば十分である」に相当する

/-- 排中律の二重否定 -/
example (P : Prop) : ¬¬ (P ∨ ¬ P) := by
  -- ¬ (P ∨ ¬ P) と仮定する
  intro h

  -- ここで、¬ Pを示せば十分である
  suffices hyp : ¬ P from by
  -- なぜなら、¬ Pが成り立つならば、P ∨ ¬Pが成り立つので、
    have : P ∨ ¬P := by
      right
      exact hyp

    -- 最初の仮定と矛盾する
    contradiction

  -- ここまでで、¬ Pを示すことができれば十分であることがわかった

  -- 以下、¬ Pを示す
  guard_target =ₛ ¬ P

  -- Pと仮定し、矛盾を導く
  intro hp

  -- この時、P ∨ ¬Pが成り立つ
  have : P ∨ ¬P := by
    left
    exact hp

  -- これは矛盾である
  contradiction

-- 3.2.3 exact?タクティクでライブラリを検索する
example (P : Prop) : (P → True) ↔ True := by
  exact?

example (P : Prop) : (True → P) ↔ P := by
  exact?

-- 3.2.4 show .. from 構文で一時的な補題を示す
-- haveタクティクのテンポラリ版のようなもの
example (P Q : Prop) (h : ¬ P ↔ Q) : (P → False) ↔ Q := by
  rw [show (P → False) ↔ ¬ P from by rfl]
  rw [h]

-- 3.2.5 practice
example (P : Prop) : ¬ (P ↔ ¬ P) := by
  exact?

example (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro h

  have hnp : ¬ P := by
    intro hp
    have : ¬ P := by
      rw [h] at hp
      exact hp
    contradiction

  have hp : P := by
    rw [← h] at hnp
    exact hnp

  contradiction

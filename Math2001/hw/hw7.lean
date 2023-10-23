import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- Exercise 4 a
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      n^2 ≥ 2^2 := by rel[hn]
      _ > 2 := by ring 
    
-- Exercise 4 b
example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  . intro h
    by_cases hP : P
    . constructor
      . apply hP
      . intro h1
        have h2: P → Q := by 
          intro h2
          apply h1
        apply h h2
    . constructor
      . apply False.elim
        apply h
        intro hp
        by_cases hQ: Q
        . apply hQ
        . contradiction
      . intro h1
        have h2: P → Q := by 
          intro h2
          apply h1
        apply h h2
  . intro h
    obtain ⟨hp,hq ⟩ := h
    intro hpq
    have h3: Q := by apply hpq hp
    contradiction

-- exercise 5 a
example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  intro h1
  use k
  apply And.intro hk (And.intro hk1 hkp)

-- exercise 5 b
example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    apply hp
    apply prime_test
    . apply hp2
    . apply H
  push_neg at H
  apply H
  

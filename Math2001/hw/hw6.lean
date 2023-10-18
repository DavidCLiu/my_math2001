import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use


def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two

-- Problem 4 a
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  . intro h1
    obtain⟨x,h2⟩:= h1
    use x
    have h3 : P x ↔ Q x := by apply h x
    obtain ⟨ h4, h5⟩ := h3 
    have h6 : Q x := by apply h4 h2
    apply h6
  . intro h1
    obtain⟨x,h2⟩:= h1
    use x
    have h3 : P x ↔ Q x := by apply h x
    obtain ⟨ h4, h5⟩ := h3 
    have h6 : P x := by apply h5 h2
    apply h6
    
-- Problem 4 b
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  . intro h
    obtain⟨x,y,h1⟩:= h
    use y
    use x
    apply h1
  . intro h
    obtain⟨y,x,h1⟩:= h
    use x
    use y
    apply h1


-- Problem 4 c

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor 
  . intro h1
    intro y
    intro x
    apply h1
  . intro h1
    intro y
    intro x
    apply h1

-- Problem 4 d

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  . intro h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨x , hx⟩ := h1
    use x
    apply And.intro (hx) h2
  . intro h
    obtain ⟨x , hx⟩ := h
    obtain⟨hp, hq⟩:= hx   
    constructor
    . use x
      apply hp
    . apply hq


-- Problem 5 a
example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h2 : Tribalanced 1
  . use 1
    constructor
    . apply h2
    . dsimp [Tribalanced]
      simp
      use 1
      numbers
  . use 0
    constructor
    . intro n
      conv => ring
      numbers
    . conv => ring
      apply h2

    
-- Problem 5 b
example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  have h1 : Superpowered 1 := by apply superpowered_one
  have h2 : ¬ Superpowered 2 := by 
    intro h3
    dsimp [Superpowered] at h3
    
    have h4 : Prime (2^2^5 + 1):= by apply h3 5
    have h5 : ¬ Prime (2^2^5 + 1):= by 
      apply not_prime 641 6700417
      . numbers
      . numbers
      . numbers
    contradiction
  apply And.intro h1 h2
    


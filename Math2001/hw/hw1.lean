import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

axiom notnotE {p : Prop} (h : ¬ ¬ p) : p

-- Question 3 a
-- example {p q r : Prop} (h : p → (q → r)) : p ∧ q → r := by
-- intro h_pq
-- obtain ⟨h_p , h_q⟩ := h_pq
-- have h_qr : q → r := by apply h h_p
-- apply h_qr h_q
-- Question 3 a
theorem Problem3a {p q r: Prop} (h : p ∧ q → r) : p → (q → r) := by
intro h_p
intro h_q
have h_pq : p ∧ q := by apply And.intro h_p h_q
apply h h_pq
-- Question 3 b
theorem Problem3b {p q r: Prop} (h : p → (q → r)): (p →q) → (p → r) := by
intro h_pq
intro h_p
have h_q : q := by apply h_pq h_p
have h_qr: q → r := by apply h h_p
apply h_qr h_q

-- Question 3 c
theorem Problem3c {p q r: Prop} (h1 : p ∧ ¬q → r) (h2: ¬r) (h3 : p) : q:= by
have h_notnotq : ¬¬q := by 
  intro not_q 
  have h_pq : p ∧ ¬q := by apply And.intro h3 not_q
  have h_r : r := by apply h1 h_pq
  contradiction
apply notnotE h_notnotq
-- intro h_q
-- have h_pq : p ∧ ¬q := by apply And.intro h3 h_q
-- have h_r : r := by apply h1 h_pq
-- contradiction


-- Question 4 a
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := 
calc
  a = 2*b + 5 := by rw [h1]
  _ = 2 * 3 + 5 := by rw [h2]
  _ = 11 := by ring
-- Question 4 b
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
calc
  x = x + 4 - 4 := by ring
  _ = 2 - 4 := by rw [h1]
  _ = -2 := by ring
-- Question 4 c
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
calc
  a = a - 5*b + 5*b := by ring
  _ = 4 + 5*b := by rw [h1]
  _ = -6 + 5*(b + 2) := by ring
  _ = -6 + 5*3 := by rw [h2]
  _ = 9 := by ring
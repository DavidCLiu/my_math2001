import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

-- lemma de_morgan2 {p q : Prop} (h1 : ¬p ∧ ¬q) : ¬(p ∨ q) := by
--   intro pq
--   have h_p: ¬p := by apply And.left h1
--   have h_q: ¬q := by apply And.right h1
--   have hp : p → ¬(p ∨ q) := by 
--     intro h_p2
--     contradiction
--   have hq : q → ¬(p ∨ q) := by 
--     intro h_q2
--     contradiction
--   have x : ¬(p ∨ q) := by apply Or.elim pq hp hq
--   contradiction
  
-- lemma de_morgan3 {p q : Prop} (h1: ¬p ∨ ¬q) : ¬(p ∧ q) := by
--   intro h_pq
--   have h_notpq1 : ¬p → ¬(p ∧ q) := by 
--     intro hnotp
--     have h_p : p := by apply And.left h_pq
--     contradiction
--   have h_notpq2 : ¬q → ¬(p ∧ q) := by 
--     intro h_notq
--     have h_p : q := by apply And.right h_pq
--     contradiction
--   have x : ¬(p ∧  q) := by apply Or.elim h1 h_notpq1 h_notpq2
  -- contradiction

lemma de_morgan2 {p q : Prop} : ¬p ∧ ¬q → ¬(p ∨ q) := by
  intro start
  obtain⟨h1,h2⟩ := start
  intro cont
  cases cont with
    | inl cont1 => apply h1 cont1
    | inr cont2 => apply h2 cont2

lemma de_morgan3 {p q : Prop} :¬p ∨ ¬q →  ¬(p ∧ q) := by
  intro start
  intro start2
  obtain⟨h1,h2⟩ := start2
  cases start with
    | inl hp => apply hp h1
    | inr hq => apply hq h2
  
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc 
    x = (x + 3) - 3 := by ring
    _ ≥ (2 * y) - 3 := by rel[h1] 
    _ ≥ (2 * 1) - 3 := by rel[h2]
    _ ≥ -1 := by ring 

example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = (a + 2*b + a)/2 := by ring
    _ ≥ (4 + a)/2 := by rel[h2]
    _ ≥ (4 + 3)/2 := by rel[h1]
    _ = 7/2 := by ring
    _ ≥ 3 := by numbers
    

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x = x ^ 3 - 8 * x ^ 2 + 2 * x := by ring
    _ = x* (x^2 - 8*x + 2) := by ring
    _ = x * (x ^2 - 8*x + 16) - 14*x := by ring
    _ = x*((x - 4)^2 - 14) := by ring
    _ ≥ 9*((9 - 4)^2 - 14) := by rel[hx]
    _ ≥ 3 := by ring


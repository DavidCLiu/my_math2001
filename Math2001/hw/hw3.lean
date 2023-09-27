import Mathlib.Data.Real.Basic
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hyt : 0 < (-x)*t := by addarith [hxt]
    have hy' : 0 > -x := by addarith [hx]
    have hyt' : 0 < x := by addarith [hx]
    have hyt'' : x * (-t)  > 0:= by calc
      x*(-t) = (-x)*t := by ring
      _ > 0 := by addarith[hxt]
    cancel x at hyt''
    apply ne_of_lt
    have hyt''' : t <0 := by addarith [hyt'']
    apply hyt'''
    
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1,a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q)/2
  constructor
  calc
    p = (p + p)/2 := by ring
    _ < (p + q)/2 := by rel[h]
  calc
    q = (q + q)/2 := by ring
    _ > (p + q)/2 := by rel[h]
  

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have h := lt_or_ge x 0
  obtain hx | hx := h
  . have hnx : -x > 0 := by addarith[hx]
    use x-1
    calc
      (x - 1)^2 = x^2 - 2*x + 1 := by ring
      _ = -x * -x - 2*x + 1 := by ring
      _ > 0*-x - 2*x + 1 := by rel[hnx]
      _ = -x-x + 1:= by ring
      _ > - x - x := by extra
      _ > 0 -x := by rel [hnx]
      _ = -x := by ring
      _ > 0 := by rel[hnx]
      _ >x := by rel[hx]
  . use x+1
    calc 
      (x+1)^2 = x^2 + 2*x + 1 := by ring
      _ = x * x + 2*x + 1 := by ring
      _ ≥ 0 * x + 2*x + 1 := by rel[hx]
      _ = 2*x + 1 := by ring
      _ > 2*x := by extra
      _ = x + x := by ring
      _ ≥ x + 0 := by rel [hx]
      _ = x := by ring
      


  
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, hxt⟩ := h
  intro H
  have h1 : x*1+ 1 < x + 1 := by calc
    x*1 + 1 = x* t + 1 := by rw[H]
    _ < x + t := by rel[hxt]
    _ = x + 1 := by rw[H]
  apply ne_of_lt h1
  ring


example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain⟨x,hx⟩ := h
  intro h1
  rw[h1] at hx
  have H := le_or_gt x 2
  obtain hxt | hxt := H
  . have := calc 
      5 = 2*x := by rw[hx]
      _ ≤ 2*2 := by rel[hxt]
      _ ≤ 4 := by numbers
    contradiction 
  . have h2 : x ≥ 3 := by addarith[hxt]
    have := calc
      5 = 2*x := by rw[hx]
      _ ≥ 2 * 3 := by rel[h2]
      _ = 6 := by ring
    contradiction
      


  
    
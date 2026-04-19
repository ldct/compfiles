/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# British Mathematical Olympiad 2009, Round 2, Problem 3

Find all functions f from the real numbers to the real numbers which satisfy
f(x³) + f(y³) = (x + y)(f(x²) + f(y²) − f(xy)) for all real numbers x and y.
-/

namespace UK2009R2P3

determine solution_set : Set (ℝ → ℝ) :=
  { f | ∃ k : ℝ, ∀ x, f x = k * x }

problem uk2009_r2_p3 :
    { f : ℝ → ℝ | ∀ x y, f (x^3) + f (y^3) = (x + y) * (f (x^2) + f (y^2) - f (x*y)) } =
    solution_set := by
  ext f
  simp only [Set.mem_setOf_eq, solution_set, Set.mem_setOf_eq]
  constructor
  · intro h
    -- Step 1: f(0) = 0
    have h00 := h 0 0
    have hf0 : f 0 = 0 := by
      simp at h00; linarith
    -- Step 2: f(x^3) = x * f(x^2)  (from y=0)
    have hfx3 : ∀ x : ℝ, f (x^3) = x * f (x^2) := by
      intro x
      have := h x 0
      simp [hf0] at this
      linarith
    -- Step 3: from y=1, with k := f 1, derive f(x^2) = (x+1)*f(x) - x*k
    set k := f 1 with hk_def
    have hfx2_pos : ∀ x : ℝ, f (x^2) = (x + 1) * f x - x * k := by
      intro x
      have hy1 := h x 1
      rw [show ((1:ℝ))^3 = 1 by ring, show ((1:ℝ))^2 = 1 by ring,
          show x * 1 = x by ring, hfx3 x] at hy1
      -- hy1 : x * f(x^2) + k = (x+1) * (f(x^2) + k - f x)
      linarith [hy1]
    -- Step 4: apply with -x
    have hfx2_neg : ∀ x : ℝ, f (x^2) = (-x + 1) * f (-x) - (-x) * k := by
      intro x
      have := hfx2_pos (-x)
      rw [show (-x)^2 = x^2 by ring] at this
      exact this
    -- Step 5: f(-x) from y=-x substitution: f(x^3) + f(-x^3) = 0
    -- h x (-x): (x + (-x)) = 0, so f(x^3) + f((-x)^3) = 0
    have hodd_cube : ∀ x : ℝ, f ((-x)^3) = -f (x^3) := by
      intro x
      have := h x (-x)
      rw [show x + (-x) = (0:ℝ) by ring] at this
      simp at this
      linarith
    -- So x * f((-x)^2) = -x * f(x^2)... wait use hfx3
    have hodd_cube' : ∀ x : ℝ, (-x) * f (x^2) = -(x * f (x^2)) := by
      intro x; ring
    -- hfx3 at (-x): f((-x)^3) = (-x) * f((-x)^2) = -x * f(x^2)
    -- Combined with hodd_cube: -f(x^3) = -x * f(x^2), so f(x^3) = x*f(x^2) — consistent, no new info
    -- Need another approach: use y=-1 substitution
    -- Setting y = -1: f(x^3) + f(-1) = (x-1)(f(x^2) + f(1) - f(-x))
    -- Setting x=1, y=-1: f(1) + f(-1) = 0*(...) = 0, so f(-1) = -f(1) = -k
    have hfneg1 : f (-1) = -k := by
      have := h 1 (-1)
      rw [show (1:ℝ) + (-1) = 0 by ring] at this
      have e1 : (1:ℝ)^3 = 1 := by ring
      have e2 : ((-1:ℝ))^3 = -1 := by ring
      rw [e1, e2] at this
      simp at this
      linarith
    -- From y=-1: f(x^3) + f(-1) = (x - 1)(f(x^2) + f(1) - f(-x))
    have hym1 : ∀ x : ℝ, f (x^3) + f (-1) = (x - 1) * (f (x^2) + f 1 - f (-x)) := by
      intro x
      have := h x (-1)
      rw [show ((-1):ℝ)^3 = -1 by ring, show ((-1):ℝ)^2 = 1 by ring,
          show x * (-1) = -x by ring] at this
      linarith
    -- Expand: x*f(x^2) - k = (x-1)*(f(x^2) + k - f(-x))
    -- Also, similar y=1: f(x^3)+f(1) = (x+1)(f(x^2)+f(1)-f(x))
    have hy1 : ∀ x : ℝ, f (x^3) + f 1 = (x + 1) * (f (x^2) + f 1 - f x) := by
      intro x
      have := h x 1
      rw [show ((1):ℝ)^3 = 1 by ring, show ((1):ℝ)^2 = 1 by ring,
          show x * 1 = x by ring] at this
      linarith
    -- From hy1: using hfx3, x*f(x^2) + k = (x+1)*(f(x^2) + k - f x)
    -- => x*f(x^2) + k = (x+1)*f(x^2) + (x+1)*k - (x+1)*f(x)
    -- => -f(x^2) = x*k - (x+1)*f(x)
    -- => f(x^2) = (x+1)*f(x) - x*k   ✓ (matches hfx2_pos)
    -- From hym1: x*f(x^2) - k = (x-1)*(f(x^2) + k - f(-x))
    -- => x*f(x^2) - k = (x-1)*f(x^2) + (x-1)*k - (x-1)*f(-x)
    -- => f(x^2) = x*k - (x-1)*k + (x-1)*f(-x)... wait
    -- x*f(x^2) - (x-1)*f(x^2) = (x-1)*k + k - (x-1)*f(-x)
    -- f(x^2) = x*k - (x-1)*f(-x)
    -- So two expressions for f(x^2):
    -- (A) f(x^2) = (x+1)*f(x) - x*k
    -- (B) f(x^2) = x*k - (x-1)*f(-x) = x*k + (1-x)*f(-x)
    have hfx2_alt : ∀ x : ℝ, f (x^2) = x * k + (1 - x) * f (-x) := by
      intro x
      have hy := hym1 x
      rw [hfx3 x, hfneg1] at hy
      linarith
    -- Sub x ↦ -x in (A): f((-x)^2) = (-x+1)*f(-x) - (-x)*k
    -- So f(x^2) = (1-x)*f(-x) + x*k   — same as (B), consistent
    -- Now replace f(-x) via (A) applied to -x:
    -- f((-x)^2) = (-x+1)*f(-x) - (-x)*k, so f(x^2) = (1-x)*f(-x) + x*k
    -- => (1-x)*f(-x) = f(x^2) - x*k = (x+1)*f(x) - x*k - x*k = (x+1)*f(x) - 2*x*k
    -- Now from (A) applied to -x: f(x^2) = (1-x)*f(-x) - (-x)*k = (1-x)*f(-x) + x*k
    -- So (1-x)*f(-x) = f(x^2) - x*k.
    -- And we want to derive f(x) = k*x. Use both (A) and (B):
    -- (A) - (B): 0 = (x+1)*f(x) - x*k - x*k - (1-x)*f(-x) = (x+1)*f(x) - 2*x*k - (1-x)*f(-x)
    -- So (x+1)*f(x) - (1-x)*f(-x) = 2*x*k ... (*)
    -- Similarly with x ↦ -x: (-x+1)*f(-x) - (1+x)*f(x) = -2*x*k
    -- Which is: -[(x+1)*f(x) - (1-x)*f(-x)] = -2*x*k. Same equation.
    -- Need another equation. Use y = x substitution.
    -- h x x: 2*f(x^3) = 2x*(f(x^2) + f(x^2) - f(x^2)) = 2x*f(x^2). Consistent with hfx3.
    -- Use h(x, -1) and h(-x, 1):
    -- h(-x, 1): f((-x)^3) + f(1) = (-x+1)*(f(x^2) + f(1) - f(-x))
    -- i.e. f(-x^3) + k = (1-x)*(f(x^2) + k - f(-x))
    -- Also h(x, -1) done above.
    -- Use h(1, y): f(1) + f(y^3) = (1+y)*(f(1) + f(y^2) - f(y))
    -- f(y^3) = y*f(y^2), so y*f(y^2) + k = (1+y)*(f(y^2) + k - f(y))
    -- => y*f(y^2) + k = (1+y)*f(y^2) + (1+y)*k - (1+y)*f(y)
    -- => -f(y^2) = y*k - (1+y)*f(y) + k - k = y*k - (1+y)*f(y)
    -- Wait: -f(y^2) = y*k - (1+y)*f(y), i.e. f(y^2) = (1+y)*f(y) - y*k. Same as (A). No new info.
    -- Try h(x, y) - h(y, x): symmetric in f(x^3)+f(y^3). And (x+y)*... is symmetric too. Consistent.
    -- Try h(x, 2) or generic y. Let me try a different approach:
    -- h(2, 1): f(8) + f(1) = 3*(f(4) + f(1) - f(2))
    -- Using (A): f(4) = 3*f(2) - 2k (from x=2: f(4) = (2+1)*f(2) - 2k = 3f(2) - 2k)
    -- f(8) = 2*f(4) (from hfx3 with x=2: f(2^3) = 2*f(2^2)) = 2*(3f(2)-2k) = 6f(2) - 4k
    -- So f(8) + k = 3*(3f(2) - 2k + k - f(2)) = 3*(2f(2) - k) = 6f(2) - 3k
    -- LHS = 6f(2) - 4k + k = 6f(2) - 3k. Consistent. No info.
    -- Need to use (x+y)(...) nonlinearly. Try specific nonlinear substitution.
    -- h(1, 1): 2f(1) = 2*(f(1) + f(1) - f(1)) = 2*f(1). Trivial.
    -- h(x, y) with y = 1/x (for x ≠ 0): f(x^3) + f(1/x^3) = (x + 1/x)*(f(x^2) + f(1/x^2) - f(1))
    -- Getting complex. Let me try yet another path.
    -- Actually: from (A), substituting x ↦ x^(1/3) won't help without surjectivity.
    -- Consider h(x, -x): done; gives f(x^3) + f(-x^3) = 0 (since x + (-x) = 0).
    -- So f is odd on cubes: f(-t) = -f(t) for t = x^3, but cubing IS surjective on ℝ.
    -- So f is odd everywhere!
    have hf_odd : ∀ t : ℝ, f (-t) = -f t := by
      intro t
      -- t = (t^(1/3))^3 with real cube root
      -- Use Real.rpow or explicit cube root
      by_cases ht : t ≥ 0
      · -- Use x = t^(1/3) via rpow; cleaner: use sign
        have hx : ∃ x : ℝ, x^3 = t := ⟨t^((1:ℝ)/3), by
          rw [← Real.rpow_natCast (t^((1:ℝ)/3)) 3, ← Real.rpow_mul ht]
          norm_num⟩
        obtain ⟨x, hx⟩ := hx
        rw [← hx]
        have := h x (-x)
        rw [show x + (-x) = (0:ℝ) by ring] at this
        simp at this
        have heq : (-x)^3 = -(x^3) := by ring
        rw [heq] at this
        linarith
      · have ht : t < 0 := not_le.mp ht
        have ht' : -t > 0 := by linarith
        have hx : ∃ x : ℝ, x^3 = -t := ⟨(-t)^((1:ℝ)/3), by
          rw [← Real.rpow_natCast ((-t)^((1:ℝ)/3)) 3, ← Real.rpow_mul (le_of_lt ht')]
          norm_num⟩
        obtain ⟨x, hx⟩ := hx
        have htt : t = -(x^3) := by linarith
        rw [htt, neg_neg]
        have := h x (-x)
        rw [show x + (-x) = (0:ℝ) by ring] at this
        simp at this
        have heq : (-x)^3 = -(x^3) := by ring
        rw [heq] at this
        linarith
    -- Now using (A) with x and -x:
    -- f(x^2) = (x+1)*f(x) - x*k
    -- f(x^2) = (-x+1)*f(-x) - (-x)*k = (1-x)*(-f(x)) + x*k = -(1-x)*f(x) + x*k = (x-1)*f(x) + x*k
    -- Subtracting: 0 = 2*f(x) - 2*x*k, so f(x) = k*x.
    use k
    intro x
    have hA := hfx2_pos x
    have hB := hfx2_pos (-x)
    rw [show (-x)^2 = x^2 by ring, hf_odd x] at hB
    -- hA: f(x^2) = (x+1)*f(x) - x*k
    -- hB: f(x^2) = (-x+1)*(-f(x)) - (-x)*k = (x-1)*f(x) + x*k
    linarith
  · rintro ⟨k, hk⟩ x y
    simp [hk]
    ring

end UK2009R2P3

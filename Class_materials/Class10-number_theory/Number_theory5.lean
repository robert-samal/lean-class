/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace Section15Sheet5

/-

# Prove that 19 ∣ 2^(2⁶ᵏ⁺²) + 3 for k = 0,1,2,...


This is the fifth question in Sierpinski's book "250 elementary problems
in number theory".

thoughts

if a(k)=2^(2⁶ᵏ⁺²)
then a(k+1)=2^(2⁶*2⁶ᵏ⁺²)=a(k)^64

Note that 16^64 is 16 mod 19 according to a brute force calculation
and so all of the a(k) are 16 mod 19 and we're done

-/

-- let's check that ^ has the right "preference"
#eval 2^3^2

example (a b c : ℕ) : a^b^c = a^(b^c) := rfl

#print ZMod

theorem sixteen_pow_sixtyfour_mod_nineteen : (16 : ZMod 19) ^ 64 = 16 := by rfl

lemma divisibility (n : ℤ) : 19 ∣ n ↔ (n : ZMod 19) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd n 19).symm

lemma divisibility2 (n : ℤ) : 19 ∣ n ↔ (n : ZMod 19) = 0 := by
  simp [ZMod.intCast_zmod_eq_zero_iff_dvd]


-- to simplify the formulas, let us define:
def a (k : ℕ) : ℤ := 2 ^ 2 ^ (6 * k + 2)

example : a 0 = 16 := by rfl
example : 19 ∣ a 0 + 3 := by rfl

lemma recursion (k : ℕ) : (a (k+1)) = (a k)^64 := by
  rw [a, a] -- we need to rewrite a twice, as `rw` changes only the first occurence
  ring      -- now it is basic calculation, but note that `ring` doesn't work before `rw`

lemma subtract (n : ZMod 19) : n + 3 = 0 ↔ n = 16 := by
  revert n -- check what it does: basically the inverse of `intro n`
  decide   -- here we use that `ZMod 19` is a finite, decidable type
  -- we can also replace the two lines above by ``decide +revert``

example : (16 : ZMod 19) + 3 = 0 := rfl

example (k : ℕ) : 19 ∣ (a k) + 3 := by induction k with
  | zero => rfl
  | succ k ih => {
     rw [ divisibility ] at ⊢ ih
     rw [recursion]
     push_cast at *
     have h2 : (↑(a k) : ZMod 19) = (16 : ZMod 19) := by
       rw [subtract] at ih
       exact ih
     rw [h2]
     rw [sixteen_pow_sixtyfour_mod_nineteen]
     rfl
  }

end Section15Sheet5

import Mathlib
-- bad style!! It is a huge library!

theorem cantor : ∀ α : Type,
∀ f : α → Set α, ¬Function.Surjective f := by
  intro α f
  let S : Set α := {x | x ∉ f x}
  unfold Function.Surjective
  intro surj -- proof by contradiction
  obtain ⟨a, ha⟩ := surj S
  have h : a ∈ S ↔ a ∉ S := by
    constructor
    · intro ha_in_S
      rw [Set.mem_setOf] at ha_in_S
      rw [← ha]
      exact ha_in_S
    · intro ha_notin_S
      rw [Set.mem_setOf]
      rw [ha]
      exact ha_notin_S
  tauto

/- or more explicitly, instead of tauto
  by_cases ha : a ∈ S
  · exact h.mp ha ha        -- contradiction: ha and h1 ha
  · exact ha (h.mpr ha)      -- contradiction: ¬ha but ha from h2
-/

def seq_converges_to (a : ℕ → ℝ) (L : ℝ) : Prop :=
   ∀ ε > 0, ∃ N, ∀ n > N, |a n - L| < ε

theorem squeeze_theorem (a b c : ℕ → ℝ) (L : ℝ)
  (a_le_b : a ≤ b)
  (b_le_c : ∀ n, b n ≤ c n)
  (a_to_L : seq_converges_to a L)
  (c_to_L : seq_converges_to c L) :
  seq_converges_to b L := by
  unfold seq_converges_to
  unfold seq_converges_to at a_to_L
  unfold seq_converges_to at c_to_L
  -- shortly: unfold seq_converges_to at a_to_L c_to_L ⊢
  intro ε ε_pos
  obtain ⟨N1, h1⟩ := a_to_L ε ε_pos
  obtain ⟨N2, h2⟩ := c_to_L ε ε_pos
  let N := max N1 N2
  use N
  intro n n_big
  have N1_big : N ≥ N1 := by
    apply le_max_left N1 N2
  have n_big1 : n > N1 := by
    apply lt_of_le_of_lt N1_big n_big
  have n_big2 : n > N2 := lt_of_le_of_lt (le_max_right N1 N2) n_big
  specialize h1 n n_big1
  specialize h2 n n_big2
  rw [abs_sub_lt_iff] at h1 h2 ⊢
  have a_le_b' : a n ≤ b n := a_le_b n
  specialize b_le_c n
  apply And.intro
  linarith
  linarith

example (f g : ℕ → ℝ) (n : ℕ) : (f + g) n = f n + g n :=
  Pi.add_apply f g n

example {x a b ε : ℝ}
    (hx : x ≤ a + b) (ha : a ≤ ε/2) (hb : b < ε/2) :
  x < ε := by
  calc
    x ≤ a + b := hx
    _ < ε/2 + ε/2 := add_lt_add_of_le_of_lt ha hb
    _ = ε := by simp [add_halves]

example {x a b ε : ℝ}
    (hx : x ≤ a + b) (ha : a ≤ ε/2) (hb : b < ε/2) :
  x < ε := by
  linarith



theorem arithmetics_of_limit (a : ℕ → ℝ) (b : ℕ → ℝ)
  (A B : ℝ)
  (a_to_A : seq_converges_to a A)
  (b_to_B : seq_converges_to b B) :
  seq_converges_to (a+b) (A+B) := by
  unfold seq_converges_to
  unfold seq_converges_to at a_to_A
  unfold seq_converges_to at b_to_B
  intro ε ε_pos
  let ε' := ε/2
  have ε'_pos : ε' > 0 := half_pos ε_pos
  specialize a_to_A ε' ε'_pos
  obtain ⟨N₁,h₁⟩ := a_to_A
  obtain ⟨N₂,h₂⟩ := b_to_B ε' ε'_pos
  let N := max N₁ N₂
  use N
  intro n n_big
  have h := Pi.add_apply a b n
  rw [h]
  have hh : |(a n - A) + (b n - B)| ≤ |a n - A| + |b n - B| :=
    abs_add  (a n - A) (b n - B)
  have n_big1 : n > N₁ := by
    apply lt_of_le_of_lt (le_max_left N₁ N₂) n_big
  have n_big2 : n > N₂ := by
    apply lt_of_le_of_lt (le_max_right N₁ N₂) n_big
  specialize h₁ n n_big1
  specialize h₂ n n_big2
  have h₃ : |(a n - A) + (b n - B)| < ε' + ε' := by
    linarith
  rw [add_halves] at h₃
  have h₀ : a n - A + (b n - B) = a n + b n - (A + B) := by ring
  simpa [h₀] using h₃

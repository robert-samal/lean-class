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

theorem infinitude_of_primes : ∀ N : ℕ, ∃ p > N, Nat.Prime p := by
  intro N -- "Consider any N"
  let M := N.factorial + 1
  have : N.factorial > 0 := Nat.factorial_pos N
  have : M > 1 := by
    simpa [M]
  have Mn1 : M ≠ 1 := by
    exact ne_of_gt this
  let p := M.minFac
  use p -- "We will show that p works."
  have p_pos : p > 0 := Nat.minFac_pos M
  have p_prime : Nat.Prime p := Nat.minFac_prime Mn1
  constructor
  . by_contra h
    push_neg at h
    have pdiv1 : p ∣ N.factorial := Nat.dvd_factorial p_pos h
    have pdiv2 : p ∣ M := Nat.minFac_dvd M
    have p1 : p ∣ (M - N.factorial) := Nat.dvd_sub pdiv2 pdiv1
    have : M - N.factorial = 1 := by simp [M]
    rw [this] at p1
    have peq1 : p = 1 := Nat.dvd_one.1 p1
    have p_not_prime : ¬ Nat.Prime p := by
      simpa [peq1] using Nat.not_prime_one
    contradiction
  . exact p_prime
























def is_rational1 (x : ℝ) :=
  ∃ p : ℤ, ∃ q > 0, x = p/q

example : is_rational1 1 := by
  use 1
  use 1
  simp











































example : is_rational1 √2 := by
  use 2
  use √2
  simp




















def is_rational2 (x : ℝ) :=
  ∃ p : ℤ, ∃ q : ℤ, q > 0 ∧ x = p/q

--  example : is_rational2 √2 := by
--   use 2
--   use √2
--   simp


example : is_rational2 1 := by
  use 1
  use 1
  simp

example : ¬ is_rational2 (√(2 : ℝ)) := by
   have h : Irrational (√(2 : ℝ)) := by
      simpa using irrational_sqrt_two
   unfold is_rational2
   push_neg
   intros p q qpos
   exact (irrational_iff_ne_rational √(2:ℝ)).mp  h p q




example {p q : ℕ} (h2 : 2 * (q : ℤ) ^ 2 = (p : ℤ) ^ 2) :
  ((p ^ 2 : ℕ) : ℝ) = ((2 * q ^ 2 : ℕ) : ℝ) := by
  -- h2: 2 * ↑q ^ 2 = ↑p ^ 2
  norm_cast at h2 ⊢
  -- h2 is now transformed to: ↑(2 * q ^ 2) = ↑(p ^ 2)
  -- This is the symmetric version of our goal.
  exact h2.symm

/- theorem sqrt_2_is_not_rational : ¬ is_rational2 √2 := by
  unfold is_rational2
  push_neg
  intros p q qpos
  have qnz : q ≠ 0 := ne_of_gt qpos
  by_contra h
  have sqrt_two_pos : (0 : ℝ) < √2 := Real.sqrt_pos.mpr two_pos
  have ppos : p > 0 := by
    rw [h] at sqrt_two_pos
    field_simp at sqrt_two_pos
    exact sqrt_two_pos
  have h2 : (√2)^2 = (p/q)^2 := by
    apply congrArg (fun x => x^2) h
  have sq2 : (√2)^2  = 2 := Real.sq_sqrt zero_le_two
  rw [sq2] at h2
  rw [div_pow] at h2
  have h3 : p^2 = 2*q^2 := by
    refine (Rat.coe_int_inj (p ^ 2) (2 * q ^ 2)).mp ?_
    rw [eq_div_iff_mul_eq] at h2
    norm_cast at h2 ⊢
    exact h2.symm
    norm_cast at ⊢
    exact pow_ne_zero 2 qnz
  let d := Int.gcd p q
  have dpos : d > 0 := by
    refine Int.gcd_pos_of_ne_zero_right p ?_
    exact qnz
  let p' := p/d
  let q' := q/d

  have p_eq : p = p' * d := by
    unfold p'
    rw [Int.ediv_mul_cancel]
    exact Int.gcd_dvd_left p q

  have q_eq : q = q' * d := by
    unfold q'
    rw [Int.ediv_mul_cancel]
    exact Int.gcd_dvd_right p q

  have coprime: Int.gcd p' q' = 1 := by
    refine Int.gcd_ediv_gcd_ediv_gcd ?_
    exact dpos

  have h4 : p'^2 = 2*q'^2 := by
    unfold p'
    unfold q'
--    simp [h3]
    sorry

  have p'even : 2 ∣ p' := by sorry
  let p'' := p'/2
  have h5 : 2 * p''^2 = q^2 := by sorry
  have q'even : 2 ∣ q' := by sorry
  -- contradiction  coprime p'even q'even
 -/


theorem ir2 : Irrational (√(2 : ℝ)) := by
  simpa using irrational_sqrt_two



/-  have sq2 : (√2)^2  = 2 := Real.sq_sqrt zero_le_two
  have h3 : p^2 = 2*q^2 := by
    refine Eq.symm ((fun m n ↦ (Rat.coe_int_inj m n).mp) (2 * q ^ 2) (p ^ 2) ?_)


     simp [h2]


  sorry

-/

theorem cantor2 {α : Type*} (f : α → Set α) : ¬ Function.Surjective f := fun surj =>
  let S : Set α := {x | x ∉ f x}
  let ⟨a, ha⟩ := surj S
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
  (Classical.em (a ∈ S)).elim
    (fun hs => h.mp hs hs)
    (fun hs => hs (h.mpr hs))

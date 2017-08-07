
universe u

section pow

open nat

variable {α : Type u}

section basics

variables [has_one α] [has_mul α]

def pow (b : α) : ℕ → α
| 0        := 1
| (succ n) := pow n * b

local infix `^` := pow

@[simp] lemma pow_zero (b : α) : b^0 = 1 := rfl

end basics

local infix `^` := pow

section comm_monoid

variables [comm_monoid α]

local infix `^` := pow

lemma one_pow {n : ℕ} (k : ℕ) : (1 : α)^k = 1 :=
begin
  induction k,
  { simp },
  { dunfold pow, simp [ih_1], }
end
lemma pow_add (p : α) (x y : ℕ)
: p^(x+y) = p^x * p^y :=
begin
  induction x,
  case zero { simp },
  case succ x
  { simp [nat.add_succ] at *,
    dunfold pow,
    simp [ih_1], },
end

lemma pow_mul (p : α) (x y : ℕ)
: p^(x*y) = ( p^x )^y :=
begin
  induction y,
  case zero { simp },
  case succ y
  { simp [mul_succ,pow_add,ih_1],
    dunfold pow, ac_refl },
end

lemma pow_pow_comm (p : α) (x y : ℕ)
: p^x^y = p^y^x :=
by rw [← pow_mul p,mul_comm,pow_mul]

end comm_monoid

section linear_ordered_semiring

variable [linear_ordered_semiring α]

lemma pow_pos_of_pos (p : α) {x : ℕ}
  (H : 1 ≤ p)
: 1 ≤ p^x :=
begin
  induction x,
  case zero
  { dunfold pow, refl },
  case succ x
  { dunfold pow,
    rw ← one_mul (1 : α),
    apply mul_le_mul ih_1 H,
    { apply zero_le_one },
    { transitivity (1 : α),
      { apply zero_le_one, },
      apply ih_1 } }
end

lemma pow_lt_pow (p : α) {x y : ℕ}
  (Hp : p > 1)
  (Hlt : x < y)
: p^x < p^y :=
begin
  induction y,
  case zero
  { exfalso,
    apply nat.not_lt_zero _ Hlt },
  case succ y
  { dunfold pow,
    rw ← mul_one (p^x),
    have Hle : x ≤ y := le_of_succ_le_succ Hlt,
    have Hpow_pos : 0 < p ^ x,
    { apply @lt_of_lt_of_le α _ _ 1,
      { apply zero_lt_one },
      { apply pow_pos_of_pos,
        apply le_of_lt Hp } },
    rw le_iff_lt_or_eq at Hle,
    cases Hle with Hlt Heq,
    { transitivity p^x * p,
      { apply mul_lt_mul_of_pos_left Hp,
        apply Hpow_pos },
      { apply mul_lt_mul_of_pos_right,
        { apply ih_1 Hlt },
        { apply lt_trans _ Hp,
          apply zero_lt_one } } },
    { subst y,
      apply mul_lt_mul_of_pos_left Hp,
      apply Hpow_pos } }
end

end linear_ordered_semiring

end pow

lemma nat_pow_def (p x : ℕ)
: nat.pow p x = pow p x :=
by { induction x, refl, simp [nat.pow,pow,ih_1], }

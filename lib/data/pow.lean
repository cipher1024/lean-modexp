
import algebra.group_power

universe u

section pow

open nat (hiding pow_succ)

variable {α : Type u}

section comm_monoid

variables [monoid α]

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
  { simp },
  case succ x
  { simp [pow_succ],
    rw ← one_mul (1 : α),
    apply mul_le_mul H ih_1,
    { apply zero_le_one },
    { transitivity (1 : α),
      { apply zero_le_one, },
      apply H } }
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
  { rw [pow_succ,← one_mul (p^x)],
    have Hle : x ≤ y := le_of_succ_le_succ Hlt,
    have Hpow_pos : 0 < p ^ x,
    { apply @lt_of_lt_of_le α _ _ 1,
      { apply zero_lt_one },
      { apply pow_pos_of_pos,
        apply le_of_lt Hp } },
    rw le_iff_lt_or_eq at Hle,
    cases Hle with Hlt Heq,
    { transitivity p * p^x,
      { apply mul_lt_mul_of_pos_right Hp,
        apply Hpow_pos },
      { apply mul_lt_mul_of_pos_left,
        { apply ih_1 Hlt },
        { apply lt_trans _ Hp,
          apply zero_lt_one } } },
    { subst y,
      apply mul_lt_mul_of_pos_right Hp,
      apply Hpow_pos } }
end

end linear_ordered_semiring

end pow

lemma nat_pow_def (p x : ℕ)
: nat.pow p x = pow_nat p x :=
by { induction x, refl, simp [nat.pow,pow_succ p a,ih_1], }

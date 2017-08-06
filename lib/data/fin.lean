
namespace fin

open nat

def pow {n} (b : fin (succ n)) : ℕ → fin (succ n)
| 0        := 1
| (succ n) := pow n * b

infix `^` := pow

@[simp] lemma pow_zero {n} (b : fin (succ n)) : b^0 = 1 := rfl

protected def neg {n} : fin n → fin n
 | ⟨x,P⟩ :=
if h : 0 < x
then
  have P' : n - x < n, from sorry,
  ⟨n-x,P'⟩
else ⟨x,P⟩

instance {n} : comm_monoid (fin (succ n)) :=
{ one := has_one.one _
, mul := has_mul.mul
, mul_one := sorry
, one_mul := sorry
, mul_assoc := sorry
, mul_comm  := sorry }

instance {n} : decidable_linear_order (fin n) :=
{ le := has_le.le
, lt := has_lt.lt
, decidable_eq := by apply_instance
, decidable_le := by apply_instance
, decidable_lt := by apply_instance
, le_total := sorry
, lt_irrefl := sorry
, le_iff_lt_or_eq := sorry
, le_antisymm := sorry
, le_trans := sorry
, le_refl  := sorry }

-- this would be a good instance to donate to the Lean library
instance {n} : decidable_linear_ordered_comm_ring (fin (succ n)) :=
{ (_ : decidable_linear_order (fin $ succ n)) with
  one := has_one.one _
, mul := has_mul.mul
, neg := fin.neg
, zero := has_zero.zero _
, add := has_add.add
, zero_lt_one := sorry
, mul_one := sorry
, one_mul := sorry
, mul_assoc := sorry
, le_total := sorry
, le_iff_lt_or_eq := sorry
, mul_pos := sorry
, mul_nonneg := sorry
, mul_comm := sorry
, zero_ne_one := sorry
, add_lt_add_left := sorry
, add_le_add_left := sorry
, lt_of_le_of_lt := sorry
, lt_of_lt_of_le := sorry
, le_of_lt := sorry
, right_distrib := sorry
, left_distrib := sorry
, add_comm := sorry
, add_left_neg := sorry
, add_zero := sorry
, zero_add := sorry
, add_assoc := sorry
}

@[simp] lemma one_pow {n : ℕ} (k : ℕ) : (1 : fin (succ n))^k = 1 :=
begin
  induction k,
  { simp },
  { simp [pow,ih_1], }
end

lemma pow_add {n : ℕ} (p : fin (succ n)) (x y : ℕ)
: p^(x+y) = p^x * p^y :=
begin
  induction x,
  case zero { simp },
  case succ x
  { simp [nat.add_succ,pow] at *,
    simp [ih_1] },
end

lemma pow_mul {n : ℕ} (p : fin (succ n)) (x y : ℕ)
: p^(x*y) = ( p^x )^y :=
begin
  induction y,
  case zero { simp },
  case succ y
  { simp [mul_succ,pow_add,ih_1,pow] },
end

lemma one_le_iff_zero_lt {n : ℕ} (p : fin (succ n))
: 1 ≤ p ↔ 0 < p :=
sorry


lemma pow_pos_of_pos {n : ℕ} (p : fin (succ n)) {x : ℕ}
  (H : 0 < p)
: 0 < p^x :=
begin
  induction x,
  case zero
  { unfold pow, apply zero_lt_one },
  case succ x
  { unfold pow,
    rw ← zero_mul (p : fin (succ n)),
    apply mul_lt_mul_of_pos_right ih_1 H, }
end

lemma pow_lt_pow {n : ℕ} (p : fin (succ n)) {x y : ℕ}
  (Hp : p > 1)
  (Hlt : x < y)
: p^x < p^y :=
begin
  induction y,
  case zero
  { exfalso,
    apply nat.not_lt_zero _ Hlt },
  case succ y
  { unfold pow,
    rw ← mul_one (p^x),
    have Hle : x ≤ y := le_of_succ_le_succ Hlt,
    rw le_iff_lt_or_eq at Hle,
    cases Hle with Hlt Heq,
    { transitivity p^x * p,
      { apply mul_lt_mul_of_pos_left Hp,
        apply pow_pos_of_pos,
        transitivity (1 : fin (succ n)),
        { apply zero_lt_one },
        { apply Hp } },
      { apply mul_lt_mul_of_pos_right,
        { apply ih_1 Hlt },
        { rw ← one_le_iff_zero_lt,
          apply le_of_lt Hp, } } },
    { subst y,
      apply mul_lt_mul_of_pos_left Hp,
      apply pow_pos_of_pos,
      rw ← one_le_iff_zero_lt,
      apply le_of_lt Hp } }
end

lemma pow_pow_comm {n} (p : fin (succ n)) (x y : ℕ)
: p^x^y = p^y^x :=
by rw [← pow_mul,mul_comm,pow_mul]

end fin

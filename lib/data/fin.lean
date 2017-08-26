
namespace fin

open nat

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
, decidable_eq := by apply_instance
, decidable_le := by apply_instance
, le_total := sorry
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
, mul_pos := sorry
, mul_nonneg := sorry
, mul_comm := sorry
, zero_ne_one := sorry
, add_lt_add_left := sorry
, add_le_add_left := sorry
, right_distrib := sorry
, left_distrib := sorry
, add_comm := sorry
, add_left_neg := sorry
, add_zero := sorry
, zero_add := sorry
, add_assoc := sorry
}

end fin


import .lib.data.fin
import .lib.data.list
import .lib.data.pow

import data.bitvec

def word_size : ℕ := 32

def window_size : ℕ := 4

def word_vals : ℕ := 2^word_size

def win_vals : ℕ := 2^window_size

lemma window_size_pos
: window_size > 0 :=
of_as_true trivial

lemma win_vals_gt_one
: win_vals > 1 :=
begin
  change (2 : ℕ)^0 < _,
  unfold win_vals,
  rw [nat_pow_def,nat_pow_def],
  apply pow_lt_pow,
  { apply nat.lt_succ_self, },
  apply window_size_pos
end

@[reducible]
def word := bitvec word_size

@[reducible]
def window := fin win_vals

section defs

open nat

def up {n : ℕ} : fin n → fin (succ n)
 | ⟨i,P⟩ := ⟨i,show i < succ n, by { transitivity n, { apply P }, { apply nat.lt_succ_self } }⟩

structure bignum :=
  (cap  : ℕ)
  (size : fin (succ cap))
  (data : array word cap)
  (all_zero : ∀ i, size ≤ up i → data.read i = 0)
  (msw_not_zero : ∀ last, fin.succ last = size → data.read last ≠ 0)

end defs

namespace bignum

def to_nat (n : bignum) : ℕ :=
n.data.iterate 0 (λ i w r, r + w.to_nat * 2 ^ (i.val * word_size))

def zero : bignum :=
{ cap := 0
, size := 0
, data := ⟨ λ i, i.elim0 ⟩
, all_zero := assume i, i.elim0
, msw_not_zero := assume i, i.elim0
}

def words (p : bignum) (n : ℕ) : word :=
if h : n < p.cap
   then p.data.read ⟨n,h⟩
   else 0

namespace add

open nat

def add_carry (p q : bignum) : ℕ → word
 | 0 := 0
 | (succ i) :=
   let c := (add_carry i).to_nat,
       x := (p.words $ succ i).to_nat,
       y := (q.words $ succ i).to_nat in
   if word_vals ≤ c + x + y
      then 1
      else 0

def add_val (p q : bignum) (i : ℕ) : word :=
p.words i + p.words i + add_carry p q i

def msw_aux {n} (ar : array word n)
: ∀ i, i < succ n → fin (succ n)
| 0 P := ⟨ _, P ⟩
| (succ i) P :=
if ar.read ⟨i,lt_of_succ_lt_succ P⟩ = 0
then msw_aux i (by { transitivity succ i, apply lt_succ_self, apply P })
else ⟨succ i,P⟩

def msw {n} (ar : array word n) : fin (succ n) :=
msw_aux ar n (lt_succ_self _)

lemma msw_not_zero {n} (ar : array word n)
: ∀ last, fin.succ last = msw ar → ar.read last ≠ 0 :=
sorry

lemma msw_all_zero {n} (ar : array word n)
: ∀ i, msw ar ≤ up i → ar.read i = 0 :=
sorry

def data {n} (p q : bignum) : array word n :=
⟨ λ i , add_val p q i.val ⟩

end add

def add (p q : bignum) : bignum :=
{ cap := max p.size.val q.size.val + 1
, data := add.data p q
, size := add.msw (add.data p q)
, msw_not_zero := add.msw_not_zero (add.data p q)
, all_zero := add.msw_all_zero (add.data p q) }

instance : has_add bignum :=
⟨ add ⟩

theorem to_nat_add (p q : bignum)
: (p + q).to_nat = p.to_nat + q.to_nat :=
sorry

-- todo: look into setoid
-- the same nat can be represented by two different bignums
-- by just padding the number with zeros
instance : add_monoid bignum :=
{ zero := zero
, add  := add
, add_zero  := sorry
, zero_add  := sorry
, add_assoc := sorry }

end bignum

namespace list

open nat

def to_nat : list window → ℕ
 | [] := 0
 | (w :: ws) := w.val + win_vals * to_nat ws

def from_nat : ℕ → list window
| n :=
if h : n > 0
then
  let x := n / win_vals,
      y := n % win_vals in
  have Hv_pos : 1 < win_vals, from win_vals_gt_one,
  have Hlt : n * 1 < n * win_vals, from mul_lt_mul_of_pos_left Hv_pos h,
  have Hdec : n / win_vals < n,
     begin
       rw [div_lt_iff_lt_mul],
       { rw mul_one at Hlt,
         apply Hlt },
       apply lt_trans _ Hv_pos,
       apply zero_lt_succ,
     end,
  (fin.of_nat y) :: from_nat x
else
  []

lemma to_nat_from_nat (n : ℕ)
: to_nat (from_nat n) = n :=
sorry

end list

namespace mod_group

infix ^ := pow

namespace version0

open list nat

def expmod {m : ℕ} (p : fin (succ m)) (e : list window) : fin (succ m) :=
e.reverse.foldl (λ r w, r^win_vals * p^w.val) 1

theorem expmod_def {m : ℕ} (p : fin (succ m)) (e : list window)
: expmod p e = p^e.to_nat :=
begin
  simp [expmod,foldl_eq_foldr],
  induction e,
  case nil
  { simp [to_nat], },
  case cons e es
  { simp [foldr,ih_1],
    simp [flip,to_nat,pow_add,pow_mul,pow_pow_comm], }
end

end version0

-- tentative
namespace version1

local infix ^ := pow

open list

@[reducible]
def bignum := list word

instance : has_one bignum :=
⟨ [1] ⟩

def bignum.to_nat : bignum → ℕ :=
sorry

def trunc_mul (n : ℕ) (p q : bignum) : bignum :=
sorry

def mod (p q : bignum) : bignum :=
sorry

def pow_table (ws : ℕ) (p : bignum) : ℕ → bignum
 | 0 := 1
 | (nat.succ n) := trunc_mul ws p (pow_table n)

def win_pow (ws : ℕ) : bignum → bignum :=
nat.repeat (λ _ p, trunc_mul ws p p) window_size

def expmod (p : bignum) (e : list window) (m : bignum) : bignum :=
let ws := m.length, -- `word size` of the modulus
    pow_t : array  bignum win_vals := array.mk (λ i, pow_table ws p i.val) in
mod (e.reverse.foldl (λ r w, trunc_mul ws (win_pow ws r) (pow_t.read w)) 1) m

theorem expmod_def (p : bignum) (e : list window) (m : bignum)
: (expmod p e m).to_nat = p.to_nat ^ e.to_nat % m.to_nat :=
sorry

-- def breakup : word → list window :=
-- sorry

-- -- return `window_size` sized windows from the most significant to the least
-- def windows (p : bignum) : list window :=
-- p.data.rev_list.bind breakup

-- def from_windows (ws : list window) : bignum :=
-- sorry

-- @[simp]
-- lemma from_windows_nil
-- : from_windows nil = 0 :=
-- sorry

-- @[simp]
-- lemma to_nat_zero
-- : bignum.to_nat 0 = 0 :=
-- sorry

-- lemma windows_eq_nil_imp_self_eq_zero {p : bignum}
--   (h : windows p = nil)
-- : p.to_nat = 0 :=
-- sorry

-- lemma to_nat_from_windows_windows_eq_to_nat_self {p : bignum}
-- : (from_windows (windows p)).to_nat = p.to_nat :=
-- sorry

end version1

end mod_group

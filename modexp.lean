
import data.bitvec

def word_size : ℕ := 32

def num_vals : ℕ := 2^word_size

@[reducible]
def word := bitvec word_size

open nat

def up {n : ℕ} : fin n → fin (succ n)
 | ⟨i,P⟩ := ⟨i,show i < succ n, by { transitivity n, { apply P }, { apply nat.lt_succ_self } }⟩

structure bignum :=
  (cap  : ℕ)
  (size : fin (succ cap))
  (data : array word cap)
  (all_zero : ∀ i, size ≤ up i → data.read i = 0)
  (msw_not_zero : ∀ last, fin.succ last = size → data.read last ≠ 0)

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

def add_carry (p q : bignum) : ℕ → word
 | 0 := 0
 | (succ i) :=
   let c := (add_carry i).to_nat,
       x := (p.words $ succ i).to_nat,
       y := (q.words $ succ i).to_nat in
   if num_vals ≤ c + x + y
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
, add := add
, add_zero := sorry
, zero_add := sorry
, add_assoc := sorry }

end bignum

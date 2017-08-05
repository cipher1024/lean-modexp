
import data.bitvec

def word_size := 32

@[reducible]
def word := bitvec word_size

open nat

def up {n : ℕ} : fin n → fin (succ n)
 | ⟨i,P⟩ := ⟨i,by { transitivity n, { apply P }, { apply nat.lt_succ_self } }⟩

#check @array.read

structure bignum :=
  (cap  : ℕ)
  (size : fin (succ cap))
  (data : array word cap)
  (all_zero : ∀ i, size ≤ up i → data.read i = 0)
  (msb_not_zero : ∀ last, fin.succ last = size → data.read last ≠ 0)

namespace bignum

def to_nat (n : bignum) : ℕ :=
n.data.iterate 0 (λ i w r, r + w.to_nat * 2 ^ (i.val * word_size))

end bignum

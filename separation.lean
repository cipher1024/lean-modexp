
import data.bitvec

universe u

open nat

@[reducible]
def pointer := ℕ

@[reducible]
def word := bitvec 32

def heap := pointer → option word

structure hstate :=
  (heap : heap)
  (next : ℕ)
  (free : ∀ p, p ≥ next → heap p = none)

@[reducible]
def prog := state_t hstate option

def hprop := heap → Prop

def disjoint (h₀ h₁ : heap) :=
(∀ p, h₀ p = none ∨ h₁ p = none)

infix ` ## `:51 := disjoint

def part'  (h₀ h₁ : heap) (_ : h₀ ## h₁) : heap
 | p := h₀ p <|> h₁ p

def maplet (p : pointer) (v : word) : heap
  | q :=
if p = q then some v else none

def heap.emp : heap :=
λ _, none

def heap.mk : pointer → list word → heap
| _ [] := heap.emp
| p (v :: vs) := λ q, maplet p v q <|> heap.mk (p+1) vs q

def left_combine (h₀ h₁ : heap) : heap
 | p := h₀ p <|> h₁ p

def heap.delete : pointer → ℕ → heap → heap
 | p 0 h q := h q
 | p (succ n) h q :=
if p = q then none
else heap.delete (p+1) n h q

infix ` <+ `:54 := left_combine

section noncomp

local attribute [instance] classical.prop_decidable

noncomputable def part (h₀ h₁ : heap) : option heap :=
if Hd : disjoint h₀ h₁
then some (part' h₀ h₁ Hd)
else none

end noncomp

lemma part_comm (h₀ h₁ : heap)
: part h₀ h₁ = part h₁ h₀ :=
sorry

lemma disjoint_symm {h₀ h₁ : heap}
  (h : h₀ ## h₁)
: h₁ ## h₀ :=
sorry

lemma part_comm' {h₀ h₁ : heap}
  (h : h₀ ## h₁)
: part' h₀ h₁ h = part' h₁ h₀ (disjoint_symm h) :=
sorry

lemma part'_part_assoc {h₀ h₁ h₂ : heap}
  (Hdisj : disjoint h₀ h₁)
  (Hdisj' : disjoint h₁ h₂)
: part (part' h₀ h₁ Hdisj) h₂ = part h₀ (part' h₁ h₂ Hdisj') := sorry

lemma disjoint_of_part {h h₀ h₁ : heap}
  (HH : some h = part h₀ h₁)
: h₀ ## h₁ :=
sorry

lemma part'_of_part {h h₀ h₁ : heap}
  (H : some h = part h₀ h₁)
: h = part' h₀ h₁ (disjoint_of_part H) :=
sorry

def s_and (p q : hprop) : hprop
 | h := ∃ h₀ h₁, some h = part h₀ h₁ ∧ p h₀ ∧ q h₁
infix ` :*: `:55 := s_and

def emp : hprop
 | h := ∀ p, h p = none

def points_to (p : ℕ) (val : word) : hprop
 | h := h p = some val ∧
        ∀ q, q ≠ p → h q = none

infix ` ↦ `:60 := points_to

def points_to_multiple : ∀ (p : ℕ), list word → hprop
 | _ [] := emp
 | p (x :: xs) := p ↦ x :*: points_to_multiple (p+1) xs

infix ` ↦* `:60 := points_to_multiple

structure spec (r : Type u) :=
  (pre : hprop)
  (post : r → hprop)

def sat {α} (p : prog α) (s : spec α) : Prop :=
∀ (σ : hstate) h₀ h₁,
   some σ.heap = part h₀ h₁ →
   s.pre h₀ →
(∃ r σ' h', p σ = some (r, σ') ∧
            some σ'.heap = part h₁ h' ∧
            s.post r h')

lemma s_and_part {h₀ h₁ : heap} {p₀ p₁ : hprop}
  (h : h₀ ## h₁)
  (Hp₀ : p₀ h₀)
  (Hp₁ : p₁ h₁)
: (p₀ :*: p₁) (part' h₀ h₁ h) :=
sorry

def embed (p : Prop) : hprop := λ ptr, p ∧ emp ptr

notation `[| `p` |]` := embed p

def hexists {α : Type u} (p : α → hprop) : hprop
 | ptr := ∃ i, p i ptr

notation `∃∃` binders `, ` r:(scoped P, hexists P) := r

lemma s_and_comm (p q : hprop)
: p :*: q = q :*: p := sorry

lemma s_and_assoc (p q r : hprop)
: p :*: (q :*: r) = (p :*: q) :*: r := sorry

lemma disjoint_disjoint {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : part' h₂ h₃ H₁ ## h₁)
: h₁ ## h₃ :=
sorry

section

variables {α β : Type}
variable P : prog α
variable P' : α → prog β
variables p q : hprop
variables r : α → hprop
variables r' : β → hprop
variable s : spec α

lemma framing
  (h : sat P { pre := p, post := r })
: sat P { pre := p :*: q, post := λ x, r x :*: q } :=
begin
  unfold sat spec.pre spec.post,
  introv Hpart Hpre,
  cases Hpre with h₂ Hpre, cases Hpre with h₃ Hpre,
  rw part'_of_part Hpre.left at Hpart,
  cases Hpre with Hpre₀ Hpre₁, cases Hpre₁ with Hpre₁ Hpre₂,
  have Hdisj := disjoint_disjoint (disjoint_of_part Hpre₀) (disjoint_of_part Hpart),
  have h' := h σ h₂ (part' h₁ h₃ Hdisj) _ Hpre₁, unfold spec.pre spec.post at h',
  { rw part_comm at Hpart,
    cases h' with x h', cases h' with σ' h', cases h' with h' h''',
    existsi x, existsi σ',
    have Hdisj' : h' ## h₃, admit,
    cases h''' with hP Ph₁, cases Ph₁ with Ph₁ Ph₂,
    existsi part' h' h₃ Hdisj',
    split, assumption,
    split,
    { rw [part'_part_assoc _ _,part_comm' (disjoint_symm Hdisj')] at Ph₁,
      apply Ph₁ },
    { apply s_and_part _ Ph₂ Hpre₂, } },
  { rw [part'_part_assoc _ (disjoint_symm Hdisj),part_comm'] at Hpart,
    apply Hpart, },
end

lemma bind
  (h  : sat P { pre := p, post := r })
  (h' : ∀ x, sat (P' x) { pre := r x, post := r' })
: sat (P >>= P') { pre := p, post := r' } :=
sorry

lemma option.get_eq_of_is_some {x : option α}
  (h : option.is_some x)
: x = some (option.get h) :=
sorry

def read (p : pointer) : prog word := do
h ← state_t.read,
state_t.lift $ h.heap p

def write (p : pointer) (v : word) : prog unit := do
s ← state_t.read,
if h : (s.heap p).is_some then
  state_t.write
    { s with
      heap := (λ q : pointer, if p = q then some v else s.heap q)
    , free :=
      begin
        intros q h',
        by_cases p = q with h'',
        { rw if_pos h'',
          exfalso, subst q,
          have h₃ := s.free p h',
          rw option.get_eq_of_is_some h at h₃,
          contradiction },
        { rw if_neg h'', apply s.free _ h' }
      end }
else state_t.lift none

def alloc (vs : list word) : prog pointer := do
s ← state_t.read,
let r := s.next,
state_t.write
  { s with next := s.next + vs.length,
           heap := heap.mk r vs <+ s.heap,
           free := sorry },
return r

open nat

def free (p : pointer) (ln : ℕ) : prog unit := do
s ← state_t.read,
state_t.write
  { s with heap := heap.delete p ln s.heap,
           free := sorry }

lemma read_spec (p : pointer) (v : word)
: sat (read p) { pre := p ↦ v, post := λ r, [| v = r |] :*: p ↦ v } :=
sorry

lemma write_spec (p : pointer) (v v' : word)
: sat (write p v') { pre := p ↦ v, post := λ r, p ↦ v' } :=
sorry

lemma alloc_spec (vs : list word)
: sat (alloc vs) { pre := emp, post := λ r, r ↦* vs } :=
sorry

lemma free_spec (p : pointer) (vs : list word)
: sat (free p vs.length) { pre := p ↦* vs, post := λ r, emp } :=
sorry

end

namespace examples

def swap_ptr (p q : pointer) : prog unit :=
sorry

def swap_ptr_spec (p q : pointer) (v₀ v₁ : word)
: sat (swap_ptr p q) { pre := p ↦ v₀ :*: q ↦ v₁
                     , post := λ _, p ↦ v₁ :*: q ↦ v₀ } :=
sorry

def map_list (p : pointer) : prog unit :=
sorry

def is_list : pointer → list word → hprop
  | p [] := [| p = 0 |]
  | p (v :: vs) := ∃∃ nx : word, [| nx ≠ 0 |] :*: p ↦* [v,nx] :*: is_list nx.to_nat vs

lemma map_list_spec (p : pointer) (vs : list word)
: sat (map_list p) { pre := is_list p vs,
                     post := λ _, is_list p (list.map (+1) vs) } :=
sorry

def list_reverse (p : pointer) : prog pointer :=
sorry

def list_reverse' (p : pointer) : prog pointer :=
sorry

lemma list_reverse_spec (p : pointer) (vs : list word)
: sat (list_reverse p) { pre := is_list p vs,
                         post := λ q, is_list q (list.reverse vs) } :=
sorry

lemma list_reverse_spec' (p : pointer) (vs : list word)
: sat (list_reverse' p) { pre := is_list p vs,
                         post := λ q, is_list q (list.reverse vs) } :=
sorry

def list_reverse_dup (p : pointer) : prog pointer :=
sorry

lemma list_reverse_dup_spec (p : pointer) (vs : list word)
: sat (list_reverse p) { pre := is_list p vs,
                         post := λ q, is_list p vs :*: is_list q (list.reverse vs) } :=
sorry

inductive tree (α : Type u)
  | leaf {} : tree
  | node : tree → α → tree → tree

def is_tree : pointer → tree word → hprop
  | p tree.leaf := [| p = 0 |]
  | p (tree.node l x r) := ∃∃ lp rp : word,
          [| p ≠ 0 |] :*:
          p ↦* [lp,x,rp] :*:
          is_tree lp.to_nat l :*:
          is_tree rp.to_nat r

def free_tree : pointer → prog unit :=
sorry

lemma free_tree_spec (p : pointer) (t : tree word)
: sat (free_tree p) { pre := is_tree p t
                    , post := λ _, emp } :=
sorry

end examples

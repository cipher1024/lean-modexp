
import data.bitvec
import util.logic
import util.control.monad.non_termination

universes u v

open nat list function

@[reducible]
def pointer := ℕ

structure word :=
to_word :: (to_ptr : ℕ)

instance : has_zero word := ⟨ ⟨ 0 ⟩ ⟩
instance : has_one word := ⟨ ⟨ 1 ⟩ ⟩
instance : has_add word := ⟨ λ x y, ⟨ x.to_ptr + y.to_ptr ⟩ ⟩

def heap := pointer → option word

structure hstate :=
  (heap : heap)
  (next : ℕ)
  (free : ∀ p, p ≥ next → heap p = none)

@[reducible]
def program := state_t hstate nonterm

def program.fix {α : Type u} {β : Type}
  (f : (α → program β) → α → program β) : α → program β :=
curry (@nonterm.fix (α × hstate) (β × hstate) $ λ g, uncurry (f $ curry g))

def program.fix2 {α : Type u} {α' : Type v} {β : Type}
  (f : (α → α' → program β) → α → α' → program β) : α → α' → program β :=
curry (program.fix $ λ g, uncurry (f $ curry g))

def program.fix_unroll {α : Type u} {β : Type}
  (f : (α → program β) → α → program β)
: program.fix f = f (program.fix f) :=
begin
  unfold program.fix,
  transitivity,
  rw [nonterm.unroll,curry_uncurry],
  refl,
end

def program.fix2_unroll {α : Type u} {α' : Type v} {β : Type}
  (f : (α → α' → program β) → α → α' → program β)
: program.fix2 f = f (program.fix2 f) :=
begin
  unfold program.fix2,
  transitivity,
  rw [program.fix_unroll,curry_uncurry],
  refl,
end

structure hprop :=
  (apply : heap → Prop)

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

def s_and (p q : hprop) : hprop :=
⟨ λ h, ∃ h₀ h₁ d, h = part' h₀ h₁ d ∧ p.apply h₀ ∧ q.apply h₁ ⟩

infix ` :*: `:55 := s_and

def emp : hprop :=
⟨ λ h, ∀ p, h p = none ⟩

@[simp]
lemma s_and_emp (p : hprop)
: p :*: emp = p :=
sorry

@[simp]
lemma emp_s_and (p : hprop)
: emp :*: p = p :=
sorry

def points_to (p : ℕ) (val : word) : hprop :=
⟨ λ h, h p = some val ∧
        ∀ q, q ≠ p → h q = none ⟩

infix ` ↦ `:60 := points_to

def points_to_multiple : ∀ (p : ℕ), list word → hprop
 | _ [] := emp
 | p (x :: xs) := p ↦ x :*: points_to_multiple (p+1) xs

infix ` ↦* `:60 := points_to_multiple

structure spec (r : Type u) :=
  (pre : hprop)
  (post : r → hprop)

def sat {α} (p : program α) (s : spec α) : Prop :=
∀ (σ : hstate) h₀ h₁,
   some σ.heap = part h₀ h₁ →
   s.pre.apply h₀ →
(∃ r σ' h', p σ ~> (r, σ') ∧
            some σ'.heap = part h₁ h' ∧
            (s.post r).apply h')

lemma s_and_part {h₀ h₁ : heap} {p₀ p₁ : hprop}
  (h : h₀ ## h₁)
  (Hp₀ : p₀.apply h₀)
  (Hp₁ : p₁.apply h₁)
: (p₀ :*: p₁).apply (part' h₀ h₁ h) :=
sorry

def embed (p : Prop) : hprop :=
⟨ λ ptr, p ∧ emp.apply ptr ⟩

notation `[| `p` |]` := embed p

@[simp]
lemma embed_s_and_self (p : Prop)
: [| p |] :*: [| p |] = [| p |] :=
sorry

lemma embed_eq_emp {p : Prop}
  (hp : p)
: [| p |] = emp :=
sorry

def hexists {α : Type u} (p : α → hprop) : hprop :=
⟨ λ ptr, ∃ i, (p i).apply ptr ⟩

notation `∃∃` binders `, ` r:(scoped P, hexists P) := r

lemma s_and_comm (p q : hprop)
: p :*: q = q :*: p := sorry

lemma s_and_assoc (p q r : hprop)
: (p :*: q) :*: r = p :*: (q :*: r) := sorry

instance : is_associative hprop s_and := ⟨ s_and_assoc ⟩
instance : is_commutative hprop s_and := ⟨ s_and_comm ⟩

lemma disjoint_disjoint {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : part' h₂ h₃ H₁ ## h₁)
: h₁ ## h₃ :=
sorry

lemma s_exists_s_and_distr {α : Type u}
  (p : α → hprop) (q : hprop)
: (∃∃ x, p x) :*: q = (∃∃ x, p x :*: q) :=
sorry

lemma s_and_s_exists_distr {α : Type u}
  (p : α → hprop) (q : hprop)
: q :*: (∃∃ x, p x) = (∃∃ x, q :*: p x) :=
sorry

@[congr]
lemma s_exists_congr {α : Type u}
  {p q : α → hprop}
  (h : ∀ x, p x = q x)
: hexists p = hexists q :=
sorry

section

variables {α β : Type}
variables {P : program α}
variable {P' : α → program β}
variables {p p₀ p₁ q : hprop}
variables {r r₁ : α → hprop}
variables {r' : β → hprop}
variable {s : spec α}

lemma framing_right (q : hprop)
  (h : sat P { pre := p, post := r })
: sat P { pre := p :*: q, post := λ x, r x :*: q } :=
begin
  unfold sat spec.pre spec.post,
  introv Hpart Hpre,
  cases Hpre with h₂ Hpre, cases Hpre with h₃ Hpre,
  cases Hpre with d Hpre,
  rw Hpre.left at Hpart,
  cases Hpre with Hpre₀ Hpre₁, cases Hpre₁ with Hpre₁ Hpre₂,
  have Hdisj := disjoint_disjoint d (disjoint_of_part Hpart),
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

lemma framing_left (q : hprop)
  (h : sat P { pre := p, post := r })
: sat P { pre := q :*: p, post := λ x, q :*: r x } :=
sorry

lemma bind_spec (r : α → hprop)
  (h  : sat P { pre := p, post := r })
  (h' : ∀ x, sat (P' x) { pre := r x, post := r' })
: sat (P >>= P') { pre := p, post := r' } :=
sorry

lemma postcondition (r : α → hprop)
 (Hspec : sat P { pre := p, post := r })
 (Hside : ∀ x, r x = r₁ x)
: sat P { pre := p, post := r₁ } :=
sorry

lemma precondition (p : hprop)
 (Hspec : sat P { pre := p, post := r })
 (Hside : p = q)
: sat P { pre := q, post := r } :=
by { subst q, apply Hspec }

lemma bind_framing_left (p₁ : hprop)
  (H₀ : sat P { pre := p₀, post := r })
  (H₂ : p = p₀ :*: p₁)
  (H₁ : ∀ x, sat (P' x) { pre := r x :*: p₁, post := r' } )
: sat (P >>= P') { pre := p, post := r' } :=
begin
  apply precondition _ _ H₂.symm,
  apply bind_spec (λ x, r x :*: p₁),
  { apply framing_right _ H₀, },
  apply H₁,
end

lemma bind_framing_right (p₀ : hprop)
  (H₀ : sat P { pre := p₁, post := r })
  (H₂ : p = p₀ :*: p₁)
  (H₁ : ∀ x, sat (P' x) { pre := p₀ :*: r x, post := r' } )
: sat (P >>= P') { pre := p, post := r' } :=
begin
  simp [s_and_comm p₀ _] at H₁,
  apply bind_framing_left p₀ H₀ _ H₁,
  rw H₂, ac_refl
end

lemma s_exists_intro_pre {P : program β}
  (H : ∀ x, sat P { pre := r x, post := r' })
: sat P { pre := (∃∃ x, r x), post := r' } :=
sorry

lemma s_exists_elim_pre {P : program β} (x : α)
  (H : sat P { pre := (∃∃ x, r x), post := r' })
: sat P { pre := r x, post := r' } :=
sorry

lemma s_exists_intro_post {P : program β} {b : α → β → hprop} (x : α)
  (H : sat P { pre := p, post := b x })
: sat P { pre := p, post := λ r, ∃∃ x, b x r } :=
sorry

lemma framing_spec  (q : hprop)
  (h : sat P { pre := p₁, post := r₁ })
  (Hpre : p = p₁ :*: q)
  (Hpost : ∀ x, r x = r₁ x :*: q)
: sat P { pre := p, post := λ x, r x } :=
begin
  simp [Hpre,Hpost],
  apply framing_right _ h
end

lemma context_left (p : Prop)
 (H : p → sat P { pre := q, post := r })
: sat P { pre := [| p |] :*: q, post := r } := sorry

lemma context_right (p : Prop)
 (H : p → sat P { pre := q, post := r })
: sat P { pre := q :*: [| p |], post := r } := sorry

lemma option.get_eq_of_is_some {x : option α}
  (h : option.is_some x)
: x = some (option.get h) :=
sorry

def read (p : pointer) : program word := do
h ← state_t.read,
state_t.lift $ option.rec_on (h.heap p) nonterm.diverge return

def write (p : pointer) (v : word) : program unit := do
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
else state_t.lift nonterm.diverge

def modify (p : pointer) (f : word → word) : program unit :=
read p >>= write p ∘ f

def alloc (vs : list word) : program pointer := do
s ← state_t.read,
let r := s.next,
state_t.write
  { s with next := s.next + vs.length,
           heap := heap.mk r vs <+ s.heap,
           free := sorry },
return r

def alloc1 (v : word) : program pointer := do
alloc [v]

def free (p : pointer) (ln : ℕ) : program unit := do
s ← state_t.read,
state_t.write
  { s with heap := heap.delete p ln s.heap,
           free := sorry }

def free1 (p : pointer) : program unit := do
free p 1

lemma return_spec' {α : Type} (x : α) (p : hprop)
: sat (return x) { pre := p, post := λ _, p } :=
sorry

lemma return_spec {α : Type} (x : α) (p : α → hprop)
: sat (return x) { pre := p x, post := λ y, p y } :=
sorry

lemma read_spec (p : pointer) (v : word)
: sat (read p) { pre := p ↦ v, post := λ r, [| r = v |] :*: p ↦ v } :=
sorry

lemma read_head_spec (p : pointer) (v : word) (vs : list word)
: sat (read p) { pre := p ↦* v :: vs, post := λ r, [| r = v |] :*: p ↦* v :: vs } :=
begin
  simp [points_to_multiple,s_and_assoc],
  apply framing_spec (p + 1 ↦* vs) (read_spec p v),
  { ac_refl },
  intro, ac_refl,
end

lemma read_nth_spec (p : pointer) (i : ℕ) (vs : list word)
  (H : i < vs.length)
: sat (read (p+i)) { pre := p ↦* vs, post := λ r, [| r = nth_le vs i H |] :*: p ↦* vs } :=
sorry

lemma write_spec (p : pointer) (v v' : word)
: sat (write p v') { pre := p ↦ v, post := λ r, p ↦ v' } :=
sorry

def replace {α} (f : α → α) : ℕ → list α → list α
  | i [] := []
  | 0 (x :: xs) := f x :: xs
  | (succ i) (x :: xs) := x :: replace i xs

lemma write_head_spec (p : pointer) (v v' : word) (vs : list word)
: sat (write p v') { pre := p ↦* v :: vs, post := λ _, p ↦* v' :: vs } :=
sorry

lemma write_nth_spec (p : pointer) (v' : word) (i : ℕ) (vs : list word)
  (H : i < vs.length)
: sat (write (p+i) v') { pre := p ↦* vs, post := λ _, p ↦* replace (const _ v') i vs } :=
sorry

lemma modify_spec (p : pointer) (f : word → word) (v : word)
: sat (modify p f) { pre := p ↦ v, post := λ _, p ↦ f v } :=
begin
  unfold modify,
  apply bind_spec _ (read_spec p v),
  intro x, simp [function.comp],
  apply context_left,
  intro, subst x,
  apply write_spec
end

lemma modify_head_spec (p : pointer) (f : word → word) (v : word) (vs : list word)
: sat (modify p f) { pre := p ↦* v :: vs, post := λ _, p ↦* f v :: vs } :=
begin
  unfold points_to_multiple,
  apply framing_right,
  apply modify_spec,
end


lemma modify_nth_spec (p : pointer) (f : word → word) (i : ℕ) (vs : list word)
  (H : i < vs.length)
: sat (modify (p+i) f) { pre := p ↦* vs, post := λ _, p ↦* replace f i vs } :=
begin
  revert i p,
  induction vs with v vs
  ; intros i p H,
  { cases nat.not_lt_zero _ H, },
  cases i,
  case zero
  { simp [replace],
    apply modify_head_spec },
  case succ i
  { simp [replace,points_to_multiple],
    apply framing_left,
    rw [add_succ,add_succ,← succ_add,add_zero],
    apply ih_1 i (succ p),
    apply lt_of_succ_lt_succ H, }
end

lemma alloc_spec (vs : list word)
: sat (alloc vs) { pre := emp, post := λ r, r ↦* vs } :=
sorry

lemma alloc1_spec (v : word)
: sat (alloc1 v) { pre := emp, post := λ r, r ↦ v } :=
begin
  have h := alloc_spec [v],
  unfold points_to_multiple at h,
  simp [s_and_emp] at h,
  apply h
end

lemma free_spec (p : pointer) (vs : list word)
: sat (free p vs.length) { pre := p ↦* vs, post := λ r, emp } :=
sorry

lemma free1_spec (p : pointer) (v : word)
: sat (free1 p) { pre := p ↦ v, post := λ r, emp } :=
sorry

def copy (p q : pointer) : program unit := do
v ← read q,
write p v

lemma copy_spec (p q : pointer) (v₀ v₁ : word)
: sat (copy p q) { pre := p ↦ v₀ :*: q ↦ v₁
                 , post := λ _, p ↦ v₁ :*: q ↦ v₁ } :=
begin
  apply bind_spec (λ r, p ↦ v₀ :*: ([| r = v₁ |] :*: q ↦ v₁)),
  { apply framing_left, apply read_spec },
  { intro r, simp,
    apply precondition (p ↦ v₀ :*: q ↦ v₁ :*: [| r = v₁ |]),
    { apply context_right, intro, subst r,
      apply framing_right,
      apply write_spec },
    { ac_refl } }
end

end

namespace examples

def swap_ptr (p q : pointer) : program unit := do
t ← alloc1 0,
copy t p,
copy p q,
copy q t,
free1 t

lemma swap_ptr_spec (p q : pointer) (v₀ v₁ : word)
: sat (swap_ptr p q) { pre := p ↦ v₀ :*: q ↦ v₁
                     , post := λ _, p ↦ v₁ :*: q ↦ v₀ } :=
begin
  unfold swap_ptr,
  apply bind_framing_right (p ↦ v₀ :*: q ↦ v₁) (alloc1_spec _),
  { simp [s_and_emp] },
  intro t, simp,
  apply bind_framing_right (q ↦ v₁) (copy_spec t p 0 v₀),
  { ac_refl },
  intro x, cases x, simp,
  apply bind_framing_right (t ↦ v₀) (copy_spec p q v₀ v₁),
  { ac_refl },
  intro x, cases x, simp,
  apply bind_framing_right (p ↦ v₁) (copy_spec q t v₁ v₀),
  { ac_refl },
  intro x, cases x, simp, rw ← s_and_assoc,
  apply framing_spec (p ↦ v₁ :*: q ↦ v₀)  (free1_spec t v₀),
  { ac_refl },
  { intro x, cases x, simp },
end

open program

def map_list : pointer → program unit :=
fix $ λ map_list p,
if h : p = 0
then return ()
else do
  modify p (+1),
  p' ← read $ p+1,
  map_list p'.to_ptr

lemma map_list_def (p : pointer)
: map_list p =
  if p = 0 then return ()
  else do
    modify p (+1),
    p' ← read $ p+1,
    map_list p'.to_ptr :=
begin
  unfold map_list,
  transitivity,
  rw [program.fix_unroll,dif_eq_if], refl
end


def is_list : pointer → list word → hprop
  | p [] := [| p = 0 |]
  | p (v :: vs) := [| p ≠ 0 |] :*: ∃∃ nx : word, p ↦* [v,nx] :*: is_list nx.to_ptr vs

lemma map_list_spec (p : pointer) (vs : list word)
: sat (map_list p)
    { pre := is_list p vs
    , post := λ _, is_list p (list.map (+1) vs) } :=
begin
  revert p,
  induction vs ; intros p,
  case nil
  { unfold map is_list,
    rw ← embed_s_and_self,
    apply context_left, simp,
    intro Hp₀, rw [map_list_def],
    rw if_pos Hp₀,
    apply return_spec' },
  case cons x xs
  { unfold map is_list,
    apply context_left, intro Hp_nz,
    rw [map_list_def],
    rw if_neg Hp_nz, simp,
    apply s_exists_intro_pre _,
    intro nx,
    apply bind_framing_right (is_list (nx.to_ptr) xs)
                             (modify_head_spec p (+1) x [nx]),
    { ac_refl },
    intro x, cases x, simp,
    apply bind_framing_right (is_list (nx.to_ptr) xs)
                             (read_nth_spec p 1 [x+1,nx] (of_as_true trivial)),
    { ac_refl },
    intro r_nx, simp [nth_le,embed_eq_emp Hp_nz],
    rw [← s_and_comm,s_and_assoc],
    apply context_left, intro Hnx,
    subst r_nx,
    apply s_exists_intro_post nx,
    apply framing_left,
    apply ih_1, }
end

def list_reverse_aux : ∀ (p r : pointer),  program pointer :=
fix2 $ λ list_reverse_aux p r,
if p = 0 then return r
else do
  p' ← read (p+1),
  write (p+1) ⟨ r ⟩,
  list_reverse_aux p'.to_ptr p

lemma list_reverse_aux_def (p r : pointer)
: list_reverse_aux p r =
  if p = 0 then return r
  else do
    p' ← read (p+1),
    write (p+1) ⟨ r ⟩,
    list_reverse_aux p'.to_ptr p :=
begin
  unfold list_reverse_aux,
  transitivity,
  rw [program.fix2_unroll], refl
end

lemma list_reverse_aux_spec (p r : pointer) (xs ys : list word)
: sat (list_reverse_aux p r)
      { pre := is_list p xs :*: is_list r ys
      , post := λ r', is_list r' (reverse xs ++ ys) } :=
begin
  revert p r ys,
  induction xs ; intros p r ys,
  case nil
  { simp [is_list],
    apply context_left,
    intro h,
    rw [list_reverse_aux_def,if_pos h],
    apply postcondition _ (return_spec r _),
    intro, simp, },
  case cons x xs
  { simp [is_list],
    rw [s_and_assoc],
    apply context_left,
    intro h,
    rw [list_reverse_aux_def,if_neg h,s_exists_s_and_distr],
    apply s_exists_intro_pre, intro nx,
    apply bind_framing_left _ (read_nth_spec p 1 [x,nx] (of_as_true trivial)),
    { rw s_and_assoc },
    intro r, simp [nth_le,s_and_assoc],
    apply context_left,
    intro, subst r,
    apply bind_framing_left _ (write_nth_spec p _ 1 [x,nx] _),
    { refl },
    intro x, cases x, simp [replace,const],
    have h : is_list r ys = is_list ( word.to_word r ).to_ptr ys, { simp },
    rw h, clear h,
    generalize : (word.to_word r) = k,
    apply s_exists_elim_pre k,
    apply precondition (is_list nx.to_ptr xs :*: is_list p (x :: ys)),
    apply ih_1 nx.to_ptr p (x :: ys),
    { simp [is_list,embed_eq_emp h],
      rw [s_and_s_exists_distr],
      apply s_exists_congr,
      intro, ac_refl },
    { apply of_as_true, trivial } }
end

def list_reverse (p : pointer) : program pointer :=
list_reverse_aux p 0

lemma list_reverse_spec (p : pointer) (xs : list word)
: sat (list_reverse p)
      { pre := is_list p xs
      , post := λ r, is_list r (reverse xs) } :=
begin
  unfold list_reverse,
  apply precondition (is_list p xs :*: is_list 0 []),
  apply postcondition _ (list_reverse_aux_spec p 0 xs []),
  { intros, simp },
  { simp [is_list,embed_eq_emp], }
end

def list_reverse' (p : pointer) : program pointer :=
sorry

lemma list_reverse_spec (p : pointer) (vs : list word)
: sat (list_reverse p) { pre := is_list p vs,
                         post := λ q, is_list q (list.reverse vs) } :=
sorry

lemma list_reverse_spec' (p : pointer) (vs : list word)
: sat (list_reverse' p) { pre := is_list p vs,
                         post := λ q, is_list q (list.reverse vs) } :=
sorry

def list_reverse_dup (p : pointer) : program pointer :=
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
          is_tree lp.to_ptr l :*:
          is_tree rp.to_ptr r

def free_tree : pointer → program unit :=
sorry

lemma free_tree_spec (p : pointer) (t : tree word)
: sat (free_tree p) { pre := is_tree p t
                    , post := λ _, emp } :=
sorry

end examples

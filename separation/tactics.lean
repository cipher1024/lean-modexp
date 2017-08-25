
import data.dlist
import ..separation.specification

universes u v

namespace tactic.interactive

open applicative
open lean.parser
open interactive
open interactive.types
open tactic has_map list nat separation

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def mk_sep_assert : list expr → expr
 | [] := `(emp)
 | (e :: []) := e
 | (e :: es) := `(%%e :*: %%(mk_sep_assert es))

meta def parse_sep_assert' : expr → tactic (dlist expr)
 | `(%%e₀ :*: %%e₁) := (++) <$> parse_sep_assert' e₀ <*> parse_sep_assert' e₁
 | e := return $ dlist.singleton e

meta def parse_sep_assert : expr → tactic (list expr) :=
map dlist.to_list ∘ parse_sep_assert'

meta def delete_expr (e : expr) : list expr → tactic (option (list expr))
 | [] := return none
 | (x :: xs) :=
(is_def_eq e x >> return (some xs))
<|>
(map (cons x) <$> delete_expr xs)

meta def match_sep : list expr → list expr → tactic (list expr × list expr × list expr)
 | es (x :: xs) := do
    es' ← delete_expr x es,
    match es' with
     | (some es') := do
       (c,l,r) ← match_sep es' xs, return (x::c,l,r)
     | none := do
       (c,l,r) ← match_sep es xs, return (c,l,x::r)
    end
 | es [] := do
return ([],es,[])

def expr_pat (t₀ t₁ : Type) : ℕ → Type
 | 0 := t₁
 | (succ n) := t₀ → expr_pat n

def tuple : ℕ → Type → Type
 | 0 _ := unit
 | 1 t := t
 | (succ n) t := t × tuple n t

meta def match_expr : ∀ (n : ℕ) (p : expr_pat expr pexpr n) (e : expr), tactic (tuple n expr)
  | 0 p e := to_expr p >>= unify e
  | 1 p e := do v ← mk_mvar, match_expr 0 (p v) e, instantiate_mvars v
  | (succ (succ n)) p e := do
v ← mk_mvar,
r ← match_expr (succ n) (p v) e,
e ← instantiate_mvars v,
return (e,r)

meta def reshuffle (e₀ e₁ : expr) : tactic unit := do
t ← target,
(t₀,t₁) ← match_eq t,
h₀ ← to_expr ``(%%t₀ = %%e₀) >>= assert `h₀,
solve1 ac_refl,
h₁ ← to_expr ``(%%t₁ = %%e₁) >>= assert `h₁,
solve1 admit,
`[rw h₀],
`[rw h₁],
tactic.clear h₀, tactic.clear h₁

meta def find_match (pat : expr) : expr → list expr → tactic expr
 | e rest := do
(unify e pat >> return (mk_sep_assert rest))
<|>
(do hprop ← to_expr ``(hprop),
    lv ← mk_meta_var hprop,
    rv ← mk_meta_var hprop,
    to_expr ``(%%lv :*: %%rv) >>= unify e,
      -- this unification could be generalized to:
      -- (le,re) ← match_pat (λ p₀ p₁, ``(%%p₀ :*: %%p₁))
    le ← instantiate_mvars lv,
    re ← instantiate_mvars rv,
    (find_match le (re :: rest) <|> find_match re (le :: rest)))
<|>
do p ← pp pat,
   e ← pp e,
   fail $ to_fmt "no match found for `" ++ p ++ to_fmt "` in: \n`" ++ e ++ to_fmt "`"

meta def sep_goal : tactic (expr × expr × expr) := do
g ← target,
t  ← to_expr ``(hprop),
e₀ ← mk_meta_var t,
e₂ ← mk_meta_var t,
e₃ ← mk_meta_var t,
pat ← to_expr ``(%%e₀ = %%e₂ :*: %%e₃) >>= unify g,
prod.mk <$> instantiate_mvars e₀
        <*> (prod.mk <$> instantiate_mvars e₂
                     <*> instantiate_mvars e₃)

/-- Apply on a goal of the form
    ``x = y :*: m?``
    with m? a meta variable. The goal is to decompose `x` into a conjunction
    made of an occurrence of `y` (anywhere).
 -/
meta def match_assert : tactic unit := do
(hp,pat,var) ← sep_goal,
e ← find_match pat hp [],
unify e var,
tactic.target >>= instantiate_mvars >>= tactic.change,
try `[simp] >> ac_refl

meta def match_one_term : tactic unit := do
`[simp [s_and_assoc]]


/-- apply on a goal of the form `sat p spec` -/
meta def extract_context_aux (h : name) : tactic unit := do
`[apply precondition _],
swap,
`[symmetry],
solve1 (do
--  cxt ← mk_meta_var `(Prop),
  (hp,pat,var) ← sep_goal,
  to_expr ``( [| _ |] ) >>= unify pat,
  e ← find_match pat hp [],
  unify e var,
  tactic.target >>= instantiate_mvars >>= tactic.change,
  ac_refl),
`[apply context_left],
intro h, return ()

meta def extract_context : parse ident* → tactic unit
 | [] := return ()
 | (h :: hs) := extract_context_aux h >> extract_context hs

meta def match_sep_imp : expr → tactic (expr × expr)
 | `(%%e₀ =*> %%e₁) := return (e₀, e₁)
 | _ := fail "expression is not an sep implication"

meta def ac_match' : tactic unit := do
-- reflexivity
-- <|> do
t ← target,
(e₀,e₁) ← (match_eq t <|> match_sep_imp t),
e₀ ← parse_sep_assert e₀,
e₁ ← parse_sep_assert e₁,
(c,l,r) ← match_sep e₀ e₁,
trace "reshuffle",
trace e₀,
trace e₁,
trace "result",
trace c,
trace l,
trace r,
reshuffle `(%%(mk_sep_assert c) :*: %%(mk_sep_assert l)) `(%%(mk_sep_assert c) :*: %%(mk_sep_assert r)),
trace "after reshuffle",
`[apply congr_arg]

meta def ac_match : tactic unit := do
ac_match'

def replicate {m : Type u → Type v} [monad m] {α} : ℕ → m α → m (list α)
 | 0 _ := return []
 | (succ n) m := lift₂ cons m (replicate n m)

private meta def get_pi_expl_arity_aux (t : expr) : expr → expr → tactic expr
| e r := do
(unify t e >> instantiate_mvars r)
<|>
match e with
| (expr.pi n bi d b) :=
  do m     ← mk_fresh_name,
--     let l := expr.local_const m n bi d,
     l ← mk_meta_var d,
     new_b ← instantiate_mvars (expr.instantiate_var b l),

     if binder_info.default = bi
     then get_pi_expl_arity_aux new_b (r l)
     else get_pi_expl_arity_aux new_b r
| e := instantiate_mvars r
end

/-- Compute the arity of the given (Pi-)type -/
meta def get_pi_expl_arity (target e : expr) : tactic expr := do
t ← infer_type e,
get_pi_expl_arity_aux target t e

meta def s_exists1 (v : parse ident) : tactic unit := do
`[simp [s_exists_s_and_distr,s_and_s_exists_distr], apply s_exists_intro_pre],
intro v, return ()

meta def s_exists (vs : parse ident*) : tactic unit :=
mmap' s_exists1 vs

meta def s_intros : parse ident* → tactic unit
 | [] := return ()
 | (x :: xs) := do
v ← tactic.try_core (s_exists1 x),
match v with
 | (some _) := s_intros xs
 | none := extract_context (x :: xs)
end

meta def decide : tactic unit := do
solve1 $ do
 `[apply of_as_true],
 triv

meta def bind_step (v : parse ident_? ) (ids : parse with_ident_list) : tactic unit := do
g ← target,
(hd,tl,spec) ← (match_expr 3 (λ e₀ e₁ s, ``(sat (%%e₀ >>= %%e₁) %%s)) g
             : tactic (expr × expr × expr)),
let (cmd,args) := hd.get_app_fn_args,
e ← resolve_name (mk_str_name cmd.const_name "spec") >>= to_expr,
r ← to_expr ``(sat _ _),
e' ← get_pi_expl_arity r e,
`[apply (bind_framing_left _ %%e')],
solve1 (try `[simp [s_and_assoc]] >> try match_assert),
all_goals (try `[apply of_as_true, apply trivial]),
interactive.intro v, `[simp],
extract_context ids,
repeat (extract_context_aux `_)

meta def last_step : tactic unit := do
g ← target,
(hd,spec) ← (match_expr 2 (λ e s, ``(sat %%e %%s)) g
             : tactic (expr × expr)),
let (cmd,args) := hd.get_app_fn_args,
e ← resolve_name (mk_str_name cmd.const_name "spec") >>= to_expr,
r ← to_expr ``(sat _ _),
e' ← get_pi_expl_arity r e,
`[apply (framing_spec _ %%e')],
solve1 (try `[simp [s_and_assoc]] >> try match_assert),
solve1 (try `[simp [s_and_assoc]] >> try match_assert),
all_goals (try `[apply of_as_true, apply trivial])

end tactic.interactive

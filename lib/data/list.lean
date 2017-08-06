
namespace list

lemma foldl_eq_foldr {α β}
  (xs : list α) (x : β)
  (f : β → α → β)
: foldl f x xs = foldr (flip f) x (reverse xs) :=
begin
  revert x,
  induction xs ; intro x,
  case nil
  { simp [foldl,foldr] },
  case cons y ys
  { simp [foldl,foldr,ih_1,flip,append_foldr], },
end

end list

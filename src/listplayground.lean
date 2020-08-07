import data.list

namespace listplayground

example (l : list ℕ) (hl : list.sorted nat.lt l) (hl' : l ≠ []) : list.sorted nat.lt l.tail :=
list.sorted.tail hl

example (l : list ℕ) (h : l ≠ []) : l = l.head :: l.tail := (list.cons_head_tail h).symm

-- surprised this isn't in mathlib... maybe bc this is too simple or something similar is?
-- either in head or tail
example (l : list ℕ) (a ∈ l) : a = l.head ∨ a ∈ l.tail :=
begin
  induction l,
  { right,
    exact H },
  { cases H,
    { left,
      exact H },
    { right,
      exact H } }
end

-- ahah this version is more succinct
example (l : list ℕ) (h : l ≠ []) (a ∈ l) : a = l.head ∨ a ∈ l.tail :=
begin
  rw (list.cons_head_tail h).symm at H,
  exact (list.mem_cons_iff a (list.head l) (list.tail l)).mp H,
end

-- cons smol is still sorted in lt order
lemma cons_smol_sorted (l : list ℕ) (hl : list.sorted nat.lt l) (hl' : l ≠ []) (a : ℕ) (h : a < l.head) :
list.sorted nat.lt (a :: l) :=
begin
  rw list.sorted_cons,
  split,
  { intros b hb,
    rw <- list.cons_head_tail hl' at hl,
    have hb' := list.rel_of_sorted_cons hl,
    rw (list.cons_head_tail hl').symm at hb,
    rw list.mem_cons_iff b (list.head l) (list.tail l) at hb,
    cases hb,
    { rwa hb },
    { specialize hb' b hb,
      exact lt_trans h hb' } },
  { exact hl }
end

example (a : ℕ) : list.sorted nat.lt (a :: []) :=
begin
  exact list.sorted_singleton a,
end

example (a : ℕ) : [a] = a :: [] := rfl

example (l : list ℕ) (h : l ≠ []) : ∃ x, x ∈ l :=
begin
  use l.head,
  exact list.mem_of_mem_head' (list.head_mem_head' h),
end

example (l : list ℕ) (h : ∀ x x' ∈ l, x ≠ x') : l = [] :=
begin
  contrapose! h,
  use [l.head, l.head],
  repeat { split, exact list.mem_of_mem_head' (list.head_mem_head' h) },
  refl,
end

example (l l' t : list ℕ) (h : l ~ l') : l ++ t ~ t ++ l' :=
begin
  calc l ++ t ~ t ++ l : list.perm_append_comm
       ... ~ t ++ l' : list.perm.append_left t h,
end

example (l : list ℕ) (a : ℕ) : list.cons a l  = [a] ++ l := list.singleton_append.symm

-- TODO define as appending all lists together
def flatten_lists : list (list ℕ) → list ℕ
| list.nil := list.nil
| [list.nil] := list.nil
| [h :: x] := h :: x
| sorry

example (l l' : list (list ℕ)) (h : l ~ l') : flatten_lists l ~ flatten_lists l' :=
begin
  sorry
end

example (a : ℕ) (l l' : list ℕ) : list.cons a (l ++ l') = a :: l ++ l' := (list.cons_append a l l').symm

end listplayground

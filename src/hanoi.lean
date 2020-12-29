import data.list
import tactic
import listplayground

open listplayground

-- THIRD TIME'S THE CHARM??
namespace hanoi

@[derive has_reflect]
structure position := (A : list ℕ) (B : list ℕ) (C : list ℕ)

instance towers_has_repr : has_repr position := ⟨λ t, "A: " ++ t.A.repr ++ " B: " ++ t.B.repr ++ " C: " ++ t.C.repr⟩

#eval position.mk [1, 2] [] []

#check position
#check position.A

-- smoooooosh
def flatten (t : position) : list ℕ := t.A ++ t.B ++ t.C

-- number of disks on the position
def num_disks (t : position) : ℕ := t.A.length + t.B.length + t.C.length

-- is it true any valid tower can get to another valid tower w/equal number of disks?
-- Kevin says yes by induction

def unique_disks (t : position) : Prop := list.nodup (flatten t)
-- ∀ d ∈ (flatten t), (list.filter (λ d', d' = d) (flatten t)) = [d]

-- valid position only have lists that are strictly increasing
-- valid position have no duplicate disks
def valid_tower (t : position) : Prop :=
list.sorted nat.lt t.A ∧ list.sorted nat.lt t.B ∧ list.sorted nat.lt t.C ∧ unique_disks t

#check valid_tower

def valid_tower' (t : position) : Prop :=
list.sorted nat.lt t.A ∧ list.sorted nat.lt t.B ∧ list.sorted nat.lt t.C
∧ list.merge nat.lt (list.merge nat.lt t.A t.B) t.C = list.range' 1 (num_disks t)

#check valid_tower' -- don't reduce this unless you want to make your computer wheeeeze

@[derive has_reflect, derive decidable_eq]
inductive tower : Type
| a | b | c


open tower

def tower_to_string : tower → string
| a := "a" | b := "b" | c := "c"

instance : has_to_string tower := ⟨tower_to_string⟩

def tow (t : position) : tower → list ℕ
| a := t.A
| b := t.B
| c := t.C

example (t : position) : tow t a = t.A := by refl

def move (t : position) : tower → tower → position
| a a := t
| a b := position.mk (t.A.tail) (t.A.head :: t.B) t.C
| a c := position.mk (t.A.tail) t.B (t.A.head :: t.C)
| b a := position.mk (t.B.head :: t.A) (t.B.tail) t.C
| b b := t
| b c := position.mk t.A (t.B.tail) (t.B.head :: t.C)
| c a := position.mk (t.C.head :: t.A) t.B (t.C.tail)
| c b := position.mk t.A (t.C.head :: t.B) (t.C.tail)
| c c := t

@[simp]
lemma move_self (t : position) (s : tower) : move t s s = t := by cases s; refl -- why does rfl not work??

#check move

def valid_move (t : position) : tower → tower → Prop
| a a := true
| a b := t.A ≠ [] ∧ ((t.B ≠ [] ∧ t.A.head < t.B.head) ∨ t.B = [])
| a c := t.A ≠ [] ∧ ((t.C ≠ [] ∧ t.A.head < t.C.head) ∨ t.C = [])
| b a := t.B ≠ [] ∧ ((t.A ≠ [] ∧ t.B.head < t.A.head) ∨ t.A = [])
| b b := true
| b c := t.B ≠ [] ∧ ((t.C ≠ [] ∧ t.B.head < t.C.head) ∨ t.C = [])
| c a := t.C ≠ [] ∧ ((t.A ≠ [] ∧ t.C.head < t.A.head) ∨ t.A = [])
| c b := t.C ≠ [] ∧ ((t.B ≠ [] ∧ t.C.head < t.B.head) ∨ t.B = [])
| c c := true

lemma invalid_move (t : position) (s d : tower) : ¬valid_move t s d ↔ (tow t s = [] ∨ (tow t s ≠ [] ∧ tow t d ≠ [] ∧ tow t d < tow t s)) :=
begin
  split,
  { intros h,
    cases s; cases d;
    try { unfold valid_move at h; exfalso; rw not_true at h, exact h };
    sorry
  },
  { sorry }
end

#check valid_move

-- also rw is huuuuge when we rw h. does not look nice!
example (t : position) (h : t = position.mk [1,2,3] [] []) : move t a b = position.mk [2,3] [1] [] :=
begin
  rw h,
  refl,
end

/- non-inductive definition is a lot of work... -/

def can_get_to_one (t t' : position) : Prop := ∃ (s d : tower), valid_move t s d ∧ move t s d = t'

-- lol is there a way to simplify this?
-- answer: use the inductive definition lmao
def can_get_to_gt_one (t t' : position) : Prop := ∃ (tows : list position), (∃ first ∈ tows, ∃ last ∈ tows, can_get_to_one t first ∧ can_get_to_one last t' ∧ (∀ tow ∈ tows, tow ≠ last → (∃ tow' ∈ tows, tow ≠ tow' ∧ can_get_to_one tow tow')))

def can_get_to (t t' : position) : Prop := can_get_to_one t t' ∨ can_get_to_gt_one t t'

#check can_get_to

lemma can_get_to_one_self (t : position) : can_get_to_one t t :=
begin
  use [a, a],
  split,
  { exact trivial },
  { refl }
end

-- you can always meander and use more moves
lemma can_get_to_one_can_get_to_gt_one (t t' : position) (h : can_get_to_one t t') : can_get_to_gt_one t t' :=
begin
  use [[t], t, t],
  split,
  { exact list.mem_singleton_self _ },
  { split,
    { exact can_get_to_one_self t },
    { split,
      { exact h },
      { intros tow htow_in htow_ne_t,
        rw list.mem_singleton at htow_in,
        contradiction } } }
end

lemma can_get_to_gt_one_self (t : position) : can_get_to_gt_one t t :=
begin
  apply can_get_to_one_can_get_to_gt_one,
  exact can_get_to_one_self t,
end

lemma can_get_to_self (t : position) : can_get_to t t :=
begin
  left,
  exact can_get_to_one_self t,
end

-- not sure how useful this will be
lemma flatten_perm (t : position) (t₁ t₂ t₃ : tower) (h : t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃) :
flatten t ~ tow t t₁ ++ tow t t₂ ++ tow t t₃ :=
begin
  rcases h with ⟨h₁, h₂, h₃⟩,
  cases t₁; cases t₂; cases t₃;
  try { contradiction }; -- get rid of any cases w/duplicates
  try { unfold flatten, unfold tow },
  { -- a b c ~ a c b
    rw [list.append_assoc, list.append_assoc],
    apply list.perm.append_left,
    exact list.perm_append_comm },
  { -- a b c ~ b a c
    apply list.perm.append_right,
    exact list.perm_append_comm },
  { -- a b c ~ b c a
    rw list.append_assoc,
    exact list.perm_append_comm },
  { -- a b c ~ c a b
    conv_rhs { rw list.append_assoc },
    exact list.perm_append_comm },
  { -- a b c ~ c b a
    have h : t.A ++ t.B ~ t.B ++ t.A := list.perm_append_comm,
    conv_rhs { rw list.append_assoc },
    calc (t.A ++ t.B) ++ t.C ~ t.C ++ (t.A ++ t.B) : list.perm_append_comm
         ... ~ t.C ++ (t.B ++ t.A) : list.perm.append_left t.C h }
end

lemma valid_move_perm (t : position) (s d : tower) (hv : valid_move t s d) : flatten t ~ flatten (move t s d) :=
begin
  cases s; cases d;
  try { rw move_self },
  case a b { apply list.perm.append_right,
             conv_lhs { rw (list.cons_head_tail hv.1).symm },
             rw list.cons_append,
             exact list.perm_middle.symm },
  case a c { have h := flatten_perm (move t a c) c a b (by tauto),
             unfold flatten at ⊢ h, unfold move at ⊢ h, unfold tow at h, dsimp only at ⊢ h,
             conv_lhs { rw <- list.cons_head_tail hv.1 },
             suffices h' : t.A.head :: t.A.tail ++ t.B ++ t.C ~ t.A.head :: t.C ++ t.A.tail ++ t.B,
             { exact list.perm.trans h' (list.perm.symm h) },
             { sorry
             }
           },
  repeat { sorry }
end

lemma valid_move_unique_disks (t : position) (h : unique_disks t) (s d : tower) (hv : valid_move t s d) :
unique_disks (move t s d) :=
begin
  unfold unique_disks,
  cases s; cases d; unfold move;
  sorry
end

lemma move_self_valid_is_valid (t : position) (s : tower) :
valid_tower t ∧ valid_move t s s → valid_tower (move t s s) :=
begin
  intros h,
  rw move_self,
  exact h.1,
end

-- moving to self is always valid
lemma move_self_valid_is_valid' (t : position) (s : tower) :
valid_tower t → valid_tower (move t s s) :=
begin
  intros h,
  rwa move_self,
end

-- a valid move on a valid position results in a valid position
lemma move_valid_is_valid (t : position) (s d : tower) :
valid_tower t ∧ valid_move t s d → valid_tower (move t s d) :=
begin
  rintros ⟨ht, hm⟩,
  cases s; cases d;
  try { exact move_self_valid_is_valid' t _ ht }; -- move to self is valid
  try { rcases ht with ⟨htA, htB, htC, htd⟩, rcases hm with ⟨hml, hmr, hmr'⟩; split };
  try { split }; try { split };
  try { exact list.sorted.tail htA }; -- moving from A guarantees A is still sorted
  try { exact list.sorted.tail htB }; -- moving from B guarantees B is still sorted
  try { exact list.sorted.tail htC }; -- moving from C guarantees C is still sorted
  try { exact htA }; -- A is unaffected
  try { exact htB }; -- B is unaffected
  try { exact htC }; -- C is unaffected
  try { unfold move; rw hm_right; exact list.sorted_singleton _ }, -- moving to nil guarantees sorted
  -- insert perms lemma to prove nodups and thus unique disks
  { exact cons_smol_sorted t.B htB hmr t.A.head hmr' },
  repeat { sorry }
end

-- TODO this is a mess
lemma valid_move_sym (t : position) (s d : tower) : valid_move t s d → valid_move (move t s d) d s :=
begin
  intros h,
  cases s; cases d,
  all_goals {sorry}
end

lemma can_get_to_one_sym (t t' : position) : can_get_to_one t t' → can_get_to_one t' t :=
begin
  intros h,
  rcases h with ⟨s, d, h⟩,
  use [d, s],
  sorry
end

lemma can_get_to_one_can_get_to (t t' : position) : can_get_to_one t t' → can_get_to t t' :=
begin
  intros h,
  left,
  exact h,
end

-- if t₁ can get to t₂ in one move, and t₂ can get to t₃ in one move, then t₁ can get to t₃
lemma can_get_to_one_twice (t₁ t₂ t₃ : position) (h₁ : can_get_to_one t₁ t₂) (h₂ : can_get_to_one t₂ t₃) : can_get_to t₁ t₃ :=
begin
  right,
  use [[t₂], t₂, t₂], -- one middle tower, thus same point of entry/exit
  split,
  { exact list.mem_singleton_self _ },
  { split,
    { exact h₁ },
    { split,
      { exact h₂ },
      { intros tow htow_in htow_ne_last,
        exfalso,
        apply htow_ne_last,
        rwa list.mem_singleton at htow_in } } }
end

-- if t₁ can get to t₂ in one move, and t₂ can get to t₃ in multiple moves, then t₁ can get to t₃
lemma can_get_to_one_gt_one (t₁ t₂ t₃ : position) (h₁ : can_get_to_one t₁ t₂) (h₂ : can_get_to_gt_one t₂ t₃) : can_get_to t₁ t₃ :=
begin
  rcases h₂ with ⟨tows, first, hfirst_in, last, hlast_in, hstart_cgt, hlast_cgt, hmid⟩,
  right,
  use [t₂ :: tows, t₂, list.mem_cons_self _ _, last, list.mem_cons_of_mem t₂ hlast_in],
  split,
  { exact h₁ },
  { split,
    { exact hlast_cgt },
    { intros tow htow_in htow_ne_last,
      cases htow_in,
      { sorry },
      { sorry }
    }
  }
end

-- TODO complicated definitions are leading to misery but ill try it anyways
-- if t₁ can get to t₂, and t₂ can get to t₃, then t₁ can get to t₃
lemma can_get_to_trans (t₁ t₂ t₃ : position) (h₁ : can_get_to t₁ t₂) (h₂ : can_get_to t₂ t₃) : can_get_to t₁ t₃ :=
begin
  cases h₁,
  { cases h₂,
    { -- can get to each other in one move
      exact can_get_to_one_twice t₁ t₂ t₃ h₁ h₂ },
    { -- can get from t₁ to t₂ in one move, but multiple moves from t₂ to t₃
      sorry
    },
  },
  { cases h₂,
    { -- multiple moves to get from t₁ to t₂ but one move from t₂ to t₃
      sorry
    },
    { -- multiple moves from each other
      sorry
    } }
end

/- inductive def should be better -/

-- alternative inductive definition (suggested by Kevin Buzzard! thanks again!)
inductive can_get_to' : position → position → Prop
| can_get_to_self' : ∀ (t : position), can_get_to' t t
| can_get_to_one' : ∀ (t t' : position), can_get_to_one t t' → can_get_to' t t'
| can_get_to_trans' : ∀ (t₁ t₂ t₃ : position), can_get_to' t₁ t₂ → can_get_to' t₂ t₃ → can_get_to' t₁ t₃
-- why does it complain about: can_get_to' t₁ t₂ ∧ can_get_to' t₂ t₃ → can_get_to' t₁ t₃??

#check can_get_to'

open can_get_to'

example (t t' : position) : can_get_to_one t t' → can_get_to' t t':=
begin
  apply can_get_to_one',
end

lemma can_get_to_trans'' (t₁ t₂ t₃ : position) : can_get_to' t₁ t₂ ∧ can_get_to' t₂ t₃ → can_get_to' t₁ t₃ :=
begin
  rintros ⟨h₁, h₂⟩,
  apply can_get_to_trans' t₁ t₂ t₃,
  exact h₁,
  exact h₂,
end

lemma can_get_to_sym' (t t' : position) : can_get_to' t t' ↔ can_get_to' t' t := sorry

-- using the non-inductive definition
def game (disks : ℕ) : Prop :=
can_get_to (position.mk (list.range' 1 disks) [] []) (position.mk [] [] (list.range' 1 disks))

-- using the inductive definition
def game' (disks : ℕ) : Prop :=
can_get_to' (position.mk (list.range' 1 disks) [] []) (position.mk [] [] (list.range' 1 disks))

#check game
#check game'

-- using non-inductive definition
example : game 1 :=
begin
  left,
  use [a, c],
  split,
  { unfold valid_move,
    exact dec_trivial },
  { refl }
end

-- using inductive definition
example : game' 1 :=
begin
  apply can_get_to_one',
  use [a, c],
  split,
  { unfold valid_move,
    exact dec_trivial },
  { refl }
end

-- making applys for tactics?
lemma can_get_to_one_move (t : position) (s d : tower) : valid_move t s d → can_get_to' t (move t s d) :=
begin
  intros h,
  apply can_get_to_one',
  use [s, d],
  split,
  { exact h },
  { refl }
end

lemma can_get_to_one_move_sym (t : position) (s d : tower) : valid_move t d s → can_get_to' (move t d s) t :=
begin
  intros h,
  apply can_get_to_one',
  use [s, d],
  split,
  { exact valid_move_sym t d s h },
  { sorry }
end

lemma fmove' {t₁ t₃ : position} (s d : tower) : valid_move t₁ s d ∧ can_get_to' (move t₁ s d) t₃ → can_get_to' t₁ t₃ :=
begin
  rintros ⟨h₁, h₂⟩,
  apply can_get_to_trans'' t₁ (move t₁ s d) t₃,
  split,
  { apply can_get_to_one_move t₁ s d,
    exact h₁ },
  { exact h₂ }
end

example : game' 1 :=
begin
  apply fmove' tower.a tower.c,
  split,
  unfold valid_move,
  simp,
  unfold move,
  simp,
  exact can_get_to_self' _,
end

lemma bmove' {t₁ t₃ : position} (s d : tower) : valid_move t₃ d s ∧ can_get_to' t₁ (move t₃ d s) → can_get_to' t₁ t₃ :=
begin
  rintros ⟨h₁, h₂⟩,
  apply can_get_to_trans'' t₁ (move t₃ d s) t₃,
  split,
  { exact h₂ },
  { sorry }
end

-- any puzzle can be solved!!
-- when we prove this, we win forever ;)
theorem ultimate : ∀ (disks : ℕ), game disks :=
begin
  intros disks,
  sorry
end

end hanoi

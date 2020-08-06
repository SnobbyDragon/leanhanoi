import data.list
import tactic

-- THIRD TIME'S THE CHARM??
namespace hanoi

structure position := (A : list ℕ) (B : list ℕ) (C : list ℕ)

instance towers_has_repr : has_repr position := ⟨λ t, "A: " ++ t.A.repr ++ " B: " ++ t.B.repr ++ " C: " ++ t.C.repr⟩
 
#eval position.mk [1, 2] [] []

#check position
#check position.A

-- number of disks on the position
def disks (t : position) : ℕ := t.A.length + t.B.length + t.C.length

-- is it true any valid tower can get to another valid tower w/equal number of disks?
-- Kevin says yes by induction

-- valid position only have lists that are strictly increasing
-- valid position have no duplicate disks
def valid_tower (t : position) : Prop :=
list.sorted nat.lt t.A ∧ list.sorted nat.lt t.B ∧ list.sorted nat.lt t.C
∧ (∀ a' ∈ t.A, ∀ b' ∈ t.B, ∀ c' ∈ t.C, a' ≠ b' ∧ b' ≠ c' ∧ a' ≠ c')  

#check valid_tower

-- no duplicate disks using different definition
def valid_tower' (t : position) : Prop :=
list.sorted nat.lt t.A ∧ list.sorted nat.lt t.B ∧ list.sorted nat.lt t.C
∧ list.merge nat.lt (list.merge nat.lt t.A t.B) t.C = list.range' 1 (disks t)

#check valid_tower' -- don't reduce this unless you want to make your computer wheeeeze

inductive tower : Type
| a | b | c

open tower

def move (t : position) : tower → tower → position
| a b := position.mk (t.A.tail) (t.A.head :: t.B) t.C
| a c := position.mk (t.A.tail) t.B (t.A.head :: t.C)
| b a := position.mk (t.B.head :: t.A) (t.B.tail) t.C
| c a := position.mk (t.C.head :: t.A) t.B (t.C.tail)
| b c := position.mk t.A (t.B.tail) (t.B.head :: t.C)
| c b := position.mk t.A (t.C.head :: t.B) (t.C.tail)
| a a := t
| b b := t
| c c := t

@[simp]
lemma move_self (t : position) (s : tower) : move t s s = t := by cases s; refl -- why does rfl not work??

#check move

def valid_move (t : position) : tower → tower → Prop
| a b := t.A ≠ [] ∧ (t.B.head < t.A.head ∨ t.B = [])
| a c := t.A ≠ [] ∧ (t.C.head < t.A.head ∨ t.C = [])
| b a := t.B ≠ [] ∧ (t.B.head < t.A.head ∨ t.A = [])
| c a := t.C ≠ [] ∧ (t.C.head < t.A.head ∨ t.A = [])
| b c := t.B ≠ [] ∧ (t.B.head < t.C.head ∨ t.C = [])
| c b := t.C ≠ [] ∧ (t.C.head < t.B.head ∨ t.B = [])
| a a := true
| b b := true
| c c := true

@[simp]
lemma move_self_valid (t : position) (s : tower) : valid_move t s s = true := by cases s; refl

#check valid_move

-- TODO not sure how to use this. needs to be reworked later?
def make_move (t : position) (s d : tower) : Prop := (∃ (t' : position), t' = move t s d) → (valid_move t s d)

#check make_move

-- also rw is huuuuge when we rw h. does not look nice!
example (t : position) (h : t = position.mk [1,2,3] [] []) : move t a b = position.mk [2,3] [1] [] :=
begin
  rw h,
  refl,
end

example (t : position) (h : t = position.mk [1,2,3] [] []) : make_move t a b :=
begin
  intros h,
  cases h with t' ht',
  unfold valid_move,
  rw h,
  simp,
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


/- WIP Playing with lists! -/
example (l : list ℕ) (hl : list.sorted nat.lt l) (hl' : l ≠ []) : list.sorted nat.lt l.tail :=
begin
  exact list.sorted.tail hl,
end

example (l : list ℕ) (h : l ≠ []) : l = l.head :: l.tail :=
begin
  exact (list.cons_head_tail h).symm,
end

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
example (l : list ℕ) (hl : list.sorted nat.lt l) (hl' : l ≠ []) (a : ℕ) (h : a < l.head) :
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
/- End of list playground... but we can still play with towers :) -/

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
  intros ht,
  cases ht with ht hm,
  by_cases hm' : (s = a ∨ s = b ∨ s = c) ∧ (d = a ∨ d = b ∨ d = c),
  { cases hm' with hs hd,
    cases hs with hsA hsBC,
    { cases hd with hdA hdBC,
      { -- a a
        rw [hsA, hdA],
        exact move_self_valid_is_valid' t a ht,
      },
      { cases hdBC with hdB hdC,
        { -- a b
          rw [hsA, hdB],
          split,
          { -- show A is sorted
            exact list.sorted.tail ht.1,
          },
          { sorry },
        },
        { sorry }
      },
    },
    { sorry }
  },
  { sorry }
end

-- TODO this is a mess
lemma valid_move_sym (t : position) (s d : tower) : valid_move t s d → valid_move (move t s d) d s :=
begin
  intros h,
  by_cases h' : (s = a ∨ s = b ∨ s = c) ∧ (d = a ∨ d = b ∨ d = c),
  { cases h' with hs hd,
    cases hs with hsA hsBC,
    { cases hd with hdA hdBC,
      { -- a a
        rw [hsA, hdA],
        sorry
      },
      { sorry }
    },
    { sorry }
  },
  { sorry }
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
-- | can_get_to_self' : ∀ (t : position), can_get_to' t t
-- not needed bc can get to self in one move
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

-- any puzzle can be solved!!
-- when we prove this, we win forever ;)
theorem ultimate : ∀ (disks : ℕ), game disks :=
begin
  intros disks,
  sorry
end

end hanoi

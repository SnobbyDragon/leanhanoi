import data.list
import tactic

-- THIRD TIME'S THE CHARM??
namespace hanoi

structure towers := (A : list ℕ) (B : list ℕ) (C : list ℕ)

instance towers_has_repr : has_repr towers := ⟨λ t, "A: " ++ t.A.repr ++ " B: " ++ t.B.repr ++ " C: " ++ t.C.repr⟩

#eval towers.mk [1, 2] [] []

#check towers
#check towers.A

-- this is pretty useless lmao
def position (t : towers) : list (list ℕ) := [t.A, t.B, t.C]

-- TODO: not sure when this will be used.
-- is it true any valid tower can get to another valid tower w/equal number of disks?
-- valid towers only have lists that are strictly increasing
-- valid towers have no duplicate disks
def valid_tower (t : towers) : Prop := sorry

-- number of disks on the towers
def disks (t : towers) : ℕ := t.A.length + t.B.length + t.C.length

inductive tower : Type
| a | b | c

open tower

def move (t : towers) : tower → tower → towers
| a b := towers.mk (t.A.tail) (t.A.head :: t.B) t.C
| a c := towers.mk (t.A.tail) t.B (t.A.head :: t.C)
| b a := towers.mk (t.B.head :: t.A) (t.B.tail) t.C
| c a := towers.mk (t.C.head :: t.A) t.B (t.C.tail)
| b c := towers.mk t.A (t.B.tail) (t.B.head :: t.C)
| c b := towers.mk t.A (t.C.head :: t.B) (t.C.tail)
| a a := t
| b b := t
| c c := t

@[simp]
lemma move_self (t : towers) (s : tower) : move t s s = t :=
begin
  cases s; refl, -- why does rfl not work??
end

#check move

def valid_move (t : towers) : tower → tower → Prop
| a b := if t.A ≠ [] ∧ (t.B.head < t.A.head ∨ t.B = []) then true else false
| a c := if t.A ≠ [] ∧ (t.C.head < t.A.head ∨ t.C = []) then true else false
| b a := if t.B ≠ [] ∧ (t.B.head < t.A.head ∨ t.A = []) then true else false
| c a := if t.C ≠ [] ∧ (t.C.head < t.A.head ∨ t.A = []) then true else false
| b c := if t.B ≠ [] ∧ (t.B.head < t.C.head ∨ t.C = []) then true else false
| c b := if t.C ≠ [] ∧ (t.C.head < t.B.head ∨ t.B = []) then true else false
| a a := true
| b b := true
| c c := true

#check valid_move

-- TODO not sure how to use this. needs to be reworked later
def make_move (t : towers) (s d : tower) : Prop := (∃ (t' : towers), t' = move t s d) → (valid_move t s d)

#check make_move

-- these definitions either suck or I don't know how to use them, or both
-- we don't want to unfold so much...
-- also rw is huuuuge when we rw h. does not look nice!
example (t : towers) (h : t = towers.mk [1,2,3] [] []) : move t a b = towers.mk [2,3] [1] [] :=
begin
  unfold move,
  rw h,
  simp,
end

example (t : towers) (h : t = towers.mk [1,2,3] [] []) : make_move t a b :=
begin
  intros h,
  cases h with t' ht',
  unfold valid_move,
  rw h,
  simp,
end

def can_get_to_one (t t' : towers) : Prop := ∃ (s d : tower), move t s d = t' → valid_move t s d

-- lol is there a way to simplify this?
-- answer: use the inductive definition lmao
def can_get_to_gt_one (t t' : towers) : Prop := ∃ (tows : list towers), (∃ first ∈ tows, ∃ last ∈ tows, can_get_to_one t first ∧ can_get_to_one last t' ∧ (∀ tow ∈ tows, tow ≠ last → (∃ tow' ∈ tows, tow ≠ tow' ∧ can_get_to_one tow tow')))

def can_get_to (t t' : towers) : Prop := can_get_to_one t t' ∨ can_get_to_gt_one t t'

#check can_get_to

-- alternative inductive definition (suggested by Kevin Buzzard! thanks again!)
inductive can_get_to' : towers → towers → Prop
| can_get_to_self' : ∀ (t : towers), can_get_to' t t
| can_get_to_one' : ∀ (t t' : towers), can_get_to_one t t' → can_get_to' t t'
| can_get_to_trans' : ∀ (t₁ t₂ t₃ : towers), can_get_to' t₁ t₂ → can_get_to' t₂ t₃ → can_get_to' t₁ t₃

#check can_get_to'

open can_get_to'

example (t t' : towers) : can_get_to_one t t' → can_get_to' t t':=
begin
  apply can_get_to_one',
end

lemma can_get_to_trans'' (t₁ t₂ t₃ : towers) : can_get_to' t₁ t₂ ∧ can_get_to' t₂ t₃ → can_get_to' t₁ t₃ :=
begin
  rintros ⟨h₁, h₂⟩,
  apply can_get_to_trans' t₁ t₂ t₃,
  exact h₁,
  exact h₂,
end

lemma can_get_to_one_self (t : towers) : can_get_to_one t t :=
begin
  use [a, a],
  intros h,
  exact trivial,
end

-- you can always meander and use more moves
lemma can_get_to_one_can_get_to_gt_one (t t' : towers) (h : can_get_to_one t t') : can_get_to_gt_one t t' :=
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

lemma can_get_to_gt_one_self (t : towers) : can_get_to_gt_one t t :=
begin
  apply can_get_to_one_can_get_to_gt_one,
  exact can_get_to_one_self t,
end

lemma can_get_to_self (t : towers) : can_get_to t t :=
begin
  left,
  exact can_get_to_one_self t,
end

-- TODO this is a mess
lemma valid_move_sym (t : towers) (s d : tower) : valid_move t s d → valid_move (move t s d) d s :=
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

lemma can_get_to_one_sym (t t' : towers) : can_get_to_one t t' → can_get_to_one t' t :=
begin
  intros h,
  rcases h with ⟨s, d, h⟩,
  use [d, s],
  intros m,
  sorry
end

lemma can_get_to_one_can_get_to (t t' : towers) : can_get_to_one t t' → can_get_to t t' :=
begin
  intros h,
  left,
  exact h,
end

-- if t₁ can get to t₂ in one move, and t₂ can get to t₃ in one move, then t₁ can get to t₃
lemma can_get_to_one_twice (t₁ t₂ t₃ : towers) (h₁ : can_get_to_one t₁ t₂) (h₂ : can_get_to_one t₂ t₃) : can_get_to t₁ t₃ :=
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
lemma can_get_to_one_gt_one (t₁ t₂ t₃ : towers) (h₁ : can_get_to_one t₁ t₂) (h₂ : can_get_to_gt_one t₂ t₃) : can_get_to t₁ t₃ :=
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
lemma can_get_to_trans (t₁ t₂ t₃ : towers) (h₁ : can_get_to t₁ t₂) (h₂ : can_get_to t₂ t₃) : can_get_to t₁ t₃ :=
begin
  cases h₁,
  { cases h₂,
    { -- can get to each other in one move
      exact can_get_to_one_twice t₁ t₂ t₃ h₁ h₂ },
    { -- can get from t₁ to t₂ in one move, but multiple moves from t₂ to t₃
      rcases h₂ with ⟨tows, first, hfirst_in, last, hlast_in, hstart_cgt, hlast_cgt, hmid⟩,
      right,
      use [t₂ :: tows, t₂, list.mem_cons_self _ _, last, list.mem_cons_of_mem t₂ hlast_in],
      split,
      { exact h₁ },
      { split,
        { exact hlast_cgt },
        { sorry },
      },
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

def game (disks : ℕ) : Prop :=
can_get_to (towers.mk (list.range' 1 disks) [] []) (towers.mk [] [] (list.range' 1 disks))

-- using the inductive definition
def game' (disks : ℕ) : Prop :=
can_get_to' (towers.mk (list.range' 1 disks) [] []) (towers.mk [] [] (list.range' 1 disks))

#check game
#check game'

-- using non-inductive definition
example : game 1 :=
begin
  left,
  use [a, c],
  intros h',
  exact trivial,
  --unfold valid_move,
end

-- using inductive definition
example : game' 1 :=
begin
  apply can_get_to_one',
  use [a, c],
  intros h',
  exact trivial,
  --unfold valid_move,
end

-- any puzzle can be solved!!
-- when we prove this, we win forever ;)
theorem ultimate : ∀ (disks : ℕ), game disks :=
begin
  intros disks,
  sorry
end

end hanoi

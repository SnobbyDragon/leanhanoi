import data.list
import tactic

-- THIS ISNT WORKING
namespace hanoi

inductive towers
| A  : list ℕ → towers
| B  : list ℕ → towers
| C  : list ℕ → towers

#check towers.A
#check towers.B
#check towers.C

open towers

#check A
#check B
#check C

-- gives the positions of the disks
def position (t : towers) : list ℕ := towers.cases_on t (λ a, a) (λ b, b) (λ c, c)

#check position
#reduce position (A $ list.range' 1 5)
#reduce position (B [])
#reduce position (C [])

--instance tower_has_repr : has_repr towers := sorry

def valid_move (s d : towers) : Prop :=
position s ≠ [] ∧ ((position s).head < (position d).head ∨ position d = [])

#check valid_move
#reduce valid_move (A $ list.range' 1 5) (B [])

def move (s d : towers) : Prop := ∃ (s' d' : towers), position d' = (position s).head :: position d ∧ position s' = (position s).drop 1

#check move
#reduce move (A $ list.range' 1 5) (B [])

-- can get from start to destination
def can_get_to (s d : towers) : Prop :=
∃ (t : towers), (move s t → position s = position d) ∨ (move t s → position s = position d)

lemma can_get_to_self (s : towers) : can_get_to s s :=
begin
  use s,
  left,
  intros h,
  refl,
end

lemma can_get_to_trans (s d₁ d₂ : towers) : can_get_to s d₁ ∧ can_get_to d₁ d₂ → can_get_to s d₂ :=
begin
  intros h,
  rcases h with ⟨hl, t, hr⟩,
  sorry
end

--def is_solvable (t : towers) : t := sorry

end hanoi

-- THIS ISNT WORKING EITHER
namespace hanoi'

structure towers :=
(pos : fin 3 → list ℕ)
(tower : ∀ i : fin 3, ∀ (n : ℕ) (h : n+1 < (pos i).length ∧ n < (pos i).length), ((pos i).nth_le n h.2 ) < ((pos i).nth_le (n+1) h.1))
--(pos i) < list.drop 1 (pos i) ++ (pos i).tail )

instance : has_repr towers := sorry

def valid_move (t : towers) (s d : fin 3) : Prop :=
(t.pos s ≠ [] ∧ ((t.pos s).head < (t.pos d).head ∨ t.pos d = []))

--def move (t : towers) (s d ∈ fin 3) (h : valid_move t s d): towers := towers.mk

--t.pos d = (t.pos s).head :: t.pos d ∧ t.pos s = (t.pos s).drop 1

def start (t : towers) (d : ℕ) := t.pos 1 = list.range' 1 d ∧ t.pos 2 = [] ∧ t.pos 3 = []

def goal (t : towers) (d : ℕ) := t.pos 1 = [] ∧ t.pos 2 = [] ∧ t.pos 3 = list.range' 1 d

example (t : towers) : start t 3 → t.pos 1 = list.range' 2 3 ∧ t.pos 2 = [] ∧ t.pos 3 = [1] :=
begin
  sorry
end

end hanoi'


-- THIRD TIME'S THE CHARM??
namespace hanoi''

structure towers := (A : list ℕ) (B : list ℕ) (C : list ℕ)

instance towers_has_repr : has_repr towers := ⟨λ t, "A: " ++ t.A.repr ++ " B: " ++ t.B.repr ++ " C: " ++ t.C.repr⟩

#eval towers.mk [1, 2] [] []

#check towers
#check towers.A

-- this is pretty useless lmao
def position (t : towers) : list (list ℕ) := [t.A, t.B, t.C]

def move (t : towers) : char → char → towers
| 'A' 'B' := towers.mk (t.A.drop 1) (t.A.head :: t.B) t.C
| 'A' 'C' := towers.mk (t.A.drop 1) t.B (t.A.head :: t.C)
| 'B' 'A' := towers.mk (t.B.head :: t.A) (t.B.drop 1) t.C
| 'C' 'A' := towers.mk (t.C.head :: t.A) t.B (t.C.drop 1)
| 'B' 'C' := towers.mk t.A (t.B.drop 1) (t.B.head :: t.C)
| 'C' 'B' := towers.mk t.A (t.C.head :: t.B) (t.C.drop 1)
| _ _ := t -- invalid input or same tower

#check move

def valid_move (t : towers) : char → char → Prop
| 'A' 'B' := if t.A ≠ [] ∧ (t.B.head < t.A.head ∨ t.B = []) then true else false
| 'A' 'C' := if t.A ≠ [] ∧ (t.C.head < t.A.head ∨ t.C = []) then true else false
| 'B' 'A' := if t.B ≠ [] ∧ (t.B.head < t.A.head ∨ t.A = []) then true else false
| 'C' 'A' := if t.C ≠ [] ∧ (t.C.head < t.A.head ∨ t.A = []) then true else false
| 'B' 'C' := if t.B ≠ [] ∧ (t.B.head < t.C.head ∨ t.C = []) then true else false
| 'C' 'B' := if t.C ≠ [] ∧ (t.C.head < t.B.head ∨ t.B = []) then true else false
| 'A' 'A' := true
| 'B' 'B' := true
| 'C' 'C' := true
| _ _ := false -- invalid input

#check valid_move

def make_move (t : towers) (s d : char) : Prop := (∃ (t' : towers), t' = move t s d) → (valid_move t s d)

#check make_move

-- these definitions either suck or I don't know how to use them, or both
-- we don't want to unfold so much...
-- also rw is huuuuge when we rw h. does not look nice!
example (t : towers) (h : t = towers.mk [1,2,3] [] []) : move t 'A' 'B' = towers.mk [2,3] [1] [] :=
begin
  unfold move,
  rw h,
  simp,
end

example (t : towers) (h : t = towers.mk [1,2,3] [] []) : make_move t 'A' 'B' :=
begin
  intros h,
  cases h with t' ht',
  unfold valid_move,
  rw h,
  simp,
end

def can_get_to_one (t t' : towers) : Prop := ∃ (s d : char), move t s d = t' → valid_move t s d

-- TODO: this is extreeeemely overly complicated :(
def can_get_to (t t' : towers) : Prop := can_get_to_one t t' ∨ ∃ (tows : list towers), ((∃ tow ∈ tows, can_get_to_one t tow) ∧ ∀ tow ∈ tows, (∃ tow' ∈ tows, tow ≠ tow' ∧ can_get_to_one tow tow') ∨ can_get_to_one tow t')

lemma can_get_to_self (t : towers) : can_get_to t t :=
begin
  left,
  use ['A', 'A'],
  intros h,
  exact trivial,
  --unfold valid_move,
end

-- TODO complicated definitions are leading to misery but ill try it anyways
lemma can_get_to_trans (t₁ t₂ t₃ : towers) (h₁ : can_get_to t₁ t₂) (h₂ : can_get_to t₂ t₃) : can_get_to t₁ t₃ :=
begin
  right,
  cases h₁,
  { cases h₂,
    { -- can get to each other in one move
      use t₂ :: list.nil, -- i dont know how to make a list...
      split,
      { use t₂,
        split,
        exact list.mem_singleton_self _,
        exact h₁ },
      { intros tow h,
        rw list.mem_singleton at h,
        right,
        rw h,
        exact h₂,
      },
    },
    { -- can get from t₁ to t₂ in one move, but multiple moves from t₂ to t₃
      -- TODO: PLEASE RENAME ALL THESE TOWERS THERES WAY TOO MANY!!!!
      rcases h₂ with ⟨tows, h₂, h₂'⟩,
      rcases h₂ with ⟨tow, htow, tow'⟩,
      specialize h₂' tow htow,
      rcases h₂' with ⟨tow'', h₂', htow'⟩,
      { sorry },
      { sorry } } },
  { cases h₂,
    { sorry },
    { sorry } }
end

def game (t : towers) (disks : ℕ) (h : t = towers.mk (list.range' 1 disks) [] []) : Prop :=
can_get_to t (towers.mk [] [] (list.range' 1 disks))

#check game

example (t : towers) (h : t = towers.mk [1] [] []) : game t 1 h :=
begin
  sorry
end

end hanoi''

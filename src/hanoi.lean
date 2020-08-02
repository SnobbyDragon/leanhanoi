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

def move (t : towers) : char → char → towers
| 'A' 'B' := towers.mk (t.A.tail) (t.A.head :: t.B) t.C
| 'A' 'C' := towers.mk (t.A.tail) t.B (t.A.head :: t.C)
| 'B' 'A' := towers.mk (t.B.head :: t.A) (t.B.tail) t.C
| 'C' 'A' := towers.mk (t.C.head :: t.A) t.B (t.C.tail)
| 'B' 'C' := towers.mk t.A (t.B.tail) (t.B.head :: t.C)
| 'C' 'B' := towers.mk t.A (t.C.head :: t.B) (t.C.tail)
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
def can_get_to_gt_one (t t' : towers) : Prop := ∃ (tows : list towers), (∃ first ∈ tows, ∃ last ∈ tows, can_get_to_one t first ∧ can_get_to_one last t' ∧ (∀ tow ∈ tows, tow ≠ last → (∃ tow' ∈ tows, tow ≠ tow' ∧ can_get_to_one tow tow')))

-- TODO: this is extreeeemely overly complicated :(
def can_get_to (t t' : towers) : Prop := can_get_to_one t t' ∨ can_get_to_gt_one t t'

#check can_get_to

lemma can_get_to_self (t : towers) : can_get_to t t :=
begin
  left,
  use ['A', 'A'],
  intros h,
  exact trivial,
  --unfold valid_move,
end

example (a b c : list ℕ) : (towers.mk a b c).A = a :=
begin
  refl,
end

-- TODO this is a mess
lemma valid_move_sym (t : towers) (s d : char) : valid_move t s d → valid_move (move t s d) d s :=
begin
  sorry
end

-- TODO this is a mess
lemma move_sym (t : towers) (s d : char) : make_move t s d → t = move (move t s d) d s :=
begin
  intros m,
  by_cases (s = 'A' ∨ s = 'B' ∨ s = 'C') ∧ (d = 'A' ∨ d = 'B' ∨ d = 'C'),
  { cases h with hs hd,
    cases hs with hsA,
    cases hd with hdA,
    { -- move from A to A
      rw [hsA, hdA],
      refl,
    },
    { cases hd with hdB hdC,
      { -- move from A to B
        rw [hsA, hdB],
        sorry
      },
      { sorry },
    },
    sorry },
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

lemma can_get_to_gt_one_iff_can_get_to_ne_one (t t' : towers) :
can_get_to t t' ∧ ¬can_get_to_one t t' ↔ can_get_to_gt_one t t' :=
begin
  split,
  { intros h,
    cases h with h₁ h₂,
    sorry
  },
  { sorry }
end

lemma can_get_to_one_gt_one (t₁ t₂ t₃ : towers) (h₁ : can_get_to_one t₁ t₂) (h₂ : can_get_to_gt_one t₂ t₃) : can_get_to t₁ t₃ :=
begin
  sorry
end

-- TODO complicated definitions are leading to misery but ill try it anyways
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

def game (t : towers) (disks : ℕ) (h : t = towers.mk (list.range' 1 disks) [] []) : Prop :=
can_get_to t (towers.mk [] [] (list.range' 1 disks))

#check game

example (t : towers) (h : t = towers.mk [1] [] []) : game t 1 h :=
begin
  sorry
end

end hanoi

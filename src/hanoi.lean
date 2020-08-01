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

instance towers_has_repr : has_repr towers := ⟨λ t, t.A.repr ++ " " ++ t.B.repr ++ " " ++ t.C.repr⟩

#eval towers.mk [1, 2] [] []

#check towers
#check towers.A

def position (t : towers) : list (list ℕ) := [t.A, t.B, t.C]

private def moveAB (t : towers) : towers := towers.mk (t.A.drop 1) (t.A.head :: t.B) t.C
private def moveAC (t : towers) : towers := towers.mk (t.A.drop 1) t.B (t.A.head :: t.C)
private def moveBA (t : towers) : towers := towers.mk (t.B.head :: t.A) (t.B.drop 1) t.C
private def moveCA (t : towers) : towers := towers.mk (t.C.head :: t.A) t.B (t.C.drop 1)
private def moveBC (t : towers) : towers := towers.mk t.A (t.B.drop 1) (t.B.head :: t.C)
private def moveCB (t : towers) : towers := towers.mk t.A (t.C.head :: t.B) (t.C.drop 1)

def move (t : towers) : char → char → towers
| 'A' 'B' := moveAB t
| 'A' 'C' := moveAC t
| 'B' 'A' := moveBA t
| 'C' 'A' := moveCA t
| 'B' 'C' := moveBC t
| 'C' 'B' := moveCB t
| _ _ := t -- invalid input or same tower

def move' (t : towers) (s d : char) : towers := move t s d

#check move

private def valid_moveAB (t : towers) : Prop := t.A ≠ [] ∧ (t.B.head < t.A.head ∨ t.B = [])
private def valid_moveAC (t : towers) : Prop := t.A ≠ [] ∧ (t.C.head < t.A.head ∨ t.C = [])
private def valid_moveBA (t : towers) : Prop := t.B ≠ [] ∧ (t.B.head < t.A.head ∨ t.A = [])
private def valid_moveCA (t : towers) : Prop := t.C ≠ [] ∧ (t.C.head < t.A.head ∨ t.A = [])
private def valid_moveBC (t : towers) : Prop := t.B ≠ [] ∧ (t.B.head < t.C.head ∨ t.C = [])
private def valid_moveCB (t : towers) : Prop := t.C ≠ [] ∧ (t.C.head < t.B.head ∨ t.B = [])

def valid_move (t : towers) : char → char → Prop
| 'A' 'B' := valid_moveAB t
| 'A' 'C' := valid_moveAC t
| 'B' 'A' := valid_moveBA t
| 'C' 'A' := valid_moveCA t
| 'B' 'C' := valid_moveBC t
| 'C' 'B' := valid_moveCB t
| 'A' 'A' := true
| 'B' 'B' := true
| 'C' 'C' := true
| _ _ := false

#check valid_move

def make_move (t : towers) (s d : char) : Prop := (∃ (t' : towers), t' = move t s d) → (valid_move t s d)

#check make_move

-- these definitions either suck or I don't know how to use them, or both
-- we don't want to unfold so much
example (t : towers) (h : position t = [[1,2,3],[],[]]) : position (move t 'A' 'B') = [[2,3],[1],[]] :=
begin
  unfold move,
  unfold moveAB,
  unfold position at h,
  simp at h,
  rcases h with ⟨hA, hB, hC⟩,
  rw [hA, hB, hC],
  simp,
  unfold position,
end

example (t : towers) (h : position t = [[1,2,3],[],[]]) : make_move t 'A' 'B' :=
begin
  intros h,
  cases h with t' ht',
  unfold valid_move,
  unfold valid_moveAB,
  unfold position at h,
  simp at h,
  rcases h with ⟨hA, hB, hC⟩,
  split,
  rw hA,
  simp,
  right,
  exact hB,
end

def can_get_to (t t' : towers) : Prop := ∃ (s d : char), position (move t s d) = position t' → valid_move t s d

lemma can_get_to_self (t : towers) : can_get_to t t :=
begin
  use ['A', 'A'],
  intros h,
  unfold valid_move,
end

-- TODO neeeeed to redefine 'can_get_to' bc this isn't going to work
lemma can_get_to_trans (t₁ t₂ t₃ : towers) (h₁ : can_get_to t₁ t₂) (h₂ : can_get_to t₂ t₃) : can_get_to t₁ t₃ :=
begin
  sorry
end

def game (t : towers) (disks : ℕ) (h : position t = [list.range' 1 disks, [], []]) : Prop := sorry
--∃ (t' : towers), 

--∃ (ts : list towers) (hts : ts ≠ []), (∀ (n : ℕ) (hn₁ : 0 < n) (hn₂ : n < ts.length), (∃ (s d : char), (move (ts.nth_le (n-1) (by linarith [hn₁, hn₂, lt_trans])) s d) = ts.nth_le n hn₂) ∧ (position (ts.last hts)) = [[], [], list.range' 1 disks])

#check game
#reduce [1, 2].nth_le 1 (by norm_num)

example (t : towers) (h : position t = [[1], [], []]) : game t 1 h :=
begin
  sorry
end

end hanoi''

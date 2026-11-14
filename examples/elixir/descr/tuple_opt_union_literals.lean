namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Optimized unions of tuple literals. -/

/-- Lists related pairwise. -/
def Pairs (R : Term → Term → Prop) : List Term → List Term → Prop
  | [], [] => True
  | x :: xs, y :: ys => R x y ∧ Pairs R xs ys
  | _, _ => False

theorem Pairs.snoc {R : Term → Term → Prop} : ∀ {a b : List Term}, Pairs R a b → ∀ {x y : Term}, R x y →
    Pairs R (a ++ [x]) (b ++ [y])
  | [], [], _, _, _, h => ⟨h, trivial⟩
  | _ :: _, _ :: _, p, _, _, h => ⟨p.1, Pairs.snoc p.2 h⟩
  | [], _ :: _, p, _, _, _ => p.elim
  | _ :: _, [], p, _, _, _ => p.elim

theorem Pairs.mono {R R' : Term → Term → Prop} (h : ∀ x y, R x y → R' x y) : ∀ {a b : List Term}, Pairs R a b →
    Pairs R' a b
  | [], [], _ => trivial
  | _ :: _, _ :: _, p => ⟨h _ _ p.1, Pairs.mono h p.2⟩
  | [], _ :: _, p => p.elim
  | _ :: _, [], p => p.elim

theorem Pairs.swap {R R' : Term → Term → Prop} (h : ∀ x y, R x y → R' y x) : ∀ {a b : List Term}, Pairs R a b →
    Pairs R' b a
  | [], [], _ => trivial
  | _ :: _, _ :: _, p => ⟨h _ _ p.1, Pairs.swap h p.2⟩
  | [], _ :: _, p => p.elim
  | _ :: _, [], p => p.elim

theorem Pairs.append {R : Term → Term → Prop} : ∀ {a b : List Term}, Pairs R a b → ∀ {c d : List Term}, Pairs R c d →
    Pairs R (a ++ c) (b ++ d)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, p, _, _, h => ⟨p.1, Pairs.append p.2 h⟩
  | [], _ :: _, p, _, _, _ => p.elim
  | _ :: _, [], p, _, _, _ => p.elim

theorem plus_one (n : Nat) : Erlang.erlang.«+/2» (.integer (n : Int)) (.integer 1) = .ok (.integer ((n + 1 : Nat) : Int)) := by
  rw [Erlang.erlang.«+/2_integers»]; congr 2

theorem strategy_start (d : Dispatcher) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") (l₁ l₂ : List Term) :
    Elixir.Module.Types.Descr.«opt_tuple_union_strategy/4» d (.atom t₁) (Term.list l₁) (.atom t₂) (Term.list l₂) =
      if t₁ = t₂ ∧ l₁.length = l₂.length then
        Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» d (Term.list l₁) (Term.list l₂) (.integer 0)
          (.atom "all_equal")
      else if t₁ = "open" ∧ l₁.length ≤ l₂.length then
        Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» d (Term.list l₁) (Term.list l₂) (.integer 0)
          (.atom "right_subtype_of_left")
      else if t₂ = "open" ∧ l₂.length ≤ l₁.length then
        Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» d (Term.list l₁) (Term.list l₂) (.integer 0)
          (.atom "left_subtype_of_right")
      else .ok (.atom "none") := by
  unfold Elixir.Module.Types.Descr.«opt_tuple_union_strategy/4»
  have le : (Ord.compare (l₁.length : Int) l₂.length).isLE = decide (l₁.length ≤ l₂.length) := by
    rcases Nat.lt_trichotomy l₁.length l₂.length with h | h | h
    · have : Ord.compare (l₁.length : Int) l₂.length = .lt := Int.compare_eq_lt.mpr (by omega)
      simp [this]; omega
    · simp [h]
    · have : Ord.compare (l₁.length : Int) l₂.length = .gt := Int.compare_eq_gt.mpr (by omega)
      simp [this]; omega
  have ge : (Ord.compare (l₁.length : Int) l₂.length).isGE = decide (l₂.length ≤ l₁.length) := by
    rcases Nat.lt_trichotomy l₁.length l₂.length with h | h | h
    · have : Ord.compare (l₁.length : Int) l₂.length = .lt := Int.compare_eq_lt.mpr (by omega)
      simp [this]; omega
    · simp [h]
    · have : Ord.compare (l₁.length : Int) l₂.length = .gt := Int.compare_eq_gt.mpr (by omega)
      simp [this]; omega
  have eqc : ((l₁.length : Int) = l₂.length) = (l₁.length = l₂.length) := by simp only [eq_iff_iff]; omega
  rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
    by_cases e : l₁.length = l₂.length <;> by_cases e' : l₁.length ≤ l₂.length <;>
    by_cases e'' : l₂.length ≤ l₁.length <;>
    simp [Erlang.erlang.«=:=/2», length_list, Erlang.erlang.«==/2», Erlang.erlang.«and/2»,
      Erlang.erlang.«=</2», Erlang.erlang.«>=/2», le, ge, eqc, e, e', e'',
      Term.true, Term.false] <;> omega

theorem split_full {c₁ s₁ c₂ s₂ : List Term} (lc : c₁.length = c₂.length) (sc : s₁ = [] ∨ s₂ = [])
    (le : (c₁ ++ s₁).length ≤ (c₂ ++ s₂).length) : s₁ = [] := by
  rcases sc with h | h
  · exact h
  · subst h; simp at le; cases s₁ with
    | nil => rfl
    | cons _ _ => simp at le; omega

theorem aob_bool (e : Term) : ∃ c : Bool, Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1» e = .ok (boolAtom c) := by
  unfold Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1»
  cases e with
  | map X =>
    simp only
    split
    · simp [Erlang.erlang.«map_size/1»]; exact (Classical.em _).symm
    · split
      · simp [Erlang.erlang.«map_size/1»]; exact (Classical.em _).symm
      · split
        · simp [Erlang.erlang.«map_size/1»]; exact (Classical.em _).symm
        · exact ⟨Bool.false, rfl⟩
  | _ => exact ⟨Bool.false, by simp [getMapKeys]⟩

def StatusForm (res : Term) : Prop :=
  res = .atom "all_equal" ∨
    (∃ (j : Int) (d₁ d₂ : Term), res = .tuple #[.atom "one_index_difference", .integer j, d₁, d₂]) ∨
    res = .atom "left_subtype_of_right" ∨ res = .atom "right_subtype_of_left" ∨ res = .atom "none"

theorem set_mid : ∀ (a : List Term) (x u : Term) (b : List Term), (a ++ x :: b).set a.length u = a ++ u :: b
  | [], _, _, _ => rfl
  | _ :: a, x, u, b => by simp [set_mid a x u b]

theorem list_eq_nil {l : List Term} : Term.list l = .nil ↔ l = [] := by
  cases l <;> simp [Term.list]

/-- The status a strategy walk ends with: equal elements make either tuple a subtype of the other. -/
def endSt : Term → Term
  | .atom "all_equal" => .atom "left_subtype_of_right"
  | st => st

theorem endSt_ne (st : Term) : endSt st ≠ .atom "all_equal" := by
  unfold endSt; split <;> simp_all

theorem endSt_of_ne {st : Term} (h : st ≠ .atom "all_equal") : endSt st = st := by
  unfold endSt; split <;> simp_all

theorem index_nil_left (d : Dispatcher) (l : List Term) (i st : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» d (Term.list []) (Term.list l) i st = .ok (endSt st) := by
  rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
  cases l <;> simp only [Term.list] <;> unfold endSt <;> split <;> simp_all

theorem index_nil_right (d : Dispatcher) (l : List Term) (i st : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4» d (Term.list l) (Term.list []) i st = .ok (endSt st) := by
  rw [Elixir.Module.Types.Descr.«opt_tuple_union_strategy_index/4».eq_def]
  cases l <;> simp only [Term.list] <;> unfold endSt <;> split <;> simp_all

/-- Uniting with all tuples never falls back to the plain union. -/
theorem strategy_top_none (d : Dispatcher) (t₁ t₂ : String) (g₁ : t₁ = "open" ∨ t₁ = "closed")
    (g₂ : t₂ = "open" ∨ t₂ = "closed") (l₁ l₂ : List Term) (top : (t₁ = "open" ∧ l₁ = []) ∨ (t₂ = "open" ∧ l₂ = []))
    (run : Elixir.Module.Types.Descr.«opt_tuple_union_strategy/4» d (.atom t₁) (Term.list l₁) (.atom t₂)
      (Term.list l₂) = .ok (.atom "none")) : False := by
  rw [strategy_start d t₁ t₂ g₁ g₂] at run
  rcases top with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · split at run
    · rw [index_nil_left] at run; simp [endSt] at run
    · split at run
      · rw [index_nil_left] at run; simp [endSt] at run
      · rename_i h₁ h₂; simp at h₂
  · split at run
    · rw [index_nil_right] at run; simp [endSt] at run
    · split at run
      · rw [index_nil_right] at run; simp [endSt] at run
      · split at run
        · rw [index_nil_right] at run; simp [endSt] at run
        · rename_i h₁ h₂ h₃; simp at h₃

end Elixir.STTDescrProofsTest

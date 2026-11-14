namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem any1_sem {m : Nat} (f : Term) (P : Term → Prop) : ∀ (l : List Term),
    (∀ x ∈ l, ∃ b : Bool, (D m).pure f #[x] = .ok (boolAtom b) ∧ (b = Bool.true ↔ P x)) →
    ∃ b : Bool, Erlang.lists.«any_1/2» (D m) f (Term.list l) = .ok (boolAtom b) ∧ (b = Bool.true ↔ ∃ x ∈ l, P x)
  | [], _ => ⟨Bool.false, by rw [Erlang.lists.«any_1/2».eq_def]; simp [boolAtom], by simp⟩
  | x :: rest, each => by
    obtain ⟨b, rb, sb⟩ := each x List.mem_cons_self
    obtain ⟨c, rc, sc⟩ := any1_sem f P rest fun y my => each y (List.mem_cons_of_mem _ my)
    rw [Erlang.lists.«any_1/2».eq_def]
    cases b
    · refine ⟨c, by simpa [rb, boolAtom] using rc, ?_⟩
      rw [sc]
      simp only [List.mem_cons, exists_eq_or_imp]
      exact ⟨Or.inr, fun h => h.elim (fun hx => absurd (sb.mpr hx) (by simp)) id⟩
    · exact ⟨Bool.true, by simp [rb, boolAtom], by simp only [true_iff]; exact ⟨x, List.mem_cons_self, sb.mp rfl⟩⟩

theorem any_sem {m : Nat} (mo nm : String) (caps : Array Term) (P : Term → Prop) (l : List Term)
    (each : ∀ x ∈ l, ∃ b : Bool, (D m).pure (.function mo nm 1 caps) #[x] = .ok (boolAtom b) ∧ (b = Bool.true ↔ P x)) :
    ∃ b : Bool, Erlang.lists.«any/2» (D m) (.function mo nm 1 caps) (Term.list l) = .ok (boolAtom b) ∧
      (b = Bool.true ↔ ∃ x ∈ l, P x) := by
  obtain ⟨b, rb, sb⟩ := any1_sem (m := m) (.function mo nm 1 caps) P l each
  refine ⟨b, ?_, sb⟩
  cases l with
  | nil => simpa [Erlang.lists.«any/2», Erlang.erlang.«is_function/2», Term.list, Erlang.lists.«any_1/2»] using rb
  | cons x rest =>
    rw [Erlang.lists.«any_1/2».eq_def] at rb
    simpa [Erlang.lists.«any/2», Erlang.erlang.«is_function/2», Term.list] using rb

section
variable {E : Term → Prop} {V : Type} {den : Term → V → Prop}

/-- Fields that allow the key to be absent. -/
def OptFields (l : List (Term × Term)) : Prop := ∀ e ∈ l, ∃ ty, e.2 = .tuple #[ty, .atom "true"]

theorem opt_fields_all (name : String) (hname : name = "-has_empty_map?/1-fun-0-" ∨ name = "-has_empty_map?/1-fun-1-")
    {l : List (Term × Term)} (hl : ∀ e ∈ l, FieldValue E e.2) {m : Nat} :
    ∃ b : Bool, Erlang.lists.«all/2» (D (m + 1)) (.function "Elixir.Module.Types.Descr" name 1 #[]) (fieldsTerm l) =
      .ok (boolAtom b) ∧ (b = Bool.true ↔ OptFields l) := by
  obtain ⟨b, rb, sb⟩ := all_sem (K' := 0) "Elixir.Module.Types.Descr" name #[] (l.map fun e => .tuple #[e.1, e.2])
    (m := m + 1) (by omega) (fun x => ∃ k ty, x = .tuple #[k, .tuple #[ty, .atom "true"]])
    (fun _ x => Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-0-/1» x)
    (fun m x => by
      rcases hname with rfl | rfl
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-has_empty_map?/1-fun-0-/1».pure]
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-has_empty_map?/1-fun-1-/1».pure]
        simp [Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-0-/1», Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-1-/1»])
    (fun x mx => by
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
      obtain ⟨ty, o, he, -⟩ := hl e me
      refine ⟨o, fun _ _ => by simp [Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-0-/1», he], ?_⟩
      cases o <;> simp [he, boolAtom])
  refine ⟨b, rb, ?_⟩
  rw [sb]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, OptFields]
  constructor
  · intro h e me
    obtain ⟨k, ty, he⟩ := h e me
    simp only [Term.tuple.injEq] at he
    have := congrArg (fun a : Array Term => a[1]?) he
    simp at this
    exact ⟨ty, this⟩
  · intro h e me
    obtain ⟨ty, he⟩ := h e me
    exact ⟨e.1, ty, by rw [he]⟩

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- The empty map of values. -/
def wNone : MW V := fun _ => none

theorem msem_none {tag : Term} {l : List (Term × Term)} (sl : FieldsV E l) :
    MSem den tag l (wNone (V := V)) ↔ OptFields l := by
  constructor
  · intro h e me
    obtain ⟨⟨s, es⟩, ty, o, he, -⟩ := sl.1 e me
    have hs := h.atoms s
    unfold FSem at hs
    rw [lookup_of_mem sl me es, he] at hs
    simp only at hs
    rw [fieldSem_mk] at hs
    rcases hs with ⟨-, rfl⟩ | ⟨x, h, -⟩
    · exact ⟨ty, he⟩
    · cases h
  · intro h
    refine ⟨fun s => ?_, fun k i => tagSem_none _ _⟩
    unfold FSem
    cases hf : mapLookup l (.atom s) with
    | none => exact tagSem_none _ _
    | some f =>
      obtain ⟨e, me, rfl⟩ := entry_of_lookup hf
      obtain ⟨ty, hty⟩ := h e (mem_of_mem_mapEntries me)
      simp only
      rw [hty, show Term.atom "true" = boolAtom Bool.true from rfl, fieldSem_mk]
      exact Or.inl ⟨rfl, rfl⟩

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- `has_empty_map?/1` holds exactly when a line holds the empty map. -/
theorem has_empty (lines : List Term) (hl : ∀ L ∈ lines, MLine E L) (m : Nat) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«has_empty_map?/1» (D (m + 3)) (Term.list lines) = .ok (boolAtom b) ∧
      (b = Bool.true ↔ ∃ L ∈ lines, InMLine den L (wNone (V := V))) := by
  obtain ⟨b, rb, sb⟩ := any_sem (m := m + 3) "Elixir.Module.Types.Descr" "-has_empty_map?/1-fun-3-" #[]
    (fun L => InMLine den L (wNone (V := V))) lines (fun L mL => by
      obtain ⟨tag, l, negs, rfl, g, sl, lits⟩ := hl L mL
      obtain ⟨b₁, r₁, s₁⟩ := opt_fields_all (E := E) "-has_empty_map?/1-fun-0-" (Or.inl rfl) (l := l)
        (fun e me => (sl.1 e me).2) (m := m + 1)
      obtain ⟨b₂, r₂, s₂⟩ := all_sem (K' := 1) "Elixir.Module.Types.Descr" "-has_empty_map?/1-fun-2-" #[] negs
        (m := m + 2) (by omega) (fun N => ¬NSem den N (wNone (V := V)))
        (fun m x => Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-2-/1» (D m) x)
        (fun m x => by rw [Erlang.program.«Elixir.Module.Types.Descr:-has_empty_map?/1-fun-2-/1».pure])
        (fun N mN => by
          obtain ⟨k, ntag, nl, rfl, -, snl⟩ := lits N mN
          refine ⟨!bp (OptFields nl), fun m' hm' => ?_, ?_⟩
          · obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
            obtain ⟨c, rc, sc⟩ := opt_fields_all (E := E) "-has_empty_map?/1-fun-1-" (Or.inr rfl) (l := nl)
              (fun e me => (snl.1 e me).2) (m := m'')
            have ec : c = bp (OptFields nl) := by
              cases c
              · exact (bp_false.mpr fun h => absurd (sc.mpr h) (by simp)).symm
              · exact (bp_true.mpr (sc.mp rfl)).symm
            subst ec
            cases h : bp (OptFields nl) <;>
              simp [Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-2-/1», rc, h, Erlang.erlang.«not/1», boolAtom]
          · rw [nsem_lit, msem_none snl]
            cases h : bp (OptFields nl)
            · simp only [Bool.not_false, true_iff]; exact bp_false.mp h
            · simp only [Bool.not_true, Bool.false_eq_true, false_iff, Classical.not_not]; exact bp_true.mp h)
      refine ⟨b₁ && b₂, ?_, ?_⟩
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-has_empty_map?/1-fun-3-/1».pure]
        cases b₁ <;> cases b₂ <;>
          simp [Elixir.Module.Types.Descr.«-has_empty_map?/1-fun-3-/1», r₁, r₂, boolAtom, Lynx.Except.andAlso]
      · rw [inMLine_iff, msem_none sl, Bool.and_eq_true, s₁, s₂])
  exact ⟨b, by simpa [Elixir.Module.Types.Descr.«has_empty_map?/1»] using rb, sb⟩

end

end Elixir.STTDescrProofsTest.Nest

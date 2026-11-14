namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Map emptiness is exact under seen sets of higher BDDs. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem lh_pair (a b : Term) : lh (.tuple #[a, b]) = max (lh a) (lh b) := by
  show lh (.tuple ⟨[a, b]⟩) = _
  rw [lh]

theorem lh_fields_mem {l : List (Term × Term)} {e : Term × Term} (me : e ∈ l) {t : Term} {o : Bool}
    (he : e.2 = .tuple #[t, boolAtom o]) : lh t ≤ lh (fieldsTerm l) := by
  have := lh_list_mem (l := l.map fun e => .tuple #[e.1, e.2]) (List.mem_map.mpr ⟨e, me, rfl⟩)
  rw [he, lh_pair, lh_pair] at this
  exact Nat.le_trans (by omega) this

theorem lh_litM {k : Int} {tag : Term} {l : List (Term × Term)} (_g : TagV E tag)
    (top : ¬(tag = .atom "open" ∧ l = [])) :
    lh (.tuple #[.integer k, tag, fieldsTerm l]) = max (lh tag) (lh (fieldsTerm l)) + 1 :=
  lh_leaf _ _ _ (fun ⟨h₁, h₂⟩ => top ⟨h₁, fieldsTerm_eq_nil.mp h₂⟩)
    (fun ⟨_, _, h⟩ => fieldsTerm_ne_atom l "term" h)
    (by rintro ⟨-, r, a, b, h⟩; cases l <;> simp [fieldsTerm, Term.list] at h) (by simp)

/-- Map literals other than the top one are one higher than their parts. -/
theorem mlit_litZ {k a b : Term} (h : MLit E (.tuple #[k, a, b])) : litZ a b = Bool.false := by
  obtain ⟨⟨k', tag, l, e, g, -⟩, nt, -⟩ := h
  obtain ⟨-, rfl, rfl⟩ := tuple3_inj e
  unfold litZ
  split
  · rename_i r a b h; cases l <;> simp [fieldsTerm, Term.list] at h
  · rfl

theorem mlit_lh_eq {k a b : Term} (h : MLit E (.tuple #[k, a, b])) : lh (.tuple #[k, a, b]) = max (lh a) (lh b) + 1 := by
  obtain ⟨⟨k', tag, l, e, g, -⟩, nt, -⟩ := h
  obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
  have top : ¬(tag = .atom "open" ∧ l = []) := fun ⟨h₁, h₂⟩ => nt ⟨_, by rw [e, h₁, h₂]; rfl⟩
  rw [e, lh_litM g top, ← e₂, ← e₃]

theorem mlit_lh {t : Term} (h : MLit E t) : 1 ≤ lh t ∧ ∀ (k : Int) (tag : Term) (l : List (Term × Term)),
    t = .tuple #[.integer k, tag, fieldsTerm l] →
      (∀ e ∈ l, ∀ u o, e.2 = .tuple #[u, boolAtom o] → lh u < lh t) ∧ ∀ e ∈ domFields tag, lh e.2 < lh t := by
  obtain ⟨⟨k, tag, l, rfl, g, sl⟩, nt, key⟩ := h
  have e₀ := mlit_lh_eq ⟨⟨k, tag, l, rfl, g, sl⟩, nt, key⟩
  refine ⟨by rw [e₀]; omega, fun k' tag' l' e => ?_⟩
  obtain ⟨-, e₂, e₃⟩ := tuple3_inj e
  have := fieldsTerm_inj e₃
  subst this e₂
  refine ⟨fun x mx u o hx => ?_, fun x mx => ?_⟩
  · have := lh_fields_mem mx hx; rw [e₀]; omega
  · rcases g with rfl | rfl | ⟨dl, rfl, -⟩
    · simp [domFields] at mx
    · simp [domFields] at mx
    · rw [domFields_fieldsTerm] at mx
      have := lh_list_mem (l := dl.map fun e => .tuple #[e.1, e.2]) (List.mem_map.mpr ⟨x, mx, rfl⟩)
      rw [lh_pair] at this
      have le : lh x.2 ≤ lh (fieldsTerm dl) := Nat.le_trans (by omega) this
      rw [e₀]; omega

/-- Literals of map BDDs are no higher than the BDD. -/
theorem mbdd_lh_le {ok : Term → Prop} {x : Term} (wx : Bdd ok x) (lits : ∀ t, ok t → MLit E t) :
    ∀ M, lh x ≤ M → Bdd (fun t => ok t ∧ lh t ≤ M) x := by
  revert lits
  refine Bdd.induction (P := fun ok x => (∀ t, ok t → MLit E t) → ∀ M, lh x ≤ M → Bdd (fun t => ok t ∧ lh t ≤ M) x)
    ?_ ?_ ?_ ?_ ok x wx
  · intro _ _ _ _; exact Bdd.top
  · intro _ _ _ _; exact Bdd.bot
  · intro ok k x y okl _ M le
    exact Bdd.leaf_iff.mpr ⟨okl, le⟩
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd lits M le
    obtain ⟨k, a, b, rfl⟩ := leaf
    have hl := mlit_lh_eq (lits _ okl)
    have nd := lh_node (.integer h) (.integer k) a b c u d (mlit_litZ (lits _ okl))
    change lh (.tuple ⟨[.integer h, .tuple ⟨[.integer k, a, b]⟩, c, u, d]⟩) ≤ M at le
    have hlit : lh (.tuple #[.integer k, a, b]) ≤ M := by omega
    have hc' : lh c ≤ M ∧ lh u ≤ M ∧ lh d ≤ M := by omega
    have lits' : ∀ t, Above ok (.tuple #[.integer k, a, b]) t → MLit E t := fun t ht => lits t ht.1
    refine Bdd.node_iff.mpr ⟨⟨k, _, _, rfl⟩, ⟨okl, hlit⟩, ?_, ?_, ?_⟩
    · exact (ic lits' M hc'.1).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩
    · exact (iu lits' M hc'.2.1).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩
    · exact (idd lits' M hc'.2.2).mono fun t ht => ⟨⟨ht.1.1, ht.2⟩, ht.1.2⟩

theorem mbdd_lh {x : Term} (wx : Bdd (MLit E) x) (nt : x ≠ .atom "bdd_top") (nb : x ≠ .atom "bdd_bot") :
    1 ≤ lh x := by
  rcases wx.shape with rfl | rfl | ⟨k, a, b, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · exact absurd rfl nt
  · exact absurd rfl nb
  · exact (mlit_lh (Bdd.leaf_iff.mp wx)).1
  · obtain ⟨⟨k, a, b, rfl⟩, okl, -⟩ := Bdd.node_iff.mp wx
    have := mlit_lh_eq okl
    have := lh_node (.integer h) (.integer k) a b c u d (mlit_litZ okl)
    change 1 ≤ lh (.tuple ⟨[.integer h, .tuple ⟨[.integer k, a, b]⟩, c, u, d]⟩)
    omega

theorem map_empty_step {d : Dispatcher} {x : Term} {S : List (Term × Term)}
    (fresh : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "map") x) e.1) (.cons (.atom "map") x) e.1 == .eq) = Bool.false) :
    Elixir.Module.Types.Descr.«map_empty?/2» d x (.map S) =
      Elixir.Module.Types.Descr.«map_bdd_empty?/4» d (.tuple #[.atom "open", .nil]) .nil x
        (.map ((.cons (.atom "map") x, .atom "true") :: S)) := by
  unfold Elixir.Module.Types.Descr.«map_empty?/2»
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
    Term.false, Erlang.maps.«put/3»]

theorem mlit_ok {t : Term} (h : MLit E t) : MapOk E t := by
  obtain ⟨⟨k, tag, l, rfl, g, sl⟩, nt, -⟩ := h
  exact ⟨⟨k, tag, l, rfl, g.plain, fun e me => (sl.1 e me).2⟩, nt⟩

theorem init_open_nil (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«init_map_line_empty?/4» d (.atom "open") .nil .nil S = .ok (.atom "false") := by
  rw [Elixir.Module.Types.Descr.«init_map_line_empty?/4».eq_def]
  simp [Erlang.lists.«any/2», Lynx.Except.orElse, Erlang.erlang.«is_function/2»]
  rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
  simp

/-- Map types decide their emptiness exactly, when the seen BDDs are higher than them. -/
theorem map_empty_exact (ef : EF nd E V den tl K) {x : Term} (fx : MField E x) (S : List (Term × Term)) :
    ∃ b : Bool, (∀ m, K + 2 ≤ m → Elixir.Module.Types.Descr.«map_empty?/2» (D m) x (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh x < N → SafeN N S → (b = Bool.true ↔ ∀ w, denMF E den x w = Bool.false) := by
  have field : MapField E x := fx.imp id fun w => w.mono fun _ h => mlit_ok h
  obtain ⟨b, hb⟩ := map_total ef.opsU ef.dopsU S field
  refine ⟨b, hb, fun N hx hS => ?_⟩
  have step := map_empty_step (d := D (K + 2)) (not_seen hS hx "map")
  have run := hb (K + 2) (Nat.le_refl _)
  dsimp only at run
  rw [step] at run
  have pos : ∀ {F : Term → Prop}, MapPosV F (.tuple #[.atom "open", .nil]) :=
    ⟨.atom "open", [], rfl, Or.inl rfl, by simp [FieldsV]⟩
  -- the top literal and BDDs without literals answer directly
  have direct : ∀ (c : Bool), Elixir.Module.Types.Descr.«map_bdd_empty?/4» (D (K + 2)) (.tuple #[.atom "open", .nil]) .nil x
      (.map ((.cons (.atom "map") x, .atom "true") :: S)) = .ok (boolAtom c) →
      (c = Bool.true ↔ ∀ w, denMF E den x w = Bool.false) → (b = Bool.true ↔ ∀ w, denMF E den x w = Bool.false) := by
    intro c hc sem
    rw [hc] at run
    have : b = c := by cases b <;> cases c <;> simp_all [boolAtom]
    rw [this]; exact sem
  have someW : Nonempty (MW V) := ⟨fun _ => Option.none⟩
  rcases fx with ⟨k, rfl⟩ | wx
  · refine direct Bool.false ?_ ⟨fun h => absurd h (by decide), fun h => absurd (h (fun _ => Option.none))
      (by rw [denMF_top]; simp)⟩
    have merge : ∀ (mod name : String) (caps : Array Term),
        Erlang.orddict.«merge/3» (D (K + 2)) (.function mod name 3 caps) .nil .nil = .ok .nil := by
      intro mod name caps; rw [Erlang.orddict.«merge/3».eq_def]; simp [Erlang.erlang.«is_function/2»]
    simp [Elixir.Module.Types.Descr.«map_bdd_empty?/4», Elixir.Module.Types.Descr.«map_line_intersection/3»,
      Elixir.Module.Types.Descr.«map_literal_intersection/6», boolAtom, merge, init_open_nil]
  by_cases top : x = .atom "bdd_top"
  · subst top
    refine direct Bool.false ?_ ⟨fun h => absurd h (by decide), fun h => absurd (h (fun _ => Option.none))
      (by rw [denMF_bdd wx]; simp)⟩
    simp [Elixir.Module.Types.Descr.«map_bdd_empty?/4», boolAtom, init_open_nil]
  by_cases bot : x = .atom "bdd_bot"
  · subst bot
    refine direct Bool.true ?_ ⟨fun _ w => by rw [denMF_bdd wx]; rfl, fun _ => rfl⟩
    simp [Elixir.Module.Types.Descr.«map_bdd_empty?/4», boolAtom]
  have one := mbdd_lh wx top bot
  have hS' := safe_put hS hx one "map"
  have ops := ef.ops (lh x) (by omega)
  have dops := ef.dops (lh x)
  have sem := ef.sem (lh x)
  have wb := mbdd_lh_le wx (fun _ h => h) (lh x) (Nat.le_refl _)
  have okLit : ∀ t, (MLit E t ∧ lh t ≤ lh x) → MapLitV (EB E (lh x)) t := by
    intro t ⟨ht, le⟩
    have hl := (mlit_lh ht).2
    obtain ⟨⟨k, tag, l, rfl, g, sl⟩, -, -⟩ := ht
    obtain ⟨hf, hd⟩ := hl k tag l rfl
    refine ⟨k, tag, l, rfl, ?_, fun e me => ⟨(sl.1 e me).1, ?_⟩, sl.2⟩
    · rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · refine Or.inr (Or.inr ⟨dl, rfl, fun e me => ⟨(dv.1 e me).1, (dv.1 e me).2, ?_⟩, dv.2⟩)
        have := hd e (by rw [domFields_fieldsTerm]; exact me); omega
    · obtain ⟨u, o, he, hu⟩ := (sl.1 e me).2
      exact ⟨u, o, he, hu, by have := hf e me u o he; omega⟩
  have agree : ∀ w, eval (valM (EB E (lh x)) den w) x = eval (valM E den w) x := fun w =>
    eval_ext wb fun t ht => by
      have h₁ := valM_iff ops dops sem (okLit t ht) (w := w)
      have h₂ := valM_iff ef.opsU ef.dopsU ef.semR ht.1.1 (w := w)
      cases e₁ : valM (EB E (lh x)) den w t <;> cases e₂ : valM E den w t <;> simp_all
  constructor
  · intro hbt w
    subst hbt
    rw [denMF_bdd wx]
    have v := map_bdd_sound ops dops sem (Nat.le_refl _) _ hS' wb okLit _ [] pos (by simp)
      (by simpa [boolAtom, Term.list] using run) w (inPosM_iff.mpr ⟨fun s => fsem_nil.mpr (Or.inl rfl), fun k i => Or.inl rfl⟩) (by simp)
    rwa [agree] at v
  · intro unsat
    have t := map_bdd_val ops dops sem (Nat.le_refl _) _ hS' wb okLit _ [] pos (by simp)
      fun w _ _ => by rw [agree]; have := unsat w; rwa [denMF_bdd wx] at this
    simp only [Term.list] at t
    rw [t] at run
    cases b <;> simp_all [boolAtom]

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem fieldValue_den {F : Term} (hF : FieldValue E F) :
    ∃ t, E t ∧ (∃ o, F = .tuple #[t, o]) ∧ ∀ x, den t x ↔ FieldSem den F (some x) := by
  obtain ⟨t, o, rfl, ht⟩ := hF
  exact ⟨t, ht, ⟨_, rfl⟩, fun x => by rw [fieldSem_mk]; simp⟩

/-- `map_get_keys/3` unites the values at atom keys of the maps of non-empty lines. -/
theorem get_keys (ef : EF nd E V den tl K) {n : Nat} (hn : K + 2 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L ∧ ∃ w, InMLine den L w) (rs : List Term) (hr : ∀ r ∈ rs, ∃ s, r = .atom s)
    {acc : Term} (ha : E acc) :
    ∃ T, Elixir.Module.Types.Descr.«map_get_keys/3» (D (n + 4)) (Term.list lines) (Term.list rs) acc = .ok T ∧
      E T ∧ ∀ x, den T x ↔ den acc x ∨ ∃ s, .atom s ∈ rs ∧ ∃ L ∈ lines, LongM den L s (some x) := by
  obtain ⟨T, ⟨hT, sT⟩, run⟩ := foldl_rel_at (m := n + 4) "Elixir.Module.Types.Descr" "-map_get_keys/3-fun-0-"
    #[Term.list lines] (fun pre a => E a ∧ ∀ x, den a x ↔ den acc x ∨ ∃ s, .atom s ∈ pre ∧ ∃ L ∈ lines, LongM den L s (some x))
    rs (fun pre r a mr ⟨ha', sa⟩ => by
      obtain ⟨s, rfl⟩ := hr r mr
      obtain ⟨F, rF, hF, sF⟩ := mdnf_fetch ef hn s lines hl
      obtain ⟨t, ht, ⟨o, rfl⟩, st⟩ := fieldValue_den (den := den) hF
      obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] ht ha' (m := n + 3) (by omega)
      refine ⟨c, ⟨hc, fun x => ?_⟩, ?_⟩
      · rw [sc, sa, st, sF]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | h | ⟨s', m', h⟩)
          · exact Or.inr ⟨s, Or.inr rfl, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨s', Or.inl m', h⟩
        · rintro (h | ⟨s', m' | e, h⟩)
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨s', m', h⟩)
          · cases e; exact Or.inl h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_get_keys/3-fun-0-/2».pure]
        simp [Elixir.Module.Types.Descr.«-map_get_keys/3-fun-0-/3», rF, Elixir.Module.Types.Descr.«opt_union/2», rc])
    acc ⟨ha, fun x => by simp⟩
  exact ⟨T, by simpa [Elixir.Module.Types.Descr.«map_get_keys/3»] using run, hT, sT⟩

theorem is_list_fieldsTerm (l : List (Term × Term)) : Erlang.erlang.«is_list/1» (fieldsTerm l) = .ok (.atom "true") := by
  cases l <;> simp [fieldsTerm, Term.list, Erlang.erlang.«is_list/1»]

/-- The type a tag gives the keys of a kind, as `map_get_domain/3` computes it. -/
theorem tag_type_run {tag : Term} (g : TagV E tag) (s : String) (d : Dispatcher) (f n acc : Term) :
    Elixir.Module.Types.Descr.«-map_get_domain/3-fun-0-/3» d (.atom s) (.tuple #[tag, f, n]) acc =
      Elixir.Module.Types.Descr.«opt_union/2» d (tagType tag s) acc := by
  rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
  · simp [Elixir.Module.Types.Descr.«-map_get_domain/3-fun-0-/3», tagType]
  · simp [Elixir.Module.Types.Descr.«-map_get_domain/3-fun-0-/3», tagType]
  · have fd := find_dom s dv
    have ne := fieldsTerm_ne_atom dl
    have il := is_list_fieldsTerm dl
    rw [tagType_dom]
    generalize fieldsTerm dl = T at fd ne il
    rw [Elixir.Module.Types.Descr.«-map_get_domain/3-fun-0-/3».eq_def]
    simp only
    split
    · exact absurd rfl (ne _)
    · exact absurd rfl (ne _)
    · simp [il, Elixir.Module.Types.Descr.«fields_get/3», fd]
      cases mapLookup dl (.atom s) <;> rfl

/-- Values of a kind that the tag of a line allows. -/
def LineTag (den : Term → V → Prop) (L : Term) (s : String) (x : V) : Prop :=
  ∃ (tag : Term) (l : List (Term × Term)) (negs : List Term), L = .tuple #[tag, fieldsTerm l, Term.list negs] ∧
    den (tagType tag s) x

/-- `map_get_domain/3` folded over kinds unites the types the tags of lines give them. -/
theorem get_domains (ef : EF nd E V den tl K) {n : Nat} (hn : K + 2 ≤ n) (lines : List Term)
    (hl : ∀ L ∈ lines, MLine E L) (ds : List Term) (hd : ∀ d ∈ ds, ∃ s, d = .atom s) {acc : Term} (ha : E acc) :
    ∃ T, Erlang.lists.«foldl/3» (D (n + 4))
        (.function "Elixir.Module.Types.Descr" "-map_get_static_dnf/3-fun-0-" 2 #[Term.list lines]) acc (Term.list ds) =
          .ok T ∧ E T ∧ ∀ x, den T x ↔ den acc x ∨ ∃ s, .atom s ∈ ds ∧ ∃ L ∈ lines, LineTag den L s x := by
  obtain ⟨T, ⟨hT, sT⟩, run⟩ := foldl_rel_at (m := n + 4) "Elixir.Module.Types.Descr" "-map_get_static_dnf/3-fun-0-"
    #[Term.list lines] (fun pre a => E a ∧ ∀ x, den a x ↔ den acc x ∨ ∃ s, .atom s ∈ pre ∧ ∃ L ∈ lines, LineTag den L s x)
    ds (fun pre r a mr ⟨ha', sa⟩ => by
      obtain ⟨s, rfl⟩ := hd r mr
      obtain ⟨c, ⟨hc, sc⟩, rc⟩ := foldl_rel_at (m := n + 3) "Elixir.Module.Types.Descr" "-map_get_domain/3-fun-0-"
        #[.atom s] (fun pre' a' => E a' ∧ ∀ x, den a' x ↔ den a x ∨ ∃ L ∈ pre', LineTag den L s x) lines
        (fun pre' L b mL ⟨hb, sb⟩ => by
          obtain ⟨tag, l, negs, rfl, g, -, -⟩ := hl L mL
          have hty := tagType_value ef.mopsE g s
          obtain ⟨c, hc, rc, sc⟩ := ef.opt_union [] hty hb (m := n + 2) (by omega)
          refine ⟨c, ⟨hc, fun x => ?_⟩, ?_⟩
          · rw [sc, sb]
            simp only [List.mem_append, List.mem_singleton]
            constructor
            · rintro (h | h | ⟨L', m', h⟩)
              · exact Or.inr ⟨_, Or.inr rfl, tag, l, negs, rfl, h⟩
              · exact Or.inl h
              · exact Or.inr ⟨L', Or.inl m', h⟩
            · rintro (h | ⟨L', m' | e, h⟩)
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr ⟨L', m', h⟩)
              · subst e
                obtain ⟨tag', l', negs', e', h'⟩ := h
                obtain ⟨rfl, -, -⟩ := tuple3_inj e'
                exact Or.inl h'
          · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_get_domain/3-fun-0-/2».pure,
              tag_type_run g s, Elixir.Module.Types.Descr.«opt_union/2», rc])
        a ⟨ha', fun x => by simp⟩
      refine ⟨c, ⟨hc, fun x => ?_⟩, ?_⟩
      · rw [sc, sa]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro ((h | ⟨s', m', h⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨s', Or.inl m', h⟩
          · exact Or.inr ⟨s, Or.inr rfl, h⟩
        · rintro (h | ⟨s', m' | e, h⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr ⟨s', m', h⟩)
          · cases e; exact Or.inr h
      · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_get_static_dnf/3-fun-0-/2».pure]
        simpa [Elixir.Module.Types.Descr.«-map_get_static_dnf/3-fun-0-/3», Elixir.Module.Types.Descr.«map_get_domain/3»]
          using rc)
    acc ⟨ha, fun x => by simp⟩
  exact ⟨T, run, hT, sT⟩

/-! Keys of map BDDs outside a negated set of atoms. -/

/-- Literals whose field keys outside a negated set are among some keys. -/
def NegNamed (N new : List (Term × Term)) (t : Term) : Prop :=
  ∀ (k : Int) (tag : Term) (l : List (Term × Term)), t = .tuple #[.integer k, tag, fieldsTerm l] →
    ∀ s ∈ keyStrs l, mapLookup N (.atom s) = none → (.atom s, .atom "true") ∈ new

/-- Keys added outside a negated set of atoms. -/
def NegNew (N new : List (Term × Term)) : Prop :=
  ∀ e ∈ new, ∃ s, e = (.atom s, .atom "true") ∧ mapLookup N (.atom s) = none

theorem negNew_append {N a b : List (Term × Term)} (ha : NegNew N a) (hb : NegNew N b) : NegNew N (a ++ b) :=
  fun e me => (List.mem_append.mp me).elim (ha e) (hb e)

theorem negNamed_mono {N a b : List (Term × Term)} (h : ∀ e ∈ a, e ∈ b) {t : Term} (ht : NegNamed N a t) :
    NegNamed N b t :=
  fun k tag l e s ms ns => h _ (ht k tag l e s ms ns)

/-- `orddict:fold/3` over fields adds their keys outside a negated set. -/
theorem neg_fold (N : List (Term × Term)) (m : Nat) : ∀ (l : List (Term × Term)), FieldsV E l → ∀ es,
    ∃ new, Erlang.orddict.«fold/3» (D m)
        (.function "Elixir.Module.Types.Descr" "-map_keys_from_negated_set/2-fun-0-" 3 #[.map N]) (.map es)
        (fieldsTerm l) = .ok (.map (new ++ es)) ∧ NegNew N new ∧
      ∀ s ∈ keyStrs l, mapLookup N (.atom s) = none → (.atom s, .atom "true") ∈ new
  | [], _, es => ⟨[], by rw [Erlang.orddict.«fold/3».eq_def]; simp [fieldsTerm, Term.list,
      Erlang.erlang.«is_function/2»], by simp [NegNew], by simp [keyStrs]⟩
  | (k, v) :: t, sl, es => by
    obtain ⟨⟨b, rfl⟩, ty, o, rfl, -⟩ := sl.1 _ List.mem_cons_self
    have step : Elixir.Module.Types.Descr.«-map_keys_from_negated_set/2-fun-0-/4» (.map N) (.atom b)
        (.tuple #[ty, boolAtom o]) (.map es) =
          .ok (.map (if (mapLookup N (.atom b)).isSome then es else (.atom b, .atom "true") :: es)) := by
      cases h : (mapLookup N (.atom b)).isSome <;>
        simp [Elixir.Module.Types.Descr.«-map_keys_from_negated_set/2-fun-0-/4», Erlang.sets.«is_element/2», h,
          Lynx.Term.isMember, Erlang.maps.«put/3», Term.true, Term.false]
    obtain ⟨new, run, hn, hk⟩ := neg_fold N m t (fieldsV_tail sl)
      (if (mapLookup N (.atom b)).isSome then es else (.atom b, .atom "true") :: es)
    cases h : (mapLookup N (.atom b)).isSome
    · simp only [h, Bool.false_eq_true, ↓reduceIte] at run
      refine ⟨new ++ [(.atom b, .atom "true")], ?_, negNew_append hn fun e me => ?_, fun s ms ns => ?_⟩
      · rw [Erlang.orddict.«fold/3».eq_def]
        simp [fieldsTerm_cons, Erlang.program.«Elixir.Module.Types.Descr:-map_keys_from_negated_set/2-fun-0-/3».pure,
          step, h, run]
      · simp at me; subst me; exact ⟨b, rfl, by simpa using h⟩
      · simp only [keyStrs, List.filterMap_cons, List.mem_cons] at ms
        rcases ms with rfl | ms
        · simp
        · exact List.mem_append_left _ (hk s ms ns)
    · simp only [h, ↓reduceIte] at run
      refine ⟨new, ?_, hn, fun s ms ns => ?_⟩
      · rw [Erlang.orddict.«fold/3».eq_def]
        simp [fieldsTerm_cons, Erlang.program.«Elixir.Module.Types.Descr:-map_keys_from_negated_set/2-fun-0-/3».pure,
          step, h, run]
      · simp only [keyStrs, List.filterMap_cons, List.mem_cons] at ms
        rcases ms with rfl | ms
        · rw [ns] at h; cases h
        · exact hk s ms ns

theorem neg_leaf (N : List (Term × Term)) (m : Nat) {t : Term} (ht : MapLitV E t) (es : List (Term × Term)) :
    ∃ new, Lynx.Dispatcher.pure (D (m + 1))
        (.function "Elixir.Module.Types.Descr" "-map_keys_from_negated_set/2-fun-1-" 2 #[.map N]) #[t, .map es] =
          .ok (.map (new ++ es)) ∧ NegNew N new ∧ NegNamed N new t := by
  obtain ⟨k, tag, l, rfl, -, sl⟩ := ht
  obtain ⟨new, run, hn, hk⟩ := neg_fold N m l sl es
  refine ⟨new, ?_, hn, fun k' tag' l' e s ms ns => ?_⟩
  · rw [Erlang.program.«Elixir.Module.Types.Descr:-map_keys_from_negated_set/2-fun-1-/2».pure]
    simpa [Elixir.Module.Types.Descr.«-map_keys_from_negated_set/2-fun-1-/3»] using run
  · obtain ⟨-, -, e₃⟩ := tuple3_inj e
    rw [← fieldsTerm_inj e₃] at ms
    exact hk s ms ns

/-- `bdd_reduce/3` collects the field keys of a map BDD outside a negated set. -/
theorem neg_reduce (N : List (Term × Term)) (m : Nat) {b : Term} (wb : Bdd (MLit E) b) :
    ∀ es, ∃ new, Elixir.Module.Types.Descr.«bdd_reduce/3» (D (m + 1)) b (.map es)
        (.function "Elixir.Module.Types.Descr" "-map_keys_from_negated_set/2-fun-1-" 2 #[.map N]) =
          .ok (.map (new ++ es)) ∧ NegNew N new ∧ Bdd (fun t => MLit E t ∧ NegNamed N new t) b := by
  refine Bdd.induction (P := fun ok b => (∀ t, ok t → MLit E t) → ∀ es, ∃ new,
      Elixir.Module.Types.Descr.«bdd_reduce/3» (D (m + 1)) b (.map es)
        (.function "Elixir.Module.Types.Descr" "-map_keys_from_negated_set/2-fun-1-" 2 #[.map N]) =
          .ok (.map (new ++ es)) ∧ NegNew N new ∧ Bdd (fun t => ok t ∧ NegNamed N new t) b)
    ?_ ?_ ?_ ?_ (MLit E) b wb (fun _ h => h)
  · intro ok _ es
    exact ⟨[], by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simp, by simp [NegNew], by simp [Bdd]⟩
  · intro ok _ es
    exact ⟨[], by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simp, by simp [NegNew], by simp [Bdd]⟩
  · intro ok k x y okl lit es
    obtain ⟨new, run, hn, hk⟩ := neg_leaf N m (lit _ okl).1 es
    exact ⟨new, by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simpa using run, hn,
      Bdd.leaf_iff.mpr ⟨okl, hk⟩⟩
  · intro ok h lit c u d isLeaf okl _ _ _ ic iu id lits es
    have lits' : ∀ t, Above ok lit t → MLit E t := fun t ht => lits t ht.1
    obtain ⟨n₀, r₀, h₀, k₀⟩ := neg_leaf N m (lits _ okl).1 es
    obtain ⟨n₁, r₁, h₁, k₁⟩ := ic lits' (n₀ ++ es)
    obtain ⟨n₂, r₂, h₂, k₂⟩ := iu lits' (n₁ ++ (n₀ ++ es))
    obtain ⟨n₃, r₃, h₃, k₃⟩ := id lits' (n₂ ++ (n₁ ++ (n₀ ++ es)))
    refine ⟨n₃ ++ n₂ ++ n₁ ++ n₀, ?_, negNew_append (negNew_append (negNew_append h₃ h₂) h₁) h₀, ?_⟩
    · rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]
      simp [r₀, r₁, r₂, r₃]
    · have lift : ∀ (n' : List (Term × Term)), (∀ e ∈ n', e ∈ n₃ ++ n₂ ++ n₁ ++ n₀) →
          ∀ t, (Above ok lit t ∧ NegNamed N n' t) → Above (fun t => ok t ∧ NegNamed N (n₃ ++ n₂ ++ n₁ ++ n₀) t) lit t :=
        fun n' sub t ⟨⟨o, lt⟩, nt⟩ => ⟨⟨o, negNamed_mono sub nt⟩, lt⟩
      exact Bdd.node_iff.mpr ⟨isLeaf, ⟨okl, negNamed_mono (fun e me => by simp [me]) k₀⟩,
        k₁.mono (lift n₁ (fun e me => by simp [me])), k₂.mono (lift n₂ (fun e me => by simp [me])), k₃.mono (lift n₃ (fun e me => by simp [me]))⟩

end

end Elixir.STTDescrProofsTest.Nest

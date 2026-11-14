namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem guard_true {g : Except Exception Term} {body next : Unit → Except Exception Term}
    (h : Lynx.Except.guard g body next = .ok (.atom "true")) :
    (g = .ok (.atom "true") ∧ body () = .ok (.atom "true")) ∨ next () = .ok (.atom "true") := by
  cases g with
  | error e =>
    simp only [Lynx.Except.guard_eq, Lynx.Except.tryWith] at h
    split at h <;> simp_all
  | ok v =>
    rw [Lynx.Except.guard_ok] at h
    split at h
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr h

theorem is_atom_true {k : Term} (h : Erlang.erlang.«is_atom/1» k = .ok (.atom "true")) : ∃ s, k = .atom s := by
  cases k <;> simp [Erlang.erlang.«is_atom/1»] at h ⊢

theorem is_boolean_true {o : Term} (h : Erlang.erlang.«is_boolean/1» o = .ok (.atom "true")) :
    ∃ b, o = boolAtom b := by
  simp only [Erlang.erlang.«is_boolean/1»] at h
  split at h
  · exact ⟨Bool.true, rfl⟩
  · exact ⟨Bool.false, rfl⟩
  · simp at h

theorem cons_nil_false {a rest : Term} (h : Erlang.erlang.«==/2» (.cons a rest) .nil = .ok (.atom "true")) : False := by
  cases nil_of_eq h

/-- A pair checked by `map_pairs?/2`: a field of an atom key, or a domain of kinds, of static types. -/
def PairN (N a : Term) : Prop :=
  (∃ (s : String) (v : Term) (b : Bool), a = .tuple #[.atom s, .tuple #[v, boolAtom b]] ∧
    «arrows_static?/2» v N = .ok (.atom "true")) ∨
  ∃ ks v, a = .tuple #[Term.list ks, v] ∧ (∀ k ∈ ks, ∃ s ∈ domainKinds, k = .atom s) ∧
    «arrows_static?/2» v N = .ok (.atom "true")

theorem pair_step {a rest N : Term} (h : Elixir.STTDescrProofsTest.«map_pairs?/2» (.cons a rest) N = .ok (.atom "true")) :
    PairN N a ∧ Elixir.STTDescrProofsTest.«map_pairs?/2» rest N = .ok (.atom "true") := by
  rw [Elixir.STTDescrProofsTest.«map_pairs?/2».eq_def] at h
  simp only at h
  -- the domain clause, after the field clause fails
  have second : ∀ {kinds value : Term}, a = .tuple #[kinds, value] →
      Lynx.Except.guard (Erlang.erlang.«is_list/1» kinds)
        (fun _ => Lynx.Except.andAlso (Lynx.Except.andAlso (Elixir.STTDescrProofsTest.«kind_list?/1» kinds)
          («arrows_static?/2» value N) Bool.true) (Elixir.STTDescrProofsTest.«map_pairs?/2» rest N) Bool.true)
        (fun _ => Erlang.erlang.«==/2» (.cons a rest) .nil) = .ok (.atom "true") →
      PairN N a ∧ Elixir.STTDescrProofsTest.«map_pairs?/2» rest N = .ok (.atom "true") := by
    intro kinds value ha g
    rcases guard_true g with ⟨-, g⟩ | g
    · simp only [Lynx.Except.andAlso_eq_true] at g
      obtain ⟨ks, rfl, hks⟩ := kind_list_ok _ g.1.1
      exact ⟨Or.inr ⟨ks, value, ha, hks, g.1.2⟩, g.2⟩
    · exact (cons_nil_false g).elim
  split at h
  · rename_i k v o ps heq
    simp only [Term.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rcases guard_true h with ⟨g1, g2⟩ | h2
    · simp only [Lynx.Except.andAlso_eq_true] at g1 g2
      obtain ⟨s, rfl⟩ := is_atom_true g1.1
      obtain ⟨b, rfl⟩ := is_boolean_true g1.2
      exact ⟨Or.inl ⟨s, v, b, rfl, g2.1⟩, g2.2⟩
    · simp only at h2
      exact second rfl h2
  · split at h
    · rename_i kinds value ps heq
      simp only [Term.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact second rfl h
    · exact (cons_nil_false h).elim

section
variable {t : Term} {d : Nat}

/-- Pairs that `map_pairs?/2` accepts at a nesting are pairs of constructors one level up. -/
theorem map_pairs_ok : ∀ (P : Term), Elixir.STTDescrProofsTest.«map_pairs?/2» P (.tuple #[.integer d, t]) =
    .ok (.atom "true") → ∃ fs, P = Term.list fs ∧ ∀ p ∈ fs, CPair t (d + 1) p
  | .cons a rest, h => by
    obtain ⟨pa, hr⟩ := pair_step h
    obtain ⟨fs, rfl, hfs⟩ := map_pairs_ok rest hr
    refine ⟨a :: fs, rfl, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp
    · rcases pa with ⟨s, v, b, rfl, hv⟩ | ⟨ks, v, rfl, hks, hv⟩
      · exact Or.inl ⟨s, v, b, rfl, Or.inl (arrows_static_ok hv)⟩
      · exact Or.inr ⟨ks, v, rfl, hks, Or.inl (arrows_static_ok hv)⟩
    · exact hfs p hp
  | .nil, _ => ⟨[], rfl, by simp⟩
  | .integer _, h | .float _, h | .atom _, h | .reference _, h | .function _ _ _ _, h | .pid _, h | .tuple _, h
  | .map _, h | .bitstring _ _ _, h => by
    rw [Elixir.STTDescrProofsTest.«map_pairs?/2».eq_def] at h
    cases nil_of_eq h

end

theorem kind_in_run (s : String) : ∀ ks : List Term, (∀ k ∈ ks, ∃ s', k = .atom s') →
    ∃ b : Bool, Elixir.STTDescrProofsTest.«kind_in?/2» (Term.list ks) (.atom s) = .ok (boolAtom b) ∧
      (b = Bool.true ↔ Term.atom s ∈ ks)
  | [], _ => ⟨Bool.false, by simp [Elixir.STTDescrProofsTest.«kind_in?/2», boolAtom], by simp⟩
  | k :: ks, h => by
    obtain ⟨s', rfl⟩ := h k (by simp)
    obtain ⟨b, ih, hb⟩ := kind_in_run s ks (fun k hk => h k (by simp [hk]))
    rw [Term.list_cons, Elixir.STTDescrProofsTest.«kind_in?/2».eq_def]
    by_cases e : s' = s
    · subst e; exact ⟨Bool.true, by simp [Erlang.erlang.«==/2», boolAtom], by simp⟩
    · have ne : ¬Term.compare (Term.fuel (.atom s') (.atom s)) (.atom s') (.atom s) = .eq := by simpa using e
      refine ⟨b, by simp [Erlang.erlang.«==/2», ne, ih], ?_⟩
      rw [hb]
      simp only [List.mem_cons, Term.atom.injEq]
      exact ⟨Or.inr, fun h => h.resolve_left fun h' => e h'.symm⟩

/-- Elements of pair lists are pairs. -/
theorem keyfind_lk (k : Term) : ∀ L : List Term, (∀ x ∈ L, ∃ a b, x = .tuple #[a, b]) →
    Erlang.lists.«keyfind/3» k (.integer 1) (Term.list L) =
      .ok ((USort.lk fk k L).getD (.atom "false"))
  | [], _ => by simp [Erlang.lists.«keyfind/3»]
  | x :: L, h => by
    obtain ⟨a, b, rfl⟩ := h x (by simp)
    have ih := keyfind_lk k L (fun y hy => h y (by simp [hy]))
    rw [Term.list_cons]
    simp only [Erlang.lists.«keyfind/3», USort.lk_cons, show fk (.tuple #[a, b]) = a from rfl]
    by_cases e : Term.compare (Term.fuel a k) a k = .eq
    · simp [e]
    · simp [e, ih]

section
variable {t : Term} {n : Nat}

/-- `domain_value/4` joins the values of the domain pairs naming a kind. -/
theorem dv_run {m : Nat} (hm : (level t n).K ≤ m) (s : String) : ∀ (rest P : List Term),
    (∀ p ∈ rest, CPair t n p) → ∀ (acc : Term) (found : Bool), (level t n).E acc → (found = Bool.true ↔ DomAny P s) →
    (found = Bool.true → ∀ x, (level t n).den acc x ↔ DomMem (t := t) (n := n) P s x) →
    ∃ U, Elixir.STTDescrProofsTest.«domain_value/4» (D m) (Term.list rest) (.atom s) acc (boolAtom found) = .ok U ∧
      (level t n).E U ∧ (DomAny (P ++ rest) s → ∀ x, (level t n).den U x ↔ DomMem (t := t) (n := n) (P ++ rest) s x) ∧
      (¬DomAny (P ++ rest) s → U = acc)
  | [], P, _, acc, found, he, hf, hd => ⟨acc, by simp [Elixir.STTDescrProofsTest.«domain_value/4»], he,
      fun a x => by simpa using hd (hf.mpr (by simpa using a)) x, fun _ => rfl⟩
  | p :: rest, P, hr, acc, found, he, hf, hd => by
    have hr' : ∀ q ∈ rest, CPair t n q := fun q hq => hr q (by simp [hq])
    have app : P ++ p :: rest = (P ++ [p]) ++ rest := by simp
    rcases hr p (by simp) with ⟨a, v, o, rfl, hv⟩ | ⟨ks, v, rfl, hks, hv⟩
    · -- fields are skipped
      have nd : ∀ ks' v', Term.tuple #[Term.list ks', v'] ∈ P ++ [Term.tuple #[.atom a, .tuple #[v, boolAtom o]]] ↔
          Term.tuple #[Term.list ks', v'] ∈ P := by
        intro ks' v'
        simp only [List.mem_append, List.mem_singleton, or_iff_left_iff_imp]
        intro h; exact absurd h.symm (field_ne_dom a _ ks' v')
      obtain ⟨U, run, hU, h1, h2⟩ := dv_run hm s rest (P ++ [Term.tuple #[.atom a, .tuple #[v, boolAtom o]]]) hr'
        acc found he
        (by simp only [DomAny, nd]; exact hf) (fun f x => by simp only [DomMem, nd]; exact hd f x)
      refine ⟨U, ?_, hU, by rw [app]; exact h1, by rw [app]; exact h2⟩
      rw [Term.list_cons, Elixir.STTDescrProofsTest.«domain_value/4».eq_def]
      simp [Erlang.erlang.«is_list/1», run]
    · have hks' : ∀ k ∈ ks, ∃ s', k = .atom s' := fun k hk => by
        obtain ⟨s', -, rfl⟩ := hks k hk; exact ⟨s', rfl⟩
      have ki := kind_in_run s ks hks'
      have anyP : ∀ s', DomAny (P ++ [Term.tuple #[Term.list ks, v]]) s' ↔ DomAny P s' ∨ Term.atom s' ∈ ks := by
        intro s'
        simp only [DomAny, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨ks', v', h1 | h1, h2⟩
          · exact Or.inl ⟨ks', v', h1, h2⟩
          · obtain ⟨rfl, rfl⟩ := dom_tuple_inj h1; exact Or.inr h2
        · rintro (⟨ks', v', h1, h2⟩ | h2)
          · exact ⟨ks', v', Or.inl h1, h2⟩
          · exact ⟨ks, v, Or.inr rfl, h2⟩
      have memP : ∀ x, DomMem (t := t) (n := n) (P ++ [Term.tuple #[Term.list ks, v]]) s x ↔
          DomMem (t := t) (n := n) P s x ∨ (Term.atom s ∈ ks ∧ (level t n).den v x) := by
        intro x
        simp only [DomMem, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨ks', v', h1 | h1, h2, h3⟩
          · exact Or.inl ⟨ks', v', h1, h2, h3⟩
          · obtain ⟨rfl, rfl⟩ := dom_tuple_inj h1; exact Or.inr ⟨h2, h3⟩
        · rintro (⟨ks', v', h1, h2, h3⟩ | ⟨h2, h3⟩)
          · exact ⟨ks', v', Or.inl h1, h2, h3⟩
          · exact ⟨ks, v, Or.inr rfl, h2, h3⟩
      obtain ⟨b, ki, hb⟩ := ki
      have nf : found = Bool.false → ¬DomAny P s := fun e h => by rw [e] at hf; simpa using hf.mpr h
      by_cases mem : Term.atom s ∈ ks
      · have bt : b = Bool.true := hb.mpr mem
        subst bt
        have anyAll : DomAny (P ++ Term.tuple #[Term.list ks, v] :: rest) s := ⟨ks, v, by simp, mem⟩
        cases found
        · obtain ⟨U, run, hU, h1, h2⟩ := dv_run hm s rest (P ++ [Term.tuple #[Term.list ks, v]]) hr' v Bool.true hv
            (by simp [anyP, mem]) (fun _ x => by
              rw [memP]
              have : ¬DomMem (t := t) (n := n) P s x := fun ⟨ks', v', h1, h2, _⟩ => nf rfl ⟨ks', v', h1, h2⟩
              simp [this, mem])
          refine ⟨U, ?_, hU, by rw [app]; exact h1, fun h => absurd anyAll h⟩
          rw [Term.list_cons, Elixir.STTDescrProofsTest.«domain_value/4».eq_def]
          simp only [boolAtom, ↓reduceIte] at run
          simp [is_list_list, ki, boolAtom, exact_ok, run]
        · obtain ⟨c, hc, rc, sc, -⟩ := (level t n).ef.union he hv
          obtain ⟨U, run, hU, h1, h2⟩ := dv_run hm s rest (P ++ [Term.tuple #[Term.list ks, v]]) hr' c Bool.true hc
            (by simp [anyP, mem]) (fun _ x => by rw [memP, sc x, hd rfl x]; simp [mem])
          refine ⟨U, ?_, hU, by rw [app]; exact h1, fun h => absurd anyAll h⟩
          rw [Term.list_cons, Elixir.STTDescrProofsTest.«domain_value/4».eq_def]
          simp only [boolAtom, ↓reduceIte] at run
          simp [is_list_list, ki, boolAtom, rc m hm, run]
      · have bf : b = Bool.false := by cases b <;> simp_all
        subst bf
        obtain ⟨U, run, hU, h1, h2⟩ := dv_run hm s rest (P ++ [Term.tuple #[Term.list ks, v]]) hr' acc found he
          (by rw [hf, anyP]; simp [mem]) (fun f x => by rw [memP, hd f x]; simp [mem])
        refine ⟨U, ?_, hU, by rw [app]; exact h1, by rw [app]; exact h2⟩
        rw [Term.list_cons, Elixir.STTDescrProofsTest.«domain_value/4».eq_def]
        cases found <;> simp only [boolAtom, ↓reduceIte, Bool.false_eq_true] at run ⊢ <;> simp [is_list_list, ki, boolAtom, run]

end

theorem lk_filter (k : Term) (s : String) (hk : k = .atom s) : ∀ L : List Term,
    (∀ x ∈ L, isF x = Bool.false → Term.compare (Term.fuel (fk x) k) (fk x) k ≠ .eq) → USort.lk fk k (L.filter isF) = USort.lk fk k L
  | [], _ => rfl
  | x :: L, h => by
    have ih := lk_filter k s hk L (fun y hy => h y (by simp [hy]))
    cases hx : isF x
    · have ne := h x (by simp) hx
      simp [hx, USort.lk_cons, ne, ih]
    · simp [hx, USort.lk_cons, ih]

section
variable {t : Term} {n : Nat}

/-- The values a tag gives the keys of a kind no pair names. -/
theorem tag_value_run (tag : String) (ht : tag = "open" ∨ tag = "closed") :
    ∃ T, Elixir.STTDescrProofsTest.«tag_value/1» (.atom tag) = .ok T ∧ (level t n).E T ∧
      ∀ x, ((level t n).den T x ↔ tag = "open") := by
  rcases ht with rfl | rfl
  · exact ⟨_, by simp [Elixir.STTDescrProofsTest.«tag_value/1», Elixir.Module.Types.Descr.«term/0»],
      (level t n).ef.term, fun x => by simp [(level t n).ef.den_term]⟩
  · exact ⟨_, by simp [Elixir.STTDescrProofsTest.«tag_value/1», Elixir.Module.Types.Descr.«none/0»],
      (level t n).ef.none, fun x => by simp [(level t n).ef.den_none]⟩

theorem domain_value_run {m : Nat} (hm : (level t n).K ≤ m) (tag : String) (ht : tag = "open" ∨ tag = "closed")
    (s : String) (fs : List Term) (h : ∀ p ∈ fs, CPair t n p) :
    ∃ U, Elixir.STTDescrProofsTest.«domain_value/3» (D m) (.atom tag) (Term.list fs) (.atom s) = .ok U ∧
      (level t n).E U ∧ ∀ x, (level t n).den U x ↔
        ((DomAny fs s ∧ DomMem (t := t) (n := n) fs s x) ∨ (¬DomAny fs s ∧ tag = "open")) := by
  obtain ⟨T, rT, eT, dT⟩ := tag_value_run (t := t) (n := n) tag ht
  obtain ⟨U, run, hU, h1, h2⟩ := dv_run hm s fs [] h T Bool.false eT (by simp [DomAny]) (by simp)
  simp only [boolAtom, ↓reduceIte, Bool.false_eq_true] at run
  refine ⟨U, by simp [Elixir.STTDescrProofsTest.«domain_value/3», rT, run], hU, fun x => ?_⟩
  simp only [List.nil_append] at h1 h2
  by_cases a : DomAny fs s
  · simp [a, h1 a x]
  · simp [a, h2 a, dT x]

/-- `atom_field/3`: the field of the last pair of a key, or the optional values of the atom domain. -/
theorem atom_field_run {m : Nat} (hm : (level t n).K ≤ m) (tag : String) (ht : tag = "open" ∨ tag = "closed")
    (s : String) (fs : List Term) (h : ∀ p ∈ fs, CPair t n p) :
    ∃ (T : Term) (b : Bool), Elixir.STTDescrProofsTest.«atom_field/3» (D m) (.atom tag) (Term.list fs) (.atom s) =
      .ok (.tuple #[T, boolAtom b]) ∧ (level t n).E T ∧ ∀ o,
        FieldSem (level t n).den (.tuple #[T, boolAtom b]) o ↔ CAtom (t := t) (n := n) tag fs s o := by
  have pairs : ∀ x ∈ fs.reverse, ∃ a b, x = .tuple #[a, b] := fun x hx => by
    rcases h x (List.mem_reverse.mp hx) with ⟨a, v, o, rfl, -⟩ | ⟨ks, v, rfl, -, -⟩
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  have kf := keyfind_lk (.atom s) fs.reverse pairs
  have lkr : USort.lk fk (.atom s) (fieldsRev fs) = USort.lk fk (.atom s) fs.reverse := by
    rw [fieldsRev, ← List.filter_reverse]
    refine lk_filter _ s rfl _ fun x hx hf => ?_
    rcases h x (List.mem_reverse.mp hx) with ⟨a, v, o, rfl, -⟩ | ⟨ks, v, rfl, -, -⟩
    · simp [isF_field] at hf
    · intro e
      have := (Term.compare_eq_atom _ _).mp e
      cases ks <;> simp [fk, Term.list] at this
  unfold CAtom
  rw [lkr]
  cases hx : USort.lk fk (.atom s) fs.reverse with
  | none =>
    obtain ⟨U, rU, eU, dU⟩ := domain_value_run hm tag ht "atom" fs h
    refine ⟨U, Bool.true, ?_, eU, fun o => ?_⟩
    · simp [Elixir.STTDescrProofsTest.«atom_field/3», reverse1_list, kf, hx, rU, boolAtom]
    · rw [fieldSem_mk]
      cases o with
      | none => simp [CKind]
      | some x => simp [CKind, dU x]
  | some x =>
    obtain ⟨mx, ex⟩ := lk_spec hx
    rcases h x (List.mem_reverse.mp mx) with ⟨a, v, o, rfl, hv⟩ | ⟨ks, v, rfl, -, -⟩
    · have e : a = s := by simpa [fk] using ex
      subst e
      refine ⟨v, o, ?_, hv, fun o' => Iff.rfl⟩
      simp [Elixir.STTDescrProofsTest.«atom_field/3», reverse1_list, kf, hx]
    · have := (Term.compare_eq_atom _ _).mp ex
      cases ks <;> simp [fk, Term.list] at this

theorem construct_run {m : Nat} (tag : String) (ht : tag = "open" ∨ tag = "closed") (P : Term) :
    Elixir.STTDescrProofsTest.«construct/2» (D m) (.atom tag) P =
      Elixir.Module.Types.Descr.«map_descr/2» (D m) (.atom tag) P := by
  rcases ht with rfl | rfl
  · simp [Elixir.STTDescrProofsTest.«construct/2», Elixir.Module.Types.Descr.«open_map/1»]
  · simp [Elixir.STTDescrProofsTest.«construct/2», Elixir.Module.Types.Descr.«closed_map/1»]

end

end Elixir.STTDescrProofsTest.Nest

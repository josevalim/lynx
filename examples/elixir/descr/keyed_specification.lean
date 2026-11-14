namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! What the specification of the optimized laws checks: keyed literals at every depth. -/

theorem sizeOf_children5 (h lit c u d : Term) :
    sizeOf lit < sizeOf (Term.tuple ⟨[h, lit, c, u, d]⟩) ∧
    sizeOf c < sizeOf (Term.tuple ⟨[h, lit, c, u, d]⟩) ∧ sizeOf u < sizeOf (Term.tuple ⟨[h, lit, c, u, d]⟩) ∧
      sizeOf d < sizeOf (Term.tuple ⟨[h, lit, c, u, d]⟩) := by
  simp only [Term.tuple.sizeOf_spec, Array.mk.sizeOf_spec, List.cons.sizeOf_spec,
    List.nil.sizeOf_spec]
  omega

theorem int_lt_true {a b : Int} (h : Erlang.erlang.«</2» (.integer a) (.integer b) = .ok Term.true) : a < b := by
  refine Classical.byContradiction fun hk => ?_
  have : Ord.compare a b ≠ .lt := fun e => hk (Int.compare_eq_lt.mp e)
  simp [Erlang.erlang.«</2», this, Term.true] at h

theorem int_ge_true {a b : Int} (h : Erlang.erlang.«>=/2» (.integer a) (.integer b) = .ok Term.true) : b ≤ a := by
  refine Classical.byContradiction fun hk => ?_
  have : Ord.compare a b = .lt := Int.compare_eq_lt.mpr (by omega)
  simp [Erlang.erlang.«>=/2», this, Term.true] at h

/-- Element checks of `keyed?/2` at a depth that ensure `P`. -/
def KeyedOk (P : Term → Prop) (depth : Term) : Prop := ∀ e, «keyed?/2» e depth = .ok Term.true → P e

section
variable {P : Term → Prop} {depth : Term}

theorem keyed_elements_spec (hP : KeyedOk P depth) :
    ∀ l : List Term, «keyed_elements?/2» (Term.list l) depth = .ok Term.true → ∀ e ∈ l, P e
  | [], _ => by simp
  | x :: xs, h => by
    rw [«keyed_elements?/2».eq_def] at h
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    intro e me
    rcases List.mem_cons.mp me with rfl | me
    · exact hP _ h.1
    · exact keyed_elements_spec hP xs h.2 e me

end

section
variable {P : Term → Prop} {depth : Term}

theorem keyed_tuple_spec (hP : KeyedOk P depth) :
    ∀ n t, sizeOf t ≤ n → «keyed_tuple_bdd?/2» t depth = .ok Term.true → TQ P t ∧ AllLits (TQ P) t := by
  intro n
  induction n with
  | zero => intro t size; cases t <;> simp at size <;> omega
  | succ n ih =>
    intro t size h
    rw [«keyed_tuple_bdd?/2».eq_def] at h
    split at h
    · rename_i h₀ lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨hl, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨sl, sc, su, sd⟩ := sizeOf_children5 h₀ lit c u d
      have il := ih lit (by omega) hl
      refine ⟨⟨fun k tag l e => by simp at e, fun k tag l e => by simp at e⟩, ?_⟩
      exact ⟨il.1, (ih c (by omega) hc).2, (ih u (by omega) hu).2, (ih d (by omega) hd).2⟩
    · rename_i key elements
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨hk, he⟩ := h
      have tq : TQ P (.tuple ⟨[key, .atom "closed", elements]⟩) := by
        refine ⟨fun k tag l e => ?_, fun k tag l e => ?_⟩
        · obtain ⟨rfl, e₂, rfl⟩ := tuple3_eq e
          simp only [Term.atom.injEq] at e₂
          subst e₂
          exact ⟨fun _ => int_lt_true (by simpa using hk), fun h => by simp at h⟩
        · obtain ⟨rfl, -, rfl⟩ := tuple3_eq e
          exact keyed_elements_spec hP l he
      exact ⟨tq, tq⟩
    · rename_i key tag elements notClosed
      simp only [Term.true, Lynx.Except.andAlso_eq_true, Lynx.Except.orElse_eq_true] at h
      obtain ⟨hk, he⟩ := h
      have tq : TQ P (.tuple ⟨[key, tag, elements]⟩) := by
        refine ⟨fun k tag' l e => ?_, fun k tag' l e => ?_⟩
        · obtain ⟨rfl, rfl, rfl⟩ := tuple3_eq e
          refine ⟨fun c => by subst c; exact absurd rfl notClosed, fun _ ne => ?_⟩
          rcases hk with hk | ⟨-, hk⟩
          · cases l with
            | nil => exact absurd rfl ne
            | cons _ _ => simp [Erlang.erlang.«==/2», Term.list] at hk
          · exact int_ge_true (by simpa using hk)
        · obtain ⟨rfl, -, rfl⟩ := tuple3_eq e
          exact keyed_elements_spec hP l he
      exact ⟨tq, tq⟩
    · rename_i other notNode notClosed notLeaf
      refine ⟨⟨fun k tag l e => absurd e (notLeaf _ _ _), fun k tag l e => absurd e (notLeaf _ _ _)⟩, ?_⟩
      unfold AllLits
      split
      · exact (notNode _ _ _ _ _ rfl).elim
      · exact (notLeaf _ _ _ rfl).elim
      · trivial

end

section
variable {P : Term → Prop} {depth : Term}

theorem keyed_values_spec (hP : KeyedOk P depth) :
    ∀ l : List (Term × Term), «keyed_values?/2» (fieldsTerm l) depth = .ok Term.true →
      ∀ e ∈ l, ∀ u o, e.2 = .tuple #[u, boolAtom o] → P u
  | [], _ => by simp
  | (k, v) :: rest, h => by
    rw [«keyed_values?/2».eq_def] at h
    simp only [fieldsTerm, List.map, Term.list] at h
    by_cases shape : ∃ a b, v = .tuple #[a, b]
    · obtain ⟨a, b, rfl⟩ := shape
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      intro e me u o hv
      rcases List.mem_cons.mp me with rfl | me'
      · simp only [Term.tuple.injEq] at hv
        have := congrArg (fun a : Array Term => a[0]?) hv
        simp at this
        subst this
        exact hP _ h.1
      · exact keyed_values_spec hP rest (by simpa [fieldsTerm, Term.list] using h.2) e me' u o hv
    · exfalso
      split at h
      · rename_i heq
        simp only [Term.cons.injEq, Term.tuple.injEq] at heq
        have := congrArg (fun a : Array Term => a[1]?) heq.1
        simp at this
        exact shape ⟨_, _, this⟩
      · rename_i heq; simp at heq
      · simp at h

theorem domain_kind_spec {k : Term} (h : «domain_kind?/1» k = .ok Term.true) : ∃ s, k = .atom s ∧ s ∈ domainKinds := by
  have mem : ∀ L : List String, isMember k (L.map Term.atom) = .atom "true" → ∃ s, k = .atom s ∧ s ∈ L := by
    intro L
    induction L with
    | nil => simp
    | cons x xs ih =>
      intro hm
      simp only [List.map, isMember_cons] at hm
      split at hm
      · rename_i e
        exact ⟨x, (compare_eq_atom _ _).mp (compare_eq_of_compareExact_eq _ _ e), List.mem_cons_self⟩
      · obtain ⟨s, rfl, ms⟩ := ih hm
        exact ⟨s, rfl, List.mem_cons_of_mem _ ms⟩
  apply mem domainKinds
  unfold «domain_kind?/1» at h
  simp only [domainKinds, List.map]
  refine Classical.byContradiction fun hm => ?_
  simp [Term.true] at h
  split at h
  · exact hm (by assumption)
  · simp at h

theorem domain_kinds_spec : ∀ dl : List (Term × Term), «domain_kinds?/1» (fieldsTerm dl) = .ok Term.true →
    (∀ e ∈ dl, ∃ s, e.1 = .atom s ∧ s ∈ domainKinds) ∧ dl.Pairwise (fun a b => Term.compare (Term.fuel a.1 b.1) a.1 b.1 = .lt)
  | [], _ => ⟨by simp, by simp⟩
  | [(k, v)], h => by
    rw [«domain_kinds?/1».eq_def] at h
    simp only [fieldsTerm, List.map, Term.list] at h
    exact ⟨by simpa using domain_kind_spec h, by simp⟩
  | (k, v) :: (k', v') :: rest, h => by
    rw [«domain_kinds?/1».eq_def] at h
    simp only [fieldsTerm, List.map, Term.list] at h
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨ha, hlt⟩, hr⟩ := h
    obtain ⟨keys, pw⟩ := domain_kinds_spec ((k', v') :: rest) (by simpa [fieldsTerm, Term.list] using hr)
    have lt := lt_true (by simpa [Term.true] using hlt)
    refine ⟨fun e me => ?_, List.pairwise_cons.mpr ⟨fun e me => ?_, pw⟩⟩
    · rcases List.mem_cons.mp me with rfl | me
      · exact domain_kind_spec (by simpa [Term.true] using ha)
      · exact keys e me
    · rcases List.mem_cons.mp me with rfl | me
      · exact lt
      · exact cmp_lt_trans lt ((List.pairwise_cons.mp pw).1 e me)

theorem keyed_domains_spec (hP : KeyedOk P depth) : ∀ n T, sizeOf T ≤ n →
    «keyed_domains?/2» T depth = .ok Term.true → ∃ dl : List (Term × Term), T = fieldsTerm dl ∧ ∀ e ∈ dl, P e.2 := by
  intro n
  induction n with
  | zero => intro T size; cases T <;> simp at size <;> omega
  | succ n ih =>
    intro T size h
    rw [«keyed_domains?/2».eq_def] at h
    split at h
    · rename_i kind type rest
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨dl, rfl, hdl⟩ := ih rest (by simp at size; omega) h.2
      refine ⟨(kind, type) :: dl, rfl, fun e me => ?_⟩
      rcases List.mem_cons.mp me with rfl | me
      · exact hP _ h.1
      · exact hdl e me
    · exact ⟨[], rfl, by simp⟩
    · simp [Term.true] at h

/-- Map leaves other than closed ones, read from the spec. -/
theorem mq_leaf (hP : KeyedOk P depth) {key tag fields : Term} (notClosed : tag ≠ .atom "closed")
    (hk : ∀ (k : Int) (l : List Term), key = .integer k → fields = Term.list l → l ≠ [] → 0 ≤ k)
    (hs : «sorted_keys?/1» fields = .ok Term.true) (hv : «keyed_values?/2» fields depth = .ok Term.true)
    (hd : ∀ dl, tag = fieldsTerm dl → DomsV P dl) : MQ P (.tuple ⟨[key, tag, fields]⟩) := by
  refine ⟨fun k tag' l e => ?_, fun k tag' l e => ?_⟩
  · obtain ⟨rfl, rfl, rfl⟩ := tuple3_eq e
    exact ⟨fun c => by subst c; exact absurd rfl notClosed, fun _ ne => hk k l rfl rfl ne⟩
  · obtain ⟨rfl, rfl, rfl⟩ := tuple3_eq e
    obtain ⟨keys, pw⟩ := sorted_keys_spec l hs
    exact ⟨pw, fun e me => ⟨keys e me, keyed_values_spec hP l hv e me⟩, hd⟩

theorem keyed_map_spec (hP : KeyedOk P depth) :
    ∀ n t, sizeOf t ≤ n → «keyed_map_bdd?/2» t depth = .ok Term.true → MQ P t ∧ AllLits (MQ P) t := by
  intro n
  induction n with
  | zero => intro t size; cases t <;> simp at size <;> omega
  | succ n ih =>
    intro t size h
    rw [«keyed_map_bdd?/2».eq_def] at h
    split at h
    · rename_i h₀ lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨hl, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨sl, sc, su, sd⟩ := sizeOf_children5 h₀ lit c u d
      have il := ih lit (by omega) hl
      refine ⟨⟨fun k tag l e => by simp at e, fun k tag l e => by simp at e⟩, ?_⟩
      exact ⟨il.1, (ih c (by omega) hc).2, (ih u (by omega) hu).2, (ih d (by omega) hd).2⟩
    · rename_i key fields
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨hk, hs⟩, hv⟩ := h
      have mq : MQ P (.tuple ⟨[key, .atom "closed", fields]⟩) := by
        refine ⟨fun k tag l e => ?_, fun k tag l e => ?_⟩
        · obtain ⟨rfl, e₂, rfl⟩ := tuple3_eq e
          simp only [Term.atom.injEq] at e₂
          subst e₂
          exact ⟨fun _ => int_lt_true (by simpa using hk), fun h => by simp at h⟩
        · obtain ⟨rfl, rfl, rfl⟩ := tuple3_eq e
          obtain ⟨keys, pw⟩ := sorted_keys_spec l hs
          exact ⟨pw, fun e me => ⟨keys e me, keyed_values_spec hP l hv e me⟩,
            fun dl e => absurd e.symm (fieldsTerm_ne_atom dl "closed")⟩
      exact ⟨mq, mq⟩
    · rename_i T notNode notClosed
      simp only at h
      split at h
      · rename_i key tag fields
        have nc : tag ≠ .atom "closed" := fun e => notClosed key fields (by rw [e])
        -- the leaf keys the tag clause reads
        have tagClause : ∀ {key fields : Term}, ((Erlang.erlang.«==/2» fields Term.nil = .ok (.atom "true") ∨
            Erlang.erlang.«==/2» fields Term.nil = .ok (.atom "false") ∧
              Erlang.erlang.«>=/2» key (Term.integer 0) = .ok (.atom "true")) ∧
            «sorted_keys?/1» fields = .ok (.atom "true")) ∧ «keyed_values?/2» fields depth = .ok (.atom "true") →
            (∀ dl, tag = fieldsTerm dl → DomsV P dl) → MQ P (.tuple ⟨[key, tag, fields]⟩) := by
          intro key fields h hd
          obtain ⟨⟨hk, hs⟩, hv⟩ := h
          refine mq_leaf hP nc (fun k l ek el ne => ?_) hs hv hd
          subst ek el
          rcases hk with hk | ⟨-, hk⟩
          · cases l with
            | nil => exact absurd rfl ne
            | cons _ _ => simp [Erlang.erlang.«==/2», Term.list] at hk
          · exact int_ge_true (by simpa using hk)
        have mq : MQ P (.tuple ⟨[key, tag, fields]⟩) := by
          cases tag with
          | nil =>
            simp [Erlang.erlang.«is_list/1», Term.true,
              Lynx.Except.andAlso_eq_true] at h
            obtain ⟨⟨⟨⟨hk, -⟩, -⟩, hs⟩, hv⟩ := h
            refine mq_leaf hP nc (fun k l ek _ _ => by subst ek; exact int_ge_true (by simpa using hk)) hs hv
              fun dl e => ?_
            have : dl = [] := fieldsTerm_eq_nil.mp e.symm
            subst this
            exact ⟨by simp, by simp⟩
          | cons a b =>
            simp [Erlang.erlang.«is_list/1», Term.true,
              Lynx.Except.andAlso_eq_true] at h
            obtain ⟨⟨⟨⟨hk, hkinds⟩, hdoms⟩, hs⟩, hv⟩ := h
            obtain ⟨dl, edl, hdl⟩ := keyed_domains_spec hP _ _ (Nat.le_refl _) hdoms
            refine mq_leaf hP nc (fun k l ek _ _ => by subst ek; exact int_ge_true (by simpa using hk)) hs hv
              fun dl' e => ?_
            rw [edl] at e hkinds
            obtain rfl := fieldsTerm_inj e
            obtain ⟨dk, dp⟩ := domain_kinds_spec dl hkinds
            exact ⟨fun e me => ⟨dk e me, hdl e me⟩, dp⟩
          | _ =>
            simp [Erlang.erlang.«is_list/1», Term.false] at h
            exact tagClause h fun dl e => absurd e (by cases dl <;> simp [fieldsTerm, Term.list])
        exact ⟨mq, mq⟩
      · rename_i notLeaf
        refine ⟨⟨fun k tag l e => absurd e (notLeaf _ _ _), fun k tag l e => absurd e (notLeaf _ _ _)⟩, ?_⟩
        unfold AllLits
        split
        · exact (notNode _ _ _ _ _ rfl).elim
        · exact (notLeaf _ _ _ rfl).elim
        · trivial

theorem keyed_list_spec (hP : KeyedOk P depth) :
    ∀ n t, sizeOf t ≤ n → «keyed_list_bdd?/2» t depth = .ok Term.true → LQ P t ∧ AllLits (LQ P) t := by
  intro n
  induction n with
  | zero => intro t size; cases t <;> simp at size <;> omega
  | succ n ih =>
    intro t size h
    rw [«keyed_list_bdd?/2».eq_def] at h
    split at h
    · rename_i h₀ lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨hl, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨sl, sc, su, sd⟩ := sizeOf_children5 h₀ lit c u d
      have il := ih lit (by omega) hl
      refine ⟨fun k a b e => by simp at e, ?_⟩
      exact ⟨il.1, (ih c (by omega) hc).2, (ih u (by omega) hu).2, (ih d (by omega) hd).2⟩
    · rename_i key list last
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      have lq : LQ P (.tuple ⟨[key, list, last]⟩) := fun k a b e => by
        obtain ⟨-, rfl, rfl⟩ := tuple3_eq e
        exact ⟨hP _ h.1, hP _ h.2⟩
      exact ⟨lq, lq⟩
    · rename_i other notNode notLeaf
      refine ⟨fun k a b e => absurd e (notLeaf _ _ _), ?_⟩
      unfold AllLits
      split
      · exact (notNode _ _ _ _ _ rfl).elim
      · exact (notLeaf _ _ _ rfl).elim
      · trivial

end

section
variable {P : Term → Prop} {depth : Term}

theorem keyed_fun_spec (hP : KeyedOk P depth) :
    ∀ n t, sizeOf t ≤ n → «keyed_fun_bdd?/2» t depth = .ok Term.true → FLQ P t ∧ AllLits (FLQ P) t := by
  intro n
  induction n with
  | zero => intro t size; cases t <;> simp at size <;> omega
  | succ n ih =>
    intro t size h
    rw [«keyed_fun_bdd?/2».eq_def] at h
    split at h
    · rename_i h₀ lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨hl, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨sl, sc, su, sd⟩ := sizeOf_children5 h₀ lit c u d
      have il := ih lit (by omega) hl
      refine ⟨fun k a b e => by simp at e, ?_⟩
      exact ⟨il.1, (ih c (by omega) hc).2, (ih u (by omega) hu).2, (ih d (by omega) hd).2⟩
    · rename_i key args ret
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      have fq : FLQ P (.tuple ⟨[key, args, ret]⟩) := fun k as r e => by
        obtain ⟨-, rfl, rfl⟩ := tuple3_eq e
        exact ⟨keyed_elements_spec hP as h.1, hP _ h.2⟩
      exact ⟨fq, fq⟩
    · rename_i other notNode notLeaf
      refine ⟨fun k a b e => absurd e (notLeaf _ _ _), ?_⟩
      unfold AllLits
      split
      · exact (notNode _ _ _ _ _ rfl).elim
      · exact (notLeaf _ _ _ rfl).elim
      · trivial

theorem keyed_arities_spec (hP : KeyedOk P depth) : ∀ es : List (Term × Term),
    «keyed_arities?/2» (Term.list (es.map fun e => .tuple #[e.1, e.2])) depth = .ok Term.true →
      ∀ e ∈ es, (∃ n : Nat, e.1 = .integer n) ∧ AllLits (FLQ P) e.2
  | [], _ => by simp
  | (k, v) :: rest, h => by
    rw [«keyed_arities?/2».eq_def] at h
    simp only [List.map_cons, Term.list, Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨⟨hi, hge⟩, hb⟩, hr⟩ := h
    have nat : ∃ n : Nat, k = .integer n := by
      cases k <;> simp [Erlang.erlang.«is_integer/1», Term.true] at hi
      rename_i z
      simp [Erlang.erlang.«>=/2», Int.isGE_compare, Term.true] at hge
      exact ⟨z.toNat, by simp only [Term.integer.injEq]; omega⟩
    intro e me
    rcases List.mem_cons.mp me with rfl | me
    · exact ⟨nat, (keyed_fun_spec hP _ _ (Nat.le_refl _) hb).2⟩
    · exact keyed_arities_spec hP rest hr e me

/-- What `keyed_fields?/3` checks of a field. -/
def FQ (P : Term → Prop) (el : Bool) (e : Term × Term) : Prop :=
  (e.1 = .atom "fun" → el = Bool.true → FunK P e.2) ∧ (e.1 = .atom "tuple" → AllLits (TQ P) e.2) ∧
    (e.1 = .atom "map" → AllLits (MQ P) e.2) ∧ (e.1 = .atom "list" → AllLits (LQ P) e.2)

/-- One field of `keyed_fields?/3`. -/
theorem keyed_fields_step (hP : KeyedOk P depth) (el : Bool) (k v rest : Term)
    (h : «keyed_fields?/3» (.cons (.tuple #[k, v]) rest) depth (boolAtom el) = .ok Term.true) :
    FQ P el (k, v) ∧ «keyed_fields?/3» rest depth (boolAtom el) = .ok Term.true := by
  rw [«keyed_fields?/3».eq_def] at h
  simp only [boolAtom] at h
  have elT : ∀ {el : Bool}, Term.atom (if el = Bool.true then "true" else "false") = .atom "true" → el = Bool.true := by
    intro el e; cases el <;> simp_all
  split at h
  · rename_i tag R fields heq₁ heq₂
    have e₀ := elT heq₂
    subst e₀
    simp only [Term.cons.injEq, Term.tuple.injEq] at heq₁
    obtain ⟨e₁, rfl⟩ := heq₁
    have hk := congrArg (fun a : Array Term => a[0]?) e₁
    have hv := congrArg (fun a : Array Term => a[1]?) e₁
    simp at hk hv
    subst hk hv
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨⟨htag, har⟩, hr⟩ := h
    simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind] at har
    have each := keyed_arities_spec hP (mapEntries R) har
    refine ⟨⟨fun _ _ => ⟨tag, R, rfl, fun ht => ?_, fun q hq => ?_, fun q v hv => ?_⟩, fun e => by simp at e,
      fun e => by simp at e, fun e => by simp at e⟩, by simpa [boolAtom] using hr⟩
    · subst ht
      rintro rfl
      simp [Erlang.erlang.«==/2», Lynx.Except.orElse, Erlang.erlang.«map_size/1», Erlang.erlang.«>/2»] at htag
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hq
      obtain ⟨e, me, qe, -⟩ := lookup_entry hv
      obtain ⟨n, hn⟩ := (each e me).1
      rw [hn, compareExact_eq_integer] at qe
      exact ⟨n, qe⟩
    · obtain ⟨e, me, -, rfl⟩ := lookup_entry hv
      exact (each e me).2
  · simp at h
  · rename_i heq
    simp only [Term.cons.injEq, Term.tuple.injEq] at heq
    obtain ⟨e₁, rfl⟩ := heq
    have hk := congrArg (fun a : Array Term => a[0]?) e₁
    have hv := congrArg (fun a : Array Term => a[1]?) e₁
    simp at hk hv
    subst hk hv
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    exact ⟨⟨fun e => by simp at e, fun _ => (keyed_tuple_spec hP _ _ (Nat.le_refl _) h.1).2, fun e => by simp at e,
      fun e => by simp at e⟩, by simpa [boolAtom] using h.2⟩
  · rename_i heq
    simp only [Term.cons.injEq, Term.tuple.injEq] at heq
    obtain ⟨e₁, rfl⟩ := heq
    have hk := congrArg (fun a : Array Term => a[0]?) e₁
    have hv := congrArg (fun a : Array Term => a[1]?) e₁
    simp at hk hv
    subst hk hv
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    exact ⟨⟨fun e => by simp at e, fun e => by simp at e, fun _ => (keyed_map_spec hP _ _ (Nat.le_refl _) h.1).2,
      fun e => by simp at e⟩, by simpa [boolAtom] using h.2⟩
  · rename_i heq
    simp only [Term.cons.injEq, Term.tuple.injEq] at heq
    obtain ⟨e₁, rfl⟩ := heq
    have hk := congrArg (fun a : Array Term => a[0]?) e₁
    have hv := congrArg (fun a : Array Term => a[1]?) e₁
    simp at hk hv
    subst hk hv
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    exact ⟨⟨fun e => by simp at e, fun e => by simp at e, fun e => by simp at e,
      fun _ => (keyed_list_spec hP _ _ (Nat.le_refl _) h.1).2⟩, by simpa [boolAtom] using h.2⟩
  · rename_i field fields notT notM notL heq notF₁ notF
    simp only [Term.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    refine ⟨⟨fun e et => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩, by simpa [boolAtom] using h⟩
    · simp only at e; subst e; subst et
      exact (notF v (by simp) rfl).elim
    · simp only at e; subst e; exact (notT v rfl).elim
    · simp only at e; subst e; exact (notM v rfl).elim
    · simp only at e; subst e; exact (notL v rfl).elim
  · rename_i heq; simp at heq
  · simp at h

end

section
variable {P : Term → Prop} {depth : Term}

theorem keyed_fields_spec (hP : KeyedOk P depth) (el : Bool) :
    ∀ es : List (Term × Term), «keyed_fields?/3» (Term.list (es.map fun e => .tuple #[e.1, e.2])) depth (boolAtom el) =
      .ok Term.true → ∀ e ∈ es, FQ P el e
  | [], _ => by simp
  | (k, v) :: rest, h => by
    obtain ⟨fq, hr⟩ := keyed_fields_step hP el k v _ (by simpa [Term.list] using h)
    intro e me
    rcases List.mem_cons.mp me with rfl | me
    · exact fq
    · exact keyed_fields_spec hP el rest hr e me

/-- The fields of a map that `keyed_fields?/3` accepts. -/
theorem keyedF_of (hP : KeyedOk P depth) (el : Bool) (X : List (Term × Term))
    (h : (do
      let l ← Erlang.maps.«to_list/1» (.map X)
      «keyed_fields?/3» l depth (boolAtom el)) = .ok Term.true) : KeyedF P el X := by
  simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind] at h
  have each := keyed_fields_spec hP el (mapEntries X) h
  have entry (q w : Term) (lookup : mapLookup X q = some w) :
      ∃ p ∈ mapEntries X, compareExact (fuel q p.1) q p.1 = .eq ∧ p.2 = w :=
    lookup_found _ q w (by rw [mapLookup_mapEntries]; exact lookup)
  refine ⟨fun et w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨p, mp, qp, rfl⟩ := entry _ w hw
    exact (each p mp).1 ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm qp)) et
  · obtain ⟨p, mp, qp, rfl⟩ := entry _ w hw
    exact (each p mp).2.1 ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm qp))
  · obtain ⟨p, mp, qp, rfl⟩ := entry _ w hw
    exact (each p mp).2.2.1 ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm qp))
  · obtain ⟨p, mp, qp, rfl⟩ := entry _ w hw
    exact (each p mp).2.2.2 ((compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm qp))

end

/-- What `keyed?/2` checks at each depth. -/
theorem keyed_spec : ∀ d : Nat, KeyedOk (Keyed d) (.integer d)
  | 0, _, _ => trivial
  | d + 1, e, h => by
    rw [«keyed?/2».eq_def] at h
    split at h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
    · rename_i _ _ heq; simp at heq; omega
    · rename_i e₀ _ _ _ _ _
      cases e₀ with
      | map X =>
        have sub : Erlang.erlang.«-/2» (.integer ((d + 1 : Nat) : Int)) (.integer 1) = .ok (.integer (d : Int)) := by
          rw [Erlang.erlang.«-/2_integers»]; congr 2; omega
        refine Or.inr (Or.inr ⟨X, rfl, keyedF_of (keyed_spec d) Bool.true X ?_⟩)
        simpa [sub, boolAtom] using h
      | _ => simp [Erlang.maps.«to_list/1»] at h

/-- The depths of the laws are natural numbers. -/
theorem depth_nat {depth : Term} (h : «depth?/1» depth = .ok Term.true) : ∃ n : Nat, depth = .integer n := by
  cases depth <;> simp [«depth?/1», Erlang.erlang.«is_integer/1», Lynx.Except.andAlso, Term.true, Erlang.erlang.«>=/2»,
    Int.isGE_compare] at h
  rename_i z
  exact ⟨z.toNat, by simp only [Term.integer.injEq]; omega⟩

theorem negatable_cases (t : Term) (n : Nat) (descr : Term)
    (h : «negatable?/2» descr (.tuple #[.integer n, t]) = .ok Term.true) :
    descr = .atom "term" ∨ ∃ X, descr = .map X ∧ Negatable (Nest t n) X :=
  negatable_map t n descr h

/-- The types of `opt_negatable?/2` are top-level types over the element types of their depth. -/
theorem opt_negatable_tc (t : Term) (n : Nat) (descr : Term)
    (h : «opt_negatable?/2» descr (.tuple #[.integer n, t]) = .ok Term.true) : TCF (level t n) descr := by
  unfold «opt_negatable?/2» at h
  split at h
  · exact Or.inl rfl
  · rename_i d nn notTerm heq
    obtain ⟨rfl, rfl⟩ : d = .integer n ∧ nn = t := by simp at heq; exact ⟨heq.1.symm, heq.2.symm⟩
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨hn, hk⟩ := h
    rcases negatable_cases _ n _ hn with rfl | ⟨X, rfl, v⟩
    · exact (notTerm rfl).elim
    · exact negatable_tc _ n v (keyedF_of (keyed_spec n) Bool.false X (by simpa [boolAtom] using hk))
  · simp at h

end Elixir.STTDescrProofsTest.Nest

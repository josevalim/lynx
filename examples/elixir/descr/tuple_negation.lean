open BddProofs

/-! Call depth: computations whose result does not depend on it, once it is deep enough. -/

abbrev D (n : Nat) : Dispatcher := Dispatcher.ofTable Erlang.program.fun_table n

def boolAtom (o : Bool) : Term := .atom (if o then "true" else "false")

theorem mapM_ok {α β : Type} (f : α → Except Exception β) (h : α → β) :
    ∀ xs : List α, (∀ x ∈ xs, f x = .ok (h x)) → xs.mapM f = .ok (xs.map h)
  | [], _ => rfl
  | x :: xs, all => by
    simp [List.mapM_cons, all x (by simp), mapM_ok f h xs (fun y my => all y (by simp [my]))]

/-- The entries `maps:intersect_with/3` returns with a combiner returning `g`. -/
def interList (g : Term → Term → Term → Term) (l r : List (Term × Term)) : List (Term × Term) :=
  ((mapEntries l).map fun e => ((mapLookup r e.1).map (g e.1 e.2)).map fun v => (e.1, v)).reduceOption

theorem intersect_with_eq (d : Dispatcher) (module name : String) (captures : Array Term)
    (l r : List (Term × Term)) (g : Term → Term → Term → Term)
    (calls : ∀ entry ∈ mapEntries l, ∀ value, mapLookup r entry.1 = some value →
      d.pure (.function module name 3 captures) #[entry.1, entry.2, value] = .ok (g entry.1 entry.2 value)) :
    (Erlang.maps.«intersect_with/3» d (.function module name 3 captures) (.map l) (.map r) :
      Except Exception Term) = .ok (.map (interList g l r)) := by
  simp only [Erlang.maps.«intersect_with/3», Dispatch.dispatch]
  rw [mapM_ok _ (fun e => ((mapLookup r e.1).map (g e.1 e.2)).map fun v => (e.1, v)) _ ?all]
  · rfl
  · intro e me
    cases hr : mapLookup r e.1 with
    | none => simp
    | some v => simp only [calls e me v hr]; rfl

/-- The entries `maps:merge_with/3` returns with a combiner returning `g`. -/
def mergeList (g : Term → Term → Term → Term) (l r : List (Term × Term)) : List (Term × Term) :=
  ((mapEntries r).map fun e => (e.1, match mapLookup l e.1 with | some v => g e.1 v e.2 | none => e.2)) ++ l

theorem merge_with_eq (d : Dispatcher) (module name : String) (captures : Array Term)
    (l r : List (Term × Term)) (g : Term → Term → Term → Term)
    (calls : ∀ entry ∈ mapEntries r, ∀ value, mapLookup l entry.1 = some value →
      d.pure (.function module name 3 captures) #[entry.1, value, entry.2] = .ok (g entry.1 value entry.2)) :
    (Erlang.maps.«merge_with/3» d (.function module name 3 captures) (.map l) (.map r) :
      Except Exception Term) = .ok (.map (mergeList g l r)) := by
  simp only [Erlang.maps.«merge_with/3», Dispatch.dispatch]
  rw [mapM_ok _ (fun e => (e.1, match mapLookup l e.1 with | some v => g e.1 v e.2 | none => e.2)) _ ?all]
  · rfl
  · intro e me
    cases hl : mapLookup l e.1 with
    | none => simp
    | some v => simp only [calls e me v hl]; rfl

/-- The entries `maps:filter/2` keeps with a predicate deciding by `keep`. -/
def filterList (keep : Term × Term → Bool) (es : List (Term × Term)) : List (Term × Term) :=
  ((mapEntries es).map fun e => (if keep e then some e.2 else none).map fun v => (e.1, v)).reduceOption

theorem filter_eq (d : Dispatcher) (module name : String) (captures : Array Term)
    (es : List (Term × Term)) (keep : Term × Term → Bool)
    (calls : ∀ entry ∈ mapEntries es, d.pure (.function module name 2 captures) #[entry.1, entry.2] =
      .ok (if keep entry then Term.true else Term.false)) :
    (Erlang.maps.«filter/2» d (.function module name 2 captures) (.map es) : Except Exception Term) =
      .ok (.map (filterList keep es)) := by
  simp only [Erlang.maps.«filter/2», Dispatch.dispatch]
  rw [mapM_ok _ (fun e => (if keep e then some e.2 else none).map fun v => (e.1, v)) _ ?all]
  · rfl
  · intro e me
    cases hk : keep e <;> simp [calls e me, hk, Term.true, Term.false]

/-- Element types `E` hold the top type, intersect into element types, and have their emptiness decided,
with the same results at every call depth from `K`. -/
structure ElemOk (E : Term → Prop) (K : Nat) : Prop where
  term : E (.atom "term")
  inter : ∀ {a b}, E a → E b → ∃ c, E c ∧ ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c
  empty : ∀ {a}, E a → ∀ S : List (Term × Term), ∃ b : Bool, ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)
  none : E (.map [])
  pos : 1 ≤ K

/-- Element types that also subtract into element types. -/
structure ElemDiff (E : Term → Prop) (K : Nat) : Prop where
  diff : ∀ {a b}, E a → E b → ∃ c, E c ∧ ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c

theorem ElemOk.mono {E : Term → Prop} {K K' : Nat} (ops : ElemOk E K) (le : K ≤ K') : ElemOk E K' := by
  refine ⟨ops.term, fun ha hb => ?_, fun ha S => ?_, ops.none, by have := ops.pos; omega⟩
  · obtain ⟨c, hc, run⟩ := ops.inter ha hb
    exact ⟨c, hc, fun m hm => run m (by omega)⟩
  · obtain ⟨b, run⟩ := ops.empty ha S
    exact ⟨b, fun m hm => run m (by omega)⟩

theorem ElemDiff.mono {E : Term → Prop} {K K' : Nat} (dops : ElemDiff E K) (le : K ≤ K') : ElemDiff E K' := by
  refine ⟨fun ha hb => ?_⟩
  obtain ⟨c, hc, run⟩ := dops.diff ha hb
  exact ⟨c, hc, fun m hm => run m (by omega)⟩

theorem succ_of_le {K m : Nat} (h : K + 1 ≤ m) : ∃ m', m = m' + 1 ∧ K ≤ m' := ⟨m - 1, by omega, by omega⟩

/-- Flat element types: valid types of bitmaps and atoms. -/
abbrev Elem (X : List (Term × Term)) : Prop := Valid X

def ElemTerm (e : Term) : Prop := e = .atom "term" ∨ ∃ X, e = .map X ∧ Elem X

theorem Elem.static {X : List (Term × Term)} (valid : Elem X) : mapLookup X (.atom "dynamic") = Option.none := by
  cases h : mapLookup X (.atom "dynamic") with
  | none => rfl
  | some w =>
    rcases valid.keys _ (by rw [h]; rfl) with bad | bad <;> simp only [Term.atom.injEq] at bad <;>
      exact absurd bad (by decide)

/-- The shape of a field of an element type. -/
def ElemField (q w : Term) : Prop :=
  (q = .atom "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
    (q = .atom "atom" ∧ AtomField w ∧ ∀ S, w = .tuple #[.atom "union", .map S] → S ≠ [])

theorem Elem.field {X : List (Term × Term)} (valid : Elem X) {q w : Term} (h : mapLookup X q = some w) :
    ElemField q w := by
  rcases valid.keys q (by simp [h]) with rfl | rfl
  · exact Or.inl ⟨rfl, valid.bitmap w h⟩
  · exact Or.inr ⟨rfl, valid.atom w h, fun S e => valid.atomUnion S (e ▸ h)⟩

/-- Intersections of static types whose common fields intersect the same way at every call depth. -/
theorem inter_uniform (K : Nat) (L R : List (Term × Term)) (sL : mapLookup L (.atom "dynamic") = Option.none)
    (sR : mapLookup R (.atom "dynamic") = Option.none) (g : Term → Term → Term → Term)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y → ∀ m, K ≤ m →
      Elixir.Module.Types.Descr.«bare_intersection/3» (D m) q x y = .ok (g q x y)) :
    ∃ I out, (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) (.map L) (.map R) =
        .ok (.map out)) ∧
      (∀ q, mapLookup I q = match (mapEntries L).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
        | some e => (mapLookup R e.1).map (g e.1 e.2)
        | none => none) ∧
      ∀ q, mapLookup out q = match (mapEntries I).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
        | some e => if kept e then some e.2 else none
        | none => none := by
  have callsI : ∀ n, K ≤ n → ∀ e ∈ mapEntries L, ∀ y, mapLookup R e.1 = some y →
      (D (n + 1)).pure (.function "Elixir.Module.Types.Descr" "bare_intersection" 3 #[]) #[e.1, e.2, y] =
        .ok (g e.1 e.2 y) := fun n hn e member y hy => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure]
    exact calls e.1 e.2 y (mapLookup_of_mem_mapEntries member) hy n hn
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup (D (K + 1)) "Elixir.Module.Types.Descr"
    "bare_intersection" #[] L R g (callsI K (Nat.le_refl _))
  have eqI : I = interList g L R := by
    have := runI.symm.trans (intersect_with_eq _ _ _ _ L R g (callsI K (Nat.le_refl _)))
    simpa using this
  subst eqI
  have callsO : ∀ n, ∀ e ∈ mapEntries (interList g L R),
      (D (n + 1)).pure (.function "Elixir.Module.Types.Descr" "-symmetrical_intersection/3-fun-0-" 2 #[])
        #[e.1, e.2] = .ok (if kept e then Term.true else Term.false) := fun n e _ => by
    rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field]
  obtain ⟨out, runO, lookO⟩ := Erlang.maps.filter_lookup (D (K + 1)) "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] (interList g L R) kept (callsO K)
  have eqO : out = filterList kept (interList g L R) := by
    have := runO.symm.trans (filter_eq _ _ _ _ _ kept (callsO K))
    simpa using this
  subst eqO
  refine ⟨interList g L R, filterList kept (interList g L R), fun m hm => ?_, lookI, lookO⟩
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»
  simp [getMapKeys_single, sL, sR]
  unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
  simp [intersect_with_eq _ _ _ _ L R g (callsI n hn), filter_eq _ _ _ _ _ kept (callsO n)]

/-- Lists of element types. -/
def AllElem (E : Term → Prop) (xs : Term) : Prop := ∃ l : List Term, xs = Term.list l ∧ ∀ e ∈ l, E e

theorem reverse_elems (l : List Term) (hl : ∀ e ∈ l, E e) :
    ∀ tail, AllElem E tail → ∃ r, Erlang.lists.«reverse/2» (Term.list l) tail = .ok r ∧ AllElem E r := by
  induction l with
  | nil => intro tail ht; exact ⟨tail, by simp [Erlang.lists.«reverse/2»], ht⟩
  | cons h t ih =>
    rintro tail ⟨lt, rfl, hlt⟩
    obtain ⟨r, run, hr⟩ := ih (fun e me => hl e (List.mem_cons_of_mem _ me)) (Term.list (h :: lt))
      ⟨h :: lt, rfl, fun e me => by
        rcases List.mem_cons.mp me with rfl | me
        · exact hl e List.mem_cons_self
        · exact hlt e me⟩
    exact ⟨r, by simpa [Term.list, Erlang.lists.«reverse/2»] using run, hr⟩

theorem zip_elems (ops : ElemOk E K) (l₁ : List Term) (h₁ : ∀ e ∈ l₁, E e) :
    ∀ (l₂ : List Term), (∀ e ∈ l₂, E e) → ∀ acc, AllElem E acc →
    ∃ r, AllElem E r ∧ ∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«zip_intersection/4» (D m)
      (Term.list l₁) (Term.list l₂) acc (.function "Elixir.Module.Types.Descr" "bare_intersection" 2 #[]) =
        .ok r := by
  induction l₁ with
  | nil =>
    rintro l₂ h₂ acc ⟨la, rfl, hla⟩
    obtain ⟨r, run, hr⟩ := reverse_elems la hla (Term.list l₂) ⟨l₂, rfl, h₂⟩
    exact ⟨r, hr, fun _ _ => by unfold Elixir.Module.Types.Descr.«zip_intersection/4»; exact run⟩
  | cons x xs ih =>
    rintro l₂ h₂ acc ⟨la, rfl, hla⟩
    cases l₂ with
    | nil =>
      obtain ⟨r, run, hr⟩ := reverse_elems la hla (Term.list (x :: xs)) ⟨_, rfl, h₁⟩
      exact ⟨r, hr, fun _ _ => by unfold Elixir.Module.Types.Descr.«zip_intersection/4»; exact run⟩
    | cons y ys =>
      obtain ⟨e, he, run⟩ := ops.inter (h₁ x List.mem_cons_self) (h₂ y List.mem_cons_self)
      obtain ⟨r, hr, runr⟩ := ih (fun e me => h₁ e (List.mem_cons_of_mem _ me)) ys
        (fun e me => h₂ e (List.mem_cons_of_mem _ me)) (Term.list (e :: la))
        ⟨e :: la, rfl, fun e' me => by
          rcases List.mem_cons.mp me with rfl | me
          · exact he
          · exact hla e' me⟩
      refine ⟨r, hr, fun m hm => ?_⟩
      obtain ⟨n, rfl, hn⟩ := succ_of_le hm
      unfold Elixir.Module.Types.Descr.«zip_intersection/4»
      simp only [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/2».pure, run n hn,
        Lynx.Except.ok_bind]
      exact runr _ hm

theorem length_list (l : List Term) : Erlang.erlang.«length/1» (Term.list l) = .ok (.integer l.length) := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [Erlang.erlang.«length/1»] at ih ⊢; simp [ih]

/-- Lines of tuples: a tag and element types. -/
def TuplePos (E : Term → Prop) (p : Term) : Prop :=
  ∃ (tag : String) (l : List Term), p = .tuple #[.atom tag, Term.list l] ∧ (tag = "open" ∨ tag = "closed") ∧
    ∀ e ∈ l, E e

/-- Tuple literals: a key, a tag, and element types. -/
def TupleLit (E : Term → Prop) (t : Term) : Prop :=
  ∃ (k : Int) (tag : String) (l : List Term), t = .tuple #[.integer k, .atom tag, Term.list l] ∧
    (tag = "open" ∨ tag = "closed") ∧ ∀ e ∈ l, E e

theorem sizes_ok (t₁ t₂ : String) (h₁ : t₁ = "open" ∨ t₁ = "closed") (h₂ : t₂ = "open" ∨ t₂ = "closed")
    (n₁ n₂ : Int) : ∃ v, Elixir.Module.Types.Descr.«tuple_sizes_strategy/4» (.atom t₁) (.integer n₁) (.atom t₂)
      (.integer n₂) = .ok v := by
  unfold Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;>
    simp [Erlang.erlang.«/=/2», Erlang.erlang.«==/2»]
  all_goals (repeat (first | exact ⟨_, rfl⟩ | split))

theorem line_ok (ops : ElemOk E K) {p t : Term} (hp : TuplePos E p) (ht : TupleLit E t) :
    (∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) p t = .ok (.atom "empty")) ∨
      ∃ p', TuplePos E p' ∧
        ∀ m, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) p t = .ok p' := by
  obtain ⟨t₁, l₁, rfl, g₁, e₁⟩ := hp
  obtain ⟨k, t₂, l₂, rfl, g₂, e₂⟩ := ht
  obtain ⟨v, strategy⟩ := sizes_ok t₁ t₂ g₁ g₂ l₁.length l₂.length
  obtain ⟨r, ⟨lr, rfl, hr⟩, zip⟩ := zip_elems ops l₁ e₁ l₂ e₂ .nil ⟨[], rfl, by simp⟩
  by_cases dis : v = .atom "disjoint"
  · subst dis
    left
    intro m _
    unfold Elixir.Module.Types.Descr.«tuple_line_intersection/2»
    simp only [length_list, Lynx.Except.ok_bind, strategy]
    rfl
  · right
    have run : ∀ tag, tag = (if t₁ = "open" ∧ t₂ = "open" then "open" else "closed") → ∀ m, K + 1 ≤ m →
        Elixir.Module.Types.Descr.«tuple_line_intersection/2» (D m) (.tuple #[.atom t₁, Term.list l₁])
          (.tuple #[.integer k, .atom t₂, Term.list l₂]) = .ok (.tuple #[.atom tag, Term.list lr]) := by
      intro tag htag m hm
      unfold Elixir.Module.Types.Descr.«tuple_line_intersection/2»
      simp only [length_list, Lynx.Except.ok_bind, strategy]
      subst htag
      rcases g₁ with rfl | rfl <;> rcases g₂ with rfl | rfl <;>
        simp [Erlang.erlang.«==/2», Lynx.Except.andAlso, zip m hm]
    exact ⟨_, ⟨_, lr, rfl, by split <;> simp, hr⟩, run _ rfl⟩

/-- The branches of an unsatisfiable node are unsatisfiable. -/
theorem unsat_children {ok : Term → Prop} {h : Int} {lit c u d : Term}
    (hc : Bdd (Above ok lit) c) (hu : Bdd (Above ok lit) u) (hd : Bdd (Above ok lit) d)
    (unsat : Unsat (.tuple #[.integer h, lit, c, u, d])) : Unsat c ∧ Unsat u ∧ Unsat d := by
  have above : ∀ v ρ t, Above ok lit t → flip ρ lit v t = ρ t := fun v ρ t ht => by
    have : Term.compare (Term.fuel t lit) t lit ≠ .eq := fun e => by
      have := ht.2; rw [Lynx.Term.compare_eq_symm e] at this; cases this
    simp [BddProofs.flip, this]
  have parts : ∀ ρ, Resp ρ → eval ρ c = Bool.false ∧ eval ρ u = Bool.false ∧ eval ρ d = Bool.false := by
    intro ρ resp
    have t := unsat _ (resp.flip lit Bool.true)
    have f := unsat _ (resp.flip lit Bool.false)
    simp only [eval_node, eval_ext hc (above Bool.true ρ), eval_ext hu (above Bool.true ρ),
      eval_ext hd (above Bool.true ρ)] at t
    simp only [eval_node, eval_ext hc (above Bool.false ρ), eval_ext hu (above Bool.false ρ),
      eval_ext hd (above Bool.false ρ)] at f
    simp [BddProofs.flip] at t f
    exact ⟨t.1, t.2, f.2⟩
  exact ⟨fun ρ r => (parts ρ r).1, fun ρ r => (parts ρ r).2.1, fun ρ r => (parts ρ r).2.2⟩

/-- Unsatisfiable tuple BDDs have no line, whatever the elements of their literals. -/
theorem tuple_bdd_empty_unsat (ops : ElemOk E K) {m : Nat} (hm : K + 1 ≤ m) {ok : Term → Prop} {r : Term}
    (wr : Bdd ok r) (lits : ∀ t, ok t → TupleLit E t) (unsat : Unsat r) :
    ∀ pos negs seen, TuplePos E pos →
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos negs r seen = .ok (.atom "true") := by
  revert lits unsat
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleLit E t) → Unsat r → ∀ pos negs seen, TuplePos E pos →
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) pos negs r seen = .ok (.atom "true"))
    ?_ ?_ ?_ ?_ ok r wr
  · intro _ _ unsat; have := unsat _ (resp_const Bool.true); simp at this
  · intro _ _ _ pos negs seen _
    unfold Elixir.Module.Types.Descr.«tuple_bdd_empty?/4»
    rfl
  · intro _ k x y _ _ unsat; have := unsat _ (resp_const Bool.true); simp at this
  · intro ok h lit c u d _ okl hc hu hd ic iu id lits unsat pos negs seen hp
    obtain ⟨uc, uu, ud⟩ := unsat_children hc hu hd unsat
    have lits' : ∀ t, Above ok lit t → TupleLit E t := fun t ht => lits t ht.1
    have dTrue := id lits' ud pos (.cons lit negs) seen hp
    have uTrue := iu lits' uu pos negs seen hp
    unfold Elixir.Module.Types.Descr.«tuple_bdd_empty?/4»
    simp only [dTrue, uTrue, Lynx.Except.andAlso]
    rcases line_ok ops hp (lits lit okl) with line | ⟨p', hp', line⟩
    · simp [line m hm]
    · have cTrue := ic lits' uc p' negs seen hp'
      obtain ⟨tg, l, rfl, -, -⟩ := hp'
      simp [line m hm, cTrue]

/-! Reading the tuple specification. -/

theorem any_bdd_spec : ∀ (n : Nat) (b lower : Term), sizeOf b ≤ n → «any_bdd?/2» b lower = .ok Term.true →
    Bdd (fun t => Term.compare (Term.fuel lower t) lower t = .lt) b := by
  intro n
  induction n with
  | zero => intro b _ size; cases b <;> simp at size <;> omega
  | succ n ih =>
    intro b lower size h
    unfold «any_bdd?/2» at h
    split at h
    · exact Bdd.top
    · exact Bdd.bot
    · rename_i key _ _
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      cases key <;> simp [Erlang.erlang.«is_integer/1»] at h
      exact Bdd.leaf_iff.mpr (Lynx.Term.compare_lt_of_gt (by simpa [Erlang.erlang.«>/2»] using h))
    · rename_i hash key x y c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨⟨⟨ih₁, ik⟩, gt⟩, hc⟩, hu⟩, hd⟩ := h
      cases hash <;> simp [Erlang.erlang.«is_integer/1»] at ih₁
      cases key <;> simp [Erlang.erlang.«is_integer/1»] at ik
      rename_i h' k
      have lt : Term.compare (Term.fuel lower (.tuple #[.integer k, x, y])) lower (.tuple #[.integer k, x, y]) = .lt :=
        Lynx.Term.compare_lt_of_gt (by simpa [Erlang.erlang.«>/2»] using gt)
      obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
      have lift : ∀ t, Term.compare (Term.fuel (.tuple #[.integer k, x, y]) t) (.tuple #[.integer k, x, y]) t = .lt →
          Above (fun t => Term.compare (Term.fuel lower t) lower t = .lt) (.tuple #[.integer k, x, y]) t :=
        fun t ht => ⟨Lynx.Term.compare_lt_trans lt ht, ht⟩
      exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, lt,
        (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
        (ih d _ (by simp at size; omega) hd).mono lift⟩
    · simp [Term.true] at h

/-- Element types that `nested?/2` accepts at a depth. -/
abbrev NestedOk (E : Term → Prop) (depth : Term) : Prop := ∀ e, «nested?/2» e depth = .ok Term.true → E e

theorem elements_spec (hE : NestedOk E depth) : ∀ {xs : Term}, «elements?/2» xs depth = .ok Term.true → AllElem E xs
  | .nil, _ => ⟨[], rfl, by simp⟩
  | .cons x xs, h => by
    unfold «elements?/2» at h
    simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
    obtain ⟨l, rfl, hl⟩ := elements_spec hE h.2
    exact ⟨x :: l, rfl, fun e me => by
      rcases List.mem_cons.mp me with rfl | me
      · exact hE _ h.1
      · exact hl e me⟩
  | .atom _, h | .integer _, h | .float _, h | .reference _, h | .function _ _ _ _, h | .pid _, h
  | .tuple _, h | .map _, h | .bitstring _ _ _, h => by unfold «elements?/2» at h; simp [Term.true] at h

/-- The top tuple literal `{_, open, []}`, which tuple operations treat as the top type. -/
def IsTop (t : Term) : Prop := ∃ k : Term, t = .tuple #[k, .atom "open", .nil]

def TupleOk (E : Term → Prop) (t : Term) : Prop := TupleLit E t ∧ ¬IsTop t

theorem tuple_literal_spec (hE : NestedOk E depth) {lit lower : Term}
    (h : «tuple_literal?/3» lit lower depth = .ok Term.true) :
    IsLeaf lit ∧ Term.compare (Term.fuel lower lit) lower lit = .lt ∧ TupleOk E lit := by
  unfold «tuple_literal?/3» at h
  simp only at h
  split at h
  · rename_i key tag elements
    simp only [Lynx.Except.guard, Lynx.Except.tryWith] at h
    split at h
    · next member =>
      have tags : tag = .atom "open" ∨ tag = .atom "closed" := by
        by_cases o : tag = .atom "open"
        · exact Or.inl o
        · by_cases c : tag = .atom "closed"
          · exact Or.inr c
          · simp [isMember, o, c] at member
      cases key <;> simp [Erlang.erlang.«is_integer/1», Lynx.Except.andAlso, Term.true] at h
      rename_i k
      by_cases gt : (Term.compare (Term.fuel (.tuple #[.integer k, tag, elements]) lower) (.tuple #[.integer k, tag, elements]) lower).isGT = Bool.true
      · have lt : Term.compare (Term.fuel lower (.tuple #[.integer k, tag, elements])) lower (.tuple #[.integer k, tag, elements]) = .lt :=
          Lynx.Term.compare_lt_of_gt (by simpa [Ordering.isGT_iff_eq_gt] using gt)
        rcases tags with rfl | rfl
        · by_cases en : elements = .nil
          · subst en
            simp [Erlang.erlang.«>/2», gt, Erlang.erlang.«==/2», Erlang.erlang.«/=/2»] at h
          · simp [Erlang.erlang.«>/2», gt, Erlang.erlang.«==/2», Erlang.erlang.«/=/2», en] at h
            obtain ⟨l, rfl, hl⟩ := elements_spec hE h
            refine ⟨⟨k, _, _, rfl⟩, lt, ⟨k, "open", l, rfl, Or.inl rfl, hl⟩, ?_⟩
            rintro ⟨_, e⟩
            simp at e
            exact en e.2
        · simp [Erlang.erlang.«>/2», gt, Erlang.erlang.«==/2»] at h
          obtain ⟨l, rfl, hl⟩ := elements_spec hE h
          refine ⟨⟨k, _, _, rfl⟩, lt, ⟨k, "closed", l, rfl, Or.inr rfl, hl⟩, ?_⟩
          rintro ⟨_, e⟩
          simp at e
      · simp [Erlang.erlang.«>/2», gt] at h
    · simp [Term.true] at h
  · simp [Term.true] at h

theorem ordered_tuple_spec (hE : NestedOk E depth) : ∀ (n : Nat) (b lower : Term), sizeOf b ≤ n →
    «ordered_tuple_bdd?/3» b lower depth = .ok Term.true → Bdd (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ TupleOk E t) b := by
  intro n
  induction n with
  | zero => intro b _ size; cases b <;> simp at size <;> omega
  | succ n ih =>
    intro b lower size h
    unfold «ordered_tuple_bdd?/3» at h
    split at h
    · exact Bdd.top
    · exact Bdd.bot
    · obtain ⟨⟨k, x, y, e⟩, lt, okl⟩ := tuple_literal_spec hE h
      simp at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      exact Bdd.leaf_iff.mpr ⟨lt, okl⟩
    · rename_i hash lit c u d
      simp only [Term.true, Lynx.Except.andAlso_eq_true] at h
      obtain ⟨⟨⟨⟨int, hl⟩, hc⟩, hu⟩, hd⟩ := h
      obtain ⟨⟨k, x, y, rfl⟩, lt, okl⟩ := tuple_literal_spec hE hl
      cases hash <;> simp [Erlang.erlang.«is_integer/1», Term.true] at int
      rename_i h'
      obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h') (.tuple #[.integer k, x, y]) c u d
      have lift : ∀ t, (Term.compare (Term.fuel (.tuple #[.integer k, x, y]) t) (.tuple #[.integer k, x, y]) t = .lt ∧ TupleOk E t) →
          Above (fun t => Term.compare (Term.fuel lower t) lower t = .lt ∧ TupleOk E t) (.tuple #[.integer k, x, y]) t :=
        fun t ht => ⟨⟨Lynx.Term.compare_lt_trans lt ht.1, ht.2⟩, ht.1⟩
      exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, ⟨lt, okl⟩,
        (ih c _ (by simp at size; omega) hc).mono lift, (ih u _ (by simp at size; omega) hu).mono lift,
        (ih d _ (by simp at size; omega) hd).mono lift⟩
    · simp [Term.true] at h

/-- Tuple types are the top tuple literal or ordered BDDs of other tuple literals. -/
abbrev TupleField (E : Term → Prop) (w : Term) : Prop :=
  (∃ k : Int, w = .tuple #[.integer k, .atom "open", .nil]) ∨ Bdd (TupleOk E) w

theorem tuple_bdd_spec (hE : NestedOk E depth) {w : Term} (h : «tuple_bdd?/2» w depth = .ok Term.true) :
    TupleField E w := by
  unfold «tuple_bdd?/2» at h
  split at h
  · rename_i key
    cases key <;> simp [Erlang.erlang.«is_integer/1», Term.true] at h
    exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ((ordered_tuple_spec hE _ w _ (Nat.le_refl _) h).mono fun _ h => h.2)

/-! Differences of two leaves. -/

@[simp] theorem atom_compareExact_eq (name : String) (t : Term) :
    compareExact (fuel (.atom name) t) (.atom name) t = .eq ↔ t = .atom name :=
  ⟨fun e => (compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm e),
    fun e => by subst e; exact compareExact_self _⟩

theorem diff_leaf_bot (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_difference/2» (.tuple #[k, x, y]) (.atom "bdd_bot") = .ok (.tuple #[k, x, y]) := by
  unfold Elixir.Module.Types.Descr.«bdd_difference/2»
  simp [Erlang.erlang.«=:=/2»]

theorem diff_leaf_top (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_difference/2» (.tuple #[k, x, y]) (.atom "bdd_top") = .ok (.atom "bdd_bot") := by
  unfold Elixir.Module.Types.Descr.«bdd_difference/2»
  simp [Erlang.erlang.«=:=/2»]

/-! The empty tuple and its negation. -/

def EmptyTuple (K : Nat) (r : Term) : Prop :=
  ∀ m S, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) r (.map S) = .ok (.atom "true")

theorem tuple_empty_of {K : Nat} {r : Term} (run : ∀ m S, K + 1 ≤ m → Elixir.Module.Types.Descr.«tuple_bdd_empty?/4»
    (D m) (.tuple #[.atom "open", .nil]) .nil r (.map S) = .ok (.atom "true")) : EmptyTuple K r := by
  intro n S hn
  have run' := fun S' => run n S' hn
  unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
  by_cases seen : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "tuple") r) e.1) (.cons (.atom "tuple") r) e.1 == .eq) = Bool.true
  · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true]
  · simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen,
      Term.false, Erlang.maps.«put/3», run']

theorem tuple_empty_unsat (ops : ElemOk E K) {ok : Term → Prop} {r : Term} (wr : Bdd ok r)
    (lits : ∀ t, ok t → TupleLit E t) (unsat : Unsat r) : EmptyTuple K r :=
  tuple_empty_of fun m S hm => tuple_bdd_empty_unsat ops hm wr lits unsat _ _ _ ⟨"open", [], rfl, Or.inl rfl, by simp⟩

theorem inter_top_leaf (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_intersection/2» (.atom "bdd_top") (.tuple #[k, x, y]) = .ok (.tuple #[k, x, y]) := by
  unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
  simp [Erlang.erlang.«=:=/2»]

theorem inter_bot_leaf (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_intersection/2» (.atom "bdd_bot") (.tuple #[k, x, y]) = .ok (.atom "bdd_bot") := by
  unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
  simp [Erlang.erlang.«=:=/2»]

theorem inter_leaf_top (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_intersection/2» (.tuple #[k, x, y]) (.atom "bdd_top") = .ok (.tuple #[k, x, y]) := by
  unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
  simp [Erlang.erlang.«=:=/2»]

theorem inter_leaf_bot (k x y : Term) :
    Elixir.Module.Types.Descr.«bdd_intersection/2» (.tuple #[k, x, y]) (.atom "bdd_bot") = .ok (.atom "bdd_bot") := by
  unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
  simp [Erlang.erlang.«=:=/2»]

/-- Two distinct leaves intersect into a node of the smaller one. -/
theorem leaf_intersection {a b : Term} (la : IsLeaf a) (lb : IsLeaf b) (same : ¬compareExact (fuel b a) b a = .eq)
    (order : Term.compare (Term.fuel a b) a b ≠ .eq) :
    ∃ h : Int, Elixir.Module.Types.Descr.«bdd_intersection/2» a b = .ok (.tuple #[.integer h, a, b, .atom "bdd_bot", .atom "bdd_bot"]) ∨
      Elixir.Module.Types.Descr.«bdd_intersection/2» a b = .ok (.tuple #[.integer h, b, a, .atom "bdd_bot", .atom "bdd_bot"]) := by
  have wa : Bdd (fun _ => True) a := by obtain ⟨_, _, _, rfl⟩ := la; exact Bdd.leaf_iff.mpr trivial
  have wb : Bdd (fun _ => True) b := by obtain ⟨_, _, _, rfl⟩ := lb; exact Bdd.leaf_iff.mpr trivial
  have ha : head a = some a := by obtain ⟨_, _, _, rfl⟩ := la; simp [head]
  have hb : head b = some b := by obtain ⟨_, _, _, rfl⟩ := lb; simp [head]
  rcases cmp : Term.compare (Term.fuel a b) a b
  · obtain ⟨h₀, c, u, d, run, split⟩ := compare_lt wa ha hb cmp
    rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
    · obtain ⟨_, _, _, rfl⟩ := la; simp at e
    obtain ⟨h₁, node⟩ := node_new a b (.atom "bdd_bot") (.atom "bdd_bot") la wb
      (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
    refine ⟨h₁, Or.inl ?_⟩
    obtain ⟨_, _, _, rfl⟩ := la
    obtain ⟨_, _, _, rfl⟩ := lb
    unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
    simp [Erlang.erlang.«=:=/2», same, run, inter_top_leaf, inter_bot_leaf, node]
  · exact absurd cmp order
  · obtain ⟨h₀, c, u, d, run, split⟩ := compare_gt wb ha hb cmp
    rcases split with ⟨_, e⟩ | ⟨-, -, rfl, rfl, rfl⟩
    · obtain ⟨_, _, _, rfl⟩ := lb; simp at e
    obtain ⟨h₁, node⟩ := node_new b a (.atom "bdd_bot") (.atom "bdd_bot") lb wa
      (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
    refine ⟨h₁, Or.inr ?_⟩
    obtain ⟨_, _, _, rfl⟩ := la
    obtain ⟨_, _, _, rfl⟩ := lb
    unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
    simp [Erlang.erlang.«=:=/2», same, run, inter_leaf_top, inter_leaf_bot, node]

theorem empty_tuple_cancel (K : Nat) (k key : Int) :
    ∃ r, Elixir.Module.Types.Descr.«bdd_intersection/2» (.tuple #[.integer k, .atom "closed", .nil])
      (.tuple #[.integer key, .atom "open", Term.list [.atom "term"]]) = .ok r ∧ EmptyTuple K r := by
  have same : ¬compareExact (fuel (.tuple #[.integer key, .atom "open", Term.list [.atom "term"]]) (.tuple #[.integer k, .atom "closed", .nil])) (.tuple #[.integer key, .atom "open", Term.list [.atom "term"]])
      (.tuple #[.integer k, .atom "closed", .nil]) = .eq := by
    intro e
    obtain ⟨_, _, _, e', -, t, -⟩ := tuple3_exact e
    simp at e'
    obtain ⟨rfl, rfl, rfl⟩ := e'
    simp at t
  have order : Term.compare (Term.fuel (.tuple #[.integer k, .atom "closed", .nil]) (.tuple #[.integer key, .atom "open", Term.list [.atom "term"]])) (.tuple #[.integer k, .atom "closed", .nil])
      (.tuple #[.integer key, .atom "open", Term.list [.atom "term"]]) ≠ .eq := by
    rw [compare_tuple]
    simp [List.compareLex_cons_cons]
  obtain ⟨h, run | run⟩ := leaf_intersection ⟨k, _, _, rfl⟩ ⟨key, _, _, rfl⟩ same order
  · refine ⟨_, run, tuple_empty_of fun n S _ => ?_⟩
    simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
      Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
      Erlang.erlang.«==/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
      Erlang.lists.«reverse/2»]
  · refine ⟨_, run, tuple_empty_of fun n S _ => ?_⟩
    simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
      Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
      Erlang.erlang.«==/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
      Erlang.lists.«reverse/2»]

/-- What survives of a tuple type and its negation is empty. -/
def TupleCancel (K : Nat) (x nb : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«tuple_intersection/2» x nb = .ok r ∧
    (kept (.atom "tuple", r) = Bool.true → EmptyTuple K r)

theorem TupleOk.lit {t : Term} (h : TupleOk E t) : TupleLit E t := h.1

/-- Intersections of tuple BDDs that are not the top literal themselves. -/
theorem tuple_intersection_bdd {x y : Term} (hx : ∀ k, x ≠ .tuple #[k, .atom "open", .nil])
    (hy : ∀ k, y ≠ .tuple #[k, .atom "open", .nil]) :
    Elixir.Module.Types.Descr.«tuple_intersection/2» x y = Elixir.Module.Types.Descr.«bdd_intersection/2» x y := by
  unfold Elixir.Module.Types.Descr.«tuple_intersection/2»
  split
  · exact (hx _ rfl).elim
  · exact (hy _ rfl).elim
  · rfl

theorem not_top_of_ok {ok : Term → Prop} {x : Term} (wx : Bdd ok x) (okNot : ∀ t, ok t → ¬IsTop t) :
    ∀ k, x ≠ .tuple #[k, .atom "open", .nil] := by
  intro k e
  subst e
  rcases wx.shape with h | h | ⟨k', x', y', h⟩ | ⟨_, _, _, _, _, h⟩ <;> simp at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact okNot _ (Bdd.leaf_iff.mp wx) ⟨_, rfl⟩

theorem tuple_cancel (ops : ElemOk E K) (x : Term) (field : TupleField E x) :
    ∃ nb, Elixir.Module.Types.Descr.«tuple_difference/2» (.tuple #[.integer 61102469, .atom "open", .nil]) x = .ok nb ∧
      (kept (.atom "tuple", nb) = Bool.true → TupleCancel K x nb) := by
  rcases field with ⟨k, rfl⟩ | wx
  · exact ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«tuple_difference/2»], fun k => by simp [kept] at k⟩
  have notTop := not_top_of_ok wx fun t h => h.2
  rcases wx.shape with rfl | rfl | ⟨k, tg, l, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩
    unfold Elixir.Module.Types.Descr.«tuple_difference/2»
    simp [diff_leaf_top]
  · refine ⟨.tuple #[.integer 61102469, .atom "open", .nil], ?_, fun _ => ⟨.atom "bdd_bot", ?_, fun k => by simp [kept] at k⟩⟩
    · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [diff_leaf_bot]
    · unfold Elixir.Module.Types.Descr.«tuple_intersection/2»
      rfl
  · obtain ⟨⟨k', tag, ls, e, tags, elems⟩, notTopX⟩ := Bdd.leaf_iff.mp wx
    simp at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    by_cases special : tag = "closed" ∧ ls = []
    · obtain ⟨rfl, rfl⟩ := special
      obtain ⟨hash, hrun, -⟩ := Erlang.erlang.phash2_range (.cons (.atom "open") (Term.list [.atom "term"]))
      refine ⟨.tuple #[.integer ((1 <<< 27) + hash), .atom "open", Term.list [.atom "term"]], ?_, fun _ => ?_⟩
      · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        simp [Erlang.erlang.«==/2», Elixir.Module.Types.Descr.«bdd_leaf_new/2», hrun,
          Elixir.Module.Types.Descr.«bdd_leaf_key/2», Erlang.erlang.«is_list/1»,
          Erlang.erlang.«length/1», Erlang.erlang.«bsl/2»]
        rfl
      · obtain ⟨r, run, empty⟩ := empty_tuple_cancel K k ((1 <<< 27) + hash)
        refine ⟨r, ?_, fun _ => empty⟩
        rw [tuple_intersection_bdd notTop (by intro k e; simp at e)]
        exact run
    · have notSpecial : ∀ k₁, Term.tuple #[.integer k, .atom tag, Term.list ls] ≠
          .tuple #[k₁, .atom "closed", .nil] := by
        intro k₁ e
        simp at e
        apply special
        refine ⟨e.2.1, ?_⟩
        cases ls <;> simp_all [Term.list]
      obtain ⟨nb, run, keep, sem⟩ := neg_ok wx
      have wnb := keep _ wx
      refine ⟨nb, ?_, fun _ => ?_⟩
      · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
        split
        · next _ _ e =>
          exfalso
          simp at e
          obtain ⟨-, rfl, hl⟩ := e
          exact notTopX ⟨_, by rw [hl]⟩
        · next _ _ e => exact (notSpecial _ e).elim
        · rename_i heq; simp only [Term.tuple.injEq] at heq; subst heq; exact run
        · next h₁ => exact (h₁ _ _ rfl rfl).elim
      · have wl : Bdd (TupleLit E) (.tuple #[.integer k, .atom tag, Term.list ls]) := wx.mono fun _ h => h.1
        obtain ⟨r, rr, kr, sr⟩ := inter_ok wl (wnb.mono fun _ h => h.1)
        refine ⟨r, ?_, fun _ => tuple_empty_unsat ops (kr _ wl (wnb.mono fun _ h => h.1)) (fun _ h => h)
          fun ρ resp => ?_⟩
        · rw [tuple_intersection_bdd notTop (not_top_of_ok wnb fun t h => h.2)]
          exact rr
        · rw [sr ρ resp, sem ρ resp]
          cases eval ρ (.tuple #[.integer k, .atom tag, Term.list ls]) <;> rfl
  · obtain ⟨nb, run, keep, sem⟩ := neg_ok wx
    have wnb := keep _ wx
    refine ⟨nb, ?_, fun _ => ?_⟩
    · unfold Elixir.Module.Types.Descr.«tuple_difference/2»
      simp [run]
    · have wl : Bdd (TupleLit E) (.tuple #[.integer h, lit, c, u, d]) := wx.mono fun _ h => h.1
      obtain ⟨r, rr, kr, sr⟩ := inter_ok wl (wnb.mono fun _ h => h.1)
      refine ⟨r, ?_, fun _ => tuple_empty_unsat ops (kr _ wl (wnb.mono fun _ h => h.1)) (fun _ h => h)
        fun ρ resp => ?_⟩
      · rw [tuple_intersection_bdd notTop (not_top_of_ok wnb fun t h => h.2)]
        exact rr
      · rw [sr ρ resp, sem ρ resp]
        cases eval ρ (.tuple #[.integer h, lit, c, u, d]) <;> rfl

namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-! Basic types: static types whose fields are non-empty bitmaps, non-empty atom types, or the
top function, list, tuple, and map types. Their operations follow the operations on sets. -/

/-- The bitmap of a type, which is zero when the field is absent. -/
def bits (X : List (Term × Term)) : Nat :=
  match mapLookup X (.atom "bitmap") with
  | some (.integer b) => b.toNat
  | _ => 0

/-- The top values of the function, list, tuple, and map fields. -/
def topValue : String → Option Term
  | "fun" => some (.tuple #[.atom "negation", .map []])
  | "list" => some (.tuple #[.integer 46675407, .atom "term", .atom "term"])
  | "tuple" => some (.tuple #[.integer 61102469, .atom "open", .nil])
  | "map" => some (.tuple #[.integer 61102469, .atom "open", .nil])
  | _ => none

/-- Whether the atom field of a type holds the term `q`. -/
def amemV : Option Term → Term → Bool
  | some (.tuple ⟨[.atom "union", .map S]⟩), q => (mapLookup S q).isSome
  | some (.tuple ⟨[.atom "negation", .map S]⟩), q => !(mapLookup S q).isSome
  | _, _ => false

def amem (M : List (Term × Term)) (q : Term) : Bool := amemV (mapLookup M (.atom "atom")) q

theorem amemV_field (pos : Bool) (S : List (Term × Term)) (q : Term) :
    amemV (some (.tuple #[.atom (if pos then "union" else "negation"), .map S])) q =
      (pos == (mapLookup S q).isSome) := by
  cases pos <;> cases h : (mapLookup S q).isSome <;> simp [amemV, h]

/-- The fields of basic types. -/
def FieldOk (name : String) (w : Term) : Prop :=
  (name = "bitmap" ∧ ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255) ∨
  (name = "atom" ∧ AtomField w ∧ ∃ q, amemV (some w) q = Bool.true) ∨
  (name ≠ "bitmap" ∧ name ≠ "atom" ∧ topValue name = some w)

/-- Whether a type has the field `name`. -/
def has (M : List (Term × Term)) (name : String) : Bool := (mapLookup M (.atom name)).isSome

structure Basic (M : List (Term × Term)) : Prop where
  keys : ∀ q, (mapLookup M q).isSome → q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
    q = .atom "list" ∨ q = .atom "tuple" ∨ q = .atom "map"
  bitmap : ∀ w, mapLookup M (.atom "bitmap") = some w → ∃ b : Nat, w = .integer b ∧ 1 ≤ b ∧ b ≤ 255
  atom : ∀ w, mapLookup M (.atom "atom") = some w → AtomField w ∧ ∃ q, amem M q = Bool.true
  top : ∀ name w, name ≠ "bitmap" → name ≠ "atom" → mapLookup M (.atom name) = some w → topValue name = some w

/-- Seen sets that never hold the top tuple and map literals, whose emptiness is then computed. -/
def SeenOk (S : Term) : Prop :=
  ∃ L : List (Term × Term), S = .map L ∧ ∀ e ∈ L, ∀ kind : String,
    compareExact (fuel (.cons (.atom kind) (.tuple #[.integer 61102469, .atom "open", .nil])) e.1) (.cons (.atom kind) (.tuple #[.integer 61102469, .atom "open", .nil])) e.1 ≠ .eq

theorem seenOk_nil : SeenOk (.map []) := ⟨[], rfl, by simp⟩

theorem seen_absent {S : Term} (ok : SeenOk S) (kind : String) :
    ∃ L, S = .map L ∧ L.any (fun e => Term.compareExact (Term.fuel (.cons (.atom kind) (.tuple #[.integer 61102469, .atom "open", .nil])) e.1) (.cons (.atom kind) (.tuple #[.integer 61102469, .atom "open", .nil])) e.1 == .eq) = Bool.false := by
  obtain ⟨L, rfl, all⟩ := ok
  refine ⟨L, rfl, ?_⟩
  simp only [List.any_eq_false]
  intro e member hit
  exact all e member kind (beq_iff_eq.mp hit)

theorem line_inter_open (d : Dispatcher) (k : Int) (fs S : Term) :
    Elixir.Module.Types.Descr.«map_line_intersection/3» d (.tuple #[.atom "open", .nil])
      (.tuple #[.integer k, .atom "open", fs]) S = .ok (.tuple #[.atom "open", fs]) := by
  simp [Elixir.Module.Types.Descr.«map_line_intersection/3», Elixir.Module.Types.Descr.«map_literal_intersection/6»]
  rw [Erlang.orddict.«merge/3».eq_def]
  simp [Erlang.erlang.«is_function/2»]

theorem tuple_top_nonempty (d : Dispatcher) {S : Term} (ok : SeenOk S) :
    Elixir.Module.Types.Descr.«tuple_empty?/2» d (.tuple #[.integer 61102469, .atom "open", .nil]) S =
      .ok (.atom "false") := by
  obtain ⟨L, rfl, fresh⟩ := seen_absent ok "tuple"
  unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
    Term.false, Erlang.maps.«put/3»]
  simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
    Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
    Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
    Erlang.lists.«reverse/2», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
    Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil, Erlang.erlang.«>=/2»]

theorem map_top_nonempty (d : Dispatcher) {S : Term} (ok : SeenOk S) :
    Elixir.Module.Types.Descr.«map_empty?/2» d (.tuple #[.integer 61102469, .atom "open", .nil]) S =
      .ok (.atom "false") := by
  obtain ⟨L, rfl, fresh⟩ := seen_absent ok "map"
  unfold Elixir.Module.Types.Descr.«map_empty?/2»
  simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
    Term.false, Erlang.maps.«put/3»]
  rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
  have line := line_inter_open d 61102469 .nil
  simp [line, Elixir.Module.Types.Descr.«init_map_line_empty?/4», any_nil]
  rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
  simp

theorem list_top_nonempty (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«list_empty?/2» d (.tuple #[.integer 46675407, .atom "term", .atom "term"]) S =
      .ok (.atom "false") := by
  unfold Elixir.Module.Types.Descr.«list_empty?/2»
  simp

theorem fun_top_nonempty (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«fun_empty?/2» d (.tuple #[.atom "negation", .map []]) S = .ok (.atom "false") := by
  unfold Elixir.Module.Types.Descr.«fun_empty?/2»
  simp

theorem empty_none_seen (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«empty_seen?/2» d (.map []) S = .ok (.atom "true") := by
  unfold Elixir.Module.Types.Descr.«empty_seen?/2»
  simp [getMapKeys, Erlang.erlang.«==/2»]

/-- Basic types are empty exactly when they have no fields. -/
theorem empty_basic (d : Dispatcher) {M : List (Term × Term)} (basic : Basic M) {S : Term} (ok : SeenOk S)
    (nonempty : M ≠ []) : Elixir.Module.Types.Descr.«empty_seen?/2» d (.map M) S = .ok (.atom "false") := by
  have static : mapLookup M (.atom "dynamic") = Option.none := by
    cases h : mapLookup M (.atom "dynamic") with
    | none => rfl
    | some w =>
      rcases basic.keys _ (by rw [h]; rfl) with e | e | e | e | e | e <;> simp at e
  have top : ∀ name, name ≠ "bitmap" → name ≠ "atom" → ∀ w, mapLookup M (.atom name) = some w →
      topValue name = some w := fun name n₁ n₂ w h => basic.top name w n₁ n₂ h
  unfold Elixir.Module.Types.Descr.«empty_seen?/2»
  simp [getMapKeys_single, static, Erlang.erlang.«==/2», nonempty]
  have tupleV := top "tuple" (by decide) (by decide)
  have mapV := top "map" (by decide) (by decide)
  have listV := top "list" (by decide) (by decide)
  have funV := top "fun" (by decide) (by decide)
  simp only [topValue] at tupleV mapV listV funV
  cases ha : mapLookup M (.atom "atom") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, Lynx.Except.andAlso]
  | none =>
  cases hb : mapLookup M (.atom "bitmap") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, hb, Erlang.erlang.«not/1», Lynx.Except.andAlso]
  | none =>
  have nT := tuple_top_nonempty d ok
  have nM := map_top_nonempty d ok
  have nL := list_top_nonempty d S
  have nF := fun_top_nonempty d S
  cases ht : mapLookup M (.atom "tuple") <;> cases hm : mapLookup M (.atom "map") <;>
    cases hl : mapLookup M (.atom "list") <;> cases hf : mapLookup M (.atom "fun") <;>
    simp_all [Erlang.erlang.«is_map_key/2», any_key, Erlang.erlang.«not/1», Lynx.Except.andAlso]
  apply nonempty
  apply nil_of_lookup_none
  intro q
  cases h : mapLookup M q with
  | none => rfl
  | some w =>
    rcases basic.keys q (by rw [h]; rfl) with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

theorem le_sum_of_mem : ∀ (l : List Nat) (x : Nat), x ∈ l → x ≤ l.sum
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := le_sum_of_mem ys x h; simp; omega

/-- A non-empty atom type: a non-empty union, or any negation, as some atom is not in a set. -/
theorem fresh_atom (E : List (Term × Term)) : ∃ q, mapLookup E q = Option.none := by
  let n : Nat := (E.map fun e => match e.1 with | .atom m => m.length | _ => 0).sum + 1
  refine ⟨.atom (String.ofList (List.replicate n 'a')), ?_⟩
  simp only [mapLookup, Option.map_eq_none_iff, List.find?_eq_none]
  intro e member hit
  have same := (compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm (of_decide_eq_true hit))
  have le : (match e.1 with | .atom m => m.length | _ => 0) ≤
      (E.map fun e => match e.1 with | .atom m => m.length | _ => 0).sum :=
    le_sum_of_mem _ _ (List.mem_map_of_mem member)
  rw [same] at le
  simp at le
  omega

/-- Atom types from set operations are non-empty unless they are `0`. -/
theorem atom_nonempty (p : Bool) (E : List (Term × Term)) (ne : p = Bool.true → E ≠ []) :
    ∃ q, amemV (some (.tuple #[.atom (if p then "union" else "negation"), .map E])) q = Bool.true := by
  cases p
  · obtain ⟨q, hq⟩ := fresh_atom E
    exact ⟨q, by simp [amemV, hq]⟩
  · cases E with
    | nil => exact absurd rfl (ne rfl)
    | cons e rest => exact ⟨e.1, by simp [amemV, mapLookup]⟩

theorem top_cases {name : String} {w : Term} (h : topValue name = some w) :
    (name = "fun" ∧ w = .tuple #[.atom "negation", .map []]) ∨
    (name = "list" ∧ w = .tuple #[.integer 46675407, .atom "term", .atom "term"]) ∨
    (name = "tuple" ∧ w = .tuple #[.integer 61102469, .atom "open", .nil]) ∨
    (name = "map" ∧ w = .tuple #[.integer 61102469, .atom "open", .nil]) := by
  unfold topValue at h
  split at h <;> simp_all

/-- The difference of two fields of basic types at the same key. -/
theorem diff_key (name : String) (x y : Term) (hx : FieldOk name x) (hy : FieldOk name y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom name) x y = .ok r) ∧
      (kept (.atom name, r) = Bool.true → FieldOk name r) ∧
      (name = "bitmap" → ∃ a b : Nat, x = .integer a ∧ y = .integer b ∧ r = .integer ↑(a - (a &&& b))) ∧
      (name = "atom" → ∀ q, amemV (if kept (.atom name, r) then some r else Option.none) q =
        (amemV (some x) q && !amemV (some y) q)) ∧
      (name ≠ "bitmap" → name ≠ "atom" → kept (.atom name, r) = Bool.false) := by
  rcases hx with ⟨rfl, a, rfl, a₁, a₂⟩ | ⟨rfl, ⟨p₁, S₁, rfl, set₁⟩, -⟩ | ⟨n₁, n₂, tx⟩
  · rcases hy with ⟨-, b, rfl, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · have le : a &&& b ≤ a := Nat.and_le_left
      refine ⟨.integer ↑(a - (a &&& b)), fun d => ?_, fun k => ?_, fun _ => ⟨a, b, rfl, rfl, rfl⟩, by simp, by simp⟩
      · simp [Elixir.Module.Types.Descr.«bare_difference/3», Erlang.erlang.«band/2»]; omega
      · simp [kept] at k
        exact Or.inl ⟨rfl, _, rfl, by omega, by omega⟩
    · simp at e
    · simp at e
  · rcases hy with ⟨e, -⟩ | ⟨-, ⟨p₂, S₂, rfl, set₂⟩, -⟩ | ⟨-, e, -⟩
    · simp at e
    · rcases atom_difference p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, setE, -, ne, mE⟩ | ⟨hE, mE⟩
      · have keep : kept (.atom "atom", .tuple #[.atom (if p then "union" else "negation"), .map E]) = Bool.true := by
          simp [kept]
        refine ⟨_, fun d => by simp [Elixir.Module.Types.Descr.«bare_difference/3», hE],
          fun _ => Or.inr (Or.inl ⟨rfl, ⟨p, E, rfl, setE⟩, atom_nonempty p E ne⟩), by simp, fun _ q => ?_, by simp⟩
        rw [keep]; simp only [ite_true, amemV_field, mE]
      · refine ⟨.integer 0, fun d => by simp [Elixir.Module.Types.Descr.«bare_difference/3», hE],
          fun k => by simp [kept] at k,
          by simp, fun _ q => ?_, by simp⟩
        have := mE q
        simp only [kept, amemV_field] at this ⊢
        simp [amemV, this]
    · simp at e
  · rcases hy with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, ty⟩
    · exact absurd e n₁
    · exact absurd e n₂
    rw [tx] at ty; cases ty
    refine ?_
    rcases top_cases tx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have keep : ∀ d, Elixir.Module.Types.Descr.«fun_repr_difference/2» d (.map []) (.map []) = .ok (.map []) := by
        intro d; simp [Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»]
      refine ⟨.integer 0, fun d => ?_, fun k => by simp [kept] at k, by simp, by simp, fun _ _ => by simp [kept]⟩
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2», keep,
        Erlang.erlang.«==/2», Erlang.erlang.«map_size/1», Lynx.Except.andAlso]
    · refine ⟨.atom "bdd_bot", fun d => ?_, fun k => by simp [kept] at k, by simp, by simp, fun _ _ => by simp [kept]⟩
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«list_difference/2»]
    · refine ⟨.atom "bdd_bot", fun d => ?_, fun k => by simp [kept] at k, by simp, by simp, fun _ _ => by simp [kept]⟩
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«tuple_difference/2»]
    · refine ⟨.atom "bdd_bot", fun d => ?_, fun k => by simp [kept] at k, by simp, by simp, fun _ _ => by simp [kept]⟩
      simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«map_difference/2»]

theorem Basic.static {M : List (Term × Term)} (basic : Basic M) : mapLookup M (.atom "dynamic") = Option.none := by
  cases h : mapLookup M (.atom "dynamic") with
  | none => rfl
  | some w => rcases basic.keys _ (by rw [h]; rfl) with e | e | e | e | e | e <;> simp at e

theorem Basic.field {M : List (Term × Term)} (basic : Basic M) {name : String} {w : Term}
    (h : mapLookup M (.atom name) = some w) : FieldOk name w := by
  by_cases b : name = "bitmap"
  · subst b; exact Or.inl ⟨rfl, basic.bitmap w h⟩
  by_cases a : name = "atom"
  · subst a
    obtain ⟨field, q, hq⟩ := basic.atom w h
    exact Or.inr (Or.inl ⟨rfl, field, q, by simpa [amem, h] using hq⟩)
  exact Or.inr (Or.inr ⟨b, a, basic.top name w b a h⟩)

theorem Basic.atomKey {M : List (Term × Term)} (basic : Basic M) {q w : Term} (h : mapLookup M q = some w) :
    ∃ name, q = .atom name := by
  rcases basic.keys q (by rw [h]; rfl) with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem basic_of {M : List (Term × Term)}
    (keys : ∀ q, (mapLookup M q).isSome → q = .atom "bitmap" ∨ q = .atom "atom" ∨ q = .atom "fun" ∨
      q = .atom "list" ∨ q = .atom "tuple" ∨ q = .atom "map")
    (fields : ∀ name w, mapLookup M (.atom name) = some w → FieldOk name w) : Basic M := by
  refine ⟨keys, fun w h => ?_, fun w h => ?_, fun name w b a h => ?_⟩
  · rcases fields _ w h with ⟨-, ok⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;> first | exact ok | simp at e
  · rcases fields _ w h with ⟨e, -⟩ | ⟨-, field, q, hq⟩ | ⟨-, e, -⟩
    · simp at e
    · exact ⟨field, q, by simpa [amem, h] using hq⟩
    · simp at e
  · rcases fields name w h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, top⟩
    · exact absurd e b
    · exact absurd e a
    · exact top

/-- Folding the difference of basic types gives the basic type of the differences of their fields. -/
theorem fold_basic (A B C : List (Term × Term)) (bA : Basic A) (bB : Basic B) (g : Term → Term → Term → Term)
    (lookC : ∀ q, mapLookup C q =
      match (mapEntries B).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) with
      | some e => (mapLookup A e.1).bind fun v₁ =>
          if kept (e.1, g e.1 v₁ e.2) then some (g e.1 v₁ e.2) else Option.none
      | none => mapLookup A q)
    (dk : ∀ name x y, mapLookup A (.atom name) = some x → mapLookup B (.atom name) = some y →
      (∃ r, g (.atom name) x y = r ∧
          (kept (.atom name, r) = Bool.true → FieldOk name r) ∧
          (name = "bitmap" → ∃ a b : Nat, x = .integer a ∧ y = .integer b ∧ r = .integer ↑(a - (a &&& b))) ∧
          (name = "atom" → ∀ q, amemV (if kept (.atom name, r) then some r else Option.none) q =
            (amemV (some x) q && !amemV (some y) q)) ∧
          (name ≠ "bitmap" → name ≠ "atom" → kept (.atom name, r) = Bool.false))) :
    Basic C ∧ bits C = bits A - (bits A &&& bits B) ∧ (∀ q, amem C q = (amem A q && !amem B q)) ∧
      ∀ name, name ≠ "bitmap" → name ≠ "atom" → has C name = (has A name && !has B name) := by
  have look : ∀ name, mapLookup C (.atom name) =
      match mapLookup B (.atom name) with
      | some y => (mapLookup A (.atom name)).bind fun x =>
          if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
      | none => mapLookup A (.atom name) := by
    intro name
    rw [lookC, find_atom]
    cases mapLookup B (.atom name) <;> rfl
  have keys : ∀ q, (mapLookup C q).isSome → (mapLookup A q).isSome := by
    intro q some
    rw [lookC] at some
    split at some
    · rename_i e hit
      have same : compareExact (fuel q e.1) q e.1 = .eq := by simpa using List.find?_some hit
      rw [mapLookup_congr same]
      cases h : mapLookup A e.1 <;> simp_all
    · exact some
  refine ⟨basic_of (fun q h => bA.keys q (keys q h)) fun name w h => ?_, ?_, fun q => ?_, fun name b a => ?_⟩
  · rw [look] at h
    cases hy : mapLookup B (.atom name) with
    | none => rw [hy] at h; exact bA.field h
    | some y =>
      rw [hy] at h
      cases hx : mapLookup A (.atom name) with
      | none => rw [hx] at h; cases h
      | some x =>
        rw [hx] at h
        obtain ⟨r, run, ok, -⟩ := dk name x y hx hy
        simp only [run, Option.bind_some] at h
        split at h
        · rename_i k; cases h; exact ok k
        · cases h
  · simp only [bits]
    rw [look]
    cases hy : mapLookup B (.atom "bitmap") with
    | none =>
      cases hx : mapLookup A (.atom "bitmap") with
      | none => simp
      | some x => obtain ⟨a, rfl, -⟩ := bA.bitmap x hx; simp
    | some y =>
      obtain ⟨b, rfl, -⟩ := bB.bitmap _ hy
      cases hx : mapLookup A (.atom "bitmap") with
      | none => simp
      | some x =>
        obtain ⟨a, rfl, -⟩ := bA.bitmap x hx
        obtain ⟨r, run, -, bm, -⟩ := dk "bitmap" _ _ hx hy
        obtain ⟨a', b', ea, eb, rfl⟩ := bm rfl
        simp only [Term.integer.injEq] at ea eb
        have ea' : a' = a := by omega
        have eb' : b' = b := by omega
        rw [ea', eb'] at run
        simp only [run, Option.bind_some]
        by_cases z : a - (a &&& b) = 0 <;> simp [kept, z]
  · simp only [amem]
    rw [look]
    cases hy : mapLookup B (.atom "atom") with
    | none => simp [amemV]
    | some y =>
      cases hx : mapLookup A (.atom "atom") with
      | none => simp [amemV]
      | some x =>
        obtain ⟨r, run, -, -, am, -⟩ := dk "atom" _ _ hx hy
        have := am rfl q
        simp only [run, Option.bind_some]
        rw [← this]
  · simp only [has]
    rw [look]
    cases hy : mapLookup B (.atom name) with
    | none => simp
    | some y =>
      cases hx : mapLookup A (.atom name) with
      | none => simp
      | some x =>
        obtain ⟨r, run, -, -, -, gone⟩ := dk name _ _ hx hy
        simp [run, gone b a]

/-- Differences of basic types are basic types of the differences of their fields. -/
theorem diff_basic (depth : Nat) (left : Term) (A B : List (Term × Term)) (bA : Basic A) (bB : Basic B)
    (hleft : left = .map A ∨ (left = .atom "term" ∧ B ≠ [] ∧
      Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map A))) :
    ∃ C, Elixir.Module.Types.Descr.«bare_difference/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
        left (.map B) = .ok (.map C) ∧ Basic C ∧
      bits C = bits A - (bits A &&& bits B) ∧ (∀ q, amem C q = (amem A q && !amem B q)) ∧
      ∀ name, name ≠ "bitmap" → name ≠ "atom" → has C name = (has A name && !has B name) := by
  by_cases emptyB : B = []
  · subst emptyB
    rcases hleft with rfl | ⟨-, ne, -⟩
    rotate_left
    · exact absurd rfl ne
    refine ⟨A, ?_, bA, by simp [bits, mapLookup], fun q => by simp [amem, amemV, mapLookup],
      fun name _ _ => by simp [has, mapLookup]⟩
    unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2»]
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_difference/3» (Dispatcher.ofTable Erlang.program.fun_table depth) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  obtain ⟨C, fold, lookC, -⟩ := difference_fold depth (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
    g (mapEntries B) A (mapEntries_distinct B) (by
      intro e member v₁ found
      have hy := mapLookup_of_mem_mapEntries member
      obtain ⟨name, key⟩ := bA.atomKey found
      rw [key] at found hy ⊢
      obtain ⟨r, run, -⟩ := diff_key name v₁ e.2
        (bA.field found) (bB.field hy)
      rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure, run]
      simp [g, run])
  have run : Elixir.Module.Types.Descr.«bare_difference/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + 2))
      left (.map B) = .ok (.map C) := by
    rcases hleft with rfl | ⟨rfl, -, term⟩
    · unfold Elixir.Module.Types.Descr.«bare_difference/2»
      simp [Erlang.erlang.«==/2», unfold_map, static_map bA.static, static_map bB.static, emptyB]
      unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
      simp [Erlang.erlang.«==/2», emptyB, Erlang.maps.«fold/3»]
      simpa using fold
    · unfold Elixir.Module.Types.Descr.«bare_difference/2»
      simp [Erlang.erlang.«==/2», unfold_map, static_map bB.static, emptyB]
      unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
      simp [Erlang.erlang.«==/2», emptyB, Erlang.maps.«fold/3», term]
      simpa using fold
  have gval : ∀ name x y r, Elixir.Module.Types.Descr.«bare_difference/3»
      (Dispatcher.ofTable Erlang.program.fun_table depth) (.atom name) x y = .ok r → g (.atom name) x y = r := by
    intro name x y r h; simp [g, h]
  exact ⟨C, run, fold_basic A B C bA bB g lookC fun name x y hx hy => by
    obtain ⟨r, run, rest⟩ := diff_key name x y
      (bA.field hx) (bB.field hy)
    exact ⟨r, gval _ _ _ _ (run _), rest⟩⟩

/-- The intersection of two fields of basic types at the same key. -/
theorem inter_key (name : String) (x y : Term) (hx : FieldOk name x) (hy : FieldOk name y) :
    ∃ r, (∀ d, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom name) x y = .ok r) ∧
      (kept (.atom name, r) = Bool.true → FieldOk name r) ∧
      (name = "bitmap" → ∃ a b : Nat, x = .integer a ∧ y = .integer b ∧ r = .integer ↑(a &&& b)) ∧
      (name = "atom" → ∀ q, amemV (if kept (.atom name, r) then some r else Option.none) q =
        (amemV (some x) q && amemV (some y) q)) ∧
      (name ≠ "bitmap" → name ≠ "atom" → kept (.atom name, r) = Bool.true) := by
  rcases hx with ⟨rfl, a, rfl, a₁, a₂⟩ | ⟨rfl, ⟨p₁, S₁, rfl, set₁⟩, -⟩ | ⟨n₁, n₂, tx⟩
  · rcases hy with ⟨-, b, rfl, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · have le : a &&& b ≤ a := Nat.and_le_left
      refine ⟨.integer ↑(a &&& b), fun d => ?_, fun k => ?_, fun _ => ⟨a, b, rfl, rfl, rfl⟩, by simp, by simp⟩
      · simp [Elixir.Module.Types.Descr.«bare_intersection/3», Erlang.erlang.«band/2»]
      · simp [kept] at k
        exact Or.inl ⟨rfl, _, rfl, by omega, by omega⟩
    · simp at e
    · simp at e
  · rcases hy with ⟨e, -⟩ | ⟨-, ⟨p₂, S₂, rfl, set₂⟩, -⟩ | ⟨-, e, -⟩
    · simp at e
    · rcases atom_intersection p₁ S₁ p₂ S₂ set₁ set₂ with ⟨p, E, hE, setE, -, ne, mE⟩ | ⟨hE, mE⟩
      · have keep : kept (.atom "atom", .tuple #[.atom (if p then "union" else "negation"), .map E]) = Bool.true := by
          simp [kept]
        refine ⟨_, fun d => by simp [Elixir.Module.Types.Descr.«bare_intersection/3», hE],
          fun _ => Or.inr (Or.inl ⟨rfl, ⟨p, E, rfl, setE⟩, atom_nonempty p E ne⟩), by simp, fun _ q => ?_, by simp⟩
        rw [keep]; simp only [ite_true, amemV_field, mE]
      · refine ⟨.integer 0, fun d => by simp [Elixir.Module.Types.Descr.«bare_intersection/3», hE],
          fun k => by simp [kept] at k,
          by simp, fun _ q => ?_, by simp⟩
        have := mE q
        simp only [kept, amemV_field] at this ⊢
        simp [amemV, this]
    · simp at e
  · rcases hy with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, ty⟩
    · exact absurd e n₁
    · exact absurd e n₂
    rw [tx] at ty; cases ty
    refine ⟨x, fun d => ?_, fun _ => Or.inr (Or.inr ⟨n₁, n₂, tx⟩), fun e => absurd e n₁, fun e => absurd e n₂,
      fun _ _ => ?_⟩
    · rcases top_cases tx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have union : Elixir.Module.Types.Descr.«fun_repr_union/2» d (.map []) (.map []) = .ok (.map []) := by
          simp [Elixir.Module.Types.Descr.«fun_repr_union/2», Elixir.Module.Types.Descr.«symmetrical_merge/3»,
            Erlang.maps.«merge_with/3»]
        simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2», union,
          Erlang.erlang.«==/2», Lynx.Except.andAlso]
      · simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«list_intersection/2»]
      · simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«tuple_intersection/2»]
      · simp [Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«map_intersection/2»]
    · rcases top_cases tx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [kept]

/-- Intersections of basic types are basic types of the intersections of their fields. -/
theorem find_isSome (M : List (Term × Term)) (q : Term) {e : Term × Term}
    (hit : (mapEntries M).find? (fun e => decide (compareExact (fuel q e.1) q e.1 = .eq)) = some e) :
    (mapLookup M q).isSome := by
  rw [← mapLookup_mapEntries]
  simp [mapLookup, hit]

theorem inter_basic (depth : Nat) (A B : List (Term × Term)) (bA : Basic A) (bB : Basic B) :
    ∃ C, Elixir.Module.Types.Descr.«bare_intersection/2» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
        (.map A) (.map B) = .ok (.map C) ∧ Basic C ∧
      bits C = bits A &&& bits B ∧ (∀ q, amem C q = (amem A q && amem B q)) ∧
      ∀ name, name ≠ "bitmap" → name ≠ "atom" → has C name = (has A name && has B name) := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_intersection/3» (Dispatcher.ofTable Erlang.program.fun_table depth)
      k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have gval : ∀ name x y r, Elixir.Module.Types.Descr.«bare_intersection/3»
      (Dispatcher.ofTable Erlang.program.fun_table depth) (.atom name) x y = .ok r → g (.atom name) x y = r := by
    intro name x y r h; simp [g, h]
  have ik := fun name x y (hx : mapLookup A (.atom name) = some x) (hy : mapLookup B (.atom name) = some y) =>
    inter_key name x y (bA.field hx) (bB.field hy)
  obtain ⟨I, runI, lookI⟩ := Erlang.maps.intersect_with_lookup
    (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr" "bare_intersection" #[] A B g (by
      intro e me y hy
      have hx := mapLookup_of_mem_mapEntries me
      obtain ⟨name, key⟩ := bA.atomKey hx
      rw [key] at hx hy ⊢
      obtain ⟨r, run, -⟩ := ik name e.2 y hx hy
      rw [Erlang.program.«Elixir.Module.Types.Descr:bare_intersection/3».pure, run, gval _ _ _ _ (run _)])
  obtain ⟨C, runC, lookC⟩ := Erlang.maps.filter_lookup
    (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr"
    "-symmetrical_intersection/3-fun-0-" #[] I kept (by
      intro e _
      rw [Erlang.program.«Elixir.Module.Types.Descr:-symmetrical_intersection/3-fun-0-/2».pure, keep_field])
  have run : Elixir.Module.Types.Descr.«bare_intersection/2»
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map A) (.map B) = .ok (.map C) := by
    unfold Elixir.Module.Types.Descr.«bare_intersection/2»
    simp [getMapKeys_single, bA.static, bB.static]
    unfold Elixir.Module.Types.Descr.«symmetrical_intersection/3»
    simp [runI, runC]
  have look : ∀ name, mapLookup C (.atom name) =
      match mapLookup A (.atom name), mapLookup B (.atom name) with
      | some x, some y => if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
      | _, _ => Option.none := by
    intro name
    rw [lookC, find_atom, lookI, find_atom]
    cases mapLookup A (.atom name) <;> cases hR : mapLookup B (.atom name) <;> simp [hR]
  have keys : ∀ q, (mapLookup C q).isSome → (mapLookup A q).isSome := by
    intro q some
    rw [lookC] at some
    split at some
    · rename_i e hit
      have hI := find_isSome I q hit
      rw [lookI] at hI
      split at hI
      · rename_i e' hit'
        exact find_isSome A q hit'
      · simp at hI
    · simp at some
  refine ⟨C, run, basic_of (fun q h => bA.keys q (keys q h)) fun name w h => ?_, ?_, fun q => ?_, fun name b a => ?_⟩
  · rw [look] at h
    cases hx : mapLookup A (.atom name) <;> cases hy : mapLookup B (.atom name) <;> rw [hx, hy] at h <;>
      try simp at h
    rename_i x y
    obtain ⟨r, run, ok, -⟩ := ik name x y hx hy
    simp only [gval _ _ _ _ (run _)] at h
    obtain ⟨k, rfl⟩ := h
    exact ok k
  · simp only [bits]
    rw [look]
    cases hx : mapLookup A (.atom "bitmap") with
    | none => simp
    | some x =>
      obtain ⟨a, rfl, -⟩ := bA.bitmap x hx
      cases hy : mapLookup B (.atom "bitmap") with
      | none => simp
      | some y =>
        obtain ⟨b, rfl, -⟩ := bB.bitmap _ hy
        obtain ⟨r, run, -, bm, -⟩ := ik "bitmap" _ _ hx hy
        obtain ⟨a', b', ea, eb, rfl⟩ := bm rfl
        simp only [Term.integer.injEq] at ea eb
        have ea' : a' = a := by omega
        have eb' : b' = b := by omega
        rw [ea', eb'] at run
        simp only [gval _ _ _ _ (run _)]
        by_cases z : a &&& b = 0 <;> simp [kept, z]
  · simp only [amem]
    rw [look]
    cases hx : mapLookup A (.atom "atom") with
    | none => simp [amemV]
    | some x =>
      cases hy : mapLookup B (.atom "atom") with
      | none => simp [amemV]
      | some y =>
        obtain ⟨r, run, -, -, am, -⟩ := ik "atom" _ _ hx hy
        have := am rfl q
        simp only [gval _ _ _ _ (run _)]
        rw [← this]
  · simp only [has]
    rw [look]
    cases hx : mapLookup A (.atom name) with
    | none => simp
    | some x =>
      cases hy : mapLookup B (.atom name) with
      | none => simp
      | some y =>
        obtain ⟨r, run, -, -, -, stay⟩ := ik name _ _ hx hy
        simp [gval _ _ _ _ (run _), stay b a]

/-- Optimized unions of static types merge their fields, uniting those in both. -/
theorem opt_union_lookup (depth : Nat) (L R : List (Term × Term)) (seen : Term)
    (staticL : mapLookup L (.atom "dynamic") = Option.none) (staticR : mapLookup R (.atom "dynamic") = Option.none)
    (calls : ∀ q x y, mapLookup L q = some x → mapLookup R q = some y →
      ∃ u, Elixir.Module.Types.Descr.«opt_union/4» (Dispatcher.ofTable Erlang.program.fun_table depth) q x y seen = .ok u) :
    ∃ U, Elixir.Module.Types.Descr.«opt_union/3» (Dispatcher.ofTable Erlang.program.fun_table (depth + 1))
        (.map L) (.map R) seen = .ok (.map U) ∧
      (∀ name, (mapLookup R (.atom name) = Option.none → mapLookup U (.atom name) = mapLookup L (.atom name)) ∧
        (∀ y, mapLookup R (.atom name) = some y → mapLookup L (.atom name) = Option.none →
          mapLookup U (.atom name) = some y) ∧
        (∀ x y u, mapLookup L (.atom name) = some x → mapLookup R (.atom name) = some y →
          Elixir.Module.Types.Descr.«opt_union/4» (Dispatcher.ofTable Erlang.program.fun_table depth) (.atom name) x y seen =
            .ok u → mapLookup U (.atom name) = some u)) ∧
      ∀ q, (mapLookup U q).isSome → (mapLookup L q).isSome ∨ (mapLookup R q).isSome := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«opt_union/4» (Dispatcher.ofTable Erlang.program.fun_table depth) k₀ v₁ v₂ seen with
    | .ok w => w
    | .error _ => .nil
  have value : ∀ q x y u, Elixir.Module.Types.Descr.«opt_union/4» (Dispatcher.ofTable Erlang.program.fun_table depth)
      q x y seen = .ok u → g q x y = u := by
    intro q x y u run; simp [g, run]
  obtain ⟨U, run, look, keys⟩ : ∃ U, Elixir.Module.Types.Descr.«opt_union/3»
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) (.map L) (.map R) seen = .ok (.map U) ∧
      (∀ name, mapLookup U (.atom name) =
        match mapLookup R (.atom name) with
        | some y => some (match mapLookup L (.atom name) with | some x => g (.atom name) x y | none => y)
        | none => mapLookup L (.atom name)) ∧
      ∀ q, (mapLookup U q).isSome → (mapLookup L q).isSome ∨ (mapLookup R q).isSome := by
    unfold Elixir.Module.Types.Descr.«opt_union/3»
    simp [getMapKeys_single, Erlang.erlang.«==/2», staticL, staticR]
    by_cases emptyL : L = []
    · subst emptyL
      refine ⟨R, by simp, fun name => ?_, fun q h => Or.inr h⟩
      cases mapLookup R (.atom name) <;> simp [mapLookup]
    by_cases emptyR : R = []
    · subst emptyR
      exact ⟨L, by simp [emptyL], fun name => by simp [mapLookup], fun q h => Or.inl h⟩
    simp only [emptyL, emptyR]
    unfold Elixir.Module.Types.Descr.«symmetrical_merge/3»
    obtain ⟨out, run, look⟩ := Erlang.maps.merge_with_lookup
      (Dispatcher.ofTable Erlang.program.fun_table (depth + 1)) "Elixir.Module.Types.Descr" "-opt_union/3-anonymous-0-"
        #[seen] L R g (by
        intro e me x hx
        have hy := mapLookup_of_mem_mapEntries me
        obtain ⟨u, ru⟩ := calls e.1 x e.2 hx hy
        rw [Erlang.program.«Elixir.Module.Types.Descr:-opt_union/3-anonymous-0-/3».pure]
        simp only [Elixir.Module.Types.Descr.«-opt_union/3-anonymous-0-/4»]
        rw [ru, value _ _ _ _ ru])
    refine ⟨out, by simpa using run, fun name => ?_, fun q h => ?_⟩
    · rw [look, find_atom]
      cases mapLookup R (.atom name) <;> rfl
    · rw [look] at h
      split at h
      · rename_i e hit; exact Or.inr (find_isSome R q hit)
      · exact Or.inl h
  refine ⟨U, run, fun name => ⟨fun hR => ?_, fun y hR hL => ?_, fun x y u hL hR ru => ?_⟩, keys⟩
  · rw [look, hR]
  · rw [look, hR, hL]
  · rw [look, hR, hL]; simp only [value _ _ _ _ ru]

/-- Types of non-empty bitmaps and atoms are basic types without top fields. -/
theorem Valid.basic {V : List (Term × Term)} (valid : Valid V) :
    Basic V ∧ ∀ name, name ≠ "bitmap" → name ≠ "atom" → has V name = Bool.false := by
  have none : ∀ name, name ≠ "bitmap" → name ≠ "atom" → mapLookup V (.atom name) = Option.none := by
    intro name b a
    cases h : mapLookup V (.atom name) with
    | none => rfl
    | some w =>
      rcases valid.keys _ (by rw [h]; rfl) with e | e <;> simp at e <;> contradiction
  refine ⟨basic_of (fun q h => ?_) fun name w h => ?_, fun name b a => by simp [has, none name b a]⟩
  · rcases valid.keys q h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · by_cases b : name = "bitmap"
    · subst b; exact Or.inl ⟨rfl, valid.bitmap w h⟩
    by_cases a : name = "atom"
    · subst a
      obtain ⟨p, S, rfl, set⟩ := valid.atom w h
      exact Or.inr (Or.inl ⟨rfl, ⟨p, S, rfl, set⟩,
        atom_nonempty p S fun pt => by subst pt; exact valid.atomUnion S (by simpa using h)⟩)
    · rw [none name b a] at h; cases h

/-- The top type is the basic type of every field. -/
theorem term_basic {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) :
    Basic T ∧ bits T = 255 ∧ (∀ q, amem T q = Bool.true) ∧
      ∀ name, name ≠ "bitmap" → name ≠ "atom" → has T name = (topValue name).isSome := by
  have keyed := fun q t (h : mapLookup T q = some t) => term_keys term h
  have eqT := term
  simp only [Elixir.Module.Types.Descr.«unfolded_term/0»] at eqT
  cases eqT
  refine ⟨basic_of (fun q h => ?_) fun name w h => ?_, by simp [bits, mapLookup], fun q => ?_, fun name b a => ?_⟩
  · obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    rcases keyed q t ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  · rcases keyed _ w h with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ <;>
      simp only [Term.atom.injEq] at e <;> subst e
    · exact Or.inl ⟨rfl, 255, rfl, by omega, by omega⟩
    · obtain ⟨q, hq⟩ := fresh_atom []
      exact Or.inr (Or.inl ⟨rfl, ⟨false, [], rfl, by simp [Erlang.sets.elements?]⟩, q, by simp [amemV, mapLookup]⟩)
    all_goals exact Or.inr (Or.inr ⟨by decide, by decide, rfl⟩)
  · simp [amem, amemV, mapLookup]
  · simp only [has]
    cases h : mapLookup _ (.atom name) with
    | none =>
      unfold topValue
      split <;> simp_all [mapLookup]
    | some t =>
      rcases keyed _ t h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ <;>
        simp only [Term.atom.injEq] at e <;> subst e <;> simp_all [topValue]

theorem inter_term_left (d : Dispatcher) (v : Term) :
    Elixir.Module.Types.Descr.«bare_intersection/2» d (.atom "term") v = .ok v := by
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl

theorem bits_le {M : List (Term × Term)} (basic : Basic M) : bits M ≤ 255 := by
  simp only [bits]
  cases h : mapLookup M (.atom "bitmap") with
  | none => simp
  | some w => obtain ⟨b, rfl, -, le⟩ := basic.bitmap w h; simp; omega

/-- Basic types without bits, atoms, or top fields have no fields. -/
theorem basic_empty {M : List (Term × Term)} (basic : Basic M) (noBits : bits M = 0)
    (noAtoms : ∀ q, amem M q = Bool.false) (noTops : ∀ name, name ≠ "bitmap" → name ≠ "atom" → has M name = Bool.false) :
    M = [] := by
  apply nil_of_lookup_none
  intro q
  cases h : mapLookup M q with
  | none => rfl
  | some w =>
    obtain ⟨name, rfl⟩ := basic.atomKey h
    by_cases b : name = "bitmap"
    · subst b
      obtain ⟨n, rfl, n₁, -⟩ := basic.bitmap w h
      simp [bits, h] at noBits; omega
    by_cases a : name = "atom"
    · subst a
      obtain ⟨-, q', hq⟩ := basic.atom w h
      rw [noAtoms q'] at hq; cases hq
    · have := noTops name b a
      simp [has, h] at this

theorem band_255 {b : Nat} (le : b ≤ 255) : 255 &&& b = b := by
  rw [Nat.and_comm]
  have := Nat.and_two_pow_sub_one_eq_mod b 8
  simp at this
  omega

theorem empty_term (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«empty_seen?/2» d (.atom "term") S = .ok (.atom "false") := by
  unfold Elixir.Module.Types.Descr.«empty_seen?/2»; rfl

theorem basic_nil : Basic [] := basic_of (fun q h => by simp [mapLookup] at h) fun name w h => by simp [mapLookup] at h

theorem term_ne_nil {T : List (Term × Term)} (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) :
    T ≠ [] := by
  obtain ⟨-, bitsT, -, -⟩ := term_basic term
  rintro rfl
  simp [bits, mapLookup] at bitsT

theorem opt_union_term_left (d : Dispatcher) (x S : Term) :
    Elixir.Module.Types.Descr.«opt_union/3» d (.atom "term") x S = .ok (.atom "term") := by
  unfold Elixir.Module.Types.Descr.«opt_union/3»; rfl

/-- The guard of the clauses that return a leaf when both operands are that leaf. -/
theorem leaf_guard {α : Type} (x y : Term) (body next : Unit → Except Exception α) :
    Lynx.Except.guard (Erlang.erlang.«=:=/2» y x) body next = if compareExact (fuel y x) y x = .eq then body () else next () := by
  by_cases h : compareExact (fuel y x) y x = .eq <;> simp [Erlang.erlang.«=:=/2», h, Term.true, Term.false]

/-- Terms exactly equal to a tuple of three elements are tuples of three exactly equal elements. -/
theorem exact_tuple3 {w a b c : Term} (h : compareExact (fuel w (.tuple #[a, b, c])) w (.tuple #[a, b, c]) = .eq) :
    ∃ a' b' c', w = .tuple #[a', b', c'] ∧ compareExact (fuel a' a) a' a = .eq ∧ compareExact (fuel b' b) b' b = .eq ∧
      compareExact (fuel c' c) c' c = .eq := by
  rw [compareExact_step] at h
  cases w <;> simp [Compare.compareStep] at h
  rename_i ws
  obtain ⟨l⟩ := ws
  match l, h with
  | [a', b', c'], h =>
    simp only [List.compareLex_cons_cons, List.compareLex_nil_nil, Ordering.then_eq_eq] at h
    exact ⟨a', b', c', rfl, h.2.1, h.2.2.1, h.2.2.2.1⟩
  | [], h => simp [List.compareLex] at h
  | [_], h => simp [List.compareLex] at h
  | [_, _], h => simp [List.compareLex] at h
  | _ :: _ :: _ :: _ :: _, h => simp [List.compareLex] at h

theorem exact_ne3 {y : Term} (h : ∀ a b c, y ≠ .tuple #[a, b, c]) {a b c : Term} :
    compareExact (fuel y (.tuple #[a, b, c])) y (.tuple #[a, b, c]) ≠ .eq := fun e =>
  let ⟨_, _, _, e', _⟩ := exact_tuple3 e
  h _ _ _ e'

/-- The guards of the equal-leaf clauses fail on atoms and BDD nodes, with leaves as the translation writes them. -/
theorem atom_ne3 (s : String) (a b c : Term) : (compareExact (fuel (.atom s) (.tuple ⟨[a, b, c]⟩)) (.atom s) (.tuple ⟨[a, b, c]⟩) = .eq) = False :=
  eq_false (exact_ne3 (by simp))

theorem node_ne3 (h l c u d a b e : Term) :
    (compareExact (fuel (.tuple #[h, l, c, u, d]) (.tuple ⟨[a, b, e]⟩)) (.tuple #[h, l, c, u, d]) (.tuple ⟨[a, b, e]⟩) = .eq) = False :=
  eq_false (exact_ne3 (by simp))

/-- Leaves of a field are not exactly the top map leaf. -/
theorem cons_ne_top3 (k a f t k₀ : Term) :
    (compareExact (fuel (.tuple #[k, a, .cons f t]) (.tuple ⟨[k₀, .atom "open", .nil]⟩)) (.tuple #[k, a, .cons f t]) (.tuple ⟨[k₀, .atom "open", .nil]⟩) = .eq) = False :=
  eq_false fun e => by
    obtain ⟨_, _, c, e₀, -, -, e₃⟩ := exact_tuple3 e
    simp only [compareExact_eq_nil] at e₃
    subst e₃
    simp at e₀

theorem opt_map_union_fallback (d : Dispatcher) (x w s : Term)
    (h : (∀ k a b, x ≠ .tuple #[k, a, b]) ∨ (∀ k a b, w ≠ .tuple #[k, a, b])) :
    Elixir.Module.Types.Descr.«opt_map_union/3» d x w s = Elixir.Module.Types.Descr.«map_union/2» x w := by
  unfold Elixir.Module.Types.Descr.«opt_map_union/3»
  split
  · unfold Elixir.Module.Types.Descr.«map_union/2»; rfl
  · unfold Elixir.Module.Types.Descr.«map_union/2»
    split
    · rename_i h₁ heq h₂; exact (h₂ _ rfl).elim
    · simp_all
    · rename_i h₁ h₂; exact (h₂ _ rfl).elim
  · simp only [leaf_guard]
    split
    · rw [ite_eq_right]
      · split
        · rcases h with h | h
          · exact (h _ _ _ rfl).elim
          · exact (h _ _ _ rfl).elim
        · rfl
      · intro e
        obtain ⟨a, b, c, rfl, -⟩ := exact_tuple3 e
        rcases h with h | h
        · exact h _ _ _ rfl
        · exact h _ _ _ rfl
    · split
      · rcases h with h | h
        · exact (h _ _ _ rfl).elim
        · exact (h _ _ _ rfl).elim
      · rfl

theorem inter_term_right (d : Dispatcher) (e : Term) :
    Elixir.Module.Types.Descr.«bare_intersection/2» d e (.atom "term") = .ok e := by
  unfold Elixir.Module.Types.Descr.«bare_intersection/2»
  split <;> simp_all

theorem diff_term_right (d : Dispatcher) (e : Term) :
    Elixir.Module.Types.Descr.«bare_difference/2» d e (.atom "term") = .ok (.map []) := by
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  rfl

/-- Element types of lines: the top type or basic types. -/
def LElem (e : Term) : Prop := e = .atom "term" ∨ ∃ M, e = .map M ∧ Basic M

theorem elem_lelem {e : Term} (h : ElemTerm e) : LElem e := by
  rcases h with rfl | ⟨X, rfl, valid⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨X, rfl, (Valid.basic valid).1⟩

theorem inter_basic_u (A B : List (Term × Term)) (bA : Basic A) (bB : Basic B) :
    ∃ C, (∀ m, 0 + 1 ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) (.map A) (.map B) =
      .ok (.map C)) ∧ Basic C := by
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_intersection/3» (D 0) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have ik := fun name x y (hx : mapLookup A (.atom name) = some x) (hy : mapLookup B (.atom name) = some y) =>
    inter_key name x y (bA.field hx) (bB.field hy)
  have gval : ∀ name x y r, (∀ d, Elixir.Module.Types.Descr.«bare_intersection/3» d (.atom name) x y = .ok r) →
      g (.atom name) x y = r := by
    intro name x y r h; simp [g, h]
  obtain ⟨I, C, run, lookI, lookC⟩ := inter_uniform 0 A B bA.static bB.static g (by
    intro q x y hx hy m _
    obtain ⟨name, key⟩ := bA.atomKey hx
    subst key
    obtain ⟨r, run, -⟩ := ik name x y hx hy
    rw [run, gval _ _ _ _ run])
  have look : ∀ name, mapLookup C (.atom name) =
      match mapLookup A (.atom name), mapLookup B (.atom name) with
      | some x, some y => if kept (.atom name, g (.atom name) x y) then some (g (.atom name) x y) else Option.none
      | _, _ => Option.none := by
    intro name
    rw [lookC, find_atom, lookI, find_atom]
    cases mapLookup A (.atom name) <;> cases hR : mapLookup B (.atom name) <;> simp [hR]
  have keys : ∀ q, (mapLookup C q).isSome → (mapLookup A q).isSome := by
    intro q some
    rw [lookC] at some
    split at some
    · rename_i e hit
      have hI := find_isSome I q hit
      rw [lookI] at hI
      split at hI
      · rename_i e' hit'
        exact find_isSome A q hit'
      · simp at hI
    · simp at some
  refine ⟨C, run, basic_of (fun q h => bA.keys q (keys q h)) fun name w h => ?_⟩
  rw [look] at h
  cases hx : mapLookup A (.atom name) <;> cases hy : mapLookup B (.atom name) <;> rw [hx, hy] at h <;>
    try simp at h
  rename_i x y
  obtain ⟨r, run, ok, -⟩ := ik name x y hx hy
  simp only [gval _ _ _ _ run] at h
  obtain ⟨k, rfl⟩ := h
  exact ok k

theorem diff_basic_u (left : Term) (A B : List (Term × Term)) (bA : Basic A) (bB : Basic B)
    (hleft : left = .map A ∨ (left = .atom "term" ∧ B ≠ [] ∧
      Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map A))) :
    ∃ C, (∀ m, 2 ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) left (.map B) = .ok (.map C)) ∧
      Basic C := by
  by_cases emptyB : B = []
  · subst emptyB
    rcases hleft with rfl | ⟨-, ne, -⟩
    rotate_left
    · exact absurd rfl ne
    refine ⟨A, fun m _ => ?_, bA⟩
    unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2»]
  let g : Term → Term → Term → Term := fun k₀ v₁ v₂ =>
    match Elixir.Module.Types.Descr.«bare_difference/3» (D 0) k₀ v₁ v₂ with
    | .ok w => w
    | .error _ => .nil
  have gval : ∀ name x y r, (∀ d, Elixir.Module.Types.Descr.«bare_difference/3» d (.atom name) x y = .ok r) →
      g (.atom name) x y = r := by
    intro name x y r h; simp [g, h]
  have fold := fun depth => difference_fold depth (.function "Elixir.Module.Types.Descr" "bare_difference" 3 #[])
    g (mapEntries B) A (mapEntries_distinct B) (by
      intro e member v₁ found
      have hy := mapLookup_of_mem_mapEntries member
      obtain ⟨name, key⟩ := bA.atomKey found
      rw [key] at found hy ⊢
      obtain ⟨r, run, -⟩ := diff_key name v₁ e.2 (bA.field found) (bB.field hy)
      rw [Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure, run, gval _ _ _ _ run])
  obtain ⟨C, -, lookC, eqC⟩ := fold 0
  refine ⟨C, fun m hm => ?_, (fold_basic A B C bA bB g lookC fun name x y hx hy => by
    obtain ⟨r, run, rest⟩ := diff_key name x y (bA.field hx) (bB.field hy)
    exact ⟨r, gval _ _ _ _ run, rest⟩).1⟩
  obtain ⟨depth, rfl⟩ : ∃ depth, m = depth + 2 := ⟨m - 2, by omega⟩
  obtain ⟨C', fold', -, eq'⟩ := fold depth
  rw [eqC, ← eq']
  rcases hleft with rfl | ⟨rfl, -, term⟩
  · unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2», unfold_map, static_map bA.static, static_map bB.static, emptyB]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», emptyB, Erlang.maps.«fold/3»]
    simpa using fold'
  · unfold Elixir.Module.Types.Descr.«bare_difference/2»
    simp [Erlang.erlang.«==/2», unfold_map, static_map bB.static, emptyB]
    unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
    simp [Erlang.erlang.«==/2», emptyB, Erlang.maps.«fold/3», term]
    simpa using fold'

theorem tuple_top_bool (L : List (Term × Term)) : ∃ b, ∀ d,
    Elixir.Module.Types.Descr.«tuple_empty?/2» d (.tuple #[.integer 61102469, .atom "open", .nil]) (.map L) =
      .ok (boolAtom b) := by
  by_cases seen : L.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "tuple") (.tuple #[.integer 61102469, .atom "open", .nil])) e.1) (.cons (.atom "tuple") (.tuple #[.integer 61102469, .atom "open", .nil])) e.1 == .eq) = Bool.true
  · refine ⟨Bool.true, fun d => ?_⟩
    unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true, boolAtom]
  · have fresh : L.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "tuple") (.tuple #[.integer 61102469, .atom "open", .nil])) e.1) (.cons (.atom "tuple") (.tuple #[.integer 61102469, .atom "open", .nil])) e.1 == .eq) = Bool.false := by
      simpa using seen
    refine ⟨Bool.false, fun d => ?_⟩
    unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
      Term.false, Erlang.maps.«put/3»]
    simp [Elixir.Module.Types.Descr.«tuple_bdd_empty?/4», Elixir.Module.Types.Descr.«tuple_line_intersection/2»,
      Erlang.erlang.«length/1», Elixir.Module.Types.Descr.«tuple_sizes_strategy/4»,
      Erlang.erlang.«==/2», Erlang.erlang.«/=/2», Lynx.Except.andAlso, Elixir.Module.Types.Descr.«zip_intersection/4»,
      Erlang.lists.«reverse/2», Elixir.Module.Types.Descr.«tuple_line_empty_seen?/4»,
      Elixir.Module.Types.Descr.«tuple_line_elements_empty?/2», any_nil, Erlang.erlang.«>=/2», boolAtom]

theorem map_top_bool (L : List (Term × Term)) : ∃ b, ∀ d,
    Elixir.Module.Types.Descr.«map_empty?/2» d (.tuple #[.integer 61102469, .atom "open", .nil]) (.map L) =
      .ok (boolAtom b) := by
  by_cases seen : L.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil])) e.1) (.cons (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil])) e.1 == .eq) = Bool.true
  · refine ⟨Bool.true, fun d => ?_⟩
    unfold Elixir.Module.Types.Descr.«map_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», seen, Term.true, boolAtom]
  · have fresh : L.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil])) e.1) (.cons (.atom "map") (.tuple #[.integer 61102469, .atom "open", .nil])) e.1 == .eq) = Bool.false := by
      simpa using seen
    refine ⟨Bool.false, fun d => ?_⟩
    unfold Elixir.Module.Types.Descr.«map_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
      Term.false, Erlang.maps.«put/3»]
    rw [Elixir.Module.Types.Descr.«map_bdd_empty?/4».eq_def]
    have line := line_inter_open d 61102469 .nil
    simp [line, Elixir.Module.Types.Descr.«init_map_line_empty?/4», any_nil]
    rw [Elixir.Module.Types.Descr.«map_line_empty?/4».eq_def]
    simp [boolAtom]

/-- The emptiness of basic types does not depend on the call depth. -/
theorem basic_empty_bool {M : List (Term × Term)} (basic : Basic M) (S : List (Term × Term)) :
    ∃ b, ∀ d, Elixir.Module.Types.Descr.«empty_seen?/2» d (.map M) (.map S) = .ok (boolAtom b) := by
  by_cases nonempty : M = []
  · subst nonempty
    exact ⟨Bool.true, fun d => by simpa [boolAtom] using empty_none_seen d (.map S)⟩
  obtain ⟨tb, ht⟩ := tuple_top_bool S
  obtain ⟨mb, hm⟩ := map_top_bool S
  have static : mapLookup M (.atom "dynamic") = Option.none := basic.static
  have top : ∀ name, name ≠ "bitmap" → name ≠ "atom" → ∀ w, mapLookup M (.atom name) = some w →
      topValue name = some w := fun name n₁ n₂ w h => basic.top name w n₁ n₂ h
  have tupleV := top "tuple" (by decide) (by decide)
  have mapV := top "map" (by decide) (by decide)
  have listV := top "list" (by decide) (by decide)
  have funV := top "fun" (by decide) (by decide)
  simp only [topValue] at tupleV mapV listV funV
  refine ⟨!(mapLookup M (.atom "atom")).isSome && !(mapLookup M (.atom "bitmap")).isSome &&
    (!(mapLookup M (.atom "tuple")).isSome || tb) && (!(mapLookup M (.atom "map")).isSome || mb) &&
    !(mapLookup M (.atom "list")).isSome && !(mapLookup M (.atom "fun")).isSome, fun d => ?_⟩
  have nL := list_top_nonempty d (.map S)
  have nF := fun_top_nonempty d (.map S)
  have tB := ht d
  have mB := hm d
  unfold Elixir.Module.Types.Descr.«empty_seen?/2»
  simp [getMapKeys_single, static, Erlang.erlang.«==/2», nonempty]
  cases ha : mapLookup M (.atom "atom") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, Lynx.Except.andAlso, boolAtom]
  | none =>
  cases hb : mapLookup M (.atom "bitmap") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, hb, Erlang.erlang.«not/1», Lynx.Except.andAlso, boolAtom]
  | none =>
  have ab : ∀ x y : Bool,
      Lynx.Except.andAlso (.ok (boolAtom x)) (.ok (boolAtom y)) Bool.true = .ok (boolAtom (x && y)) := by
    intro x y; cases x <;> cases y <;> rfl
  have abT : ∀ x : Bool, Lynx.Except.andAlso (.ok (boolAtom x)) (.ok (.atom "true")) Bool.true = .ok (boolAtom x) := by
    intro x; cases x <;> rfl
  have abF : ∀ x : Bool, Lynx.Except.andAlso (.ok (boolAtom x)) (.ok (.atom "false")) Bool.true = .ok (.atom "false") := by
    intro x; cases x <;> rfl
  have bt : boolAtom Bool.true = .atom "true" := rfl
  have bf : boolAtom Bool.false = .atom "false" := rfl
  have val : ∀ {key : String} {v : Term}, (∀ w, mapLookup M (.atom key) = some w → some v = some w) →
      mapLookup M (.atom key) = Option.none ∨ mapLookup M (.atom key) = some v := by
    intro key v h
    cases e : mapLookup M (.atom key) with
    | none => exact Or.inl rfl
    | some w => exact Or.inr (by rw [Option.some.inj (h w e)])
  rcases val tupleV with htu | htu <;> rcases val mapV with hma | hma <;>
    rcases val listV with hl | hl <;> rcases val funV with hf | hf <;>
    simp [Erlang.erlang.«is_map_key/2», any_key, Erlang.erlang.«not/1», ab, abT, abF, bt, bf, ha, hb, htu, hma, hl, hf, tB, mB, nL, nF]
  all_goals
    apply nonempty
    apply nil_of_lookup_none
    intro q
    cases h : mapLookup M q with
    | none => rfl
    | some w =>
      rcases basic.keys q (by rw [h]; rfl) with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

theorem lelemOk : ElemOk LElem 2 := by
  refine ⟨Or.inl rfl, fun {a b} ha hb => ?_, fun {a} ha S => ?_, Or.inr ⟨[], rfl, basic_nil⟩, by decide⟩
  · rcases ha with rfl | ⟨A, rfl, bA⟩
    · exact ⟨b, hb, fun _ _ => by unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl⟩
    rcases hb with rfl | ⟨B, rfl, bB⟩
    · exact ⟨_, Or.inr ⟨A, rfl, bA⟩, fun m _ => inter_term_right _ _⟩
    obtain ⟨C, run, bC⟩ := inter_basic_u A B bA bB
    exact ⟨_, Or.inr ⟨C, rfl, bC⟩, fun m hm => run m (by omega)⟩
  · rcases ha with rfl | ⟨M, rfl, bM⟩
    · exact ⟨Bool.false, fun m _ => by rw [Elixir.Module.Types.Descr.«empty_seen?/2».eq_def]; rfl⟩
    · obtain ⟨b, run⟩ := basic_empty_bool bM S
      exact ⟨b, fun m _ => run _⟩

theorem lelemDiff : ElemDiff LElem 2 := by
  refine ⟨fun {a b} ha hb => ?_⟩
  rcases hb with rfl | ⟨B, rfl, bB⟩
  · exact ⟨_, Or.inr ⟨[], rfl, basic_nil⟩, fun m _ => diff_term_right _ _⟩
  by_cases empty : B = []
  · subst empty
    refine ⟨a, ha, fun m _ => ?_⟩
    unfold Elixir.Module.Types.Descr.«bare_difference/2»
    rcases ha with rfl | ⟨A, rfl, -⟩ <;> simp [Erlang.erlang.«==/2»]
  rcases ha with rfl | ⟨A, rfl, bA⟩
  · obtain ⟨T, term, -⟩ := unfolded_term_fields
    obtain ⟨C, run, bC⟩ := diff_basic_u (.atom "term") T B (term_basic term).1 bB (Or.inr ⟨rfl, empty, term⟩)
    exact ⟨_, Or.inr ⟨C, rfl, bC⟩, run⟩
  · obtain ⟨C, run, bC⟩ := diff_basic_u (.map A) A B bA bB (Or.inl rfl)
    exact ⟨_, Or.inr ⟨C, rfl, bC⟩, run⟩

theorem TupleOk.mono {E E' : Term → Prop} (h : ∀ e, E e → E' e) {t : Term} (ok : TupleOk E t) : TupleOk E' t := by
  obtain ⟨⟨k, tag, l, rfl, tags, el⟩, notTop⟩ := ok
  exact ⟨⟨k, tag, l, rfl, tags, fun e me => h e (el e me)⟩, notTop⟩

theorem MapTag.mono {E E' : Term → Prop} (h : ∀ e, E e → E' e) {tag : Term} (g : MapTag E tag) : MapTag E' tag := by
  rcases g with rfl | rfl | ⟨dl, rfl, hdl⟩
  · exact MapTag.atom_open
  · exact MapTag.atom_closed
  · exact Or.inr (Or.inr ⟨dl, rfl, fun e me => h _ (hdl e me)⟩)

theorem MapOk.mono {E E' : Term → Prop} (h : ∀ e, E e → E' e) {t : Term} (ok : MapOk E t) : MapOk E' t := by
  obtain ⟨⟨k, tag, l, rfl, tags, fs⟩, notTop⟩ := ok
  refine ⟨⟨k, tag, l, rfl, tags.mono h, fun e me => ?_⟩, notTop⟩
  obtain ⟨t, o, ht, et⟩ := fs e me
  exact ⟨t, o, ht, h t et⟩

theorem Negatable.mono {E E' : Term → Prop} (h : ∀ e, E e → E' e) {X : List (Term × Term)} (v : Negatable E X) :
    Negatable E' X := by
  refine ⟨v.keys, v.bitmap, v.atom, v.atomUnion, v.funs, v.arities, fun w hw => (v.lists w hw).imp id fun b =>
    b.mono fun _ ⟨ok, k, x, y, e, hx, hy⟩ => ⟨ok, k, x, y, e, h _ hx, h _ hy⟩, fun w hw => ?_, fun w hw => ?_⟩
  · rcases v.tuples w hw with top | b
    · exact Or.inl top
    · exact Or.inr (b.mono fun _ ok => ok.mono h)
  · rcases v.maps w hw with top | b
    · exact Or.inl top
    · exact Or.inr (b.mono fun _ ok => ok.mono h)

end Elixir.STTDescrProofsTest

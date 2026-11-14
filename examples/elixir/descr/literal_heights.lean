namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Literal heights: how deep literals nest in a type, up to exact equality. -/

theorem sizeOf_entry_lt {X : List (Term × Term)} {e : Term × Term} (h : e ∈ mapEntries X) :
    sizeOf e.2 < sizeOf (Term.map X) := by
  have m := mem_of_mem_mapEntries h
  have := List.sizeOf_lt_of_mem m
  simp only [Term.map.sizeOf_spec]
  cases e with
  | mk a b => simp at this ⊢; omega

/-- The height of literals in a type: literals add one to the height of their parts, except the top leaf `{_, open, []}`
and the top list leaf, which have no height, and BDD nodes, lists, pairs, and maps take the largest height of their
parts. The top type has no height either: its literals are those top leaves. The top BDD counts as a literal, since
differences from it hold the literals they remove, and so does the empty BDD, since the difference of the top list
leaf and the empty BDD is the top BDD. The literal of the expansion of a recursive node,
`{_, closed, [term(), node]}`, is as high as the node, so unfolding a node keeps its height. -/
def lh : Term → Nat
  | .atom "bdd_top" => 1
  | .atom "bdd_bot" => 1
  | .tuple ⟨[_, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)]⟩ =>
    lh (.tuple ⟨[.reference r, .map a, b]⟩)
  | .tuple ⟨[_, .atom "open", .nil]⟩ => 0
  | .tuple ⟨[.integer 46675407, .atom "term", .atom "term"]⟩ => 0
  | .tuple ⟨[.reference _, .map _, _]⟩ => 1
  | .tuple ⟨[_, x, y]⟩ => max (lh x) (lh y) + 1
  | .tuple ⟨[_, .tuple ⟨[_, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)]⟩,
      c, u, d]⟩ => max (lh (.tuple ⟨[.reference r, .map a, b]⟩)) (max (lh c) (max (lh u) (lh d)))
  | .tuple ⟨[_, .tuple ⟨[_, x, y]⟩, c, u, d]⟩ => max (max (lh x) (lh y) + 1) (max (lh c) (max (lh u) (lh d)))
  | .tuple ⟨[a, b, c, d, e]⟩ => max (lh a) (max (lh b) (max (lh c) (max (lh d) (lh e))))
  | .tuple ⟨[a, b]⟩ => max (lh a) (lh b)
  | .cons h t => max (lh h) (lh t)
  | .map X => ((mapEntries X).attach.map fun ⟨e, _⟩ => lh e.2).foldr max 0
  | _ => 0
termination_by t => sizeOf t
decreasing_by
  all_goals first
    | (rename_i h; have := sizeOf_entry_lt h; simp only [Term.map.sizeOf_spec] at this; simp_wf; omega)
    | (simp_wf; omega)

/-- Lists of exactly equal terms. -/
def ExactL : List Term → List Term → Prop
  | [], [] => True
  | a :: as, b :: bs => compareExact (fuel a b) a b = .eq ∧ ExactL as bs
  | _, _ => False

theorem exactL_of_lex : ∀ {xs ys : List Term}, List.compareLex (fun a b => compareExact (fuel a b) a b) xs ys = .eq → ExactL xs ys
  | [], [], _ => trivial
  | [], _ :: _, h => by simp [List.compareLex_nil_cons] at h
  | _ :: _, [], h => by simp [List.compareLex_cons_nil] at h
  | _ :: _, _ :: _, h => by
    simp only [List.compareLex_cons_cons, Ordering.then_eq_eq] at h
    exact ⟨h.1, exactL_of_lex h.2⟩

theorem tuple_exact {xs : Array Term} {b : Term} (h : compareExact (fuel (.tuple xs) b) (.tuple xs) b = .eq) :
    ∃ ys : Array Term, b = .tuple ys ∧ ExactL xs.toList ys.toList := by
  cases b <;> rw [compareExact_step] at h <;> simp [Compare.compareStep] at h
  rename_i ys
  exact ⟨ys, rfl, exactL_of_lex h.2⟩

theorem cons_exact {x xs b : Term} (h : compareExact (fuel (.cons x xs) b) (.cons x xs) b = .eq) :
    ∃ y ys, b = .cons y ys ∧ compareExact (fuel x y) x y = .eq ∧ compareExact (fuel xs ys) xs ys = .eq := by
  obtain ⟨y, ys, rfl⟩ := cons_compareExact_eq x xs b h
  rw [compareExact_cons, Ordering.then_eq_eq] at h
  exact ⟨y, ys, rfl, h⟩

theorem map_exact {X : List (Term × Term)} {b : Term} (h : compareExact (fuel (.map X) b) (.map X) b = .eq) :
    ∃ Y, b = .map Y := by
  cases b <;> rw [compareExact_step] at h <;> simp [Compare.compareStep] at h
  exact ⟨_, rfl⟩

theorem foldr_max_le {l : List Nat} {n : Nat} : l.foldr max 0 ≤ n ↔ ∀ x ∈ l, x ≤ n := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.max_le]

theorem lh_map_le {X : List (Term × Term)} {n : Nat} : lh (.map X) ≤ n ↔ ∀ e ∈ mapEntries X, lh e.2 ≤ n := by
  rw [lh, foldr_max_le]
  constructor
  · intro h e me
    exact h _ (List.mem_map.mpr ⟨⟨e, me⟩, List.mem_attach _ _, rfl⟩)
  · intro h x mx
    obtain ⟨⟨e, me⟩, -, rfl⟩ := List.mem_map.mp mx
    exact h e me

theorem le_lh_map {X : List (Term × Term)} {e : Term × Term} (me : e ∈ mapEntries X) : lh e.2 ≤ lh (.map X) :=
  lh_map_le.mp (Nat.le_refl _) e me

theorem entry_of_lookup {X : List (Term × Term)} {q v : Term} (h : mapLookup X q = some v) :
    ∃ e ∈ mapEntries X, e.2 = v := by
  rw [← mapLookup_mapEntries] at h
  simp only [mapLookup, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  exact ⟨e, List.mem_of_find?_eq_some he, rfl⟩

theorem lookup_exact {X Y : List (Term × Term)} (h : compareExact (fuel (.map X) (.map Y)) (.map X) (.map Y) = .eq) {q v : Term}
    (hv : mapLookup X q = some v) : ∃ w, mapLookup Y q = some w ∧ compareExact (fuel v w) v w = .eq := by
  have rel := lookup_of_map_compareExact_eq X Y h q
  change Option.Rel _ (mapLookup X q) (mapLookup Y q) at rel
  rw [hv] at rel
  cases hw : mapLookup Y q with
  | none => rw [hw] at rel; cases rel
  | some w => rw [hw] at rel; cases rel; exact ⟨w, rfl, by assumption⟩

theorem lh_leaf_top (k : Term) : lh (.tuple ⟨[k, .atom "open", .nil]⟩) = 0 := by simp [lh]

theorem lh_leaf_list : lh (.tuple ⟨[.integer 46675407, .atom "term", .atom "term"]⟩) = 0 := by simp [lh]

/-- The literal of the expansion of a recursive node `{ref, state, generator}`, `{_, closed, [term(), node]}`. -/
def NodeLit (_k x y : Term) : Prop :=
  x = .atom "closed" ∧ ∃ r a b, y = .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)

theorem lh_nodeLit {k : Term} {r : List Nat} {a : List (Term × Term)} {b : Term} :
    lh (.tuple ⟨[k, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference r, .map a, b]⟩) .nil)]⟩) =
      lh (.tuple ⟨[.reference r, .map a, b]⟩) := by
  rw [lh]

theorem lh_node_term {r : List Nat} {a : List (Term × Term)} {b : Term} :
    lh (.tuple ⟨[.reference r, .map a, b]⟩) = 1 := by
  rw [lh]

theorem lh_leaf (k x y : Term) (ho : ¬(x = .atom "open" ∧ y = .nil))
    (ht : ¬(k = .integer 46675407 ∧ x = .atom "term" ∧ y = .atom "term")) (hn : ¬NodeLit k x y)
    (hr : ¬∃ r a, k = .reference r ∧ x = .map a) :
    lh (.tuple ⟨[k, x, y]⟩) = max (lh x) (lh y) + 1 := by
  rw [lh]
  all_goals first
    | (intro r a h₁ h₂; exact hr ⟨r, a, h₁, h₂⟩)
    | (intro r a b h₁ h₂; subst h₁ h₂; exact hn ⟨rfl, r, a, b, rfl⟩)
    | (intro h₁ h₂; exact ho ⟨h₁, h₂⟩)
    | (rintro rfl rfl rfl; exact ht ⟨rfl, rfl, rfl⟩)

/-- Expansion literals of recursive nodes, which count as high as the node in BDD nodes. -/
def litZ : Term → Term → Bool
  | .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference _, .map _, _]⟩) .nil) => Bool.true
  | _, _ => Bool.false

theorem lh_node (h a x y c u d : Term) (hz : litZ x y = Bool.false) :
    lh (.tuple ⟨[h, .tuple ⟨[a, x, y]⟩, c, u, d]⟩) = max (max (lh x) (lh y) + 1) (max (lh c) (max (lh u) (lh d))) := by
  rw [lh]
  rintro r a b rfl rfl; simp [litZ] at hz

theorem lh_node_z (h a x y c u d : Term) (hz : litZ x y = Bool.true) :
    lh (.tuple ⟨[h, .tuple ⟨[a, x, y]⟩, c, u, d]⟩) = max (lh (.tuple ⟨[a, x, y]⟩)) (max (lh c) (max (lh u) (lh d))) := by
  unfold litZ at hz
  split at hz
  · conv => lhs; rw [lh]
    rw [lh_nodeLit]
  · cases hz

/-- BDD nodes of literals other than top leaves are as high as their literal and their branches. -/
theorem lh_node_lit (h k x y c u d : Term) (ho : ¬(x = .atom "open" ∧ y = .nil))
    (hl : ¬(k = .integer 46675407 ∧ x = .atom "term" ∧ y = .atom "term")) (hr : ¬∃ r a, k = .reference r ∧ x = .map a) :
    lh (.tuple ⟨[h, .tuple ⟨[k, x, y]⟩, c, u, d]⟩) = max (lh (.tuple ⟨[k, x, y]⟩)) (max (lh c) (max (lh u) (lh d))) := by
  cases hz : litZ x y
  · rw [lh_node _ _ _ _ _ _ _ hz, lh_leaf _ _ _ ho hl ?_ hr]
    rintro ⟨rfl, r, a, b, rfl⟩; simp [litZ] at hz
  · rw [lh_node_z _ _ _ _ _ _ _ hz]

theorem lh_five (a b c d e : Term) (hb : ∀ k x y, b ≠ .tuple ⟨[k, x, y]⟩) :
    lh (.tuple ⟨[a, b, c, d, e]⟩) = max (lh a) (max (lh b) (max (lh c) (max (lh d) (lh e)))) := by
  rw [lh]
  all_goals first
    | exact fun _ _ _ h => hb _ _ _ h
    | exact fun _ h => hb _ _ _ h
    | exact fun _ _ _ _ h => hb _ _ _ h

theorem nil_exact {y y' : Term} (h : compareExact (fuel y y') y y' = .eq) : y = .nil ↔ y' = .nil := by
  constructor
  · rintro rfl; exact (compareExact_eq_nil _).mp (Lynx.Term.compareExact_eq_symm h)
  · rintro rfl; exact (compareExact_eq_nil _).mp h

theorem atom_exact {y y' : Term} {s : String} (h : compareExact (fuel y y') y y' = .eq) : y = .atom s ↔ y' = .atom s := by
  constructor
  · rintro rfl; exact (compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm h)
  · rintro rfl; exact (compareExact_eq_atom _ _).mp h

theorem int_exact {y y' : Term} {n : Int} (h : compareExact (fuel y y') y y' = .eq) : y = .integer n ↔ y' = .integer n := by
  constructor
  · rintro rfl; exact (integer_compareExact_eq _ _).mp h
  · rintro rfl; exact (compareExact_eq_integer _ _).mp h

theorem nodeLit_exact {k x y k' x' y' : Term} (_e₁ : compareExact (fuel k k') k k' = .eq) (e₂ : compareExact (fuel x x') x x' = .eq)
    (e₃ : compareExact (fuel y y') y y' = .eq) (h : NodeLit k x y) : NodeLit k' x' y' := by
  obtain ⟨rfl, r, a, b, rfl⟩ := h
  · refine ⟨(atom_compareExact_eq _ _).mp e₂ |>.symm ▸ rfl, ?_⟩
    obtain ⟨t, rest, rfl, et, er⟩ := cons_exact e₃
    obtain ⟨n, _, rfl, en, enil⟩ := cons_exact er
    obtain ⟨ys, rfl, ex⟩ := tuple_exact en
    obtain ⟨l⟩ := ys
    match l, ex with
    | [r', a', b'], ex =>
      obtain ⟨A', rfl⟩ := map_exact ex.2.1
      refine ⟨r, A', b', ?_⟩
      rw [(atom_compareExact_eq _ _).mp et, (nil_exact enil).mp rfl, (reference_compareExact_eq _ _).mp ex.1]

theorem litZ_exact {x y x' y' : Term} (e₂ : compareExact (fuel x x') x x' = .eq) (e₃ : compareExact (fuel y y') y y' = .eq) :
    litZ x y = litZ x' y' := by
  have one : ∀ {x y x' y' : Term}, compareExact (fuel x x') x x' = .eq → compareExact (fuel y y') y y' = .eq → litZ x y = Bool.true →
      litZ x' y' = Bool.true := by
    intro x y x' y' e₂ e₃ h
    unfold litZ at h
    split at h
    · rename_i r a b
      rw [(atom_compareExact_eq _ _).mp e₂]
      obtain ⟨t, rest, rfl, et, er⟩ := cons_exact e₃
      obtain ⟨n, _, rfl, en, enil⟩ := cons_exact er
      obtain ⟨ys, rfl, ex⟩ := tuple_exact en
      obtain ⟨l⟩ := ys
      match l, ex with
      | [r', a', b'], ex =>
        obtain ⟨A', rfl⟩ := map_exact ex.2.1
        rw [(atom_compareExact_eq _ _).mp et, (nil_exact enil).mp rfl, (reference_compareExact_eq _ _).mp ex.1]
        rfl
    · cases h
  cases h : litZ x y
  · cases h' : litZ x' y'
    · rfl
    · rw [one (Lynx.Term.compareExact_eq_symm e₂) (Lynx.Term.compareExact_eq_symm e₃) h'] at h; cases h
  · exact (one e₂ e₃ h).symm

/-- Literal heights do not change under exact equality. -/
theorem lh_exact : ∀ (n : Nat) (a b : Term), sizeOf a < n → compareExact (fuel a b) a b = .eq → lh a = lh b
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, a, b, size, h => by
    have ih := lh_exact n
    cases a with
    | tuple xs =>
      obtain ⟨ys, rfl, ex⟩ := tuple_exact h
      obtain ⟨l⟩ := xs
      obtain ⟨l'⟩ := ys
      simp only [Term.tuple.sizeOf_spec, Array.mk.sizeOf_spec] at size
      simp only at ex
      match l, l', ex with
      | [], [], _ => rfl
      | [a₁], [b₁], ex => simp [lh]
      | [a₁, a₂], [b₁, b₂], ex =>
        simp only [List.cons.sizeOf_spec] at size
        simp only [lh]
        rw [ih a₁ b₁ (by omega) ex.1, ih a₂ b₂ (by omega) ex.2.1]
      | [a₁, a₂, a₃], [b₁, b₂, b₃], ex =>
        simp only [List.cons.sizeOf_spec] at size
        by_cases top : a₂ = .atom "open" ∧ a₃ = .nil
        · obtain ⟨rfl, rfl⟩ := top
          rw [(atom_exact ex.2.1).mp rfl, (nil_exact ex.2.2.1).mp rfl, lh_leaf_top, lh_leaf_top]
        have top' : ¬(b₂ = .atom "open" ∧ b₃ = .nil) := fun ⟨h₂, h₃⟩ =>
          top ⟨(atom_exact ex.2.1).mpr h₂, (nil_exact ex.2.2.1).mpr h₃⟩
        by_cases lt : a₁ = .integer 46675407 ∧ a₂ = .atom "term" ∧ a₃ = .atom "term"
        · obtain ⟨rfl, rfl, rfl⟩ := lt
          rw [(int_exact ex.1).mp rfl, (atom_exact ex.2.1).mp rfl, (atom_exact ex.2.2.1).mp rfl]
        have lt' : ¬(b₁ = .integer 46675407 ∧ b₂ = .atom "term" ∧ b₃ = .atom "term") := fun ⟨h₁, h₂, h₃⟩ =>
          lt ⟨(int_exact ex.1).mpr h₁, (atom_exact ex.2.1).mpr h₂, (atom_exact ex.2.2.1).mpr h₃⟩
        by_cases nd : ∃ r p, a₁ = .reference r ∧ a₂ = .map p
        · obtain ⟨r, p, rfl, rfl⟩ := nd
          have rr := (reference_compareExact_eq _ _).mp ex.1
          obtain ⟨Q, rfl⟩ := map_exact ex.2.1
          subst rr
          rw [lh_node_term, lh_node_term]
        have nd' : ¬∃ r p, b₁ = .reference r ∧ b₂ = .map p := by
          rintro ⟨r, p, rfl, rfl⟩
          have rr := (reference_compareExact_eq _ _).mp (Lynx.Term.compareExact_eq_symm ex.1)
          obtain ⟨Q, rfl⟩ := map_exact (Lynx.Term.compareExact_eq_symm ex.2.1)
          exact nd ⟨r, Q, rr, rfl⟩
        by_cases nl : NodeLit a₁ a₂ a₃
        · obtain ⟨rfl, r, p, q, rfl⟩ := nl
          obtain ⟨t, rest, e₃, et, er⟩ := cons_exact ex.2.2.1
          obtain ⟨n, _, rfl, en, enil⟩ := cons_exact er
          obtain ⟨ys, rfl, exn⟩ := tuple_exact en
          obtain ⟨l⟩ := ys
          match l, exn with
          | [r', p', q'], exn =>
            have rb := (atom_exact ex.2.1).mp rfl
            have rt := (atom_compareExact_eq _ _).mp et
            have rn := (nil_exact enil).mp rfl
            have rr := (reference_compareExact_eq _ _).mp exn.1
            obtain ⟨Q, rfl⟩ := map_exact exn.2.1
            subst rb rt rn rr e₃
            rw [lh_nodeLit, lh_nodeLit]
            exact ih _ _ (by simp at size ⊢; omega) en
        have nl' : ¬NodeLit b₁ b₂ b₃ := fun h => nl (nodeLit_exact (Lynx.Term.compareExact_eq_symm ex.1)
          (Lynx.Term.compareExact_eq_symm ex.2.1) (Lynx.Term.compareExact_eq_symm ex.2.2.1) h)
        rw [lh_leaf _ _ _ top lt nl nd, lh_leaf _ _ _ top' lt' nl' nd', ih a₂ b₂ (by omega) ex.2.1,
          ih a₃ b₃ (by omega) ex.2.2.1]
      | [a₁, a₂, a₃, a₄], [b₁, b₂, b₃, b₄], ex => simp [lh]
      | [a₁, a₂, a₃, a₄, a₅], [b₁, b₂, b₃, b₄, b₅], ex =>
        simp only [List.cons.sizeOf_spec] at size
        have i₃ := ih a₃ b₃ (by omega) ex.2.2.1
        have i₄ := ih a₄ b₄ (by omega) ex.2.2.2.1
        have i₅ := ih a₅ b₅ (by omega) ex.2.2.2.2.1
        by_cases three : ∃ k x y, a₂ = .tuple ⟨[k, x, y]⟩
        · obtain ⟨k, x, y, rfl⟩ := three
          obtain ⟨ys, rfl, exl⟩ := tuple_exact ex.2.1
          obtain ⟨l₂⟩ := ys
          simp only [Term.tuple.sizeOf_spec, Array.mk.sizeOf_spec, List.cons.sizeOf_spec] at size
          simp only at exl
          match l₂, exl with
          | [k', x', y'], exl =>
            have z : litZ x y = litZ x' y' := litZ_exact exl.2.1 exl.2.2.1
            cases hz : litZ x y
            · rw [lh_node _ _ _ _ _ _ _ hz, lh_node _ _ _ _ _ _ _ (z ▸ hz), i₃, i₄, i₅, ih x x' (by omega) exl.2.1,
                ih y y' (by omega) exl.2.2.1]
            · rw [lh_node_z _ _ _ _ _ _ _ hz, lh_node_z _ _ _ _ _ _ _ (z ▸ hz), i₃, i₄, i₅,
                ih _ _ (by simp at size ⊢; omega) ex.2.1]
          | [], exl => exact exl.elim
          | [_], exl => exact exl.2.elim
          | [_, _], exl => exact exl.2.2.elim
          | _ :: _ :: _ :: _ :: _, exl => exact exl.2.2.2.elim
        · have three' : ∀ k x y, b₂ ≠ .tuple ⟨[k, x, y]⟩ := by
            rintro k x y rfl
            obtain ⟨ys, e, exl⟩ := tuple_exact (Lynx.Term.compareExact_eq_symm ex.2.1)
            subst e
            obtain ⟨l₂⟩ := ys
            simp only at exl
            match l₂, exl with
            | [k', x', y'], _ => exact three ⟨k', x', y', rfl⟩
            | [], exl => exact exl.elim
            | [_], exl => exact exl.2.elim
            | [_, _], exl => exact exl.2.2.elim
            | _ :: _ :: _ :: _ :: _, exl => exact exl.2.2.2.elim
          rw [lh_five _ _ _ _ _ fun k x y h' => three ⟨k, x, y, h'⟩, lh_five _ _ _ _ _ three', i₃, i₄, i₅,
            ih a₁ b₁ (by omega) ex.1, ih a₂ b₂ (by omega) ex.2.1]
      | _ :: _ :: _ :: _ :: _ :: _ :: _, _ :: _ :: _ :: _ :: _ :: _ :: _, ex => simp [lh]
      | [], _ :: _, ex => exact ex.elim
      | _ :: _, [], ex => exact ex.elim
      | [_], _ :: _ :: _, ex => exact ex.2.elim
      | _ :: _ :: _, [_], ex => exact ex.2.elim
      | [_, _], _ :: _ :: _ :: _, ex => exact ex.2.2.elim
      | _ :: _ :: _ :: _, [_, _], ex => exact ex.2.2.elim
      | [_, _, _], _ :: _ :: _ :: _ :: _, ex => exact ex.2.2.2.elim
      | _ :: _ :: _ :: _ :: _, [_, _, _], ex => exact ex.2.2.2.elim
      | [_, _, _, _], _ :: _ :: _ :: _ :: _ :: _, ex => exact ex.2.2.2.2.elim
      | _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _], ex => exact ex.2.2.2.2.elim
      | [_, _, _, _, _], _ :: _ :: _ :: _ :: _ :: _ :: _, ex => exact ex.2.2.2.2.2.elim
      | _ :: _ :: _ :: _ :: _ :: _ :: _, [_, _, _, _, _], ex => exact ex.2.2.2.2.2.elim
    | cons x xs =>
      obtain ⟨y, ys, rfl, ex, exs⟩ := cons_exact h
      simp only [Term.cons.sizeOf_spec] at size
      simp only [lh]
      rw [ih x y (by omega) ex, ih xs ys (by omega) exs]
    | map X =>
      obtain ⟨Y, rfl⟩ := map_exact h
      have sym := Lynx.Term.compareExact_eq_symm h
      apply Nat.le_antisymm
      · refine lh_map_le.mpr fun e me => ?_
        obtain ⟨w, hw, ew⟩ := lookup_exact h (mapLookup_of_mem_mapEntries me)
        obtain ⟨e', me', rfl⟩ := entry_of_lookup hw
        rw [ih e.2 e'.2 (by have := sizeOf_entry_lt me; omega) ew]
        exact le_lh_map me'
      · refine lh_map_le.mpr fun e' me' => ?_
        obtain ⟨w, hw, ew⟩ := lookup_exact sym (mapLookup_of_mem_mapEntries me')
        obtain ⟨e, me, rfl⟩ := entry_of_lookup hw
        rw [← ih e.2 e'.2 (by have := sizeOf_entry_lt me; omega) (Lynx.Term.compareExact_eq_symm ew)]
        exact le_lh_map me
    | _ =>
      cases b <;> rw [compareExact_step] at h <;> simp [Compare.compareStep] at h <;>
        first | rfl | (subst_vars; rfl) | simp [lh]

/-! Element types of values: the interface each nesting level provides to the next. -/

/-- Seen sets of BDDs whose literals reach height `N`, and at least 1: their literals have elements. The BDDs are
keyed by their kind or arity. -/
def SafeN (N : Nat) (S : List (Term × Term)) : Prop :=
  ∀ e ∈ S, ∃ (h b : Term), e.1 = .cons h b ∧ 1 ≤ lh b ∧ N ≤ lh b

theorem safeN_nil (N : Nat) : SafeN N [] := fun _ h => by simp at h

/-- Seen sets as `SafeN`, except that BDDs keyed by an arity, which only function checks look up, may be one lower. -/
def SafeT (N : Nat) (S : List (Term × Term)) : Prop :=
  ∀ e ∈ S, ∃ (h b : Term), e.1 = .cons h b ∧ 1 ≤ lh b ∧ (N ≤ lh b ∨ (∃ i : Int, h = .integer i) ∧ N ≤ lh b + 1)

theorem SafeN.toT {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) : SafeT N S := fun e me =>
  let ⟨h, b, e₁, one, hb⟩ := hS e me
  ⟨h, b, e₁, one, Or.inl hb⟩

/-- Types that combine the node `nd` with types of height zero: their tuple field is a BDD of the expansion literal
of `nd`, and their other fields have height zero. -/
def Combo (nd a : Term) : Prop :=
  a = .atom "term" ∨ IsT nd a ∨ ∃ X, a = .map X ∧
    (∀ w, mapLookup X (.atom "tuple") = some w → OField (PureLit nd) w) ∧
    ∀ name w, name ≠ "tuple" → mapLookup X (.atom name) = some w → lh w = 0

/-- Seen sets of walks on tuple BDDs of height one: their keys are higher than zero and are not tuple BDDs of the
expansion literal of `nd`. -/
def Safe1 (nd : Term) (S : List (Term × Term)) : Prop :=
  SafeN 1 S ∧ ∀ e ∈ S, ∀ x, OField (PureLit nd) x → compareExact (fuel (.cons (.atom "tuple") x) e.1) (.cons (.atom "tuple") x) e.1 ≠ .eq

/-- Element types `E` of values `V`: closed under the plain and optimized operations, which hold the values `den`
says, with exact emptiness and sound subtyping and disjointness, at every call depth from `K`. Plain operations keep
literals, so they keep literal heights; emptiness is sound when the seen BDDs are higher than the type, and `tl`
holds of the values the tail of an improper list cannot be. -/
structure EF (nd : Term) (E : Term → Prop) (V : Type) (den : Term → V → Prop) (tl : V → Prop) (K : Nat) : Prop where
  term : E (.atom "term")
  den_term : ∀ v, den (.atom "term") v
  static : ∀ {a}, E a → Static a
  node : ∀ {a}, E a → IsNode a → IsT nd a
  low : ∀ {a}, E a → lh a = 0 → Combo nd a
  cinter : ∀ {a b c m}, E a → E b → Combo nd a → Combo nd b → K ≤ m →
    Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c → Combo nd c
  cdiff : ∀ {a b c m}, E a → E b → Combo nd a → Combo nd b → K ≤ m →
    Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c → Combo nd c
  cempty : ∀ {a S m b}, E a → Combo nd a → Safe1 nd S → K ≤ m →
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b) → (b = Bool.true ↔ ∀ v, ¬den a v)
  inhabited : Nonempty V
  resp : ∀ {e e' : Term} {v : V}, E e → E e' → compare (fuel e e') e e' = .eq → den e' v → den e v
  union : ∀ {a b}, E a → E b → ∃ c, E c ∧ (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok c) ∧
    (∀ v, den c v ↔ den a v ∨ den b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N
  inter : ∀ {a b}, E a → E b → ∃ c, E c ∧
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok c) ∧
    (∀ v, den c v ↔ den a v ∧ den b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N
  diff : ∀ {a b}, E a → E b → ∃ c, E c ∧
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok c) ∧
    (∀ v, den c v ↔ den a v ∧ ¬den b v) ∧ ∀ N, lh a < N → lh b < N → lh c < N
  opt_union : ∀ {a b} (S : List (Term × Term)) {m}, E a → E b → K ≤ m → ∃ c, E c ∧
    Elixir.Module.Types.Descr.«opt_union/3» (D m) a b (.map S) = .ok c ∧ ∀ v, den c v ↔ den a v ∨ den b v
  opt_inter : ∀ {a b} (S : List (Term × Term)) {m}, E a → E b → K ≤ m → ∃ c, E c ∧
    Elixir.Module.Types.Descr.«opt_intersection/3» (D m) a b (.map S) = .ok c ∧ ∀ v, den c v ↔ den a v ∧ den b v
  opt_diff : ∀ {a b} (S : List (Term × Term)) {m}, E a → E b → K ≤ m → ∃ c, E c ∧
    Elixir.Module.Types.Descr.«opt_difference/3» (D m) a b (.map S) = .ok c ∧ ∀ v, den c v ↔ den a v ∧ ¬den b v
  empty : ∀ {a} (S : List (Term × Term)), E a → ∃ b : Bool,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«empty_seen?/2» (D m) a (.map S) = .ok (boolAtom b)) ∧
    ∀ N, lh a < N → SafeN N S → (b = Bool.true ↔ ∀ v, ¬den a v)
  sub : ∀ {a b}, E a → E b → ∃ s : Bool,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (boolAtom s)) ∧
    (s = Bool.true → ∀ v, den a v → den b v)
  subc : ∀ {a b}, E a → E b → (∀ v, den a v → den b v) → ∀ m, K ≤ m →
    Elixir.Module.Types.Descr.«subtype?/2» (D m) a b = .ok (.atom "true")
  disj : ∀ {a b}, E a → E b → ∃ s : Bool,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«disjoint?/2» (D m) a b = .ok (boolAtom s)) ∧
    (s = Bool.true → ∀ v, den a v → den b v → False)
  fuse : ∀ {a b} (n : Int) {m}, E a → E b → compareExact (fuel a b) a b ≠ .eq → K ≤ m → ∃ r,
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» (D m) a b (.integer n) = .ok r ∧
    (r = .atom "nil" ∨ (E r ∧ ∀ v, den r v ↔ den a v ∨ den b v))
  tail : ∀ {e}, E e → ∃ e', (∀ m, 1 ≤ m → Elixir.Module.Types.Descr.«list_tail_unfold/1» (D m) e = .ok e') ∧ E e' ∧
    (∀ v, den e' v ↔ den e v ∧ ¬tl v) ∧ lh e' ≤ lh e
  tl_witness : ∃ v, ¬tl v
  none : E (.map [])
  pos : 1 ≤ K

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Element types below a literal height. -/
abbrev EB (E : Term → Prop) (N : Nat) (a : Term) : Prop := E a ∧ lh a < N

theorem lh_nil_map : lh (.map []) = 0 := by
  refine Nat.le_zero.mp (lh_map_le.mpr fun e me => ?_)
  have := mem_of_mem_mapEntries me
  simp at this

theorem EF.ops (ef : EF nd E V den tl K) (N : Nat) (hN : 0 < N) : ElemOk (EB E N) K :=
  ⟨⟨ef.term, by simpa [lh] using hN⟩,
    fun ha hb => let ⟨c, hc, run, _, h⟩ := ef.inter ha.1 hb.1; ⟨c, ⟨hc, h N ha.2 hb.2⟩, run⟩,
    fun ha S => let ⟨b, run, _⟩ := ef.empty S ha.1; ⟨b, run⟩, ⟨ef.none, by rw [lh_nil_map]; exact hN⟩, ef.pos⟩

theorem EF.dops (ef : EF nd E V den tl K) (N : Nat) : ElemDiff (EB E N) K :=
  ⟨fun ha hb => let ⟨c, hc, run, _, h⟩ := ef.diff ha.1 hb.1; ⟨c, ⟨hc, h N ha.2 hb.2⟩, run⟩⟩

theorem EF.sem (ef : EF nd E V den tl K) (N : Nat) : ElemSem (EB E N) K V den (SafeN N) where
  term := ef.den_term
  inter := fun ha hb hm run v => by
    obtain ⟨c, -, run', h, -⟩ := ef.inter ha.1 hb.1
    rw [run' _ hm] at run; cases run; exact h v
  diff := fun ha hb hm run v => by
    obtain ⟨c, -, run', h, -⟩ := ef.diff ha.1 hb.1
    rw [run' _ hm] at run; cases run; exact h v
  empty := fun {a S m b} ha hS hm run => by
    obtain ⟨b', run', h⟩ := ef.empty S ha.1
    rw [run' _ hm] at run
    have : b' = b := by cases b <;> cases b' <;> simp_all [boolAtom]
    subst this
    exact h N ha.2 hS
  inhabited := ef.inhabited
  resp := fun he he' h d => ef.resp he.1 he'.1 h d

theorem EF.tsem (ef : EF nd E V den tl K) (N : Nat) : TailSem (EB E N) den tl :=
  ⟨fun he => let ⟨e', run, he', h, hl⟩ := ef.tail he.1; ⟨e', run, ⟨he', by have := he.2; omega⟩, h⟩, ef.tl_witness⟩

end

end Elixir.STTDescrProofsTest.Nest

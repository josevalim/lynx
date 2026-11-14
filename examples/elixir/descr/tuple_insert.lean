namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-- `tuple_bdd_positive?/1` answers a boolean on BDDs. -/
theorem positive_run : ∀ (ok : Term → Prop) (b : Term), Bdd ok b →
    ∃ q : Bool, Elixir.Module.Types.Descr.«tuple_bdd_positive?/1» b = .ok (boolAtom q) := by
  refine Bdd.induction (P := fun _ b => ∃ q : Bool, Elixir.Module.Types.Descr.«tuple_bdd_positive?/1» b = .ok (boolAtom q))
    ?_ ?_ ?_ ?_
  · intro _; exact ⟨Bool.false, by simp [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1», boolAtom]⟩
  · intro _; exact ⟨Bool.true, by simp [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1», boolAtom]⟩
  · intro _ k x y _; exact ⟨Bool.true, by simp [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1», boolAtom]⟩
  · intro ok h lit c u d _ _ _ _ _ _ ⟨q, hq⟩ _
    by_cases shape : c = .atom "bdd_top" ∧ d = .atom "bdd_bot"
    · obtain ⟨rfl, rfl⟩ := shape
      exact ⟨q, by rw [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1».eq_def]; simpa using hq⟩
    · refine ⟨Bool.false, ?_⟩
      rw [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1».eq_def]
      split
      all_goals first
        | (rename_i heq; simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at heq; simp_all; done)
        | (simp_all [boolAtom]; done)
        | rfl

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem ins_exists {P : List Term} {Q : Term → List V → Prop} {i : Nat} {R : V → Prop} {w : List V} :
    Ins (fun u => ∃ p ∈ P, Q p u) i R w ↔ ∃ p ∈ P, Ins (Q p) i R w := by
  constructor
  · rintro ⟨w₁, y, w₂, e, len, hy, p, mp, h⟩; exact ⟨p, mp, w₁, y, w₂, e, len, hy, h⟩
  · rintro ⟨p, mp, w₁, y, w₂, e, len, hy, h⟩; exact ⟨w₁, y, w₂, e, len, hy, p, mp, h⟩

/-- The fold of `tuple_insert_static/3` inserts an element into each literal and unites them. -/
theorem insert_pieces (ef : EF nd E V den tl K) {x : Term} (hx : E x) (i : Nat) (P : List Term) (tP : ∀ p ∈ P, Piece E p)
    {m : Nat} {res : Term}
    (run : Erlang.lists.«foldl/3» (D m) (.function "Elixir.Module.Types.Descr" "-tuple_insert_static/3-fun-0-" 2
      #[.integer i, x]) (.atom "bdd_bot") (Term.list P) = .ok res) :
    TField E res ∧ ∀ w, denTF E den res w = Bool.true ↔ ∃ p ∈ P, Ins (PieceIn den p) i (den x) w := by
  refine foldl_ok (m := m) _ _ _ (fun pre a => TField E a ∧ ∀ w, denTF E den a w = Bool.true ↔
      ∃ p ∈ pre, Ins (PieceIn den p) i (den x) w) P (fun pre p a a' mp ⟨ta, sa⟩ step => ?_) _
    ⟨Or.inr Bdd.bot, fun w => by simp [denTF_bot]⟩ res run
  obtain ⟨tag, l, rfl, g, hl⟩ := tP p mp
  rw [Erlang.program.«Elixir.Module.Types.Descr:-tuple_insert_static/3-fun-0-/2».pure] at step
  simp only [Elixir.Module.Types.Descr.«-tuple_insert_static/3-fun-0-/4»] at step
  cases hr : Elixir.Module.Types.Descr.«tuple_insert_leaf/4» (.atom tag) (Term.list l) (.integer i) x with
  | error _ => simp [hr] at step
  | ok r =>
    rw [hr, Lynx.Except.ok_bind] at step
    obtain ⟨fr, sr⟩ := insert_leaf (den := den) ef g hl hx i hr
    obtain ⟨u, ru, tu, su, -⟩ := tuple_union_lh (den := den) fr ta
    rw [ru] at step
    cases step
    refine ⟨tu, fun w => ?_⟩
    rw [su, Bool.or_eq_true, sr, sa]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | ⟨q, mq, hq⟩)
      · exact ⟨_, Or.inr rfl, (ins_congr fun u => pieceIn_iff).mpr h⟩
      · exact ⟨q, Or.inl mq, hq⟩
    · rintro ⟨q, mq | rfl, hq⟩
      · exact Or.inr ⟨q, mq, hq⟩
      · exact Or.inl ((ins_congr fun u => pieceIn_iff).mp hq)

/-- `tuple_insert_static/3` inserts an element into the tuple field of a map. -/
theorem insert_static (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) {X : List (Term × Term)} {b : Term}
    (hb : mapLookup X (.atom "tuple") = some b) (fb : TField E b) {x : Term} (hx : E x) (i : Nat) {res : Term}
    (run : Elixir.Module.Types.Descr.«tuple_insert_static/3» (D (n + 3)) (.map X) (.integer i) x = .ok res) :
    ∃ b', res = .map ((.atom "tuple", b') :: X) ∧ TField E b' ∧
      ∀ w, denTF E den b' w = Bool.true ↔ Ins (fun u => denTF E den b u = Bool.true) i (den x) w := by
  have upd : ∀ b', Erlang.maps.«update/3» (.atom "tuple") b' (.map X) = .ok (.map ((.atom "tuple", b') :: X)) := by
    intro b'
    have : (X.find? fun entry => decide (compareExact (fuel (.atom "tuple") entry.1) (.atom "tuple") entry.1 = .eq)).isSome := by
      have := congrArg Option.isSome hb
      simpa [mapLookup] using this
    simp [Erlang.maps.«update/3», this]
  -- The positive path, on any tuple field.
  have positive : ∀ (ok : Term → Prop), Bdd ok b → (∀ t, ok t → TupleLit E t) → (∀ w, denTF E den b w = eval (valT E den w) b) →
      ∀ r, Elixir.Module.Types.Descr.«tuple_insert_leaves/4» b (.integer i) x (.atom "bdd_bot") = .ok r →
      TField E r ∧ ∀ w, denTF E den r w = Bool.true ↔ Ins (fun u => denTF E den b u = Bool.true) i (den x) w := by
    intro ok wb okT same r hr
    obtain ⟨tr, sr⟩ := insert_leaves (den := den) ef hx i ok b wb okT (.atom "bdd_bot") r (Or.inr Bdd.bot) hr
    refine ⟨tr, fun w => ?_⟩
    rw [sr, denTF_bot]
    simp only [Bool.false_eq_true, false_or]
    exact ins_congr fun u => by rw [same u]
  rcases fb with ⟨k, rfl⟩ | wb
  · simp only [Elixir.Module.Types.Descr.«tuple_insert_static/3», getMapKeys_single, hb, Option.toList_some] at run
    simp [Elixir.Module.Types.Descr.«tuple_bdd_positive?/1», Lynx.Term.isMember, Lynx.Except.guard] at run
    cases hr : Elixir.Module.Types.Descr.«tuple_insert_leaves/4» (.tuple #[.integer k, .atom "open", .nil]) (.integer i) x
        (.atom "bdd_bot") with
    | error _ => simp [hr] at run
    | ok r =>
      simp [hr, Erlang.erlang.«is_map/1», upd] at run
      subst run
      have lit : TupleLit E (.tuple #[.integer k, .atom "open", .nil]) := ⟨k, "open", [], rfl, Or.inl rfl, by simp⟩
      obtain ⟨tr, sr⟩ := positive (TupleLit E) (Bdd.leaf_iff.mpr lit) (fun t h => h) (fun w => by
        rw [denTF_top, eval_leaf]
        have := (vT_lit (den := den) (v := w) ef (Or.inl rfl) (l := []) (k := k) (by simp)).mpr (InT.open_nil w)
        exact this.symm) r hr
      exact ⟨r, rfl, tr, sr⟩
  · obtain ⟨q, rq⟩ := positive_run _ b wb
    have hb' : Lynx.Term.getMapKeys [.atom "tuple"] (.map X) = [b] := by simp [getMapKeys_single, hb]
    cases q
    · obtain ⟨P, rP, tP, sP⟩ := no_negs (den := den) ef hn wb
      unfold Elixir.Module.Types.Descr.«tuple_insert_static/3» at run
      simp only [hb', rq, rP] at run
      simp [Lynx.Term.isMember, Lynx.Except.guard, boolAtom] at run
      cases hr : Erlang.lists.«foldl/3» (D (n + 3))
          (.function "Elixir.Module.Types.Descr" "-tuple_insert_static/3-fun-0-" 2 #[.integer i, x]) (.atom "bdd_bot")
          (Term.list P) with
      | error _ => simp [hr] at run
      | ok r =>
        simp [hr, Erlang.erlang.«is_map/1», upd] at run
        subst run
        obtain ⟨tr, sr⟩ := insert_pieces (den := den) ef hx i P tP hr
        refine ⟨r, rfl, tr, fun w => ?_⟩
        rw [sr, ← ins_exists]
        exact ins_congr fun u => by rw [sP u, denTF_bdd wb]
    · unfold Elixir.Module.Types.Descr.«tuple_insert_static/3» at run
      simp only [hb', rq] at run
      simp [Lynx.Term.isMember, Lynx.Except.guard, boolAtom] at run
      cases hr : Elixir.Module.Types.Descr.«tuple_insert_leaves/4» b (.integer i) x (.atom "bdd_bot") with
      | error _ => simp [hr] at run
      | ok r =>
        simp [hr, Erlang.erlang.«is_map/1», upd] at run
        subst run
        obtain ⟨tr, sr⟩ := positive (TLit E) wb (fun t h => h.1.1) (fun w => denTF_bdd wb w) r hr
        exact ⟨r, rfl, tr, sr⟩

end

theorem lookup_put (X : List (Term × Term)) (b' : Term) (name : String) :
    mapLookup ((.atom "tuple", b') :: X) (.atom name) = if name = "tuple" then some b' else mapLookup X (.atom name) := by
  by_cases h : name = "tuple" <;> simp [mapLookup, h]

theorem descrC_put {Fn TF LF MF : Term → Prop} {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) {b' : Term}
    (tb : TF b') : DescrC Fn TF LF MF ((.atom "tuple", b') :: X) where
  keys q h := by
    by_cases e : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq
    · exact ⟨"tuple", by simp [names], (compareExact_eq_atom _ _).mp e⟩
    · have : (mapLookup X q).isSome := by simpa [mapLookup, List.find?_cons, e] using h
      exact sX.keys q this
  fields name x h := by
    rw [lookup_put] at h
    split at h
    · rename_i e; subst e
      simp only [Option.some.injEq] at h; subst h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, tb⟩))))
    · exact sX.fields name x h

theorem size_map (d : Dispatcher) {X : List (Term × Term)} {b : Term} (hb : mapLookup X (.atom "tuple") = some b)
    (i : Term) : Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» d (.map X) i =
      Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» d (.map [(.atom "tuple", b)]) i := by
  unfold Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2»
  simp only [getMapKeys_single, hb, Option.toList_some]
  simp [mapLookup]

section
variable {t : Term} {n : Nat}

/-- `tuple_insert_at_checked/3` on static types of the next level: when it gives a type, the input holds only tuples,
all long enough, and the result holds those tuples with a value of the element inserted. -/
theorem insert_tuple {X : List (Term × Term)} (hX : DE (level t n).E (.map X)) {x : Term} (hx : (level t n).E x) (i : Nat)
    {m : Nat} (hm : (level t n).K + 25 ≤ m) {Y : List (Term × Term)}
    (run : Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» (D m) (.map X) (.integer i) x = .ok (.map Y)) :
    TOnly t n X ∧ (∀ w, TT t n X w → i ≤ w.length) ∧ DE (level t n).E (.map Y) ∧
      (∀ v : PN t n, denD (.map Y) v → v.1.1 = "tuple") ∧ ∀ w, TT t n Y w ↔ Ins (TT t n X) i ((level t n).den x) w := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have sX := de_map hX
  have ef := (level t n).ef
  unfold Elixir.Module.Types.Descr.«tuple_insert_at_checked/3» at run
  simp only [Erlang.maps.«take/2», sX.static, Lynx.Except.ok_bind] at run
  cases hb : mapLookup X (.atom "tuple") with
  | none =>
    exfalso
    simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Lynx.Except.andAlso,
      Lynx.Except.guard] at run
    split at run
    · simp [Erlang.erlang.«/=/2»] at run
    · cases h : Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (k + 3)) (.map X) (.integer i) <;>
        simp [h, Erlang.erlang.«/=/2»] at run
  | some b =>
    have fb : TField (level t n).E b := fieldC_tuple (sX.fields "tuple" b hb)
    obtain ⟨dR, sR⟩ := rest_tuple hX
    have rE := next_empty dR (m := k + 3) (by omega)
    obtain ⟨eb, reb, seb⟩ := tuple_empty_exact (level t n).ef fb []
    have seb := seb (lh b + 1) (by omega) (safeT_nil _)
    have tt : ∀ w, TT t n X w ↔ denTF (level t n).E (level t n).den b w = Bool.true := fun w => by simp [TT, hb]
    have only : TOnly t n X ↔ (∀ v : PN t n, ¬denD (.map (rmT X)) v) ∧ eb = Bool.false := by
      constructor
      · rintro ⟨h₁, w, hw⟩
        refine ⟨fun v hv => ((sR v).mp hv).2 (h₁ v ((sR v).mp hv).1), ?_⟩
        cases eb
        · rfl
        · have := seb.mp rfl w; rw [(tt w).mp hw] at this; cases this
      · rintro ⟨h₁, h₂⟩
        refine ⟨fun v hv => Classical.byContradiction fun ne => h₁ v ((sR v).mpr ⟨hv, ne⟩), ?_⟩
        obtain ⟨w, hw⟩ := Classical.not_forall.mp (mt seb.mpr (by simp [h₂]))
        exact ⟨w, (tt w).mpr (by simpa using hw)⟩
    have nonEmpty : Elixir.Module.Types.Descr.«non_empty_tuple_only?/1» (D (k + 3)) (.map X) =
        .ok (boolAtom (bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) && !eb)) := by
      simp only [Elixir.Module.Types.Descr.«non_empty_tuple_only?/1», Erlang.maps.«take/2», hb]
      rw [show (List.filter (fun entry => compareExact (fuel (.atom "tuple") entry.fst) (.atom "tuple") entry.fst != Ordering.eq) X) = rmT X from rfl]
      simp only [Lynx.Except.ok_bind, rE, reb (k + 3) (by omega)]
      cases bp (∀ v : PN t n, ¬denD (.map (rmT X)) v) <;> cases eb <;>
        simp [Lynx.Except.andAlso, Erlang.erlang.«not/1», boolAtom]
    have key : Elixir.Module.Types.Descr.«descr_key?/2» (.map X) (.atom "tuple") = .ok (.atom "true") := by
      simp [Elixir.Module.Types.Descr.«descr_key?/2», Erlang.erlang.«is_map_key/2», any_key, hb, Term.true]
    -- The size check.
    obtain ⟨sz, rsz, ssz⟩ : ∃ sz : Bool, Lynx.Except.orElse (Erlang.erlang.«==/2» (.integer i) (.integer 0))
        (Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (k + 3)) (.map X) (.integer i)) = .ok (boolAtom sz) ∧
        (sz = Bool.true → ∀ w, TT t n X w → i ≤ w.length) := by
      by_cases z : i = 0
      · subst z
        exact ⟨Bool.true, by simp [Lynx.Except.orElse, Erlang.erlang.«==/2», boolAtom], fun _ w _ => Nat.zero_le _⟩
      · obtain ⟨sz, rs, ss⟩ := size_at_least (level t n).ef (m := k + 3) (by omega) fb i (by omega)
        refine ⟨sz, ?_, fun h w hw => ss.mp h w ((tt w).mp hw)⟩
        have eq0 : Erlang.erlang.«==/2» (.integer (i : Int)) (.integer 0) = .ok (.atom "false") := by
          simp [Erlang.erlang.«==/2»]; omega
        rw [size_map _ hb, eq0]
        simpa [Lynx.Except.orElse] using rs
    obtain ⟨c, rc, sc⟩ : ∃ c : Bool, Elixir.Module.Types.Descr.«non_empty_tuple_only?/1» (D (k + 3)) (.map X) =
        .ok (boolAtom c) ∧ (c = Bool.true → TOnly t n X) := by
      refine ⟨_, nonEmpty, fun h => only.mpr ?_⟩
      simp only [Bool.and_eq_true, bp_true, Bool.not_eq_true'] at h
      exact h
    simp only [key, rc, rsz] at run
    cases c <;> cases sz <;>
      simp [boolAtom, Lynx.Except.andAlso, Erlang.erlang.«/=/2», pure, Except.pure] at run
    have onlyX := sc rfl
    obtain ⟨b', e, tb', sb'⟩ := insert_static (den := (level t n).den) (level t n).ef (n := k) (by omega) hb fb hx i run
    simp only [Term.map.injEq] at e
    subst e
    have ttY : ∀ w, TT t n ((.atom "tuple", b') :: X) w ↔ denTF (level t n).E (level t n).den b' w = Bool.true :=
      fun w => by simp [TT, lookup_put]
    refine ⟨onlyX, ssz rfl, Or.inr ⟨_, rfl, descrC_put sX tb'⟩, fun v hv => ?_, fun w => ?_⟩
    · by_cases h : v.1.1 = "tuple"
      · exact h
      · apply onlyX.1 v
        rw [denD_map] at hv ⊢
        rwa [lookup_put, ite_eq_right h] at hv
    · rw [ttY, sb']
      exact ins_congr fun u => (tt u).symm

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem fetch_step_pos (d : Dispatcher) (tag : String) (l lines : List Term) (i : Nat) (ea : Term) (ob : Bool)
    (nh : ¬(ea = .atom "term" ∧ ob = Bool.true)) {descr u : Term} {o : Bool}
    (hfe : Elixir.Module.Types.Descr.«tuple_fetch_element/3» (Term.list l) (.integer i) (.atom tag) =
      .ok (.tuple #[descr, boolAtom o]))
    (hu : Elixir.Module.Types.Descr.«opt_union/2» d descr ea = .ok u) :
    Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» d (Term.list (.tuple #[.atom tag, Term.list l, Term.list []] :: lines))
      (.integer i) (.tuple #[ea, boolAtom ob]) =
    Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» d (Term.list lines) (.integer i) (.tuple #[u, boolAtom (o || ob)]) := by
  rw [Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3».eq_def]
  simp only [Term.list]
  split
  all_goals first
    | (exfalso; simp_all [boolAtom]; done)
    | skip
  · rename_i hx heq₁ heq₂
    simp only [Term.cons.injEq, Term.tuple.injEq] at heq₁ heq₂
    obtain ⟨⟨rfl, rfl, -⟩, rfl⟩ := heq₁
    obtain ⟨rfl, rfl⟩ := heq₂
    cases o <;> cases ob <;> simp [hfe, hu, Lynx.Except.orElse, boolAtom]
  · rename_i h₁ h₂ h₃ h₄
    exact (h₃ _ _ _ _ _ rfl rfl).elim

theorem fetch_step_negs (d : Dispatcher) (tag : String) (l negs lines : List Term) (i : Nat) (ea : Term) (ob : Bool)
    (nh : ¬(ea = .atom "term" ∧ ob = Bool.true)) (nn : negs ≠ []) {res next : Term}
    (ht : Elixir.Module.Types.Descr.«tuple_take_element/3» (Term.list l) (.integer i) (.atom tag) = .ok res)
    (hn : (res = .atom "empty" ∧ next = .tuple #[ea, boolAtom ob]) ∨
      ∃ value rest P s value' u, res = .tuple #[value, rest] ∧
        Elixir.Module.Types.Descr.«tuple_split_negative_pairs/2» d (Term.list negs) (.integer i) = .ok (Term.list P) ∧
        Elixir.Module.Types.Descr.«tuple_pair_projection_keeps_full_fst?/2» d (Term.list P) rest = .ok (boolAtom s) ∧
        ((s = Bool.true ∧ value' = value) ∨ (s = Bool.false ∧ ∃ Q,
          Elixir.Module.Types.Descr.«tuple_project_negative_pairs/3» d (Term.list P) value rest = .ok (Term.list Q) ∧
          Erlang.lists.«foldl/3» d (.function "Elixir.Module.Types.Descr" "-tuple_bdd_fetch_lines/3-fun-0-" 2 #[])
            (.map []) (Term.list Q) = .ok value')) ∧
        Elixir.Module.Types.Descr.«opt_union/2» d value' ea = .ok u ∧ next = .tuple #[u, boolAtom ob]) :
    Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» d (Term.list (.tuple #[.atom tag, Term.list l, Term.list negs] :: lines))
      (.integer i) (.tuple #[ea, boolAtom ob]) =
    Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» d (Term.list lines) (.integer i) next := by
  have nnil : Term.list negs ≠ .nil := by cases negs <;> simp_all [Term.list]
  rw [Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3».eq_def]
  simp only [Term.list] at nnil ⊢
  split
  all_goals first
    | (exfalso; simp_all [boolAtom]; done)
    | skip
  · rename_i hx hneg heq₁ heq₂
    simp only [Term.cons.injEq, Term.tuple.injEq] at heq₁ heq₂
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := heq₁
    obtain ⟨rfl, rfl⟩ := heq₂
    rcases hn with ⟨rfl, rfl⟩ | ⟨value, rest, P, s, value', u, rfl, hs, hk, hv, hu, rfl⟩
    · simp [ht]
    · rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, Q, hq, hf⟩
      · simp [ht, hs, hk, hu, Lynx.Term.isMember, boolAtom]
      · simp [ht, hs, hk, hq, hf, hu, Lynx.Term.isMember, boolAtom]
  · rename_i h₁ h₂ h₃ h₄
    exact (h₄ _ _ _ _ _ _ rfl rfl).elim

section
variable {V : Type} {den : Term → V → Prop}

theorem InT.open_append : ∀ {l : List Term} {v : List V} (w : List V), InT den Bool.false l v →
    InT den Bool.false l (v ++ w)
  | [], [], [], _ => trivial
  | [], [], _ :: _, _ => rfl
  | [], _ :: _, _, _ => rfl
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, w, h => ⟨h.1, InT.open_append w h.2⟩

theorem InT.open_take : ∀ {l : List Term} {v : List V}, InT den Bool.false l v → InT den Bool.false l (v.take l.length)
  | [], [], _ => trivial
  | [], _ :: _, _ => trivial
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => ⟨h.1, InT.open_take h.2⟩

/-- Values at an index of the tuples of a line. -/
def LongIn (den : Term → V → Prop) (L : Term) (i : Nat) (y : V) : Prop :=
  ∃ v₁ v₂, v₁.length = i ∧ InLine den L (v₁ ++ y :: v₂)

/-- Lines holding tuples without an index. -/
def ShortIn (den : Term → V → Prop) (L : Term) (i : Nat) : Prop := ∃ v, InLine den L v ∧ v.length ≤ i

end

theorem fetch_nil (d : Dispatcher) (i : Nat) (acc : Term) :
    Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» d (Term.list []) (.integer i) acc = .ok acc := by
  rw [Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3».eq_def]
  simp only [Term.list]
  split <;> simp_all

theorem fetch_halt (d : Dispatcher) (lines : Term) (i : Nat) :
    Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» d lines (.integer i) (.tuple #[.atom "term", .atom "true"]) =
      .ok (.tuple #[.atom "term", .atom "true"]) := by
  rw [Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3».eq_def]
  rfl

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- A line without negations, at an index: its element there, or the top or empty type past its elements. -/
theorem line_pos (ef : EF nd E V den tl K) {m : Nat} (hm : K ≤ m) (i : Nat) {tag : String} {l : List Term}
    (g : tag = "open" ∨ tag = "closed") (hl : ∀ e ∈ l, E e) (ne : ∃ v, InT den (tag == "closed") l v)
    (lines : List Term) {ea : Term} (hea : E ea) (ob : Bool) (nh : ¬(ea = .atom "term" ∧ ob = Bool.true)) :
    ∃ ea' ob', Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» (D m)
        (Term.list (.tuple #[.atom tag, Term.list l, Term.list []] :: lines)) (.integer i) (.tuple #[ea, boolAtom ob]) =
      Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» (D m) (Term.list lines) (.integer i)
        (.tuple #[ea', boolAtom ob']) ∧ E ea' ∧ (∀ y, den ea y → den ea' y) ∧
      (∀ y, LongIn den (.tuple #[.atom tag, Term.list l, Term.list []]) i y → den ea' y) ∧
      (ob = Bool.true → ob' = Bool.true) ∧
      (ob' = Bool.true → ob = Bool.true ∨ ShortIn den (.tuple #[.atom tag, Term.list l, Term.list []]) i) ∧
      (ob' = Bool.false → ob = Bool.false ∧ ∀ y, den ea' y →
        den ea y ∨ LongIn den (.tuple #[.atom tag, Term.list l, Term.list []]) i y) := by
  obtain ⟨v₀, hv₀⟩ := ne
  have inl : ∀ v, InLine den (.tuple #[.atom tag, Term.list l, Term.list []]) v ↔ InT den (tag == "closed") l v :=
    fun v => by rw [inLine_iff]; simp
  have hfe := fetch_element tag g l i
  by_cases short : i < l.length
  · obtain ⟨l₁, x, l₂, rfl, len₁⟩ : ∃ l₁ x l₂, l = l₁ ++ x :: l₂ ∧ l₁.length = i := by
      refine ⟨l.take i, l[i]'short, l.drop (i + 1), ?_, by simp; omega⟩
      simp
    have hx : E x := hl x (by simp)
    obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] hx hea hm
    have long : ∀ y, LongIn den (.tuple #[.atom tag, Term.list (l₁ ++ x :: l₂), Term.list []]) i y ↔ den x y := by
      intro y
      constructor
      · rintro ⟨v₁, v₂, len, hv⟩
        exact ((InT.split l₁ x l₂ v₁ y v₂ (by omega)).mp ((inl _).mp hv)).1
      · intro hy
        obtain ⟨w₁, y₀, w₂, rfl, h₁, -, h₂⟩ := (InT.mid l₁ x l₂).mp hv₀
        have lw := h₁.closed_length
        have rest := ((InT.split l₁ x l₂ w₁ y₀ w₂ (by omega)).mp hv₀).2
        exact ⟨w₁, w₂, by omega, (inl _).mpr ((InT.split l₁ x l₂ w₁ y w₂ (by omega)).mpr ⟨hy, rest⟩)⟩
    have e : (l₁ ++ x :: l₂)[i]'(by simp; omega) = x := by subst len₁; simp
    refine ⟨u, Bool.false || ob, fetch_step_pos (D m) tag _ lines i ea ob nh (descr := x) (o := Bool.false) (by rw [hfe, dite_eq_left short, e]; rfl)
      (by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using ru), hu, fun y h => (su y).mpr (Or.inr h),
      fun y h => (su y).mpr (Or.inl ((long y).mp h)), fun h => by simp [h], fun h => Or.inl (by simpa using h),
      fun h => ⟨by simpa using h,
        fun y hy => ((su y).mp hy).elim (fun h => Or.inr ((long y).mpr h)) Or.inl⟩⟩
  · rcases g with rfl | rfl
    · obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] ef.term hea hm
      refine ⟨u, Bool.true || ob, fetch_step_pos (D m) "open" _ lines i ea ob nh (descr := .atom "term") (o := Bool.true) (by rw [hfe]; simp [short])
        (by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using ru), hu, fun y h => (su y).mpr (Or.inr h),
        fun y _ => (su y).mpr (Or.inl (ef.den_term y)), fun _ => by simp, fun _ => Or.inr ⟨v₀.take l.length, (inl _).mpr ?_, ?_⟩,
        fun h => by simp at h⟩
      · exact InT.open_take (by simpa using hv₀)
      · simp; omega
    · obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] ef.none hea hm
      have nolong : ∀ y, ¬LongIn den (.tuple #[.atom "closed", Term.list l, Term.list []]) i y := by
        rintro y ⟨v₁, v₂, len, hv⟩
        exact InT.split_closed (l := l) (v₁ := v₁) (by omega) (by simpa using (inl _).mp hv)
      refine ⟨u, Bool.true || ob, fetch_step_pos (D m) "closed" _ lines i ea ob nh (descr := .map []) (o := Bool.true) (by rw [hfe]; simp [short])
        (by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using ru), hu, fun y h => (su y).mpr (Or.inr h),
        fun y h => absurd h (nolong y), fun _ => by simp, fun _ => Or.inr ⟨v₀, (inl _).mpr hv₀, ?_⟩, fun h => by simp at h⟩
      have := (by simpa using hv₀ : InT den Bool.true l v₀).closed_length
      omega

/-- A line with negations, at an index: the values there of its tuples, projected outside the negated pairs. -/
theorem line_negs (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) (i : Nat) {tag : String} {l negs : List Term}
    (g : tag = "open" ∨ tag = "closed") (hl : ∀ e ∈ l, E e) (lits : ∀ t ∈ negs, TupleLit E t) (nn : negs ≠ [])
    (ne : ∃ v, InLine den (.tuple #[.atom tag, Term.list l, Term.list negs]) v)
    (lines : List Term) {ea : Term} (hea : E ea) (ob : Bool) (nh : ¬(ea = .atom "term" ∧ ob = Bool.true)) :
    ∃ ea', Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» (D (n + 2))
        (Term.list (.tuple #[.atom tag, Term.list l, Term.list negs] :: lines)) (.integer i) (.tuple #[ea, boolAtom ob]) =
      Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» (D (n + 2)) (Term.list lines) (.integer i)
        (.tuple #[ea', boolAtom ob]) ∧ E ea' ∧ (∀ y, den ea y → den ea' y) ∧
      (∀ y, LongIn den (.tuple #[.atom tag, Term.list l, Term.list negs]) i y → den ea' y) ∧
      (∀ y, den ea' y → den ea y ∨ LongIn den (.tuple #[.atom tag, Term.list l, Term.list negs]) i y) := by
  obtain ⟨v₀, hv₀⟩ := ne
  obtain ⟨hv₀, -⟩ := inLine_iff.mp hv₀
  obtain ⟨res, ht, ⟨rfl, none⟩ | ⟨⟨value, rest, rfl, hval, hr⟩, nr, lenR, sem⟩⟩ := take_pair ef g hl i
  · refine ⟨ea, fetch_step_negs (D (n + 2)) tag l negs lines i ea ob nh nn ht (Or.inl ⟨rfl, rfl⟩), hea, fun y h => h,
      fun y ⟨v₁, v₂, len, hv⟩ => absurd (inLine_iff.mp hv).1 (none v₁ y v₂ len), fun y h => Or.inl h⟩
  obtain ⟨P, rP, hP, sP⟩ := split_pairs (den := den) ef negs lits i (m := n + 2)
  -- The pair holds a tuple long enough, so its remaining tuples are not empty.
  obtain ⟨v, hv, long⟩ : ∃ v, InT den (tag == "closed") l v ∧ i < v.length := by
    rcases g with rfl | rfl
    · obtain ⟨y₀⟩ := ef.inhabited
      exact ⟨v₀ ++ List.replicate (i + 1) y₀, InT.open_append _ (by simpa using hv₀), by simp; omega⟩
    · by_cases short : l.length ≤ i
      · have := take_closed_short l i short
        rw [this] at ht; cases ht
      · have := (by simpa using hv₀ : InT den Bool.true l v₀).closed_length
        exact ⟨v₀, hv₀, by omega⟩
  have split : v = v.take i ++ v[i] :: v.drop (i + 1) := by simp
  have restNe : ∃ w, denTF E den rest w = Bool.true := by
    rw [split] at hv
    have := (sem (v.take i) v[i] (v.drop (i + 1)) (by simp; omega)).mp hv
    exact ⟨_, (pairIn_iff.mp this).2⟩
  obtain ⟨s, value', rk, hs₁, hs₂, hv', sv'⟩ := proj_value ef hn P hP hval hr restNe
  obtain ⟨u, hu, ru, su⟩ := ef.opt_union [] hv' hea (show K ≤ n + 2 by omega)
  have hsv : (s = Bool.true ∧ value' = value) ∨ (s = Bool.false ∧ ∃ Q,
      Elixir.Module.Types.Descr.«tuple_project_negative_pairs/3» (D (n + 2)) (Term.list P) value rest = .ok (Term.list Q) ∧
      Erlang.lists.«foldl/3» (D (n + 2)) (.function "Elixir.Module.Types.Descr" "-tuple_bdd_fetch_lines/3-fun-0-" 2 #[])
        (.map []) (Term.list Q) = .ok value') := by
    cases s
    · exact Or.inr ⟨rfl, hs₂ rfl⟩
    · exact Or.inl ⟨rfl, hs₁ rfl⟩
  have run := fetch_step_negs (D (n + 2)) tag l negs lines i ea ob nh nn ht (Or.inr ⟨value, rest, P, s, value', u, rfl, rP,
    rk, hsv, by simpa [Elixir.Module.Types.Descr.«opt_union/2»] using ru, rfl⟩)
  have longIff : ∀ y, LongIn den (.tuple #[.atom tag, Term.list l, Term.list negs]) i y ↔ den value' y := by
    intro y
    rw [sv']
    constructor
    · rintro ⟨v₁, v₂, len, hvl⟩
      obtain ⟨hin, hneg⟩ := inLine_iff.mp hvl
      obtain ⟨hy, hw⟩ := pairIn_iff.mp ((sem v₁ y v₂ len).mp hin)
      exact ⟨v₁ ++ v₂, hy, hw, fun p mp hp => (sP v₁ y v₂ len).mpr ⟨p, mp, hp⟩ |>.elim fun N ⟨mN, hN⟩ => hneg N mN hN⟩
    · rintro ⟨w, hy, hw, hno⟩
      have lw := lenR y w (pairIn_iff.mpr ⟨hy, hw⟩)
      have ew : w = w.take i ++ w.drop i := by simp
      refine ⟨w.take i, w.drop i, by simp; omega, inLine_iff.mpr ⟨?_, fun N mN hN => ?_⟩⟩
      · rw [sem _ y _ (by simp; omega), ← ew]
        exact pairIn_iff.mpr ⟨hy, hw⟩
      · obtain ⟨p, mp, hp⟩ := (sP _ y _ (by simp; omega)).mp ⟨N, mN, hN⟩
        rw [← ew] at hp
        exact hno p mp hp
  exact ⟨u, run, hu, fun y h => (su y).mpr (Or.inr h), fun y h => (su y).mpr (Or.inl ((longIff y).mp h)),
    fun y h => ((su y).mp h).elim (fun h => Or.inr ((longIff y).mpr h)) Or.inl⟩

/-- `tuple_bdd_fetch_lines/3` unites the values at an index of the tuples of non-empty lines, and flags lines holding
tuples without that index, unless it reaches the top type, flagged. -/
theorem fetch_lines_sem (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) (i : Nat) :
    ∀ (lines : List Term), (∀ L ∈ lines, TLine E L ∧ ∃ v, InLine den L v) → ∀ (ea : Term) (ob : Bool), E ea →
      ∃ e o, Elixir.Module.Types.Descr.«tuple_bdd_fetch_lines/3» (D (n + 2)) (Term.list lines) (.integer i)
          (.tuple #[ea, boolAtom ob]) = .ok (.tuple #[e, boolAtom o]) ∧ E e ∧ (∀ y, den ea y → den e y) ∧
        (∀ L ∈ lines, ∀ y, LongIn den L i y → den e y) ∧ (ob = Bool.true → o = Bool.true) ∧
        (o = Bool.true → ob = Bool.true ∨ ∃ L ∈ lines, ShortIn den L i) ∧
        (o = Bool.false → ∀ y, den e y → den ea y ∨ ∃ L ∈ lines, LongIn den L i y)
  | lines, hlines, ea, ob, hea => by
    by_cases halt : ea = .atom "term" ∧ ob = Bool.true
    · obtain ⟨rfl, rfl⟩ := halt
      exact ⟨_, Bool.true, fetch_halt _ _ _, ef.term, fun y _ => ef.den_term y, fun _ _ y _ => ef.den_term y,
        fun _ => rfl, fun _ => Or.inl rfl, fun h => by cases h⟩
    cases lines with
    | nil =>
      exact ⟨ea, ob, fetch_nil _ _ _, hea, fun y h => h, by simp, id, fun h => Or.inl h, fun _ y h => Or.inl h⟩
    | cons L rest =>
      obtain ⟨⟨tag, l, negs, rfl, g, hl, lits⟩, ne⟩ := hlines _ List.mem_cons_self
      have hrest := fun L' (m : L' ∈ rest) => hlines L' (List.mem_cons_of_mem _ m)
      by_cases nn : negs = []
      · subst nn
        obtain ⟨v, hv⟩ := ne
        obtain ⟨ea', ob', run, hea', sub, long, mono, short, back⟩ := line_pos ef (m := n + 2) (by omega) i g hl
          ⟨v, (inLine_iff.mp hv).1⟩ rest hea ob halt
        obtain ⟨e, o, run', he, sub', long', mono', short', back'⟩ := fetch_lines_sem ef hn i rest hrest ea' ob' hea'
        refine ⟨e, o, run.trans run', he, fun y h => sub' y (sub y h), fun L' mL' y h => ?_, fun h => mono' (mono h),
          fun h => ?_, fun h y hy => ?_⟩
        · rcases List.mem_cons.mp mL' with rfl | mL'
          · exact sub' y (long y h)
          · exact long' L' mL' y h
        · rcases short' h with h | ⟨L', mL', h⟩
          · rcases short h with h | h
            · exact Or.inl h
            · exact Or.inr ⟨_, List.mem_cons_self, h⟩
          · exact Or.inr ⟨L', List.mem_cons_of_mem _ mL', h⟩
        · rcases back' h y hy with h' | ⟨L', mL', h'⟩
          · cases ob' with
            | true => rw [mono' rfl] at h; cases h
            | false =>
              rcases (back rfl).2 y h' with h'' | h''
              · exact Or.inl h''
              · exact Or.inr ⟨_, List.mem_cons_self, h''⟩
          · exact Or.inr ⟨L', List.mem_cons_of_mem _ mL', h'⟩
      · obtain ⟨ea', run, hea', sub, long, back⟩ := line_negs ef hn i g hl lits nn ne rest hea ob halt
        obtain ⟨e, o, run', he, sub', long', mono', short', back'⟩ := fetch_lines_sem ef hn i rest hrest ea' ob hea'
        refine ⟨e, o, run.trans run', he, fun y h => sub' y (sub y h), fun L' mL' y h => ?_, mono', fun h => ?_,
          fun h y hy => ?_⟩
        · rcases List.mem_cons.mp mL' with rfl | mL'
          · exact sub' y (long y h)
          · exact long' L' mL' y h
        · rcases short' h with h | ⟨L', mL', h⟩
          · exact Or.inl h
          · exact Or.inr ⟨L', List.mem_cons_of_mem _ mL', h⟩
        · rcases back' h y hy with h' | ⟨L', mL', h'⟩
          · rcases back y h' with h'' | h''
            · exact Or.inl h''
            · exact Or.inr ⟨_, List.mem_cons_self, h''⟩
          · exact Or.inr ⟨L', List.mem_cons_of_mem _ mL', h'⟩

theorem ge_ints (a b : Nat) : Erlang.erlang.«>=/2» (.integer (a : Int)) (.integer (b : Int)) =
    .ok (boolAtom (decide (b ≤ a))) := by
  by_cases h : b ≤ a <;> simp [Erlang.erlang.«>=/2», h, boolAtom, Int.isGE_compare] <;> omega

/-- `tuple_bdd_positive_size_at_least?/3` finds a lower bound of the sizes of the tuples of a BDD from its literals. -/
theorem pos_size (ef : EF nd E V den tl K) (n : Nat) {ok : Term → Prop} {r : Term} (wr : Bdd ok r)
    (okT : ∀ t, ok t → TupleOk E t) : ∀ g : Bool, ∃ b : Bool,
      Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/3» r (.integer n) (boolAtom g) = .ok (boolAtom b) ∧
      (b = Bool.true → ∀ v, eval (valT E den v) r = Bool.true → (g = Bool.true → n ≤ v.length) → n ≤ v.length) := by
  refine Bdd.induction (P := fun ok r => (∀ t, ok t → TupleOk E t) → ∀ g : Bool, ∃ b : Bool,
      Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/3» r (.integer n) (boolAtom g) = .ok (boolAtom b) ∧
      (b = Bool.true → ∀ v, eval (valT E den v) r = Bool.true → (g = Bool.true → n ≤ v.length) → n ≤ v.length))
    ?_ ?_ ?_ ?_ ok r wr okT
  · intro ok _ g
    refine ⟨g, ?_, fun h v _ hg => hg h⟩
    cases g <;> rfl
  · intro ok _ g
    refine ⟨Bool.true, ?_, fun _ v h => by simp at h⟩
    cases g <;> rfl
  · intro ok k x y okl okLit g
    obtain ⟨⟨k', tag, l, e, gt, el⟩, -⟩ := okLit _ okl
    cases g
    · refine ⟨decide (n ≤ l.length), ?_, fun h v hv _ => ?_⟩
      · rw [e]
        unfold Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/3»
        by_cases h : n ≤ l.length <;> simp [length_list, boolAtom, h]
      · simp only [decide_eq_true_eq] at h
        rw [eval_leaf, e] at hv
        have := (lit_sem (valT_lit ef.semR ⟨k', tag, l, rfl, gt, el⟩ hv)).length_le
        omega
    · exact ⟨Bool.true, by rfl, fun _ v _ hg => hg rfl⟩
  · intro ok h lit c u d leaf okl hc hu hd ic iu idd okLit g
    have hl := okLit _ okl
    obtain ⟨k', tag, l, rfl, gt, el⟩ := hl.1
    have okLit' : ∀ t, Above ok (.tuple #[.integer k', .atom tag, Term.list l]) t → TupleOk E t := fun t ht => okLit t ht.1
    cases g
    · obtain ⟨bu, ru, su⟩ := iu okLit' Bool.false
      obtain ⟨bc, rc, sc⟩ := ic okLit' (decide (n ≤ l.length))
      obtain ⟨bd, rd, sd⟩ := idd okLit' Bool.false
      refine ⟨bu && bc && bd, ?_, fun hb v hv _ => ?_⟩
      · unfold Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/3»
        simp only [boolAtom_false] at ru rd
        have rc' := rc
        by_cases hn : n ≤ l.length <;> simp only [hn, decide_true, decide_false, boolAtom_true, boolAtom_false] at rc' <;>
          cases bu <;> cases bc <;> cases bd <;>
          simp [length_list, ru, rc', rd, Lynx.Except.andAlso, boolAtom, hn]
      · simp only [Bool.and_eq_true] at hb
        rw [eval_node] at hv
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hv
        rcases hv with (⟨hlit, hcv⟩ | huv) | ⟨-, hdv⟩
        · refine sc hb.1.2 v hcv fun hg => ?_
          simp only [decide_eq_true_eq] at hg
          have := (lit_sem (valT_lit ef.semR ⟨k', tag, l, rfl, gt, el⟩ hlit)).length_le
          omega
        · exact su hb.1.1 v huv (by simp)
        · exact sd hb.2 v hdv (by simp)
    · exact ⟨Bool.true, by rfl, fun _ v _ hg => hg rfl⟩

theorem pos2_ne (b : Term) {n : Nat} (hn : 1 ≤ n) :
    Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/2» b (.integer n) =
      Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/3» b (.integer n) (.atom "false") := by
  unfold Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/2»
  split
  · rename_i h; simp at h; omega
  · rfl

theorem inT_terms_iff (hterm : ∀ y, den (.atom "term") y) (n : Nat) (v : List V) :
    InT den Bool.false (List.replicate n (.atom "term")) v ↔ n ≤ v.length :=
  ⟨fun h => by simpa using h.length_le, InT.open_any hterm n v⟩

/-- `tuple_of_size_at_least_static?/2` decides whether every tuple of a tuple type has a size. -/
theorem size_at_least (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {b : Term} (hb : TField E b) (n : Nat)
    (hn : 1 ≤ n) : ∃ sz : Bool, Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D m)
      (.map [(.atom "tuple", b)]) (.integer n) = .ok (boolAtom sz) ∧
      (sz = Bool.true ↔ ∀ v, denTF E den b v = Bool.true → n ≤ v.length) := by
  -- The positive check, sound.
  obtain ⟨p, rp, sp⟩ : ∃ p : Bool, Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/2» b (.integer n) =
      .ok (boolAtom p) ∧ (p = Bool.true → ∀ v, denTF E den b v = Bool.true → n ≤ v.length) := by
    rw [pos2_ne b hn]
    rcases hb with ⟨k, rfl⟩ | wb
    · refine ⟨Bool.false, ?_, by simp⟩
      have := ge_ints 0 n
      have nn : decide (n ≤ 0) = Bool.false := by simp; omega
      rw [nn] at this
      simpa [Elixir.Module.Types.Descr.«tuple_bdd_positive_size_at_least?/3», Erlang.erlang.«length/1»] using this
    · obtain ⟨p, rp, sp⟩ := pos_size ef n wb (fun t h => h.1) Bool.false
      exact ⟨p, rp, fun h v hv => sp h v (by rwa [denTF_bdd wb] at hv) (by simp)⟩
  obtain ⟨k, rk, key⟩ := leaf_new_key "open" (Or.inl rfl) (List.replicate n (.atom "term"))
  have hl : ∀ e ∈ List.replicate n (.atom "term"), E e := fun e me => by rw [List.eq_of_mem_replicate me]; exact ef.term
  obtain ⟨d, rd, td, sd, -⟩ := tuple_diff_lh ef hb (tleaf_field (Or.inl rfl) hl key)
  obtain ⟨e, re, se⟩ := tuple_empty_exact ef td []
  have se := se (lh d + 1) (by omega) (safeT_nil _)
  have leafSem : ∀ v, denTF E den (.tuple #[.integer k, .atom "open", Term.list (List.replicate n (.atom "term"))]) v =
      Bool.true ↔ n ≤ v.length := fun v => by
    rw [denTF_leaf ef (Or.inl rfl) hl, vT_lit ef (Or.inl rfl) hl]
    exact inT_terms_iff ef.den_term n v
  cases p
  · refine ⟨e, ?_, ?_⟩
    · unfold Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2»
      simp [getMapKeys_single, mapLookup, rp, dup_nat, Elixir.Module.Types.Descr.«tuple_new/2», rk, rd, re m hm,
        Lynx.Except.orElse, boolAtom]
    · rw [se]
      constructor
      · intro h v hv
        have := h v
        rw [sd, hv] at this
        simp only [Bool.true_and, Bool.not_eq_false'] at this
        exact (leafSem v).mp this
      · intro h v
        rw [sd]
        cases hv : denTF E den b v
        · rfl
        · simp [(leafSem v).mpr (h v hv)]
  · refine ⟨Bool.true, ?_, ⟨fun _ => sp rfl, fun _ => rfl⟩⟩
    unfold Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2»
    simp [getMapKeys_single, mapLookup, rp, Lynx.Except.orElse, boolAtom]

/-- `tuple_bdd_fetch_static/2` finds the values at an index of the tuples of a BDD, and whether some tuple has no such
index. -/
theorem bdd_fetch (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) {r : Term} (wr : Bdd (TLit E) r) (i : Nat) :
    ∃ e o, Elixir.Module.Types.Descr.«tuple_bdd_fetch_static/2» (D (n + 2)) r (.integer i) =
        .ok (.tuple #[e, boolAtom o]) ∧ E e ∧
      (∀ v₁ y v₂, v₁.length = i → denTF E den r (v₁ ++ y :: v₂) = Bool.true → den e y) ∧
      (o = Bool.true ↔ ∃ v, denTF E den r v = Bool.true ∧ v.length ≤ i) ∧
      (o = Bool.false → ∀ y, den e y → ∃ v₁ v₂, v₁.length = i ∧ denTF E den r (v₁ ++ y :: v₂) = Bool.true) := by
  obtain ⟨lines, rl, tl', sl⟩ := dnf_neg (den := den) ef.opsU ef.dopsU ef.msemZ rfl (m := n + 2) (by omega) wr
  have inR : ∀ v, denTF E den r v = Bool.true ↔ ∃ L ∈ lines, InLine den L v := fun v => by rw [denTF_bdd wr]; exact sl v
  obtain ⟨e, o, rf, he, -, long, -, short, back⟩ := fetch_lines_sem ef hn i lines tl' (.map []) Bool.false ef.none
  obtain ⟨sz, rs, ss⟩ := size_at_least ef (m := n + 2) (by omega) (Or.inr wr) (i + 1) (by omega)
  have shortIff : (∃ v, denTF E den r v = Bool.true ∧ v.length ≤ i) ↔ sz = Bool.false := by
    rw [← Bool.not_eq_true, ss]
    constructor
    · rintro ⟨v, hv, len⟩ h; have := h v hv; omega
    · intro h
      obtain ⟨v, hv⟩ := Classical.not_forall.mp h
      obtain ⟨hv, len⟩ := Classical.not_imp.mp hv
      exact ⟨v, hv, by omega⟩
  refine ⟨e, o || !sz, ?_, he, fun v₁ y v₂ len hv => ?_, ?_, fun h y hy => ?_⟩
  · unfold Elixir.Module.Types.Descr.«tuple_bdd_fetch_static/2»
    have rs' : Elixir.Module.Types.Descr.«tuple_of_size_at_least_static?/2» (D (n + 2)) (.map [(.atom "tuple", r)])
        (.integer ((i : Int) + 1)) = .ok (boolAtom sz) := by simpa using rs
    simp only [rl, rf, Lynx.Except.ok_bind, plus_one, boolAtom_false] at rf ⊢
    cases o <;> cases sz <;> simp [rs', Lynx.Except.orElse, Erlang.erlang.«not/1», boolAtom]
  · obtain ⟨L, mL, hL⟩ := (inR _).mp hv
    exact long L mL y ⟨v₁, v₂, len, hL⟩
  · rw [shortIff]
    cases o <;> cases sz <;> simp
    obtain h | ⟨L, mL, v, hv, len⟩ := short rfl
    · cases h
    · have := (shortIff.mp ⟨v, (inR v).mpr ⟨L, mL, hv⟩, len⟩); cases this
  · simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at h
    rcases back h.1 y hy with h' | ⟨L, mL, v₁, v₂, len, hL⟩
    · exact absurd h' (ef.den_none y)
    · exact ⟨v₁, v₂, len, (inR _).mpr ⟨L, mL, hL⟩⟩

/-- `tuple_fetch_element/3` on a non-empty literal: the values at an index of its tuples, and whether one is shorter. -/
theorem leaf_fetch (ef : EF nd E V den tl K) {tag : String} (g : tag = "open" ∨ tag = "closed") {l : List Term}
    (hl : ∀ e ∈ l, E e) (ne : ∃ v, InT den (tag == "closed") l v) (i : Nat) :
    ∃ e o, Elixir.Module.Types.Descr.«tuple_fetch_element/3» (Term.list l) (.integer i) (.atom tag) =
        .ok (.tuple #[e, boolAtom o]) ∧ E e ∧
      (∀ v₁ y v₂, v₁.length = i → InT den (tag == "closed") l (v₁ ++ y :: v₂) → den e y) ∧
      (o = Bool.true ↔ ∃ v, InT den (tag == "closed") l v ∧ v.length ≤ i) ∧
      (o = Bool.false → ∀ y, den e y → ∃ v₁ v₂, v₁.length = i ∧ InT den (tag == "closed") l (v₁ ++ y :: v₂)) := by
  obtain ⟨v₀, hv₀⟩ := ne
  have hfe := fetch_element tag g l i
  by_cases short : i < l.length
  · obtain ⟨l₁, x, l₂, rfl, len₁⟩ : ∃ l₁ x l₂, l = l₁ ++ x :: l₂ ∧ l₁.length = i := by
      refine ⟨l.take i, l[i]'short, l.drop (i + 1), ?_, by simp; omega⟩
      simp
    have e : (l₁ ++ x :: l₂)[i]'(by simp; omega) = x := by subst len₁; simp
    refine ⟨x, Bool.false, by rw [hfe, dite_eq_left short, e]; rfl, hl x (by simp),
      fun v₁ y v₂ len h => ((InT.split l₁ x l₂ v₁ y v₂ (by omega)).mp h).1, ⟨fun h => (by cases h), ?_⟩, fun _ y hy => ?_⟩
    · rintro ⟨v, hv, len⟩
      have := hv.length_le
      simp at this; omega
    · obtain ⟨w₁, y₀, w₂, rfl, h₁, -, h₂⟩ := (InT.mid l₁ x l₂).mp hv₀
      have lw := h₁.closed_length
      have rest := ((InT.split l₁ x l₂ w₁ y₀ w₂ (by omega)).mp hv₀).2
      exact ⟨w₁, w₂, by omega, (InT.split l₁ x l₂ w₁ y w₂ (by omega)).mpr ⟨hy, rest⟩⟩
  · rcases g with rfl | rfl
    · refine ⟨.atom "term", Bool.true, by rw [hfe]; simp [short], ef.term, fun _ y _ _ _ => ef.den_term y,
        ⟨fun _ => ⟨v₀.take l.length, InT.open_take (by simpa using hv₀), by simp; omega⟩, fun _ => rfl⟩,
        fun h => by cases h⟩
    · refine ⟨.map [], Bool.true, by rw [hfe]; simp [short], ef.none,
        fun v₁ y v₂ len h => absurd h (InT.split_closed (l := l) (v₁ := v₁) (by omega)), ⟨fun _ => ⟨v₀, hv₀, ?_⟩, fun _ => rfl⟩,
        fun h => by cases h⟩
      have := (by simpa using hv₀ : InT den Bool.true l v₀).closed_length
      omega

/-- `tuple_fetch_static/2` on a static type with a non-empty tuple field. -/
theorem static_fetch (ef : EF nd E V den tl K) {n : Nat} (hn : K + 1 ≤ n) {X : List (Term × Term)} {b : Term}
    (hb : mapLookup X (.atom "tuple") = some b) (fb : TField E b) (ne : ∃ v, denTF E den b v = Bool.true) (i : Nat) :
    ∃ e o, Elixir.Module.Types.Descr.«tuple_fetch_static/2» (D (n + 2)) (.map X) (.integer i) =
        .ok (.tuple #[e, boolAtom o]) ∧ E e ∧
      (∀ v₁ y v₂, v₁.length = i → denTF E den b (v₁ ++ y :: v₂) = Bool.true → den e y) ∧
      (o = Bool.true ↔ ∃ v, denTF E den b v = Bool.true ∧ v.length ≤ i) ∧
      (o = Bool.false → ∀ y, den e y → ∃ v₁ v₂, v₁.length = i ∧ denTF E den b (v₁ ++ y :: v₂) = Bool.true) := by
  by_cases three : ∃ k x y, b = .tuple #[k, x, y]
  · obtain ⟨k₀, x₀, y₀, e₀⟩ := three
    obtain ⟨k, tag, l, rfl, g, hl⟩ := tfield_three fb e₀
    have sem : ∀ v, denTF E den (.tuple #[.integer k, .atom tag, Term.list l]) v = Bool.true ↔
        InT den (tag == "closed") l v := fun v => by rw [denTF_leaf ef g hl, vT_lit ef g hl]
    obtain ⟨v₀, hv₀⟩ := ne
    obtain ⟨e, o, run, he, s₁, s₂, s₃⟩ := leaf_fetch ef g hl ⟨v₀, (sem v₀).mp hv₀⟩ i
    refine ⟨e, o, ?_, he, fun v₁ y v₂ len h => s₁ v₁ y v₂ len ((sem _).mp h), ?_, fun h y hy => ?_⟩
    · unfold Elixir.Module.Types.Descr.«tuple_fetch_static/2»
      simp [getMapKeys_single, hb, run]
    · rw [s₂]; simp only [sem]
    · obtain ⟨v₁, v₂, len, h⟩ := s₃ h y hy
      exact ⟨v₁, v₂, len, (sem _).mpr h⟩
  · have wb : Bdd (TLit E) b := by
      rcases fb with ⟨k, rfl⟩ | wb
      · exact absurd ⟨_, _, _, rfl⟩ three
      · exact wb
    obtain ⟨e, o, run, he, s₁, s₂, s₃⟩ := bdd_fetch (den := den) ef hn wb i
    refine ⟨e, o, ?_, he, s₁, s₂, s₃⟩
    unfold Elixir.Module.Types.Descr.«tuple_fetch_static/2»
    rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · simp [getMapKeys_single, hb, run]
    · simp [getMapKeys_single, hb, run]
    · exact absurd ⟨_, _, _, rfl⟩ three
    · simp [getMapKeys_single, hb, run]

end

end Elixir.STTDescrProofsTest.Nest

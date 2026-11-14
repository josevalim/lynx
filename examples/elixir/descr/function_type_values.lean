namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Function types hold function values: the valuation of arrows a function induces, and the emptiness of a BDD of
arrows of one arity. -/

section
variable {V : Type} {E : Term → Prop} {den : Term → V → Prop}

/-- The valuation of function literals that a function `g` induces, up to comparison: a literal holds when every
row of `g` is one its arrow allows. -/
noncomputable def valF (E : Term → Prop) (den : Term → V → Prop) (g : List (FunSem.Row V)) (t : Term) : Bool :=
  bp (∃ (k : Term) (args : List Term) (ret : Term), Term.compare (Term.fuel t (.tuple #[k, Term.list args, ret])) t (.tuple #[k, Term.list args, ret]) = .eq ∧
    (∀ a ∈ args, E a) ∧ E ret ∧ ∀ r ∈ g, FunSem.Allows (args.map den, den ret) r)

theorem valF_resp (g : List (FunSem.Row V)) : Resp (valF E den g) := by
  intro a b h
  simp only [valF]
  congr 1
  apply propext
  constructor
  · rintro ⟨k, args, ret, e, rest⟩; exact ⟨k, args, ret, Lynx.Term.compare_eq_trans (Lynx.Term.compare_eq_symm h) e, rest⟩
  · rintro ⟨k, args, ret, e, rest⟩; exact ⟨k, args, ret, Lynx.Term.compare_eq_trans h e, rest⟩

theorem valF_iff (cg : DenCongr E den) (g : List (FunSem.Row V)) {k : Term} {args : List Term} {ret : Term}
    (hargs : ∀ a ∈ args, E a) (hret : E ret) :
    valF E den g (.tuple #[k, Term.list args, ret]) = Bool.true ↔ ∀ r ∈ g, FunSem.Allows (args.map den, den ret) r := by
  simp only [valF, bp_true]
  constructor
  · rintro ⟨k', args', ret', e, hargs', hret', h⟩
    obtain ⟨b₀, b₁, b₂, eq, -, e₁, e₂⟩ := tuple3_cmp e
    simp only [Term.tuple.injEq, Array.mk.injEq, List.cons.injEq] at eq
    obtain ⟨-, rfl, rfl, -⟩ := eq
    rw [map_den_f2 cg hargs hargs' (list_cmp _ _ e₁), cg hret hret' e₂]
    exact h
  · exact fun h => ⟨k, args, ret, compare_self _, hargs, hret, h⟩

/-- Literals of arity `n` as `phi/5` and the line checks take them. -/
theorem lits_enc {n : Nat} : ∀ (pos : List Term), (∀ t ∈ pos, FunLit E n t) →
    ∃ P : List (Term × List Term × Term), pos = P.map (fun p => .tuple #[p.1, Term.list p.2.1, p.2.2]) ∧ PosOk E n P
  | [], _ => ⟨[], rfl, by simp [PosOk]⟩
  | t :: pos, h => by
    obtain ⟨k, args, ret, rfl, len, hargs, hret⟩ := h t List.mem_cons_self
    obtain ⟨P, rfl, hP⟩ := lits_enc pos fun u mu => h u (List.mem_cons_of_mem _ mu)
    refine ⟨(.integer k, args, ret) :: P, rfl, fun p mp => ?_⟩
    rcases List.mem_cons.mp mp with rfl | mp
    · exact ⟨hargs, hret, by simp only; omega⟩
    · exact hP p mp

/-- A function satisfies a line exactly when the positive arrows allow its rows and no negative arrow does. -/
theorem lineSat_valF (cg : DenCongr E den) (g : List (FunSem.Row V)) {n : Nat} (P N : List (Term × List Term × Term))
    (hP : PosOk E n P) (hN : PosOk E n N) :
    LineSat (valF E den g) (.tuple #[encP P, encP N]) ↔
      (∀ p ∈ semP den P, ∀ r ∈ g, FunSem.Allows p r) ∧ ∀ q ∈ semP den N, ¬∀ r ∈ g, FunSem.Allows q r := by
  constructor
  · rintro ⟨pos, negs, e, hp, hn⟩
    obtain ⟨el, er⟩ := line_inj e
    subst el; subst er
    refine ⟨fun p mp => ?_, fun q mq => ?_⟩
    · obtain ⟨p', mp', rfl⟩ := List.mem_map.mp mp
      exact (valF_iff cg g (hP p' mp').1 (hP p' mp').2.1).mp (hp _ (List.mem_map.mpr ⟨p', mp', rfl⟩))
    · obtain ⟨q', mq', rfl⟩ := List.mem_map.mp mq
      intro h
      have := hn _ (List.mem_map.mpr ⟨q', mq', rfl⟩)
      rw [(valF_iff cg g (hN q' mq').1 (hN q' mq').2.1).mpr h] at this
      cases this
  · rintro ⟨hp, hn⟩
    refine ⟨_, _, rfl, fun t mt => ?_, fun t mt => ?_⟩
    · obtain ⟨p, mp, rfl⟩ := List.mem_map.mp mt
      exact (valF_iff cg g (hP p mp).1 (hP p mp).2.1).mpr (hp _ (List.mem_map.mpr ⟨p, mp, rfl⟩))
    · obtain ⟨q, mq, rfl⟩ := List.mem_map.mp mt
      cases h : valF E den g (.tuple #[q.1, Term.list q.2.1, q.2.2])
      · rfl
      · exact absurd ((valF_iff cg g (hN q mq).1 (hN q mq).2.1).mp h) (hn _ (List.mem_map.mpr ⟨q, mq, rfl⟩))

/-- Lines of literals `L` of arity `n`, as `phi/5` and the line checks take them. -/
theorem lines_enc {n : Nat} {L : Term → Prop} (hL : ∀ t, L t → FunLit E n t) : ∀ (lines : List Term),
    (∀ l ∈ lines, LineOk L l) → ∃ ls : List (List (Term × List Term × Term) × List (Term × List Term × Term)),
      lines = ls.map (fun l => .tuple #[encP l.1, encP l.2]) ∧
      ∀ l ∈ ls, PosOk E n l.1 ∧ PosOk E n l.2 ∧ (∀ p ∈ l.1, L (.tuple #[p.1, Term.list p.2.1, p.2.2])) ∧
        ∀ p ∈ l.2, L (.tuple #[p.1, Term.list p.2.1, p.2.2])
  | [], _ => ⟨[], rfl, by simp⟩
  | l :: lines, h => by
    obtain ⟨pos, negs, rfl, hp, hn⟩ := h l List.mem_cons_self
    obtain ⟨P, rfl, hP⟩ := lits_enc (E := E) pos fun t mt => hL t (hp t mt)
    obtain ⟨N, rfl, hN⟩ := lits_enc (E := E) negs fun t mt => hL t (hn t mt)
    obtain ⟨ls, rfl, hls⟩ := lines_enc hL lines fun l ml => h l (List.mem_cons_of_mem _ ml)
    refine ⟨(P, N) :: ls, rfl, fun l ml => ?_⟩
    rcases List.mem_cons.mp ml with rfl | ml
    · exact ⟨hP, hN, fun p mp => hp _ (List.mem_map.mpr ⟨p, mp, rfl⟩),
        fun p mp => hn _ (List.mem_map.mpr ⟨p, mp, rfl⟩)⟩
    · exact hls l ml

/-- A BDD of arrows of arity `n` holds no function of arity `n` exactly when each of its lines is empty. -/
theorem bdd_empty_lines (cg : DenCongr E den) {n : Nat} {L : Term → Prop} (hL : ∀ t, L t → FunLit E n t) {b : Term}
    (wb : Bdd L b) :
    ∃ ls : List (List (Term × List Term × Term) × List (Term × List Term × Term)),
      Elixir.Module.Types.Descr.«bdd_to_dnf/4» (Term.list []) (Term.list []) (Term.list []) b =
        .ok (Term.list (ls.map (fun l => .tuple #[encP l.1, encP l.2]))) ∧
      (∀ l ∈ ls, PosOk E n l.1 ∧ PosOk E n l.2 ∧ (∀ p ∈ l.1, L (.tuple #[p.1, Term.list p.2.1, p.2.2])) ∧
        ∀ p ∈ l.2, L (.tuple #[p.1, Term.list p.2.1, p.2.2])) ∧
      ((∀ g : List (FunSem.Row V), (∀ r ∈ g, FunSem.ValidRow n r) → eval (valF E den g) b = Bool.false) ↔
        ∀ l ∈ ls, FunSem.LineEmpty n (semP den l.1) (semP den l.2)) := by
  obtain ⟨lines, run, hlines⟩ := dnf_lines wb L (fun _ h => h) [] [] [] (by simp) (by simp) (by simp)
  obtain ⟨ls, rfl, hls⟩ := lines_enc (E := E) hL lines hlines
  obtain ⟨lines₁, run₁, sat⟩ := dnf_sat wb [] [] []
  obtain ⟨lines₂, run₂, -, cover⟩ := nl_dnf_cover wb [] [] []
  rw [run] at run₁ run₂
  have e₁ := list_inj (Except.ok.inj run₁)
  have e₂ := list_inj (Except.ok.inj run₂)
  rw [← e₁] at sat
  rw [← e₂] at cover
  refine ⟨ls, run, hls, ⟨fun h l ml g vg allP => ?_, fun h g vg => ?_⟩⟩
  · apply Classical.byContradiction
    intro hn
    simp only [not_exists, not_and] at hn
    have ls₁ : LineSat (valF E den g) (.tuple #[encP l.1, encP l.2]) :=
      (lineSat_valF cg g l.1 l.2 (hls l ml).1 (hls l ml).2.1).mpr ⟨allP, fun q mq hq => hn q mq hq⟩
    rcases sat _ (List.mem_map.mpr ⟨l, ml, rfl⟩) with m | sat
    · simp at m
    · have := (sat _ ls₁).2.2
      rw [h g vg] at this; cases this
  · cases he : eval (valF E den g) b
    · rfl
    · obtain ⟨t, mt, lt⟩ := cover _ (by simp) (by simp) he
      obtain ⟨l, ml, rfl⟩ := List.mem_map.mp mt
      obtain ⟨allP, noN⟩ := (lineSat_valF cg g l.1 l.2 (hls l ml).1 (hls l ml).2.1).mp lt
      obtain ⟨q, mq, hq⟩ := h l ml g vg allP
      exact absurd hq (noN q mq)

theorem encP_inj : ∀ {P P' : List (Term × List Term × Term)}, encP P = encP P' → P = P'
  | [], [], _ => rfl
  | p :: P, p' :: P', h => by
    simp only [encP, List.map_cons, Term.list, Term.cons.injEq] at h
    obtain ⟨h₁, h₂⟩ := h
    obtain ⟨e₁, e₂, e₃⟩ := enc_inj h₁
    rw [encP_inj (P := P) (P' := P') h₂]
    obtain ⟨a, b, c⟩ := p
    obtain ⟨a', b', c'⟩ := p'
    simp_all
  | [], _ :: _, h => by simp [encP, Term.list] at h
  | _ :: _, [], h => by simp [encP, Term.list] at h

theorem lookup_entry {R : List (Term × Term)} {q b : Term} (h : mapLookup R q = some b) :
    ∃ e ∈ mapEntries R, compareExact (fuel q e.1) q e.1 = .eq ∧ e.2 = b := by
  rw [← mapLookup_mapEntries] at h
  simp only [mapLookup, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he, rfl⟩

/-- `fun_empty?/2` on a union of arities: no function of any arity is in it, when the seen set does not hold its
BDDs and the lines of each BDD are decided under the seen set with that BDD, from call depth `K`. -/
theorem fun_union_sem (cg : DenCongr E den) {K : Nat} (R S : List (Term × Term)) (L : Term → Nat → Term → Prop)
    (hL : ∀ b n t, L b n t → FunLit E n t)
    (hR : ∀ e ∈ mapEntries R, ∃ n : Nat, e.1 = .integer n ∧ Bdd (L e.2 n) e.2)
    (fresh : ∀ e ∈ mapEntries R, S.any (fun s => Term.compareExact (Term.fuel (.cons e.1 e.2) s.1) (.cons e.1 e.2) s.1 == .eq) = Bool.false)
    (lines : ∀ e ∈ mapEntries R, ∀ n : Nat, e.1 = .integer n → ∀ P N, PosOk E n P → PosOk E n N →
      (∀ p ∈ P, L e.2 n (.tuple #[p.1, Term.list p.2.1, p.2.2])) →
      (∀ p ∈ N, L e.2 n (.tuple #[p.1, Term.list p.2.1, p.2.2])) →
      ∃ b : Bool, (∀ m, K ≤ m → Elixir.Module.Types.Descr.«fun_line_empty?/3» (D m) (encP P) (encP N)
        (.map ((.cons e.1 e.2, .atom "true") :: S)) = .ok (boolAtom b)) ∧
        (b = Bool.true ↔ FunSem.LineEmpty n (semP den P) (semP den N))) :
    ∃ b : Bool, (∀ m, K + 2 ≤ m →
      Elixir.Module.Types.Descr.«fun_empty?/2» (D m) (.tuple #[.atom "union", .map R]) (.map S) = .ok (boolAtom b)) ∧
      (b = Bool.true ↔ ∀ (n : Nat) (g : List (FunSem.Row V)), (∀ r ∈ g, FunSem.ValidRow n r) →
        evalR R (.integer n) (valF E den g) = Bool.false) := by
  -- What each entry answers.
  let ES : Term × Term → Prop := fun e => ∀ (n : Nat), e.1 = .integer n → ∀ g : List (FunSem.Row V),
    (∀ r ∈ g, FunSem.ValidRow n r) → eval (valF E den g) e.2 = Bool.false
  let res : Term → Bool := fun t => bp (∃ e ∈ mapEntries R, t = .tuple #[e.1, e.2] ∧ ES e)
  have each : ∀ e ∈ mapEntries R, res (.tuple #[e.1, e.2]) = bp (ES e) ∧ ∀ m, K + 2 ≤ m →
      (D m).pure (.function "Elixir.Module.Types.Descr" "-fun_empty?/2-fun-1-" 1 #[.map S]) #[.tuple #[e.1, e.2]] =
        .ok (boolAtom (bp (ES e))) := by
    intro e me
    refine ⟨bp_congr ⟨fun ⟨e', me', h, es⟩ => ?_, fun h => ⟨e, me, rfl, h⟩⟩, fun m hm => ?_⟩
    · have h₀ := congrArg (fun a : Term => match a with | .tuple ⟨[x, _]⟩ => x | _ => .nil) h
      have h₁ := congrArg (fun a : Term => match a with | .tuple ⟨[_, y]⟩ => y | _ => .nil) h
      simp only at h₀ h₁
      intro n hn g vg
      rw [h₁]; exact es n (h₀ ▸ hn) g vg
    obtain ⟨n, hn, wb⟩ := hR e me
    obtain ⟨ls, dnf, hls, sem⟩ := bdd_empty_lines (E := E) cg (hL e.2 n) wb
    have ES_iff : ES e ↔ ∀ l ∈ ls, FunSem.LineEmpty n (semP den l.1) (semP den l.2) := by
      rw [← sem]
      constructor
      · exact fun h => h n hn
      · intro h n' hn' g vg
        rw [hn] at hn'
        simp only [Term.integer.injEq] at hn'
        obtain rfl : n' = n := by omega
        exact h g vg
    let resL : Term → Bool := fun t => bp (∃ l ∈ ls, t = .tuple #[encP l.1, encP l.2] ∧
      FunSem.LineEmpty n (semP den l.1) (semP den l.2))
    obtain ⟨m', rfl, hm'⟩ := succ_of_le hm
    have all := all_list (D m') "Elixir.Module.Types.Descr" "-fun_empty?/2-fun-0-"
      #[.map ((.cons e.1 e.2, .atom "true") :: S)] resL (ls.map fun l => .tuple #[encP l.1, encP l.2]) (by
        intro t mt
        obtain ⟨l, ml, rfl⟩ := List.mem_map.mp mt
        obtain ⟨hP, hN, LP, LN⟩ := hls l ml
        obtain ⟨b, rb, sb⟩ := lines e me n hn l.1 l.2 hP hN LP LN
        obtain ⟨m'', rfl, hm''⟩ := succ_of_le hm'
        rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_empty?/2-fun-0-/1».pure]
        simp only [Elixir.Module.Types.Descr.«-fun_empty?/2-fun-0-/2»]
        rw [rb m'' hm'']
        congr 2
        cases b
        · symm; refine bp_false.mpr fun ⟨l', ml', e', h⟩ => ?_
          have e'' := congrArg (fun a : Term => match a with | .tuple ⟨[x, y]⟩ => (x, y) | _ => (.nil, .nil)) e'
          simp only [Prod.mk.injEq] at e''
          rw [← encP_inj e''.1, ← encP_inj e''.2] at h
          exact absurd (sb.mpr h) (by simp)
        · symm; exact bp_true.mpr ⟨l, ml, rfl, sb.mp rfl⟩)
    have allIff : (ls.map fun l => Term.tuple #[encP l.1, encP l.2]).all resL = bp (ES e) := by
      rw [bp_congr ES_iff]
      cases h : (ls.map fun l => Term.tuple #[encP l.1, encP l.2]).all resL
      · symm; refine bp_false.mpr fun hall => ?_
        obtain ⟨t, mt, ht⟩ := List.all_eq_false.mp h
        obtain ⟨l, ml, rfl⟩ := List.mem_map.mp mt
        have : resL (.tuple #[encP l.1, encP l.2]) = Bool.true := bp_true.mpr ⟨l, ml, rfl, hall l ml⟩
        simp_all
      · symm; refine bp_true.mpr fun l ml => ?_
        have := List.all_eq_true.mp h _ (List.mem_map.mpr ⟨l, ml, rfl⟩)
        obtain ⟨l', ml', e', h'⟩ := bp_true.mp this
        have e'' := congrArg (fun a : Term => match a with | .tuple ⟨[x, y]⟩ => (x, y) | _ => (.nil, .nil)) e'
        simp only [Prod.mk.injEq] at e''
        rw [encP_inj e''.1, encP_inj e''.2]; exact h'
    simp only [Term.list] at dnf
    rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_empty?/2-fun-1-/1».pure]
    simp [Elixir.Module.Types.Descr.«-fun_empty?/2-fun-1-/2», Elixir.Module.Types.Descr.«empty_bdd_seen_key/2»,
      Erlang.erlang.«is_map_key/2», fresh e me, Term.false, Erlang.maps.«put/3»,
      Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf, all, allIff]
  have run : ∀ m, K + 2 ≤ m → Erlang.lists.«all/2» (D m)
      (.function "Elixir.Module.Types.Descr" "-fun_empty?/2-fun-1-" 1 #[.map S])
      (Term.list ((mapEntries R).map fun e => .tuple #[e.1, e.2])) =
      .ok (boolAtom (((mapEntries R).map fun e => Term.tuple #[e.1, e.2]).all res)) := fun m hm =>
    all_list _ _ _ _ res _ fun t mt => by
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mt
      rw [(each e me).2 m hm, (each e me).1]
  refine ⟨((mapEntries R).map fun e => Term.tuple #[e.1, e.2]).all res, fun m hm => ?_, ?_⟩
  · unfold Elixir.Module.Types.Descr.«fun_empty?/2»
    simpa [Erlang.maps.«to_list/1»] using run m hm
  · rw [List.all_eq_true]
    constructor
    · intro h n g vg
      cases hl : mapLookup R (.integer n) with
      | none => simp [evalR, hl]
      | some b =>
        obtain ⟨e, me, ek, rfl⟩ := lookup_entry hl
        have := h _ (List.mem_map.mpr ⟨e, me, rfl⟩)
        rw [(each e me).1, bp_true] at this
        simp only [evalR, hl, Option.elim]
        exact this n ((integer_compareExact_eq n e.1).mp ek) g vg
    · intro h t mt
      obtain ⟨e, me, rfl⟩ := List.mem_map.mp mt
      rw [(each e me).1, bp_true]
      intro n hn g vg
      have := h n g vg
      simp only [evalR, ← hn, mapLookup_of_mem_mapEntries me, Option.elim] at this
      exact this

end

end Elixir.STTDescrProofsTest.Nest

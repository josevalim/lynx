namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {E : Term → Prop}

theorem dom_lookup_of_mem : ∀ {dl : List (Term × Term)}, DomsV E dl → ∀ {d : String} {v : Term},
    (Term.atom d, v) ∈ dl → mapLookup dl (.atom d) = some v
  | [], _, _, _, me => by simp at me
  | x :: xs, dv, d, v, me => by
    obtain ⟨⟨a, ha, -⟩, -⟩ := dv.1 x List.mem_cons_self
    obtain ⟨k, f⟩ := x
    simp only at ha
    subst ha
    have dv' : DomsV E xs := ⟨fun e me => dv.1 e (List.mem_cons_of_mem _ me), (List.pairwise_cons.mp dv.2).2⟩
    rcases List.mem_cons.mp me with e | me
    · simp only [Prod.mk.injEq, Term.atom.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp [lookup_cons_atom]
    · have lt := (List.pairwise_cons.mp dv.2).1 _ me
      have ne : a ≠ d := fun h => by subst h; exact cmp_lt_ne lt rfl
      rw [lookup_cons_atom, ite_eq_right ne]
      exact dom_lookup_of_mem dv' me

theorem dom_mem_of_lookup {dl : List (Term × Term)} {d : String} {v : Term} (h : mapLookup dl (.atom d) = some v) :
    (Term.atom d, v) ∈ dl := by
  rw [mapLookup] at h
  cases e : dl.find? (fun entry => decide (compareExact (fuel (.atom d) entry.1) (.atom d) entry.1 = .eq)) with
  | none => rw [e] at h; cases h
  | some r =>
    rw [e] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have mr := List.mem_of_find?_eq_some e
    have := List.find?_some e
    simp only [decide_eq_true_eq] at this
    have e₁ : r.1 = .atom d := (compareExact_eq_atom _ _).mp (Lynx.Term.compareExact_eq_symm this)
    rw [show r = (r.1, r.2) from rfl, e₁, h] at mr
    exact mr

end

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Map types none of whose literals mention two atom keys hold the same maps with those keys swapped. -/
theorem swap_seen (ef : EF nd E V den tl K) {b : Term} {S : List (Term × Term)}
    (wb : (∃ k : Int, b = .tuple #[.integer k, .atom "open", .nil]) ∨ Bdd (fun u => MLit E u ∧ SeenNamed S u) b)
    {s c : String} (hs : (Term.atom s, Term.nil) ∉ S) (hc : (Term.atom c, Term.nil) ∉ S) (w : MW V) :
    denMF E den b (swapW s c w) = denMF E den b w := by
  rcases wb with ⟨k, rfl⟩ | wb
  · rw [denMF_top, denMF_top]
  rw [denMF_bdd (wb.mono fun _ h => h.1), denMF_bdd (wb.mono fun _ h => h.1)]
  refine eval_ext wb fun u ⟨lt, nt⟩ => ?_
  obtain ⟨k, tag, l, rfl, -, -⟩ := lt.1
  have fresh : ∀ a, (Term.atom a, Term.nil) ∉ S → mapLookup l (.atom a) = none := fun a na =>
    lookup_fresh' fun ma => na (nt k tag l rfl a ma)
  have lit : MapLitV E (.tuple #[.integer k, tag, fieldsTerm l]) := lt.1
  rw [Bool.eq_iff_iff, valM_iff ef.mopsE ef.mdopsE ef.semR lit, valM_iff ef.mopsE ef.mdopsE ef.semR lit, nsem_lit,
    nsem_lit, msem_swapW_iff (fresh s hs) (fresh c hc)]

end

section
variable {t : Term} {n : Nat}

/-- `map_to_list_static/3` on the lines of a map type: the pairs of `term()` when a line is open, otherwise the pairs of
the domains of its lines and of its atom keys. -/
theorem mtl_static3 {M : Nat} (hM : (level t (n + 1)).K + 23 ≤ M) {b : Term} (fb : MField (level t (n + 1)).E b)
    (lines : List Term) (hl : ∀ L ∈ lines, MLine (level t (n + 1)).E L ∧ ∃ w, InMLine (level t (n + 1)).den L w) :
    (∃ L ∈ lines, OpenLine L ∧ ∃ P, Elixir.Module.Types.Descr.«map_to_list_static/3» (D (M + 5)) b (Term.list lines) mtlF =
        .ok P ∧ DE (level t (n + 1)).E P ∧ ∀ p, denD P p ↔ PairPt t (n + 1) (.atom "term") (.atom "term") p) ∨
      ((∀ L ∈ lines, ¬OpenLine L) ∧ ∃ S inner,
        Elixir.Module.Types.Descr.«map_to_list_static/3» (D (M + 5)) b (Term.list lines) mtlF = .ok inner ∧
        SeenOk S ∧ ((∃ k : Int, b = .tuple #[.integer k, .atom "open", .nil]) ∨
          Bdd (fun u => MLit (level t (n + 1)).E u ∧ SeenNamed S u) b) ∧ DE (level t (n + 1)).E inner ∧
        ∀ p, denD inner p ↔ (∃ L ∈ lines, LinePairs t n L p) ∨ ∃ s, (Term.atom s, Term.nil) ∈ S ∧ AtomPair t n lines s p) := by
  have hl' : ∀ L ∈ lines, MLine (level t (n + 1)).E L := fun L m => (hl L m).1
  rcases lines_pairs (t := t) (n := n) (M := M + 3) (by omega) lines hl' with ⟨L, mL, o, run⟩ |
    ⟨acc₀, run, no, d₀, s₀⟩
  · obtain ⟨P, rP, dP, sP⟩ := mtl_pair (t := t) (n := n + 1) (level t (n + 1)).ef.term (level t (n + 1)).ef.term
      (Or.inl rfl) (Or.inl rfl) (M + 5)
    refine Or.inl ⟨L, mL, o, P, ?_, dP, sP⟩
    simp only [Elixir.Module.Types.Descr.«map_to_list_static/3», Lynx.Except.tryWith]
    simp [run, Lynx.Exception.classTerm, Lynx.Exception.reason, rP]
  · have ha : AccOk t n lines acc₀ [] acc₀ := ⟨d₀, fun p => by simp⟩
    obtain ⟨S, a, rr, hS, -, ha', named⟩ : ∃ S a, Elixir.Module.Types.Descr.«bdd_reduce/3» (D (M + 5)) b
        (.tuple #[.map [], acc₀])
        (.function "Elixir.Module.Types.Descr" "-map_to_list_static/3-fun-3-" 2 #[Term.list lines, mtlF]) =
          .ok (.tuple #[.map S, a]) ∧ SeenOk S ∧ True ∧ AccOk t n lines acc₀ S a ∧
        ((∃ k : Int, b = .tuple #[.integer k, .atom "open", .nil]) ∨
          Bdd (fun u => MLit (level t (n + 1)).E u ∧ SeenNamed S u) b) := by
      rcases fb with ⟨k, rfl⟩ | wb
      · obtain ⟨S, a, run, hS, -, -, ha'⟩ := fetch_leaf hM lines hl acc₀ (lit := .tuple #[.integer k, .atom "open", .nil])
          ⟨k, .atom "open", [], rfl, Or.inl rfl, ⟨by simp, by simp⟩⟩ [] acc₀ (by simp [SeenOk]) ha
        exact ⟨S, a, by rw [Elixir.Module.Types.Descr.«bdd_reduce/3».eq_def]; simpa using run, hS, trivial, ha',
          Or.inl ⟨k, rfl⟩⟩
      · obtain ⟨S, a, run, hS, -, ha', named⟩ := fetch_reduce hM lines hl acc₀ wb [] acc₀ (by simp [SeenOk]) ha
        exact ⟨S, a, run, hS, trivial, ha', Or.inr named⟩
    refine Or.inr ⟨no, S, a, ?_, hS, named, ha'.1, fun p => ?_⟩
    · simp only [Elixir.Module.Types.Descr.«map_to_list_static/3», Lynx.Except.tryWith]
      simp [run, rr]
    · rw [ha'.2, s₀]

end

end Elixir.STTDescrProofsTest.Nest

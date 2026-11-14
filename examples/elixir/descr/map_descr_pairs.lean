namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem foldl_first (m : Nat) (f acc : Term) (fs : List Term) (hf : f = .function "Elixir.Module.Types.Descr" "-map_descr_pairs/1-fun-0-" 2 #[]) :
    Erlang.lists.«foldl/3» (D m) f acc (Term.list fs) = Erlang.lists.«foldl_1/3» (D m) f acc (Term.list fs) := by
  subst hf
  cases fs with
  | nil => simp [Erlang.lists.«foldl/3», Erlang.lists.«foldl_1/3», Erlang.erlang.«is_function/2»]
  | cons p rest =>
    rw [Term.list_cons, Erlang.lists.«foldl_1/3».eq_def]
    simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»]

theorem kdk_field (a : String) (f : Term) : USort.KdK (.integer 1) fk (.tuple #[.atom a, f]) := by
  refine ⟨by simp [Erlang.erlang.«element/2», fk], fun x y e => ?_⟩
  have := (Term.compare_eq_atom _ _).mp (USort.c_eq_symm (show Term.compare (Term.fuel (.atom a) (.cons x y)) (.atom a) (.cons x y) = .eq from e))
  cases this

section
variable {t : Term} {n : Nat}

theorem fieldsRev_mem {fs : List Term} (h : ∀ p ∈ fs, CPair t n p) {x : Term} (hx : x ∈ fieldsRev fs) :
    ∃ (a : String) (v : Term) (o : Bool), x = .tuple #[.atom a, .tuple #[v, boolAtom o]] ∧ (level t n).E v := by
  simp only [fieldsRev, List.mem_reverse, List.mem_filter] at hx
  rcases h x hx.1 with h | ⟨ks, v, rfl, -, -⟩
  · exact h
  · simp [isF_dom] at hx

/-- `map_descr_pairs/1` of static pairs: the fields sorted by key, the last pair of each key first, and the
domains. -/
theorem descr_pairs_run {m : Nat} (hm : (level t n).K ≤ m) (fs : List Term) (h : ∀ p ∈ fs, CPair t n p) :
    ∃ R dl b, Elixir.Module.Types.Descr.«map_descr_pairs/1» (D (m + 1)) (Term.list fs) =
      .ok (.tuple #[Term.list R, fieldsTerm dl, Term.list R, fieldsTerm dl, .atom "false", boolAtom b]) ∧
      USort.SA fk R ∧ USort.Eqv fk R (fieldsRev fs) ∧ DomL t n dl ∧ DomSem t n fs dl := by
  obtain ⟨dl, b, run, hd, hs⟩ := fold_pairs hm fs [] h [] Bool.false ⟨by simp [SKL], by simp⟩
    ⟨by simp, fun s => ⟨by simp [mapLookup, DomAny], by simp [mapLookup]⟩⟩
  obtain ⟨R, rk, sr, er⟩ := USort.ukeysort_spec (κ := fk) 1 (by decide) (fieldsRev fs) (fun x hx => by
    obtain ⟨a, v, o, rfl, -⟩ := fieldsRev_mem h hx; exact kdk_field a _)
  refine ⟨R, dl, b, ?_, sr, er, hd, by simpa using hs⟩
  have init : Term.tuple #[.nil, .nil, .nil, .nil, .atom "false", .atom "false"] = accT (fieldsRev []) [] Bool.false := rfl
  simp only [List.nil_append] at run
  unfold Elixir.Module.Types.Descr.«map_descr_pairs/1»
  simp only [Lynx.Except.pure_eq_ok, Lynx.Except.ok_bind]
  rw [foldl_first _ _ _ _ rfl, init, run]
  simp only [accT, Lynx.Except.ok_bind, rk]

end

end Elixir.STTDescrProofsTest.Nest

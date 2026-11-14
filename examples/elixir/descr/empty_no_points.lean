namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop}
  {H : Prop}

/-- Types with no points are checked empty. -/
theorem descr_empty_none (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hS : FS []) {m : Nat} (hm : K ≤ m)
    {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X)
    (none : ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup X (.atom name)) p = Bool.false) :
    Elixir.Module.Types.Descr.«empty_seen?/2» (D m) (.map X) (.map []) = .ok (.atom "true") := by
  by_cases ne : X = []
  · subst ne
    simpa [boolAtom] using empty_none_seen (D m) (.map [])
  have key : ∀ name x, mapLookup X (.atom name) = some x →
      Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map []) = .ok (.atom "true") :=
    fun name x h => fieldC_empty_none ks fc hm (sX.fields name x h) (fun _ => hS) fun p ok => by
      have := none name p ok; rwa [h] at this
  have run := descr_empty_run (D m) (S := .map []) (bt := Bool.true) (bm := Bool.true) (bl := Bool.true)
    (bf := Bool.true) sX.static ne
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom] using key "tuple" x h)
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom] using key "map" x h)
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom] using key "list" x h)
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3», boolAtom] using key "fun" x h)
  have noA : (mapLookup X (.atom "atom")).isSome = Bool.false := by
    cases h : mapLookup X (.atom "atom") with
    | none => rfl
    | some x =>
      obtain ⟨p, ok, hp⟩ := atom_full sX h
      have := none "atom" p ok; rw [h, hp] at this; cases this
  have noB : (mapLookup X (.atom "bitmap")).isSome = Bool.false := by
    cases h : mapLookup X (.atom "bitmap") with
    | none => rfl
    | some x =>
      obtain ⟨p, ok, hp⟩ := bitmap_full sX h
      have := none "bitmap" p ok; rw [h, hp] at this; cases this
  rw [noA, noB] at run
  simpa [boolAtom] using run

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Emptiness of types over the structural kinds. -/

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}
  {FS : List (Term × Term) → Prop}
  {H : Prop}

/-- The emptiness check of a field, as a Boolean, for absent fields `true`. -/
theorem key_bool (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) {m : Nat} (hm : K ≤ m)
    {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) (S : List (Term × Term)) (hS : FS S) (name : String) :
    ∃ b : Bool, (∀ x, mapLookup X (.atom name) = some x →
        Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map S) = .ok (boolAtom b)) ∧
      (mapLookup X (.atom name) = none → b = Bool.true) ∧
      ∀ N, lh (.map X) < N → SafeN N S →
        ((∀ p, PtOkC TV LV MV FV name p → dn name (mapLookup X (.atom name)) p = Bool.false) → b = Bool.true) ∧
        (b = Bool.true → ∀ p, PtOkC TV LV MV FV name p → dn name (mapLookup X (.atom name)) p = Bool.false) := by
  cases hx : mapLookup X (.atom name) with
  | none => exact ⟨Bool.true, ⟨fun _ h => by simp at h, fun _ => rfl, fun _ _ _ => ⟨fun _ => rfl, fun _ p _ => dn_none _ _⟩⟩⟩
  | some x =>
    obtain ⟨b, run, ex⟩ := fieldC_empty ks fc hH hm (sX.fields name x hx) S (fun _ => hS)
    exact ⟨b, ⟨fun x' h => by simp only [Option.some.injEq] at h; subst h; exact run, fun h => by simp at h,
      fun N hN hs => ex N (by have := lh_field_le hx; omega) hs⟩⟩

theorem descr_empty_run (d : Dispatcher) {X : List (Term × Term)} (static : mapLookup X (.atom "dynamic") = none)
    (nonempty : X ≠ []) {S : Term} {bt bm bl bf : Bool}
    (ht : ∀ x, mapLookup X (.atom "tuple") = some x → Elixir.Module.Types.Descr.«tuple_empty?/2» d x S = .ok (boolAtom bt))
    (hm : ∀ x, mapLookup X (.atom "map") = some x → Elixir.Module.Types.Descr.«map_empty?/2» d x S = .ok (boolAtom bm))
    (hl : ∀ x, mapLookup X (.atom "list") = some x → Elixir.Module.Types.Descr.«list_empty?/2» d x S = .ok (boolAtom bl))
    (hf : ∀ x, mapLookup X (.atom "fun") = some x → Elixir.Module.Types.Descr.«fun_empty?/2» d x S = .ok (boolAtom bf)) :
    Elixir.Module.Types.Descr.«empty_seen?/2» d (.map X) S = .ok (boolAtom (
      !(mapLookup X (.atom "atom")).isSome && !(mapLookup X (.atom "bitmap")).isSome &&
      ((mapLookup X (.atom "tuple")).isNone || bt) && ((mapLookup X (.atom "map")).isNone || bm) &&
      ((mapLookup X (.atom "list")).isNone || bl) && ((mapLookup X (.atom "fun")).isNone || bf))) := by
  unfold Elixir.Module.Types.Descr.«empty_seen?/2»
  simp [getMapKeys_single, static, Erlang.erlang.«==/2», nonempty]
  cases ha : mapLookup X (.atom "atom") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, Lynx.Except.andAlso, boolAtom]
  | none =>
  cases hb : mapLookup X (.atom "bitmap") with
  | some _ => simp [Erlang.erlang.«is_map_key/2», any_key, ha, hb, Erlang.erlang.«not/1», Lynx.Except.andAlso, boolAtom]
  | none =>
  cases h₁ : mapLookup X (.atom "tuple") <;> cases h₂ : mapLookup X (.atom "map") <;>
    cases h₃ : mapLookup X (.atom "list") <;> cases h₄ : mapLookup X (.atom "fun") <;>
    simp [Erlang.erlang.«is_map_key/2», any_key, Erlang.erlang.«not/1», Lynx.Except.andAlso, ha, hb, h₁, h₂, h₃, h₄,
      ht, hm, hl, hf] <;>
    cases bt <;> cases bm <;> cases bl <;> cases bf <;> simp [boolAtom]

theorem names_mem {name : String} (h : name ∈ names) :
    name = "bitmap" ∨ name = "atom" ∨ name = "fun" ∨ name = "list" ∨ name = "tuple" ∨ name = "map" := by
  simp [names] at h; omega

theorem atom_full {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) {x : Term}
    (hx : mapLookup X (.atom "atom") = some x) : ∃ p, PtOkC TV LV MV FV "atom" p ∧ dn "atom" (some x) p = Bool.true := by
  obtain ⟨⟨p₀, S₀, e, -⟩, q, hq⟩ := fieldC_atom (sX.fields "atom" x hx)
  exact ⟨(0, q, fun _ => Bool.true), ⟨resp_const _, by simp, by simp, by simp, by simp, by simp⟩, by simp [dn_atom, hq]⟩

theorem bitmap_full {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) {x : Term}
    (hx : mapLookup X (.atom "bitmap") = some x) : ∃ p, PtOkC TV LV MV FV "bitmap" p ∧ dn "bitmap" (some x) p = Bool.true := by
  obtain ⟨i, lt, hi⟩ := bit_point (fieldC_bitmap (sX.fields "bitmap" x hx))
  exact ⟨(i, .nil, fun _ => Bool.true), ⟨resp_const _, fun _ => lt, by simp, by simp, by simp, by simp⟩, by simp [dn_bitmap, hi]⟩

/-- Types decide their emptiness: completely, and soundly when their function field is checked non-empty. -/
theorem descr_empty (ks : Kinds K TF LF MF TV LV MV) (fc : FunC K Fn FV FS H) (hH : H) {m : Nat} (hm : K ≤ m)
    {X : List (Term × Term)} (sX : DescrC Fn TF LF MF X) (S : List (Term × Term)) (hS : FS S) :
    ∃ b : Bool, Elixir.Module.Types.Descr.«empty_seen?/2» (D m) (.map X) (.map S) = .ok (boolAtom b) ∧
      ∀ N, lh (.map X) < N → SafeN N S →
        ((∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup X (.atom name)) p = Bool.false) → b = Bool.true) ∧
        (b = Bool.true → ∀ name p, PtOkC TV LV MV FV name p → dn name (mapLookup X (.atom name)) p = Bool.false) := by
  by_cases ne : X = []
  · subst ne
    exact ⟨Bool.true, by simpa [boolAtom] using empty_none_seen (D m) (.map S),
      fun _ _ _ => ⟨fun _ => rfl, fun _ name p _ => by simp [mapLookup, dn_none]⟩⟩
  obtain ⟨bt, rt, nt, et⟩ := key_bool ks fc hH hm sX S hS "tuple"
  obtain ⟨bm, rm, nm, em⟩ := key_bool ks fc hH hm sX S hS "map"
  obtain ⟨bl, rl, nl, el⟩ := key_bool ks fc hH hm sX S hS "list"
  obtain ⟨bf, rf, nf, efu⟩ := key_bool ks fc hH hm sX S hS "fun"
  have run := descr_empty_run (D m) (S := .map S) (bt := bt) (bm := bm) (bl := bl) (bf := bf) sX.static ne
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using rt x h)
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using rm x h)
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using rl x h)
    (fun x h => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using rf x h)
  refine ⟨_, run, fun N hN hs => ⟨fun none => ?_, fun yes name p ok => ?_⟩⟩
  · have noA : (mapLookup X (.atom "atom")).isSome = Bool.false := by
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
    rw [noA, noB, (et N hN hs).1 (none "tuple"), (em N hN hs).1 (none "map"), (el N hN hs).1 (none "list"),
      (efu N hN hs).1 (none "fun")]
    simp
  · simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isSome_eq_false_iff, Option.isNone_iff_eq_none,
      Bool.or_eq_true] at yes
    obtain ⟨⟨⟨⟨⟨hA, hB⟩, yt⟩, ym⟩, yl⟩, yf⟩ := yes
    by_cases mem : name ∈ names
    rotate_left
    · have : mapLookup X (.atom name) = none := by
        cases h : mapLookup X (.atom name) with
        | none => rfl
        | some x =>
          obtain ⟨name', m', e⟩ := sX.keys _ (by rw [h]; rfl)
          simp only [Term.atom.injEq] at e; subst e; exact absurd m' mem
      rw [this, dn_none]
    have kindCase : ∀ {b : Bool}, (mapLookup X (.atom name) = none ∨ b = Bool.true) →
        (b = Bool.true → dn name (mapLookup X (.atom name)) p = Bool.false) →
        dn name (mapLookup X (.atom name)) p = Bool.false := fun h k => by
      rcases h with h | h
      · rw [h, dn_none]
      · exact k h
    rcases names_mem mem with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hB, dn_none]
    · rw [hA, dn_none]
    · exact kindCase yf fun h => (efu N hN hs).2 h p ok
    · exact kindCase yl fun h => (el N hN hs).2 h p ok
    · exact kindCase yt fun h => (et N hN hs).2 h p ok
    · exact kindCase ym fun h => (em N hN hs).2 h p ok
end

end Elixir.STTDescrProofsTest.Nest

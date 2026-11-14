namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem tolist_one (d : Dispatcher) (x : Term) :
    Elixir.Module.Types.Descr.«map_to_list/1» d x = Elixir.Module.Types.Descr.«map_to_list/2» d x mtlF := by
  simp [Elixir.Module.Types.Descr.«map_to_list/1», mtlF]

theorem tolist_term (d : Dispatcher) (f : Term) :
    Elixir.Module.Types.Descr.«map_to_list/2» d (.atom "term") f = .ok (.atom "badmap") := by
  rw [Elixir.Module.Types.Descr.«map_to_list/2».eq_def]
  rfl

section
variable {t : Term} {n : Nat}

theorem same_tuple {a : Term} (ha : DE (level t n).E a) {y : PN t n} {w : List (level t n).V}
    (hw : ∀ Y, denD (.map Y) y ↔ TT t n Y w) : denD a y ↔ denD a (tpt w) := by
  rcases ha with rfl | ⟨Z, rfl, -⟩
  · exact ⟨fun _ => denD_term _, fun _ => denD_term _⟩
  · exact (hw Z).trans (denD_tpt w).symm

/-- Lists of a type of pairs are lists of `map_to_list/1` when its pairs are pairs of the map. -/
theorem nel_sub {P inner : Term} (dP : DE (level t (n + 1)).E P) (dI : DE (level t (n + 1)).E inner)
    (incl : ∀ y : PN t (n + 1), denD P y → denD inner y) (nil : Bool) (k k' : Int) :
    SubN t (n + 2) (lTy Bool.false k' P) (lTy nil k inner) := by
  intro q hq
  rw [lTy_den _ _ dP] at hq
  rw [lTy_den _ _ dI]
  rcases hq with ⟨h, -⟩ | ⟨hl, h⟩
  · cases h
  · exact Or.inr ⟨hl, fun v hv => ⟨fun y my => incl _ ((h v hv).1 y my), (h v hv).2⟩⟩

theorem denD_atom_pt {Y : List (Term × Term)} {v : PN t n} (hv : v.1.1 = "atom") :
    denD (.map Y) v ↔ denD (.map Y) (aPt (t := t) (n := n) v.1.2.2.1) := by
  rw [denD_aPt, denD_map, hv]
  cases mapLookup Y (.atom "atom") <;> simp [dn_none, dn_atom, amemV]

/-- The empty map type, as `empty_map/0` builds it. -/
def emptyMapT : Term := .map [(.atom "map", .tuple #[.integer (-288230376038284242), .atom "closed", .nil])]

theorem emptyMap_run : Elixir.Module.Types.Descr.«empty_map/0» = .ok emptyMapT := rfl

theorem emptyMap_field :
    MField (level t n).E (.tuple #[.integer (-288230376038284242), .atom "closed", fieldsTerm []]) :=
  mleaf_field (Or.inr (Or.inl rfl)) ⟨by simp, by simp⟩ fun k tag l e => by
    obtain ⟨e₁, e₂, -⟩ := tuple3_inj e
    simp only [Term.integer.injEq, Term.atom.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨fun _ => by omega, fun h => by simp at h⟩

theorem emptyMap_de : DE (level t n).E emptyMapT := mfused_de emptyMap_field

theorem mt_emptyMap (w : MW (level t n).V) : MT t n [(.atom "map", .tuple #[.integer (-288230376038284242), .atom "closed",
    .nil])] w ↔ w = wNone := by
  simp only [MT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left']
  rw [show (Term.nil : Term) = fieldsTerm [] from rfl, denMF_leaf (level t n).ef ⟨by simp, by simp⟩ (Or.inr (Or.inl rfl))]
  constructor
  · intro h
    funext κ
    cases κ with
    | atom s => simpa [FSem, TagSem, mapLookup, wNone] using h.atoms s
    | dom k i => simpa [TagSem, wNone] using h.doms k i
  · rintro rfl
    exact ⟨fun s => by simp [FSem, TagSem, mapLookup, wNone], fun k i => by simp [TagSem, wNone]⟩

/-- A map holding a value at some key gives `map_to_list/1` a pair. -/
theorem inner_of_value {b inner : Term} (sI : InnerSem t n b inner) {w : MW (level t (n + 1)).V}
    (hw : denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true) {κ : MKey} {x : (level t (n + 1)).V}
    (hx : w κ = some x) : ∃ p : PN t (n + 1), denD inner p := by
  cases κ with
  | atom s =>
    exact ⟨_, sI.1 w hw s x hx (aPt (t := t) (n := n) (.atom s))
      ((den_succ (atomT_de s) _).mpr ((atomT_den s _).mpr ⟨rfl, rfl⟩))⟩
  | dom kk i =>
    obtain ⟨T, -, kT⟩ := kind_run (t := t) (n := n) (domKind_mem kk) (m := (level t n).K + 23) (Nat.le_refl _)
    obtain ⟨v, -, pv⟩ := kT.wit (domKind_ne_atom kk)
    exact ⟨_, sI.2.1 w hw kk i x hx v pv⟩

theorem inner_empty_iff {b inner : Term} (sI : InnerSem t n b inner) :
    (∀ p : PN t (n + 1), ¬denD inner p) ↔
      ∀ w, denMF (level t (n + 1)).E (level t (n + 1)).den b w = Bool.true → w = wNone := by
  constructor
  · intro h w hw
    funext κ
    cases e : w κ with
    | none => rfl
    | some x => obtain ⟨p, hp⟩ := inner_of_value sI hw e; exact absurd hp (h p)
  · intro h p hp
    obtain ⟨-, -, k, x, -, w, hw, κ, wκ⟩ := sI.2.2 p hp
    rw [h w hw] at wκ
    cases wκ

theorem lTy_nil_sub {inner : Term} (dI : DE (level t (n + 1)).E inner) (nil : Bool) (k : Int) :
    SubN t (n + 2) (lTy nil k inner) nilT ↔ ∀ p : PN t (n + 1), ¬denD inner p := by
  constructor
  · intro h y hy
    let v : LV (level t (n + 2)).V := ⟨[y], nilPt (t := t) (n := n + 1)⟩
    have lv : ListVal (level t (n + 2)).tl v := ⟨by simp [v], fun h => by
      change tlD (nilPt (t := t) (n := n + 1)) at h
      simp [tlD, nilPt, bPt] at h⟩
    have hq : denD (lTy nil k inner) (lpt v lv) := by
      rw [lTy_den _ _ dI]
      refine Or.inr ⟨rfl, fun v' hv' => (dn_nil_list dI k hv').mp ((dn_nil_list dI k rfl).mpr ⟨fun y' my' => ?_, ?_⟩)⟩
      · have e : y' = y := List.mem_singleton.mp my'
        rw [e]; exact hy
      · exact nilPt_den
    have := (nilT_den _).mp (h _ hq)
    simp [lpt] at this
  · intro h q hq
    rw [lTy_den _ _ dI] at hq
    rcases hq with ⟨-, hb, h2⟩ | ⟨hl, hv⟩
    · exact (nilT_den q).mpr ⟨hb, h2⟩
    · obtain ⟨v, ⟨ne, -⟩, ev⟩ := list_val q hl
      obtain ⟨y, my⟩ := List.exists_mem_of_ne_nil v.xs ne
      exact absurd ((hv v ev).1 y my) (h _)

theorem nilT_sub_lTy {inner : Term} (dI : DE (level t (n + 1)).E inner) (nil : Bool) (k : Int) :
    SubN t (n + 2) nilT (lTy nil k inner) ↔ nil = Bool.true := by
  constructor
  · intro h
    have := (lTy_den _ _ dI _).mp (h _ (nilPt_den (t := t) (n := n + 2)))
    rcases this with ⟨h, -⟩ | ⟨hl, -⟩
    · exact h
    · simp [nilPt, bPt] at hl
  · intro h q hq
    rw [lTy_den _ _ dI]
    exact Or.inl ⟨h, (nilT_den q).mp hq⟩

/-- `map_split_keys_and_domains/1` on `term()` selects every key. -/
theorem term_split {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ rs neg ds, Elixir.Module.Types.Descr.«map_split_keys_and_domains/1» (D (m + 1)) (.atom "term") =
        .ok (splitT rs neg ds) ∧ SplitOk rs neg ds ∧ ∀ κ, SplitKey rs neg ds κ := by
  obtain ⟨T, rT, sT, -, allT⟩ := termT (level t n)
  have dT : DE (level t n).E (.map T) := Or.inr ⟨T, rfl, sT⟩
  have hU : ∀ S, mapLookup T (.atom "atom") = some (.tuple #[.atom "union", .map S]) →
      ∀ q, (mapLookup S q).isSome → ∃ s, q = .atom s := by
    intro S hS q hq
    obtain ⟨T', rT', -, hat, -, -⟩ := unfolded_term_fields
    rw [rT] at rT'; cases rT'
    rw [hat] at hS; simp at hS
  obtain ⟨rs, neg, ds, run, ok, sa, sd⟩ := split_map dT hU hm
  refine ⟨rs, neg, ds, ?_, ok, fun κ => ?_⟩
  · rw [Elixir.Module.Types.Descr.«map_split_keys_and_domains/1».eq_def]
    simp [rT, run]
  · cases κ with
    | atom s => exact (sa s).mpr (allT _)
    | dom kk i =>
      obtain ⟨K₀, -, kT⟩ := kind_run (t := t) (n := n) (domKind_mem kk) (m := (level t n).K + 23) (Nat.le_refl _)
      obtain ⟨v, -, pv⟩ := kT.wit (domKind_ne_atom kk)
      exact (sd kk i).mpr ⟨v, allT v, pv⟩

theorem lTy_mono {A B : Term} (dA : DE (level t (n + 1)).E A) (dB : DE (level t (n + 1)).E B)
    (incl : ∀ y : PN t (n + 1), denD A y → denD B y) {nA nB : Bool} (hn : nA = Bool.true → nB = Bool.true) (kA kB : Int) :
    SubN t (n + 2) (lTy nA kA A) (lTy nB kB B) := by
  intro q hq
  rw [lTy_den _ _ dA] at hq
  rw [lTy_den _ _ dB]
  rcases hq with ⟨h, hb⟩ | ⟨hl, h⟩
  · exact Or.inl ⟨hn h, hb⟩
  · exact Or.inr ⟨hl, fun v hv => ⟨fun y my => incl _ ((h v hv).1 y my), (h v hv).2⟩⟩

theorem nilT_sub_true {B : Term} (dB : DE (level t (n + 1)).E B) (kB : Int) : SubN t (n + 2) nilT (lTy Bool.true kB B) :=
  (nilT_sub_lTy dB Bool.true kB).mpr rfl

end

end Elixir.STTDescrProofsTest.Nest

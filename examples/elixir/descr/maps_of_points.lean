namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

/-- A point of the next level that is the map of some values. -/
def MapOf (p : PN t n) (w : MW (level t n).V) : Prop := ∀ (Y : List (Term × Term)), denD (.map Y) p ↔ MT t n Y w

theorem mapOf_mpt (w : MW (level t n).V) : MapOf (mpt (t := t) (n := n) w) w := fun _ => denD_mpt w

/-- Map types whose points are maps of values satisfying a condition. -/
def MapsOf (t : Term) (n : Nat) (H : Term) (Q : MW (level t n).V → Prop) : Prop :=
  DE (level t n).E H ∧ (∀ p : PN t n, denD H p → p.1.1 = "map") ∧ ∀ (p : PN t n) w, MapOf p w → (denD H p ↔ Q w)

theorem mapsOf_one (b : Term) (fb : MField (level t n).E b) :
    MapsOf t n (.map [(.atom "map", b)]) (fun w => MT t n [(.atom "map", b)] w) := by
  refine ⟨mfused_de fb, fun p hp => ?_, fun p w hw => hw _⟩
  rw [denD_map] at hp
  by_cases h : p.1.1 = "map"
  · exact h
  · simp [mapLookup, h, dn_none] at hp

theorem mapsOf_inter {A B : Term} {QA QB : MW (level t n).V → Prop} (hA : MapsOf t n A QA) (hB : MapsOf t n B QB)
    {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    ∃ C, Elixir.Module.Types.Descr.«bare_intersection/2» (D m) A B = .ok C ∧ MapsOf t n C (fun w => QA w ∧ QB w) := by
  obtain ⟨c, hc, rc, sc, -⟩ := (ef_next t n).inter hA.1 hB.1
  exact ⟨c, rc m hm, hc, fun p hp => hA.2.1 p ((sc p).mp hp).1, fun p w hw => by rw [sc, hA.2.2 p w hw, hB.2.2 p w hw]⟩

/-- `atoms_hold/3` intersects maps holding values of a type at atom keys. -/
theorem atoms_hold_run {v : Term} (hv : Static v) (he : (level t n).E v) {m : Nat} (hm : (level t n).K + 24 ≤ m) :
    ∀ (atoms : List Term), (∀ a ∈ atoms, ∃ s, a = .atom s) → ∀ (acc : Term) (Q : MW (level t n).V → Prop),
      MapsOf t n acc Q → ∃ H, Elixir.STTDescrProofsTest.«atoms_hold/3» (D m) (Term.list atoms) v acc = .ok H ∧
        MapsOf t n H (fun w => Q w ∧ ∀ s, .atom s ∈ atoms → OkAt (level t n).den v (w (.atom s)))
  | [], _, acc, Q, h => ⟨acc, by simp [Elixir.STTDescrProofsTest.«atoms_hold/3»], by simpa using h⟩
  | a :: rest, ha, acc, Q, h => by
    obtain ⟨s, rfl⟩ := ha _ List.mem_cons_self
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨k, rk, key⟩ := open_map_opt s hv m'
    have piece := mapsOf_one (t := t) (n := n) _ (mleaf_field (Or.inl rfl) (fieldsV_opt he) key)
    obtain ⟨C, rC, hC⟩ := mapsOf_inter h piece (m := m' + 1) (by omega)
    obtain ⟨H, rH, hH⟩ := atoms_hold_run hv he hm rest (fun a ma => ha a (List.mem_cons_of_mem _ ma)) C _ hC
    refine ⟨H, ?_, hH.1, hH.2.1, fun p w hw => ?_⟩
    · simp only [Term.list] at rk rH ⊢
      simp [Elixir.STTDescrProofsTest.«atoms_hold/3», rk, rC, rH]
    · rw [hH.2.2 p w hw]
      simp only [mt_open_opt he s k w]
      simp only [List.mem_cons, Term.atom.injEq]
      constructor
      · rintro ⟨⟨hq, hs⟩, hr⟩
        exact ⟨hq, fun s' hs' => hs'.elim (fun e => e ▸ hs) (hr s')⟩
      · rintro ⟨hq, hr⟩
        exact ⟨⟨hq, hr s (Or.inl rfl)⟩, fun s' m' => hr s' (Or.inr m')⟩

/-- `kinds_hold/3` intersects maps holding values of a type at the keys of kinds. -/
theorem kinds_hold_run {v : Term} (hv : Static v) (he : (level t n).E v) {m : Nat} (hm : (level t n).K + 24 ≤ m) :
    ∀ (kinds : List Term), (∀ d ∈ kinds, ∃ s ∈ domainKinds, d = .atom s) → ∀ (acc : Term) (Q : MW (level t n).V → Prop),
      MapsOf t n acc Q → ∃ H, Elixir.STTDescrProofsTest.«kinds_hold/3» (D m) (Term.list kinds) v acc = .ok H ∧
        MapsOf t n H (fun w => Q w ∧ ∀ d, .atom d ∈ kinds →
          (d = "atom" → ∀ s, OkAt (level t n).den v (w (.atom s))) ∧
            ∀ k i, domKind k = d → OkAt (level t n).den v (w (.dom k i)))
  | [], _, acc, Q, h => ⟨acc, by simp [Elixir.STTDescrProofsTest.«kinds_hold/3»], by simpa using h⟩
  | a :: rest, hk, acc, Q, h => by
    obtain ⟨d, md, rfl⟩ := hk _ List.mem_cons_self
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨k, rk, key⟩ := open_map_dom md hv he m'
    have fb : MField (level t n).E (.tuple #[.integer k, fieldsTerm (domL d v), .nil]) :=
      mleaf_field (Or.inr (Or.inr ⟨_, rfl, domsV_domL d he⟩)) (l := []) ⟨by simp, by simp⟩ key
    have piece := mapsOf_one (t := t) (n := n) _ fb
    obtain ⟨C, rC, hC⟩ := mapsOf_inter h piece (m := m' + 1) (by omega)
    obtain ⟨H, rH, hH⟩ := kinds_hold_run hv he hm rest (fun a ma => hk a (List.mem_cons_of_mem _ ma)) C _ hC
    refine ⟨H, ?_, hH.1, hH.2.1, fun p w hw => ?_⟩
    · simp only [Term.list] at rk rH ⊢
      simp [Elixir.STTDescrProofsTest.«kinds_hold/3», rk, rC, rH]
    · rw [hH.2.2 p w hw]
      simp only [mt_dom he k w, List.mem_cons, Term.atom.injEq]
      constructor
      · rintro ⟨⟨hq, hs⟩, hr⟩
        exact ⟨hq, fun d' hd' => hd'.elim (fun e => e ▸ hs) (hr d')⟩
      · rintro ⟨hq, hr⟩
        exact ⟨⟨hq, hr d (Or.inl rfl)⟩, fun d' m' => hr d' (Or.inr m')⟩

/-- `keys_hold/3`: maps holding values of a type at the keys of the given atoms and kinds. -/
theorem keys_hold_run (atoms kinds : List Term) (ha : ∀ a ∈ atoms, ∃ s, a = .atom s)
    (hk : ∀ d ∈ kinds, ∃ s ∈ domainKinds, d = .atom s) {v : Term} (hv : Static v) (he : (level t n).E v) {m : Nat}
    (hm : (level t n).K + 24 ≤ m) :
    ∃ H, Elixir.STTDescrProofsTest.«keys_hold/3» (D m) (Term.list atoms) (Term.list kinds) v = .ok H ∧
      MapsOf t n H (fun w => ∀ κ, KeysOf atoms kinds κ → OkAt (level t n).den v (w κ)) := by
  have top := mapsOf_one (t := t) (n := n) (.tuple #[.integer 61102469, .atom "open", .nil]) (Or.inl ⟨_, rfl⟩)
  obtain ⟨A, rA, hA⟩ := atoms_hold_run hv he hm atoms ha _ _ top
  obtain ⟨H, rH, hH⟩ := kinds_hold_run hv he hm kinds hk A _ hA
  refine ⟨H, by simp [Elixir.STTDescrProofsTest.«keys_hold/3», Elixir.Module.Types.Descr.«open_map/0», rA, rH],
    hH.1, hH.2.1, fun p w hw => ?_⟩
  rw [hH.2.2 p w hw]
  have tw : MT t n [(.atom "map", .tuple #[.integer 61102469, .atom "open", .nil])] w := by
    simp [MT, mapLookup, denMF_top]
  constructor
  · rintro ⟨⟨-, has⟩, hks⟩ κ hκ
    cases κ with
    | atom s =>
      rcases hκ with h | h
      · exact has s h
      · exact (hks "atom" h).1 rfl s
    | dom k i => exact (hks _ hκ).2 k i rfl
  · intro h
    refine ⟨⟨tw, fun s hs => h (.atom s) (Or.inl hs)⟩, fun d hd => ⟨fun e s => ?_, fun k i e => ?_⟩⟩
    · subst e; exact h (.atom s) (Or.inr hd)
    · subst e; exact h (.dom k i) hd

end

end Elixir.STTDescrProofsTest.Nest

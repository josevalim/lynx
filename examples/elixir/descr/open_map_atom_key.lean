namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

section
variable {t : Term} {n : Nat}

theorem sub_of_maps {A B : Term} {QA QB : MW (level t n).V → Prop} (hA : MapsOf t n A QA) (hB : MapsOf t n B QB)
    (h : ∀ w, QA w → QB w) : SubN t n A B := fun p hp => by
  obtain ⟨w, hw⟩ := pt_map p (hA.2.1 p hp)
  exact (hB.2.2 p w hw).mpr (h w ((hA.2.2 p w hw).mp hp))

theorem maps_of_sub {A B : Term} {QA QB : MW (level t n).V → Prop} (hA : MapsOf t n A QA) (hB : MapsOf t n B QB)
    (h : SubN t n A B) : ∀ w, QA w → QB w := fun w q =>
  (hB.2.2 _ w (mapOf_mpt w)).mp (h _ ((hA.2.2 _ w (mapOf_mpt w)).mpr q))

theorem some_map {C : Term} {Q : MW (level t n).V → Prop} (hC : MapsOf t n C Q)
    (ne : ¬∀ p : PN t n, ¬denD C p) : ∃ w, Q w := by
  obtain ⟨p, hp⟩ := Classical.not_forall.mp ne
  have hp := Classical.not_not.mp hp
  obtain ⟨w, hw⟩ := pt_map p (hC.2.1 p hp)
  exact ⟨w, (hC.2.2 p w hw).mp hp⟩

theorem sub_true {A B : Term} {QA QB : MW (level t n).V → Prop} (hA : MapsOf t n A QA) (hB : MapsOf t n B QB)
    (h : ∀ w, QA w → QB w) {m : Nat} (hm : (level t n).K + 23 ≤ m) :
    Elixir.Module.Types.Descr.«subtype?/2» (D m) A B = .ok (.atom "true") := by
  rw [next_sub hA.1 hB.1 hm, bp_true.mpr (sub_of_maps hA hB h)]; rfl

/-- `open_map/1` of one atom key with a field. -/
theorem single_atom (s : String) {T : Term} (b : Bool) (he : (level t n).E T) (m : Nat) :
    ∃ H, Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[.atom s, .tuple #[T, boolAtom b]]]) =
      .ok H ∧ MapsOf t n H (fun w => FieldSem (level t n).den (.tuple #[T, boolAtom b]) (w (.atom s))) := by
  have hv := (level t n).ef.static he
  cases b
  · obtain ⟨k, run, key⟩ := open_map_run s hv m
    refine ⟨_, run, mapsOf_congr (mapsOf_one _ (mleaf_field (Or.inl rfl) (fieldsV_req he) key)) fun w => ?_⟩
    rw [mt_open_at he s k w, fieldSem_mk]
    simp
  · obtain ⟨k, run, key⟩ := open_map_opt s hv m
    refine ⟨_, run, mapsOf_congr (mapsOf_one _ (mleaf_field (Or.inl rfl) (fieldsV_opt he) key)) fun w => ?_⟩
    rw [mt_open_opt he s k w, fieldSem_mk]
    simp [OkAt]

/-- `open_map/1` of one domain kind. -/
theorem single_kind {d : String} (hd : d ∈ domainKinds) {U : Term} (he : (level t n).E U) (m : Nat) :
    ∃ H, Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[Term.list [.atom d], U]]) = .ok H ∧
      MapsOf t n H (fun w => (d = "atom" → ∀ s, OkAt (level t n).den U (w (.atom s))) ∧
        ∀ k i, domKind k = d → OkAt (level t n).den U (w (.dom k i))) := by
  obtain ⟨k, run, key⟩ := open_map_dom hd ((level t n).ef.static he) he m
  have fb : MField (level t n).E (.tuple #[.integer k, fieldsTerm (domL d U), .nil]) :=
    mleaf_field (Or.inr (Or.inr ⟨_, rfl, domsV_domL d he⟩)) (l := []) ⟨by simp, by simp⟩ key
  exact ⟨_, run, mapsOf_congr (mapsOf_one _ fb) fun w => mt_dom he k w⟩

theorem ckind_open {tag : String} {fs : List Term} {s : String} {o : Option (level t n).V}
    (h : CKind (t := t) (n := n) tag fs s o) : CKind (t := t) (n := n) "open" fs s o := by
  rcases h with h | ⟨x, rfl, (h | ⟨h, -⟩)⟩
  · exact Or.inl h
  · exact Or.inr ⟨x, rfl, Or.inl h⟩
  · exact Or.inr ⟨x, rfl, Or.inr ⟨h, rfl⟩⟩

theorem csem_open {tag : String} {fs : List Term} {w : MW (level t n).V} (h : CSem (t := t) (n := n) tag fs w) :
    CSem (t := t) (n := n) "open" fs w := by
  refine ⟨fun s => ?_, fun k i => ckind_open (h.2 k i)⟩
  have := h.1 s
  unfold CAtom at this ⊢
  split at this
  · exact this
  · exact ckind_open this

theorem csem_set {tag : String} {fs : List Term} {w : MW (level t n).V} (h : CSem (t := t) (n := n) tag fs w)
    (s : String) {o : Option (level t n).V} (ho : CAtom (t := t) (n := n) tag fs s o) :
    CSem (t := t) (n := n) tag fs (setK s o w) := by
  refine ⟨fun s' => ?_, fun k i => by simpa [setK] using h.2 k i⟩
  by_cases e : s' = s
  · subst e; simpa [setK] using ho
  · have : (MKey.atom s' = MKey.atom s) ↔ False := by simp [e]
    simpa [setK, this] using h.1 s'

/-- A map of values with a key of a kind set. -/
def setD {V : Type} (k : Fin 11) (o : Option V) (w : MW V) : MW V := fun q => if q = .dom k 0 then o else w q

theorem csem_setD {tag : String} {fs : List Term} {w : MW (level t n).V} (h : CSem (t := t) (n := n) tag fs w)
    (k : Fin 11) {o : Option (level t n).V} (ho : CKind (t := t) (n := n) tag fs (domKind k) o) :
    CSem (t := t) (n := n) tag fs (setD k o w) := by
  refine ⟨fun s => by simpa [setD] using h.1 s, fun k' i => ?_⟩
  by_cases e : k' = k ∧ i = 0
  · obtain ⟨rfl, rfl⟩ := e; simpa [setD] using ho
  · have : (MKey.dom k' i = MKey.dom k 0) ↔ False := by simp only [MKey.dom.injEq]; exact ⟨fun h => e h, False.elim⟩
    simpa [setD, this] using h.2 k' i

theorem exists_domKind {d : String} (hd : d ∈ domainKinds) (ne : d ≠ "atom") : ∃ k : Fin 11, domKind k = d := by
  simp only [domainKinds, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl ne
  all_goals first
    | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩
    | exact ⟨6, rfl⟩ | exact ⟨7, rfl⟩ | exact ⟨8, rfl⟩ | exact ⟨9, rfl⟩ | exact ⟨10, rfl⟩

theorem ckind_iff {tag : String} {fs : List Term} {s : String} {U : Term}
    (dU : ∀ x, (level t n).den U x ↔ ((DomAny fs s ∧ DomMem (t := t) (n := n) fs s x) ∨ (¬DomAny fs s ∧ tag = "open")))
    (o : Option (level t n).V) : CKind (t := t) (n := n) tag fs s o ↔ OkAt (level t n).den U o := by
  cases o with
  | none => simp [CKind, OkAt]
  | some x => simp [CKind, OkAt, dU x]

end

section
variable {t : Term} {d : Nat}

theorem ctor_closed_open_core {fs : List Term} (h : ∀ p ∈ fs, CPair t (d + 1) p) {m : Nat}
    (hm : (level t (d + 1)).K + 24 ≤ m) (depth node : Term) :
    Elixir.STTDescrProofsTest.«map_constructor_closed_open:ensures/3» (D (m + 1)) (Term.list fs) depth node =
      .ok (.atom "true") := by
  obtain ⟨C, rC, hC⟩ := descr_maps (m := m) (by omega) "closed" (Or.inr rfl) fs h
  obtain ⟨O, rO, hO⟩ := descr_maps (m := m) (by omega) "open" (Or.inl rfl) fs h
  simp [Elixir.STTDescrProofsTest.«map_constructor_closed_open:ensures/3», Elixir.Module.Types.Descr.«closed_map/1»,
    Elixir.Module.Types.Descr.«open_map/1», rC, rO, sub_true hC hO (fun w q => csem_open q) (m := m + 1) (by omega)]

theorem ctor_atom_core {tag : String} (ht : tag = "open" ∨ tag = "closed") {fs : List Term}
    (h : ∀ p ∈ fs, CPair t (d + 1) p) (s : String) {m : Nat} (hm : (level t (d + 1)).K + 24 ≤ m) (depth node : Term) :
    Elixir.STTDescrProofsTest.«map_constructor_atom:ensures/5» (D (m + 1)) (.atom tag) (Term.list fs) (.atom s)
      depth node = .ok (.atom "true") := by
  obtain ⟨C, rC, hC⟩ := descr_maps (m := m) (by omega) tag ht fs h
  obtain ⟨T, b, rA, eT, iA⟩ := atom_field_run (by omega : (level t (d + 1)).K ≤ m + 1) tag ht s fs h
  obtain ⟨H, rH, hH⟩ := single_atom (t := t) (n := d + 1) s b eT m
  simp [Elixir.STTDescrProofsTest.«map_constructor_atom:ensures/5», construct_run tag ht, rC, rA, rH,
    sub_true hC hH (fun w q => (iA _).mpr (q.1 s)) (m := m + 1) (by omega)]

theorem ctor_kind_core {tag : String} (ht : tag = "open" ∨ tag = "closed") {fs : List Term}
    (h : ∀ p ∈ fs, CPair t (d + 1) p) {kind : String} (hk : kind ∈ domainKinds) (na : kind ≠ "atom") {m : Nat}
    (hm : (level t (d + 1)).K + 24 ≤ m) (depth node : Term) :
    Elixir.STTDescrProofsTest.«map_constructor_kind:ensures/5» (D (m + 1)) (.atom tag) (Term.list fs) (.atom kind)
      depth node = .ok (.atom "true") := by
  obtain ⟨C, rC, hC⟩ := descr_maps (m := m) (by omega) tag ht fs h
  obtain ⟨U, rU, eU, dU⟩ := domain_value_run (by omega : (level t (d + 1)).K ≤ m + 1) tag ht kind fs h
  obtain ⟨H, rH, hH⟩ := single_kind (t := t) (n := d + 1) hk eU m
  simp [Elixir.STTDescrProofsTest.«map_constructor_kind:ensures/5», construct_run tag ht, rC, rU, rH,
    sub_true hC hH (fun w q => ⟨fun e => absurd e na, fun k i e => by
      subst e; exact (ckind_iff dU _).mp (q.2 k i)⟩) (m := m + 1) (by omega)]

theorem not_empty_of {C : Term} {Q : MW (level t (d + 1)).V → Prop} (hC : MapsOf t (d + 1) C Q) {M : Nat}
    (hM : (level t (d + 1)).K + 23 ≤ M)
    (r : (Elixir.Module.Types.Descr.«empty?/1» (D M) C >>= fun y => Erlang.erlang.«not/1» y) = .ok (.atom "true")) :
    ∃ w, Q w := by
  rw [next_empty hC.1 hM, Lynx.Except.ok_bind] at r
  refine some_map hC fun h => ?_
  rw [bp_true.mpr h] at r
  simp [boolAtom, Erlang.erlang.«not/1»] at r

theorem sub_of_true {A B : Term} {QA QB : MW (level t (d + 1)).V → Prop} (hA : MapsOf t (d + 1) A QA)
    (hB : MapsOf t (d + 1) B QB) {M : Nat} (hM : (level t (d + 1)).K + 23 ≤ M)
    (r : Elixir.Module.Types.Descr.«subtype?/2» (D M) A B = .ok (.atom "true")) : ∀ w, QA w → QB w := by
  rw [next_sub hA.1 hB.1 hM] at r
  exact maps_of_sub hA hB (bp_true.mp (boolAtom_inj (q := Bool.true) (Except.ok.inj r)))

theorem ctor_atom_least_core {tag : String} (ht : tag = "open" ∨ tag = "closed") {fs : List Term}
    (h : ∀ p ∈ fs, CPair t (d + 1) p) (s : String) {v : Term} (ev : (level t (d + 1)).E v) (o : Bool) {m : Nat}
    (hm : (level t (d + 1)).K + 24 ≤ m)
    (r1 : (Elixir.STTDescrProofsTest.«construct/2» (D (m + 1)) (.atom tag) (Term.list fs) >>= fun x =>
      Elixir.Module.Types.Descr.«empty?/1» (D (m + 1)) x >>= fun y => Erlang.erlang.«not/1» y) = .ok (.atom "true"))
    (r2 : (Elixir.STTDescrProofsTest.«construct/2» (D (m + 1)) (.atom tag) (Term.list fs) >>= fun x =>
      Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[.atom s, .tuple #[v, boolAtom o]]]) >>=
        fun y => Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) x y) = .ok (.atom "true")) (depth node : Term) :
    Elixir.STTDescrProofsTest.«map_constructor_atom_least:ensures/7» (D (m + 1)) (.atom tag) (Term.list fs) (.atom s)
      v (boolAtom o) depth node = .ok (.atom "true") := by
  obtain ⟨C, rC, hC⟩ := descr_maps (m := m) (by omega) tag ht fs h
  obtain ⟨T, b, rA, eT, iA⟩ := atom_field_run (by omega : (level t (d + 1)).K ≤ m + 1) tag ht s fs h
  obtain ⟨H, rH, hH⟩ := single_atom (t := t) (n := d + 1) s o ev m
  rw [construct_run tag ht, rC, Lynx.Except.ok_bind] at r1 r2
  rw [rH, Lynx.Except.ok_bind] at r2
  obtain ⟨w, hw⟩ := not_empty_of hC (by omega) r1
  have inc := sub_of_true hC hH (by omega) r2
  -- every value of the field is a value of the type
  have sem : ∀ x, (level t (d + 1)).den T x → (level t (d + 1)).den v x := by
    intro x hx
    have hs := inc _ (csem_set hw s ((iA (some x)).mp ((fieldSem_mk).mpr (Or.inr ⟨x, rfl, hx⟩))))
    rw [fieldSem_mk] at hs
    simp [setK] at hs
    exact hs
  -- an optional field allows no value, which only an optional field of the type allows
  have opt : o = Bool.true ∨ b = Bool.false := by
    cases b
    · exact Or.inr rfl
    · have hs := inc _ (csem_set hw s ((iA none).mp ((fieldSem_mk).mpr (Or.inl ⟨rfl, rfl⟩))))
      rw [fieldSem_mk] at hs
      simp [setK] at hs
      exact Or.inl hs
  have sub := (level t (d + 1)).ef.subc eT ev sem (m + 1) (by omega)
  simp only [Elixir.STTDescrProofsTest.«map_constructor_atom_least:ensures/7», rA, Lynx.Except.ok_bind]
  rcases opt with rfl | rfl
  · cases b <;> simp [Erlang.erlang.«element/2», sub, boolAtom, Lynx.Except.orElse]
  · cases o <;> simp [Erlang.erlang.«element/2», sub, boolAtom, Lynx.Except.orElse, Erlang.erlang.«not/1»]

theorem ctor_kind_least_core {tag : String} (ht : tag = "open" ∨ tag = "closed") {fs : List Term}
    (h : ∀ p ∈ fs, CPair t (d + 1) p) {kind : String} (hk : kind ∈ domainKinds) (na : kind ≠ "atom") {v : Term}
    (ev : (level t (d + 1)).E v) {m : Nat} (hm : (level t (d + 1)).K + 24 ≤ m)
    (r1 : (Elixir.STTDescrProofsTest.«construct/2» (D (m + 1)) (.atom tag) (Term.list fs) >>= fun x =>
      Elixir.Module.Types.Descr.«empty?/1» (D (m + 1)) x >>= fun y => Erlang.erlang.«not/1» y) = .ok (.atom "true"))
    (r2 : (Elixir.STTDescrProofsTest.«construct/2» (D (m + 1)) (.atom tag) (Term.list fs) >>= fun x =>
      Elixir.Module.Types.Descr.«open_map/1» (D (m + 1)) (Term.list [.tuple #[Term.list [.atom kind], v]]) >>=
        fun y => Elixir.Module.Types.Descr.«subtype?/2» (D (m + 1)) x y) = .ok (.atom "true")) (depth node : Term) :
    Elixir.STTDescrProofsTest.«map_constructor_kind_least:ensures/6» (D (m + 1)) (.atom tag) (Term.list fs)
      (.atom kind) v depth node = .ok (.atom "true") := by
  obtain ⟨C, rC, hC⟩ := descr_maps (m := m) (by omega) tag ht fs h
  obtain ⟨U, rU, eU, dU⟩ := domain_value_run (by omega : (level t (d + 1)).K ≤ m + 1) tag ht kind fs h
  obtain ⟨H, rH, hH⟩ := single_kind (t := t) (n := d + 1) hk ev m
  rw [construct_run tag ht, rC, Lynx.Except.ok_bind] at r1 r2
  rw [rH, Lynx.Except.ok_bind] at r2
  obtain ⟨w, hw⟩ := not_empty_of hC (by omega) r1
  have inc := sub_of_true hC hH (by omega) r2
  obtain ⟨k, hkd⟩ := exists_domKind hk na
  subst hkd
  have sem : ∀ x, (level t (d + 1)).den U x → (level t (d + 1)).den v x := by
    intro x hx
    have hs := (inc _ (csem_setD hw k ((ckind_iff dU _).mpr (Or.inr ⟨x, rfl, hx⟩)))).2 k 0 rfl
    simp [setD, OkAt] at hs
    exact hs
  simp [Elixir.STTDescrProofsTest.«map_constructor_kind_least:ensures/6», rU,
    (level t (d + 1)).ef.subc eU ev sem (m + 1) (by omega)]

end

section
variable {t : Term} {n : Nat}

/-- The maps of `empty_map/0`: no key holds a value. -/
theorem empty_map_maps : MapsOf t n (.map [(.atom "map", .tuple #[.integer (-288230376038284242), .atom "closed", .nil])])
    (CSem (t := t) (n := n) "closed" []) := by
  have key : KeyOk (.tuple #[.integer (-288230376038284242), .atom "closed", fieldsTerm []]) := by
    intro k tag l e
    obtain ⟨e₁, e₂, -⟩ := tuple3_inj e
    simp only [Term.integer.injEq, Term.atom.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨fun _ => by decide, fun h => absurd h (by decide)⟩
  have g : TagV (level t n).E (.atom "closed") := Or.inr (Or.inl rfl)
  have sl : FieldsV (level t n).E [] := ⟨by simp, by simp⟩
  refine mapsOf_congr (mapsOf_one _ (mleaf_field g sl key)) fun w => ?_
  simp only [MT, mapLookup, List.find?_cons, compareExact_eq_atom, decide_true, Option.map_some, Option.some.injEq,
    exists_eq_left']
  rw [show (Term.nil : Term) = fieldsTerm [] from rfl, denMF_leaf (level t n).ef sl g]
  have none : ∀ (s : String) (o : Option (level t n).V), CKind (t := t) (n := n) "closed" [] s o ↔ o = none := by
    intro s o; cases o <;> simp [CKind, DomAny]
  constructor
  · intro ms
    refine ⟨fun s => ?_, fun k i => (none _ _).mpr ?_⟩
    · have := ms.atoms s
      unfold FSem at this
      simp only [mapLookup, List.find?_nil, Option.map_none, tagSem_atom] at this
      unfold CAtom
      simp only [fieldsRev, List.filter_nil, List.reverse_nil, USort.lk_nil]
      exact (none _ _).mpr (by simpa using this)
    · have := ms.doms k i; rw [tagSem_atom] at this; simpa using this
  · rintro ⟨ha, hd⟩
    refine ⟨fun s => ?_, fun k i => ?_⟩
    · have := ha s
      unfold CAtom at this
      simp only [fieldsRev, List.filter_nil, List.reverse_nil, USort.lk_nil] at this
      unfold FSem
      simp only [mapLookup, List.find?_nil, Option.map_none, tagSem_atom]
      exact Or.inr ((none _ _).mp this)
    · rw [tagSem_atom]; exact Or.inr ((none _ _).mp (hd k i))

theorem ctor_empty_core {m : Nat} (hm : (level t n).K + 24 ≤ m) :
    Elixir.STTDescrProofsTest.«map_constructor_empty:ensures/0» (D (m + 1)) = .ok (.atom "true") := by
  obtain ⟨C, rC, hC⟩ := descr_maps (t := t) (n := n) (m := m) (by omega) "closed" (Or.inr rfl) [] (by simp)
  have hE := empty_map_maps (t := t) (n := n)
  have s1 := sub_true hE hC (fun w q => q) (m := m + 1) (by omega)
  have s2 := sub_true hC hE (fun w q => q) (m := m + 1) (by omega)
  simp [Elixir.STTDescrProofsTest.«map_constructor_empty:ensures/0», Elixir.Module.Types.Descr.«empty_map/0»,
    Elixir.Module.Types.Descr.«closed_map/1», rC, Elixir.Module.Types.Descr.«equal?/2», s1, s2,
    Erlang.erlang.«==/2»]

end

theorem tag_ok {tag : Term} (h : isMember tag [.atom "open", .atom "closed"] = .atom "true") :
    ∃ s, tag = .atom s ∧ (s = "open" ∨ s = "closed") := by
  obtain ⟨c, mc, e⟩ := isMember_true h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mc
  rcases mc with rfl | rfl
  · exact ⟨"open", (compareExact_eq_atom _ _).mp e, Or.inl rfl⟩
  · exact ⟨"closed", (compareExact_eq_atom _ _).mp e, Or.inr rfl⟩

theorem ne_atom_ok {k : String} (h : Erlang.erlang.«/=/2» (.atom k) (.atom "atom") = .ok (.atom "true")) :
    k ≠ "atom" := by
  intro e; subst e; simp [Erlang.erlang.«/=/2»] at h

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

theorem pairs_domain_list (m : Nat) (ks : List Term) {v : Term} (hv : Static v) (acc : Term) :
    Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2» (D m) (.tuple #[Term.list ks, v]) acc =
      Elixir.Module.Types.Descr.«map_descr_domain/3» (D m) (Term.list ks) v acc := by
  cases ks <;> rcases hv with rfl | ⟨X, rfl, -⟩ | ⟨r, st, g, rfl⟩ <;>
    simp [Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2», Erlang.erlang.«is_list/1», Term.list]

theorem pairs_field (m : Nat) (a : String) (v : Term) (o : Bool) (acc : Term) :
    Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2» (D m) (.tuple #[.atom a, .tuple #[v, boolAtom o]]) acc =
      Elixir.Module.Types.Descr.«map_descr_pair/4» (.atom a) v (boolAtom o) acc := by
  cases o <;> simp [Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2», Erlang.erlang.«is_atom/1»,
    Erlang.erlang.«is_boolean/1», boolAtom]

/-- The state of the fold over the pairs of a map constructor: the field pairs, newest first, and the domains. -/
def accT (F : List Term) (dl : List (Term × Term)) (b : Bool) : Term :=
  .tuple #[Term.list F, fieldsTerm dl, Term.list F, fieldsTerm dl, .atom "false", boolAtom b]

theorem em' (p : Prop) : ¬p ∨ p := (Classical.em p).symm

theorem step_field (m : Nat) (a : String) {v : Term} (hv : Static v) (o : Bool) (F : List Term)
    (dl : List (Term × Term)) (b : Bool) : ∃ b' : Bool,
    Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2» (D m) (.tuple #[.atom a, .tuple #[v, boolAtom o]])
      (accT F dl b) = .ok (accT (.tuple #[.atom a, .tuple #[v, boolAtom o]] :: F) dl b') := by
  rw [pairs_field]
  cases b <;> cases o <;>
    simp [Elixir.Module.Types.Descr.«map_descr_pair/4», accT, split_static hv, boolAtom, Lynx.Except.orElse,
      Erlang.erlang.«==/2»] <;>
    first
    | exact ⟨Bool.false, rfl⟩
    | exact ⟨Bool.true, rfl⟩
    | exact em' _
    | (split <;> first | exact ⟨Bool.true, rfl⟩ | exact ⟨Bool.false, rfl⟩)

theorem lk_spec {κ : Term → Term} {s z : Term} {A : List Term} (h : USort.lk κ s A = some z) :
    z ∈ A ∧ Term.compare (Term.fuel (κ z) s) (κ z) s = .eq := by
  induction A with
  | nil => simp at h
  | cons y ys ih =>
    by_cases e : Term.compare (Term.fuel (κ y) s) (κ y) s = .eq
    · simp [USort.lk_cons, e] at h; subst h; simp [e]
    · simp [USort.lk_cons, e] at h; have := ih h; exact ⟨by simp [this.1], this.2⟩

theorem atom_kdu (s : String) : USort.KdU (.atom s) := by
  intro a b e
  have := (Term.compare_eq_atom _ _).mp (USort.c_eq_symm e)
  cases this

/-- `lists:usort/1` of atoms sorts them strictly, keeping the same atoms. -/
theorem usort_atoms (ks : List Term) (ha : ∀ k ∈ ks, ∃ s, k = .atom s) :
    ∃ R, Erlang.lists.«usort/1» (Term.list ks) = .ok (Term.list R) ∧ SAK R ∧ ∀ k, k ∈ R ↔ k ∈ ks := by
  obtain ⟨R, run, sr, er⟩ := USort.usort_spec ks (fun x hx => by obtain ⟨s, rfl⟩ := ha x hx; exact atom_kdu s)
  refine ⟨R, run, sr, fun k => ⟨fun hk => USort.mem_of_eqv sr.ne er hk, fun hk => ?_⟩⟩
  obtain ⟨s, rfl⟩ := ha k hk
  obtain ⟨z, hz⟩ := USort.lk_some (κ := fun x => x) hk (Term.compare_self _)
  have hz' : USort.lk (fun x => x) (.atom s) R = some z := (er _).trans hz
  obtain ⟨mz, ez⟩ := lk_spec hz'
  have := (Term.compare_eq_atom _ _).mp ez
  subst this
  exact mz

section
variable {t : Term} {n : Nat}

theorem is_list_list (ks : List Term) : Erlang.erlang.«is_list/1» (Term.list ks) = .ok (.atom "true") := by
  cases ks <;> rfl

/-- A domain pair joins its value into the domains at its kinds. -/
theorem step_domain {m : Nat} (hm : (level t n).K ≤ m) (ks : List Term) (hks : ∀ k ∈ ks, ∃ s, k = .atom s)
    {v : Term} (hv : (level t n).E v) (F : List Term) (dl : List (Term × Term)) (hd : DomL t n dl) (b : Bool) :
    ∃ dl', Elixir.Module.Types.Descr.«-map_descr_pairs/1-fun-0-/2» (D m) (.tuple #[Term.list ks, v]) (accT F dl b) =
      .ok (accT F dl' b) ∧ DomL t n dl' ∧ (∀ e ∈ dl', e.1 ∈ dl.map Prod.fst ∨ e.1 ∈ ks) ∧
      ∀ s, ((mapLookup dl' (.atom s)).isNone ↔ (mapLookup dl (.atom s)).isNone ∧ Term.atom s ∉ ks) ∧
        ∀ U', mapLookup dl' (.atom s) = some U' → ∀ x, (level t n).den U' x ↔
          ((∃ U, mapLookup dl (.atom s) = some U ∧ (level t n).den U x) ∨ (Term.atom s ∈ ks ∧ (level t n).den v x)) := by
  have sv := (level t n).ef.static hv
  obtain ⟨R, ru, sr, mr⟩ := usort_atoms ks hks
  obtain ⟨dl', run, hd', keys, sem⟩ := mpd_run hm hv (dl.length + R.length) dl R (Nat.le_refl _) hd sr
    (fun k hk => hks k ((mr k).mp hk))
  refine ⟨dl', ?_, hd', fun e he => ?_, fun s => ?_⟩
  · rw [pairs_domain_list m ks sv]
    simp [Elixir.Module.Types.Descr.«map_descr_domain/3», accT, split_static sv,
      Elixir.Module.Types.Descr.«map_put_domain/3», is_list_list, ru, run, Lynx.Except.orElse]
  · rcases keys e he with h | h
    · exact Or.inl h
    · exact Or.inr ((mr _).mp h)
  · have := sem s
    simp only [mr] at this
    exact this

end

/-- The key of a pair of a map constructor. -/
def fk (x : Term) : Term :=
  match x with
  | .tuple es => es[0]?.getD .nil
  | _ => .nil

/-- Field pairs, with an atom key. -/
def isF (p : Term) : Bool :=
  match fk p with
  | .atom _ => Bool.true
  | _ => Bool.false

/-- The field pairs of a list of pairs, newest first. -/
def fieldsRev (P : List Term) : List Term := (P.filter isF).reverse

/-- Some domain pair names a kind. -/
def DomAny (P : List Term) (s : String) : Prop := ∃ ks v, Term.tuple #[Term.list ks, v] ∈ P ∧ Term.atom s ∈ ks

section
variable {t : Term} {n : Nat}

/-- Pairs of map constructors of a level: fields of atom keys and domains of kinds. -/
def CPair (t : Term) (n : Nat) (p : Term) : Prop :=
  (∃ (a : String) (v : Term) (o : Bool), p = .tuple #[.atom a, .tuple #[v, boolAtom o]] ∧ (level t n).E v) ∨
    ∃ ks v, p = .tuple #[Term.list ks, v] ∧ (∀ k ∈ ks, ∃ s ∈ domainKinds, k = .atom s) ∧ (level t n).E v

/-- A value of the types that some domain pair gives a kind. -/
def DomMem (P : List Term) (s : String) (x : (level t n).V) : Prop :=
  ∃ ks v, Term.tuple #[Term.list ks, v] ∈ P ∧ Term.atom s ∈ ks ∧ (level t n).den v x

/-- Domains holding, at each kind, the union of the types of the pairs naming it. -/
def DomSem (t : Term) (n : Nat) (P : List Term) (dl : List (Term × Term)) : Prop :=
  (∀ e ∈ dl, ∃ s ∈ domainKinds, e.1 = .atom s) ∧
  ∀ s, ((mapLookup dl (.atom s)).isNone ↔ ¬DomAny P s) ∧
    ∀ U, mapLookup dl (.atom s) = some U → ∀ x, (level t n).den U x ↔ DomMem (t := t) (n := n) P s x

theorem isF_field (a : String) (f : Term) : isF (.tuple #[.atom a, f]) = Bool.true := rfl

theorem isF_dom (ks : List Term) (v : Term) : isF (.tuple #[Term.list ks, v]) = Bool.false := by
  cases ks <;> rfl

theorem dom_tuple_inj {ks ks' : List Term} {v v' : Term}
    (h : Term.tuple #[Term.list ks', v'] = .tuple #[Term.list ks, v]) : ks' = ks ∧ v' = v := by
  simp only [Term.tuple.injEq] at h
  have e₀ := congrArg (fun a : Array Term => a[0]?) h
  have e₁ := congrArg (fun a : Array Term => a[1]?) h
  simp at e₀ e₁
  exact ⟨list_inj e₀, e₁⟩

theorem field_ne_dom (a : String) (f : Term) (ks : List Term) (v : Term) :
    Term.tuple #[.atom a, f] ≠ .tuple #[Term.list ks, v] := by
  intro h
  simp only [Term.tuple.injEq] at h
  have e₀ := congrArg (fun a : Array Term => a[0]?) h
  simp at e₀
  cases ks <;> simp [Term.list] at e₀

theorem fold_pairs {m : Nat} (hm : (level t n).K ≤ m) : ∀ (rest P : List Term), (∀ p ∈ rest, CPair t n p) →
    ∀ (dl : List (Term × Term)) (b : Bool), DomL t n dl → DomSem t n P dl →
    ∃ dl' b', Erlang.lists.«foldl_1/3» (D (m + 1)) (.function "Elixir.Module.Types.Descr" "-map_descr_pairs/1-fun-0-" 2 #[])
        (accT (fieldsRev P) dl b) (Term.list rest) = .ok (accT (fieldsRev (P ++ rest)) dl' b') ∧
      DomL t n dl' ∧ DomSem t n (P ++ rest) dl'
  | [], P, _, dl, b, hd, hs => ⟨dl, b, by simp [Erlang.lists.«foldl_1/3»], hd, by simpa using hs⟩
  | p :: rest, P, hr, dl, b, hd, hs => by
    rcases hr p (by simp) with ⟨a, v, o, rfl, hv⟩ | ⟨ks, v, rfl, hks, hv⟩
    · obtain ⟨b', st⟩ := step_field m a ((level t n).ef.static hv) o (fieldsRev P) dl b
      have e : fieldsRev (P ++ [Term.tuple #[.atom a, .tuple #[v, boolAtom o]]]) =
          .tuple #[.atom a, .tuple #[v, boolAtom o]] :: fieldsRev P := by
        unfold fieldsRev
        rw [List.filter_append, List.filter_cons, isF_field]
        simp
      have hs' : DomSem t n (P ++ [Term.tuple #[.atom a, .tuple #[v, boolAtom o]]]) dl := by
        refine ⟨hs.1, fun s => ?_⟩
        have nd : ∀ ks' v', Term.tuple #[Term.list ks', v'] ∈ P ++ [Term.tuple #[.atom a, .tuple #[v, boolAtom o]]] ↔
            Term.tuple #[Term.list ks', v'] ∈ P := by
          intro ks' v'
          simp only [List.mem_append, List.mem_singleton, or_iff_left_iff_imp]
          intro h; exact absurd h.symm (field_ne_dom a _ ks' v')
        simp only [DomAny, DomMem, nd]
        exact hs.2 s
      obtain ⟨dl', b'', run, hd', hs''⟩ := fold_pairs hm rest _ (fun q hq => hr q (by simp [hq])) dl b' hd hs'
      refine ⟨dl', b'', ?_, hd', by simpa using hs''⟩
      rw [Term.list_cons, Erlang.lists.«foldl_1/3».eq_def]
      simp only [D, Erlang.program.«Elixir.Module.Types.Descr:-map_descr_pairs/1-fun-0-/2».pure]
      simp only [st, Lynx.Except.ok_bind]
      rw [← e]
      simpa using run
    · have hks' : ∀ k ∈ ks, ∃ s, k = .atom s := fun k hk => by obtain ⟨s, -, rfl⟩ := hks k hk; exact ⟨s, rfl⟩
      obtain ⟨dl', st, hd', keys, sem⟩ := step_domain hm ks hks' hv (fieldsRev P) dl hd b
      have e : fieldsRev (P ++ [Term.tuple #[Term.list ks, v]]) = fieldsRev P := by
        simp [fieldsRev, isF_dom]
      have hs' : DomSem t n (P ++ [Term.tuple #[Term.list ks, v]]) dl' := by
        refine ⟨fun e he => ?_, fun s => ⟨?_, fun U' hU' x => ?_⟩⟩
        · rcases keys e he with h | h
          · obtain ⟨e', he', hee⟩ := List.mem_map.mp h; rw [← hee]; exact hs.1 e' he'
          · obtain ⟨s, ms, hs⟩ := hks _ h; exact ⟨s, ms, hs⟩
        · rw [(sem s).1, (hs.2 s).1]
          simp only [DomAny, List.mem_append, List.mem_singleton]
          constructor
          · rintro ⟨h1, h2⟩ ⟨ks', v', h3 | h3, h4⟩
            · exact h1 ⟨ks', v', h3, h4⟩
            · obtain ⟨rfl, rfl⟩ := dom_tuple_inj h3; exact h2 h4
          · intro h
            exact ⟨fun ⟨ks', v', h3, h4⟩ => h ⟨ks', v', Or.inl h3, h4⟩, fun h4 => h ⟨ks, v, Or.inr rfl, h4⟩⟩
        · rw [(sem s).2 U' hU' x]
          simp only [DomMem, List.mem_append, List.mem_singleton]
          constructor
          · rintro (⟨U, hU, hx⟩ | ⟨h4, hx⟩)
            · obtain ⟨ks', v', h3, h4, h5⟩ := ((hs.2 s).2 U hU x).mp hx
              exact ⟨ks', v', Or.inl h3, h4, h5⟩
            · exact ⟨ks, v, Or.inr rfl, h4, hx⟩
          · rintro ⟨ks', v', h3 | h3, h4, h5⟩
            · left
              cases hl : mapLookup dl (.atom s) with
              | none =>
                exact absurd ⟨ks', v', h3, h4⟩ (((hs.2 s).1).mp (by simp [hl]))
              | some U => exact ⟨U, rfl, ((hs.2 s).2 U hl x).mpr ⟨ks', v', h3, h4, h5⟩⟩
            · obtain ⟨rfl, rfl⟩ := dom_tuple_inj h3; exact Or.inr ⟨h4, h5⟩
      obtain ⟨dl'', b'', run, hd'', hs''⟩ := fold_pairs hm rest _ (fun q hq => hr q (by simp [hq])) dl' b hd' hs'
      refine ⟨dl'', b'', ?_, hd'', by simpa using hs''⟩
      rw [Term.list_cons, Erlang.lists.«foldl_1/3».eq_def]
      simp only [D, Erlang.program.«Elixir.Module.Types.Descr:-map_descr_pairs/1-fun-0-/2».pure]
      simp only [st, Lynx.Except.ok_bind]
      rw [← e]
      simpa using run

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Fusing element types of the next level. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Tuple fields that are 3-tuples are leaves: the top leaf or tuple literals. -/
theorem tfield_three {x a b c : Term} (fx : TField E x) (h : x = .tuple ⟨[a, b, c]⟩) :
    ∃ (k : Int) (tag : String) (l : List Term), x = .tuple #[.integer k, .atom tag, Term.list l] ∧
      (tag = "open" ∨ tag = "closed") ∧ (∀ e ∈ l, E e) := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact ⟨k, "open", [], rfl, Or.inl rfl, by simp⟩
  rcases wx.shape with rfl | rfl | ⟨k, y, z, rfl⟩ | ⟨h', lit, c', u, d, rfl⟩
  · cases h
  · cases h
  · obtain ⟨⟨⟨k', tag, l, e, g, els⟩, -⟩, key⟩ := Bdd.leaf_iff.mp wx
    exact ⟨k', tag, l, e, g, els⟩
  · simp at h

theorem denTF_leaf (ef : EF nd E V den tl K) {k : Int} {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed")
    (hl : ∀ e ∈ l, E e) (v : List V) :
    denTF E den (.tuple #[.integer k, .atom tag, Term.list l]) v = valT E den v (.tuple #[.integer k, .atom tag, Term.list l]) := by
  by_cases top : tag = "open" ∧ l = []
  · obtain ⟨rfl, rfl⟩ := top
    have : valT E den v (.tuple #[.integer k, .atom "open", Term.list []]) = Bool.true := by
      rw [vT_lit ef g hl]
      cases v <;> simp [InT]
    rw [this]; exact denTF_top _ _
  · have nt : isOpenTop (.tuple #[.integer k, .atom tag, Term.list l]) = Bool.false := by
      cases l with
      | nil =>
        have : tag ≠ "open" := fun e => top ⟨e, rfl⟩
        simp only [Term.list]
        unfold isOpenTop
        split
        · rename_i heq; simp at heq; exact absurd heq.2 this
        · rfl
      | cons _ _ => simp [isOpenTop, Term.list]
    simp [denTF, denO, nt]

/-- A single tuple leaf, as a type of the next level. -/
theorem fused_de {k : Int} {tag : String} {l : List Term} (g : tag = "open" ∨ tag = "closed") (hl : ∀ e ∈ l, E e)
    (key : KeyOk (.tuple #[.integer k, .atom tag, Term.list l])) :
    DE E (.map [(.atom "tuple", .tuple #[.integer k, .atom tag, Term.list l])]) := by
  refine Or.inr ⟨_, rfl, fun q h => ?_, fun name w h => ?_⟩
  · simp only [mapLookup, List.find?_cons, List.find?_nil] at h
    by_cases e : compareExact (fuel q (.atom "tuple")) q (.atom "tuple") = .eq
    · exact ⟨"tuple", by simp [names], (compareExact_eq_atom _ _).mp e⟩
    · simp [e] at h
  · simp only [mapLookup, List.find?_cons, List.find?_nil, compareExact_eq_atom, Term.atom.injEq] at h
    by_cases e : name = "tuple"
    · subst e
      simp at h
      subst h
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))))
      by_cases top : tag = "open" ∧ l = []
      · obtain ⟨rfl, rfl⟩ := top; exact Or.inl ⟨k, rfl⟩
      · refine Or.inr (Bdd.leaf_iff.mpr ⟨⟨⟨k, tag, l, rfl, g, hl⟩, fun ⟨k', e⟩ => top ?_⟩, key⟩)
        simp only [Term.tuple.injEq] at e
        have e₁ := congrArg (fun a : Array Term => a[1]?) e
        have e₂ := congrArg (fun a : Array Term => a[2]?) e
        simp [list_eq_nil] at e₁ e₂
        exact ⟨e₁, e₂⟩
    · simp [e] at h

theorem single_other {A : List (Term × Term)} {x : Term} (size : Erlang.erlang.«map_size/1» (.map A) = .ok (.integer 1))
    (hx : mapLookup A (.atom "tuple") = some x) {name : String} (hn : name ≠ "tuple") : mapLookup A (.atom name) = none := by
  cases h : mapLookup A (.atom name) with
  | none => rfl
  | some y => exact absurd ((compareExact_eq_atom _ _).mp (size_one_keys size h hx)) (by simpa using hn)

/-- The fused single tuple leaf holds the values of both single tuple leaves. -/
theorem fused_sem (ef : EF nd E V den tl K) {A B : List (Term × Term)} {kA kB k : Int} {t : String} {lA lB l : List Term}
    (g : t = "open" ∨ t = "closed") (hA : ∀ e ∈ lA, E e) (hB : ∀ e ∈ lB, E e) (hl : ∀ e ∈ l, E e)
    (tA : mapLookup A (.atom "tuple") = some (.tuple #[.integer kA, .atom t, Term.list lA]))
    (sA : Erlang.erlang.«map_size/1» (.map A) = .ok (.integer 1))
    (tB : mapLookup B (.atom "tuple") = some (.tuple #[.integer kB, .atom t, Term.list lB]))
    (sB : Erlang.erlang.«map_size/1» (.map B) = .ok (.integer 1))
    (sem : ∀ w, InT den (t == "closed") l w ↔ InT den (t == "closed") lA w ∨ InT den (t == "closed") lB w)
    (v : PtD E den tl (FVal E den)) :
    denD (.map [(.atom "tuple", .tuple #[.integer k, .atom t, Term.list l])]) v ↔ denD (.map A) v ∨ denD (.map B) v := by
  obtain ⟨⟨name, p⟩, m, ok⟩ := v
  simp only [denD_map]
  by_cases hn : name = "tuple"
  · subst hn
    obtain ⟨w, hw⟩ := ok.2.2.2.1 rfl
    have one : mapLookup [(.atom "tuple", .tuple #[.integer k, .atom t, Term.list l])] (.atom "tuple") =
        some (.tuple #[.integer k, .atom t, Term.list l]) := by simp [mapLookup]
    rw [one, tA, tB, dn_tupleT hw, dn_tupleT hw, dn_tupleT hw, denTF_leaf ef g hl, denTF_leaf ef g hA,
      denTF_leaf ef g hB, vT_fused ef (k₁ := kA) (k₂ := kB) g g hA hB hl sem, Bool.or_eq_true]
  · have none : mapLookup [(.atom "tuple", .tuple #[.integer k, .atom t, Term.list l])] (.atom name) = none := by
      simp [mapLookup, hn]
    rw [none, single_other sA tA hn, single_other sB tB hn]
    simp [dn_none]

end

end Elixir.STTDescrProofsTest.Nest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The structural kinds of types (lists, tuples, maps): what each provides to the types holding them. -/

/-- A field, when an operation keeps it. -/
def keptO (name : String) (w : Term) : Option Term := if kept (.atom name, w) then some w else none

/-- A structural kind `name`, with fields `F` and points whose valuations `Val` come from values: plain and optimized
operations hold the points they should, and emptiness is exact under seen sets of higher BDDs, at call depths from
`K`. Plain operations keep literal heights, except differences by the empty field. -/
structure KindOk (K : Nat) (name : String) (F : Term → Prop) (Val : (Term → Bool) → Prop) : Prop where
  resp : ∀ ρ, Val ρ → Resp ρ
  wit : ∃ ρ, Val ρ
  top : ∀ t, TopAt name t → F t ∧ lh t = 0 ∧ ∀ p : Point, Val p.2.2 → dn name (some t) p = Bool.true
  congr : ∀ {x x'}, F x → F x' → Term.compare (Term.fuel x x') x x' = .eq → ∀ p : Point, Val p.2.2 →
    dn name (some x) p = dn name (some x') p
  union : ∀ {x y}, F x → F y → ∃ w, (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_union/3» (D m) (.atom name) x y = .ok w) ∧
    F w ∧ (∀ p : Point, Val p.2.2 → dn name (some w) p = (dn name (some x) p || dn name (some y) p)) ∧
    lh w ≤ max (lh x) (lh y)
  inter : ∀ {x y}, F x → F y → ∃ w,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_intersection/3» (D m) (.atom name) x y = .ok w) ∧
    (kept (.atom name, w) = Bool.true → F w ∧ lh w ≤ max (lh x) (lh y)) ∧
    ∀ p : Point, Val p.2.2 → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p)
  diff : ∀ {x y}, F x → F y → ∃ w,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«bare_difference/3» (D m) (.atom name) x y = .ok w) ∧
    (kept (.atom name, w) = Bool.true → F w ∧ lh w ≤ max (lh x) (lh y)) ∧
    ∀ p : Point, Val p.2.2 → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p)
  opt_union : ∀ {x y} (S : List (Term × Term)) {m}, F x → F y → K ≤ m → ∃ w,
    Elixir.Module.Types.Descr.«opt_union/4» (D m) (.atom name) x y (.map S) = .ok w ∧ F w ∧
    ∀ p : Point, Val p.2.2 → dn name (some w) p = (dn name (some x) p || dn name (some y) p)
  opt_inter : ∀ {x y} (S : List (Term × Term)) {m}, F x → F y → K ≤ m → ∃ w,
    Elixir.Module.Types.Descr.«opt_intersection/4» (D m) (.atom name) x y (.map S) = .ok w ∧
    (kept (.atom name, w) = Bool.true → F w) ∧
    ∀ p : Point, Val p.2.2 → dn name (keptO name w) p = (dn name (some x) p && dn name (some y) p)
  opt_diff : ∀ {x y} (S : List (Term × Term)) {m}, F x → F y → K ≤ m → ∃ w,
    Elixir.Module.Types.Descr.«opt_difference/4» (D m) (.atom name) x y (.map S) = .ok w ∧
    (kept (.atom name, w) = Bool.true → F w) ∧
    ∀ p : Point, Val p.2.2 → dn name (keptO name w) p = (dn name (some x) p && !dn name (some y) p)
  empty : ∀ {x} (S : List (Term × Term)), F x → ∃ b : Bool,
    (∀ m, K ≤ m → Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom name) x (.map S) = .ok (boolAtom b)) ∧
    ∀ N, lh x < N → SafeN N S → (b = Bool.true ↔ ∀ p : Point, Val p.2.2 → dn name (some x) p = Bool.false)

theorem keptO_true {name : String} {w : Term} (h : kept (.atom name, w) = Bool.true) : keptO name w = some w := by
  simp [keptO, h]

theorem keptO_false {name : String} {w : Term} (h : kept (.atom name, w) = Bool.false) : keptO name w = none := by
  simp [keptO, h]

/-- Fields dropped from BDD kinds are the empty BDD. -/
theorem dropped_bdd {w : Term} (h : kept (.atom "x", w) = Bool.false) (nz : w ≠ .integer 0) : w = .atom "bdd_bot" := by
  simp only [kept, Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd ((compareExact_eq_integer _ _).mp h) nz
  · exact (compareExact_eq_atom _ _).mp h

theorem kept_name {name name' : String} (w : Term) : kept (.atom name, w) = kept (.atom name', w) := rfl

theorem kept_ne_bot {name : String} {w : Term} (h : kept (.atom name, w) = Bool.true) : w ≠ .atom "bdd_bot" := by
  rintro rfl; simp [kept] at h

theorem tuple_cmp_top {k b : Term} (h : Term.compare (Term.fuel (.tuple #[k, .atom "open", .nil]) b) (.tuple #[k, .atom "open", .nil]) b = .eq) :
    ∃ k', b = .tuple #[k', .atom "open", .nil] := by
  cases b <;> rw [compare_step] at h <;> simp [Compare.compareStep] at h
  rename_i ys
  obtain ⟨l⟩ := ys
  match l, h with
  | [k', x, y], h =>
    simp [List.compareLex_cons_cons, Ordering.then_eq_eq] at h
    obtain ⟨-, hx, hy, -⟩ := h
    subst hy
    have hx' := (compare_eq_atom _ _).mp (Lynx.Term.compare_eq_symm hx)
    subst hx'
    exact ⟨k', rfl⟩
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h
  | _ :: _ :: _ :: _ :: _, h => simp at h

/-- Open fields mean the same up to comparison. -/
theorem denO_congr {ok : Term → Prop} (okNot : ∀ t, ok t → ¬IsTop t) {x x' : Term} (fx : OField ok x)
    (fx' : OField ok x') (e : Term.compare (Term.fuel x x') x x' = .eq) {ρ : Term → Bool} (resp : Resp ρ) : denO x ρ = denO x' ρ := by
  rcases fx with ⟨k, rfl⟩ | wx
  · obtain ⟨k', rfl⟩ := tuple_cmp_top e
    rw [denO_top, denO_top]
  rcases fx' with ⟨k', rfl⟩ | wx'
  · obtain ⟨k, rfl⟩ := tuple_cmp_top (Lynx.Term.compare_eq_symm e)
    obtain ⟨k'', rfl⟩ := leaf_int wx
    exact absurd ⟨_, rfl⟩ (okNot _ (Bdd.leaf_iff.mp wx))
  rw [denO_bdd okNot wx, denO_bdd okNot wx', eval_congr_cmp wx resp e]

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem dn_tupleT {x : Term} {p : Point} {v : List V} (e : p.2.2 = valT E den v) :
    dn "tuple" (some x) p = denTF E den x v := by
  rw [dn_tuple, e]; rfl

theorem tfield_nz {w : Term} (fw : TField E w) : w ≠ .integer 0 := by
  rcases fw with ⟨k, rfl⟩ | ww
  · simp
  · exact bdd_ne_zero ww

/-- Tuples are a structural kind. -/
theorem tupleKind (ef : EF nd E V den tl K) : KindOk (K + 2) "tuple" (TField E) (ValT E den) where
  resp := valT_respT
  wit := ⟨_, [], rfl⟩
  top := fun t ht => by
    rcases ht with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨-, rfl⟩ | ⟨h, _⟩ <;> try simp at h
    exact ⟨Or.inl ⟨_, rfl⟩, lh_top_leaf _, fun p _ => by rw [dn_tuple, denO_top]⟩
  congr := fun fx fx' e p ⟨v, hv⟩ => by
    rw [dn_tuple, dn_tuple, hv]
    exact denO_congr tlit_not fx fx' e (valT_resp v)
  union := fun fx fy => by
    obtain ⟨w, run, fw, sem, le⟩ := tuple_union_lh (den := den) fx fy
    exact ⟨w, fun m _ => by simp [Elixir.Module.Types.Descr.«bare_union/3», run], fw,
      fun p ⟨v, hv⟩ => by rw [dn_tupleT hv, dn_tupleT hv, dn_tupleT hv, sem], le⟩
  inter := fun fx fy => by
    obtain ⟨w, run, fw, sem, le⟩ := tuple_inter_lh (den := den) fx fy
    refine ⟨w, fun m _ => by simp [Elixir.Module.Types.Descr.«bare_intersection/3», run], fun _ => ⟨fw, le⟩,
      fun p ⟨v, hv⟩ => ?_⟩
    cases k : kept (.atom "tuple", w)
    · rw [keptO_false k, dn_none, dn_tupleT hv, dn_tupleT hv, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (tfield_nz fw), denTF_bot]
    · rw [keptO_true k, dn_tupleT hv, dn_tupleT hv, dn_tupleT hv, sem]
  diff := fun fx fy => by
    obtain ⟨w, run, fw, sem, le⟩ := tuple_diff_lh ef (den := den) fx fy
    refine ⟨w, fun m _ => by simp [Elixir.Module.Types.Descr.«bare_difference/3», run], fun k => ⟨fw, le (kept_ne_bot k)⟩,
      fun p ⟨v, hv⟩ => ?_⟩
    cases k : kept (.atom "tuple", w)
    · rw [keptO_false k, dn_none, dn_tupleT hv, dn_tupleT hv, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (tfield_nz fw), denTF_bot]
    · rw [keptO_true k, dn_tupleT hv, dn_tupleT hv, dn_tupleT hv, sem]
  opt_union := by
    intro x y S m fx fy hm
    obtain ⟨w, run, fw, sem⟩ := opt_tuple_union_sem ef (m := m) (by omega) fx fy
    exact ⟨w, by simpa [Elixir.Module.Types.Descr.«opt_union/4»] using run, fw,
      fun p ⟨v, hv⟩ => by rw [dn_tupleT hv, dn_tupleT hv, dn_tupleT hv, sem]⟩
  opt_inter := by
    intro x y S m fx fy hm
    obtain ⟨w, run, fw, sem⟩ := opt_tuple_inter_val ef hm fx fy S
    refine ⟨w, by simpa [Elixir.Module.Types.Descr.«opt_intersection/4»] using run, fun _ => fw, fun p ⟨v, hv⟩ => ?_⟩
    cases k : kept (.atom "tuple", w)
    · rw [keptO_false k, dn_none, dn_tupleT hv, dn_tupleT hv, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (tfield_nz fw), denTF_bot]
    · rw [keptO_true k, dn_tupleT hv, dn_tupleT hv, dn_tupleT hv, sem]
  opt_diff := by
    intro x y S m fx fy hm
    obtain ⟨n, rfl, hn⟩ := succ_of_le (show K + 1 ≤ m by omega)
    obtain ⟨w, run, fw, sem⟩ := opt_tuple_diff_val ef hn fx fy
    refine ⟨w, by simpa [Elixir.Module.Types.Descr.«opt_difference/4»] using run, fun _ => fw, fun p ⟨v, hv⟩ => ?_⟩
    cases k : kept (.atom "tuple", w)
    · rw [keptO_false k, dn_none, dn_tupleT hv, dn_tupleT hv, ← sem,
        dropped_bdd (by rw [kept_name]; exact k) (tfield_nz fw), denTF_bot]
    · rw [keptO_true k, dn_tupleT hv, dn_tupleT hv, dn_tupleT hv, sem]
  empty := fun S fx => by
    obtain ⟨b, run, ex⟩ := tuple_empty_exact ef fx S
    refine ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using run m (by omega),
      fun N hx hS => (ex N hx hS.toT).trans ⟨fun h p ⟨v, hv⟩ => by rw [dn_tupleT hv]; exact h v,
        fun h v => by have := h (0, .nil, valT E den v) ⟨v, rfl⟩; rwa [dn_tupleT rfl] at this⟩⟩

end

end Elixir.STTDescrProofsTest.Nest

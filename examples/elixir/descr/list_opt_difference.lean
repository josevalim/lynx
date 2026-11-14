namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Optimized differences of list fields on lists of values. -/

variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

/-- Valuations of list literals induced by lists of values. -/
def ValLG (E : Term → Prop) (den : Term → V → Prop) (tl : V → Prop) (ρ : Term → Bool) : Prop :=
  ∃ v, ListVal tl v ∧ ρ = valL E den v

theorem valLG_resp : ∀ ρ, ValLG E den tl ρ → Resp ρ := fun _ ⟨v, _, e⟩ => e ▸ valL_resp v

/-- `opt_list_leaf_difference/3` compares list literals soundly. -/
theorem nl_list_cmp (ef : EF nd E V den tl K) {n : Nat} (hn : K ≤ n) (a₁ a₂ type : Term) (h₁ : LLit E a₁)
    (h₂ : LLit E a₂) :
    ∃ res, (D (n + 1)).pure (.function "Elixir.Module.Types.Descr" "opt_list_leaf_difference" 3 #[])
      #[a₁, a₂, type] = .ok res ∧ CmpOk (ValLG E den tl) (LLit E) a₁ a₂ type res := by
  obtain ⟨k₁, l₁, t₁, rfl, hl₁, ht₁⟩ := h₁
  obtain ⟨k₂, l₂, t₂, rfl, hl₂, ht₂⟩ := h₂
  rw [Erlang.program.«Elixir.Module.Types.Descr:opt_list_leaf_difference/3».pure]
  obtain ⟨b₁, hb₁, s₁⟩ := ef.disj hl₁ hl₂
  obtain ⟨b₂, hb₂, s₂⟩ := ef.disj ht₁ ht₂
  have r₁ := hb₁ n hn
  have r₂ := hb₂ n hn
  cases b₁
  · cases b₂
    · refine ⟨.atom "none", ?_, Or.inr (Or.inr (Or.inr rfl))⟩
      rw [Elixir.Module.Types.Descr.«opt_list_leaf_difference/3».eq_def]
      simp [r₁, r₂, boolAtom, Lynx.Except.orElse, isMember]
    · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, fun ρ ⟨v, lv, e⟩ => ?_⟩⟩
      · rw [Elixir.Module.Types.Descr.«opt_list_leaf_difference/3».eq_def]
        simp [r₁, r₂, boolAtom, Lynx.Except.orElse, isMember]
      · subst e
        apply Bool.eq_false_iff.mpr
        intro h
        rw [Bool.and_eq_true, nl_llit_val ef hl₁ ht₁, nl_llit_val ef hl₂ ht₂] at h
        exact s₂ rfl _ h.1.2 h.2.2
  · refine ⟨.atom "disjoint", ?_, Or.inl ⟨rfl, fun ρ ⟨v, lv, e⟩ => ?_⟩⟩
    · rw [Elixir.Module.Types.Descr.«opt_list_leaf_difference/3».eq_def]
      simp [r₁, boolAtom, Lynx.Except.orElse, isMember]
    · subst e
      apply Bool.eq_false_iff.mpr
      intro h
      rw [Bool.and_eq_true, nl_llit_val ef hl₁ ht₁, nl_llit_val ef hl₂ ht₂] at h
      obtain ⟨x, mx⟩ := List.exists_mem_of_ne_nil v.xs lv.1
      exact s₁ rfl x (h.1.1 x mx) (h.2.1 x mx)

/-- Optimized differences of list fields hold the lists of the first and not the second. -/
theorem nl_opt_diff (ef : EF nd E V den tl K) {m : Nat} (hm : K + 1 ≤ m) {x y : Term} (wx : LF E x) (wy : LF E y)
    (S : List (Term × Term)) :
    ∃ w, Elixir.Module.Types.Descr.«opt_difference/4» (D m) (.atom "list") x y (.map S) = .ok w ∧ LF E w ∧
      ∀ v, ListVal tl v → dL E den w v = (dL E den x v && !dL E den y v) := by
  obtain ⟨n, rfl, hn⟩ := succ_of_le hm
  simp only [Elixir.Module.Types.Descr.«opt_difference/4»]
  have spec := fun a₁ a₂ type (_ : TypeOk type) (h₁ : LLit E a₁) (h₂ : LLit E a₂) =>
    nl_list_cmp ef hn a₁ a₂ type h₁ h₂
  have viaDiff3 : Elixir.Module.Types.Descr.«opt_list_difference/3» (D (n + 1)) x y (.map S) =
      Elixir.Module.Types.Descr.«bdd_difference/3» (D (n + 1)) x y optListCmp → ∃ w,
      Elixir.Module.Types.Descr.«opt_list_difference/3» (D (n + 1)) x y (.map S) = .ok w ∧ LF E w ∧
      ∀ v, ListVal tl v → dL E den w v = (dL E den x v && !dL E den y v) := by
    intro e
    obtain ⟨r, hr, okr, semr⟩ := diff3_ok valLG_resp spec _ y wy (fun _ h => h) x wx
    exact ⟨r, by rw [e, hr], okr, fun v lv => semr _ ⟨v, lv, rfl⟩⟩
  have viaBare : Elixir.Module.Types.Descr.«opt_list_difference/3» (D (n + 1)) x y (.map S) =
      Elixir.Module.Types.Descr.«list_difference/2» x y → ∃ w,
      Elixir.Module.Types.Descr.«opt_list_difference/3» (D (n + 1)) x y (.map S) = .ok w ∧ LF E w ∧
      ∀ v, ListVal tl v → dL E den w v = (dL E den x v && !dL E den y v) := by
    intro e
    obtain ⟨w, run, ww, sem, -⟩ := nl_bare_diff ef wx wy
    exact ⟨w, by rw [e]; simpa [Elixir.Module.Types.Descr.«bare_difference/3»] using run (D (n + 1)), ww,
      fun v _ => sem v⟩
  have same : ∀ {k a b : Term}, x = .tuple #[k, a, b] → compareExact (fuel y x) y x = .eq → ∃ w,
      Elixir.Module.Types.Descr.«opt_list_difference/3» (D (n + 1)) x y (.map S) = .ok w ∧ LF E w ∧
      ∀ v, ListVal tl v → dL E den w v = (dL E den x v && !dL E den y v) := by
    rintro k a b rfl e
    refine ⟨_, opt_list_same e, Bdd.bot, fun v _ => ?_⟩
    simp only [dL, eval_exact wx (valL_resp v) e, eval_bot, Bool.and_not_self]
  by_cases tx : ∃ k, x = .tuple #[k, .atom "term", .atom "term"]
  · obtain ⟨k, rfl⟩ := tx
    by_cases e : compareExact (fuel y (.tuple #[k, .atom "term", .atom "term"])) y (.tuple #[k, .atom "term", .atom "term"]) = .eq
    · exact same rfl e
    obtain ⟨k', rfl⟩ := leaf_int wx
    obtain ⟨r, hr, okr, semr⟩ := neg_ok wy
    refine ⟨r, by rw [opt_list_top, ite_eq_right e, hr], okr _ wy, fun v _ => ?_⟩
    simp only [dL, semr _ (valL_resp v), eval_leaf, nl_top_val ef, Bool.true_and]
  have nt : ∀ k, x ≠ .tuple #[k, .atom "term", .atom "term"] := fun k e => tx ⟨k, e⟩
  by_cases leaves : (∃ k a b, x = .tuple #[k, a, b]) ∧ ∃ k a b, y = .tuple #[k, a, b]
  rotate_left
  · exact viaDiff3 (opt_list_other nt leaves)
  obtain ⟨⟨k₁, l₁, t₁, rfl⟩, ⟨k₂, l₂, t₂, rfl⟩⟩ := leaves
  obtain ⟨k₁, rfl⟩ := leaf_int wx
  obtain ⟨k₂, rfl⟩ := leaf_int wy
  obtain ⟨k₁', l₁', t₁', e₁, hl₁, ht₁⟩ := Bdd.leaf_iff.mp wx
  obtain ⟨-, e₁₂, e₁₃⟩ := tuple3_inj e₁
  subst e₁₂ e₁₃
  obtain ⟨k₂', l₂', t₂', e₂, hl₂, ht₂⟩ := Bdd.leaf_iff.mp wy
  obtain ⟨-, e₂₂, e₂₃⟩ := tuple3_inj e₂
  subst e₂₂ e₂₃
  have ntop : ¬(l₁ = .atom "term" ∧ t₁ = .atom "term") := fun ⟨a, b⟩ => nt _ (by rw [a, b])
  by_cases e : compareExact (fuel (.tuple #[.integer k₂, l₂, t₂]) (.tuple #[.integer k₁, l₁, t₁])) (.tuple #[.integer k₂, l₂, t₂]) (.tuple #[.integer k₁, l₁, t₁]) = .eq
  · exact same rfl e
  obtain ⟨c₁, hc₁, sc₁⟩ := ef.sub hl₁ hl₂
  obtain ⟨c₂, hc₂, sc₂⟩ := ef.sub ht₁ ht₂
  have r₁ := hc₁ (n + 1) (by omega)
  have r₂ := hc₂ (n + 1) (by omega)
  obtain ⟨L₁, L₂, L₃, L₄⟩ := opt_list_leaves (d := D (n + 1)) (S := .map S) (k₁ := .integer k₁) (k₂ := .integer k₂)
    (t₂ := t₂) ntop e
  cases c₁
  · exact viaDiff3 (L₁ r₁)
  have sl := sc₁ rfl
  cases c₂
  · rcases opt_bdd_seen_map S (.atom "list_difference") (.tuple #[.integer k₁, l₁, t₁])
        (.tuple #[.integer k₂, l₂, t₂]) with seen | ⟨S', ok⟩
    · exact viaBare (L₃ r₁ r₂ seen)
    obtain ⟨c, hc, run, semc⟩ := ef.opt_diff S' ht₁ ht₂ (show K ≤ n + 1 by omega)
    obtain ⟨k, leaf⟩ := nl_leaf_new ef hl₁ hc
    refine ⟨.tuple #[.integer k, l₁, c], by rw [L₄ _ r₁ r₂ ok, run]; exact leaf,
      Bdd.leaf_iff.mpr ⟨k, l₁, c, rfl, hl₁, hc⟩, fun v lv => ?_⟩
    simp only [dL, eval_leaf]
    apply Bool.eq_iff_iff.mpr
    rw [nl_llit_val ef hl₁ hc, Bool.and_eq_true, nl_llit_val ef hl₁ ht₁, Bool.not_eq_true', Bool.eq_false_iff, Ne,
      nl_llit_val ef hl₂ ht₂, semc]
    constructor
    · rintro ⟨all, last, nlast⟩
      exact ⟨⟨all, last⟩, fun ⟨_, h⟩ => nlast h⟩
    · rintro ⟨⟨all, last⟩, h⟩
      exact ⟨all, last, fun hl => h ⟨fun x mx => sl x (all x mx), hl⟩⟩
  · have st := sc₂ rfl
    refine ⟨.atom "bdd_bot", L₂ r₁ r₂, Bdd.bot, fun v lv => ?_⟩
    simp only [dL, eval_leaf, eval_bot]
    cases h : valL E den v (.tuple #[.integer k₁, l₁, t₁])
    · rfl
    · rw [nl_llit_val ef hl₁ ht₁] at h
      have : valL E den v (.tuple #[.integer k₂, l₂, t₂]) = Bool.true :=
        (nl_llit_val ef hl₂ ht₂ v).mpr ⟨fun x mx => sl x (h.1 x mx), st _ h.2⟩
      rw [this]; rfl

/-- `empty_key?/3` decides exactly whether list fields hold lists of values. -/
theorem nl_empty_key (ef : EF nd E V den tl K) {x : Term} (wx : LF E x) (S : List (Term × Term)) :
    ∃ b : Bool, (∀ m, K + 2 ≤ m →
        Elixir.Module.Types.Descr.«empty_key?/3» (D m) (.atom "list") x (.map S) = .ok (boolAtom b)) ∧
      ∀ N, lh x < N → SafeN N S → (b = Bool.true ↔ ∀ v, ListVal tl v → dL E den x v = Bool.false) := by
  obtain ⟨b, run, exact⟩ := nl_list_empty ef wx S
  exact ⟨b, fun m hm => by simpa [Elixir.Module.Types.Descr.«empty_key?/3»] using run m hm, exact⟩

end Elixir.STTDescrProofsTest.Nest

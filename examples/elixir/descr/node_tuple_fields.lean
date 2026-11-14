namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Tuple fields of the expansion literal of the node `t`: their heights, meaning, and emptiness. -/

section
variable {t : Term}

theorem lh_isT {e : Term} (h : IsT t e) : lh e = 1 := by
  obtain ⟨S, rfl, -⟩ := h.node
  exact lh_node_term

theorem lh_litN {e : Term} (h : IsT t e) (k : Int) : lh (litN e k) = 1 := by
  obtain ⟨S, rfl, -⟩ := h.node
  simp only [litN, Term.list]
  rw [show (#[.integer k, .atom "closed", .cons (.atom "term") (.cons (.tuple #[.reference (refOf t), .map S, gen]) .nil)] :
      Array Term) = ⟨[.integer k, .atom "closed", .cons (.atom "term") (.cons (.tuple ⟨[.reference (refOf t), .map S, gen]⟩) .nil)]⟩
      from rfl, lh_nodeLit]
  exact lh_node_term

theorem lh_bt (b : Bool) : lh (bt b) = 1 := by cases b <;> simp [bt, lh]

theorem pure_one {x : Term} (fx : OField (PureLit t) x) (nt : ∀ k, x ≠ .tuple #[.integer k, .atom "open", .nil]) :
    lh x = 1 := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact absurd rfl (nt k)
  rcases pure_shape wx with rfl | rfl | ⟨e, he, rfl⟩ | ⟨j, e, c, u, d, he, rfl⟩
  · simp [lh]
  · simp [lh]
  · exact lh_litN he _
  · obtain ⟨S, rfl, -⟩ := he.node
    simp only [litN, Term.list]
    rw [show (#[.integer j, .tuple #[.integer (keyOf t), .atom "closed", .cons (.atom "term")
        (.cons (.tuple #[.reference (refOf t), .map S, gen]) .nil)], bt c, bt u, bt d] : Array Term) =
        ⟨[.integer j, .tuple ⟨[.integer (keyOf t), .atom "closed", .cons (.atom "term")
        (.cons (.tuple ⟨[.reference (refOf t), .map S, gen]⟩) .nil)]⟩, bt c, bt u, bt d]⟩ from rfl,
      lh_node_z _ _ _ _ _ _ _ (by simp [litZ]), lh_nodeLit, lh_node_term]
    simp [lh_bt]

theorem pure_le {x : Term} (fx : OField (PureLit t) x) : lh x ≤ 1 := by
  by_cases nt : ∃ k, x = .tuple #[.integer k, .atom "open", .nil]
  · obtain ⟨k, rfl⟩ := nt
    simp [lh]
  · exact Nat.le_of_eq (pure_one fx fun k h => nt ⟨k, h⟩)

theorem pureLit_exact {a b : Term} (ha : PureLit t a) (hb : PureLit t b) : compareExact (fuel b a) b a = .eq := by
  obtain ⟨e, he, rfl⟩ := ha
  obtain ⟨e', he', rfl⟩ := hb
  simp [litN, Term.list, compareExact_tuple, List.compareLex_cons_cons, compareExact_cons, isT_exact he' he,
    List.compareLex_nil_nil]

theorem pure_cases {x : Term} (fx : OField (PureLit t) x) :
    (∃ k : Int, x = .tuple #[.integer k, .atom "open", .nil]) ∨ x = .atom "bdd_top" ∨ x = .atom "bdd_bot" ∨
      (∃ e, IsT t e ∧ x = litN e (keyOf t)) ∨
      ∃ (j : Int) (e : Term) (c u d : Bool), IsT t e ∧ x = .tuple #[.integer j, litN e (keyOf t), bt c, bt u, bt d] := by
  rcases fx with ⟨k, rfl⟩ | wx
  · exact Or.inl ⟨k, rfl⟩
  · exact Or.inr (pure_shape wx)

/-- Pure tuple fields mean the same under a valuation and under the constant valuation of its literal. -/
theorem pure_val {x : Term} (fx : OField (PureLit t) x) {ρ : Term → Bool} (_hρ : Resp ρ) :
    ∃ b, denO x ρ = denO x (fun _ => b) := by
  rcases pure_cases fx with ⟨k, rfl⟩ | rfl | rfl | ⟨e, he, rfl⟩ | ⟨j, e, c, u, d, he, rfl⟩
  · exact ⟨Bool.true, by simp [denO_top]⟩
  · exact ⟨Bool.true, rfl⟩
  · exact ⟨Bool.true, rfl⟩
  · refine ⟨ρ (litN e (keyOf t)), ?_⟩
    simp [denO, isOpenTop, litN, Term.list]
  · refine ⟨ρ (litN e (keyOf t)), ?_⟩
    cases c <;> cases u <;> cases d <;> simp [denO, isOpenTop, eval, bt, litN, Term.list]

/-- The emptiness of pure tuple fields, when neither the field nor the node was seen. -/
theorem pure_empty_val {x : Term} (fx : OField (PureLit t) x) {S : List (Term × Term)}
    (fresh : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "tuple") x) e.1) (.cons (.atom "tuple") x) e.1 == .eq) = Bool.false)
    (noid : idIn (refOf t) S = Bool.false) {m : Nat} (hm : 2 ≤ m) :
    Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) =
      .ok (boolAtom (!denO x (fun _ => Bool.true) && !denO x (fun _ => Bool.false))) := by
  have walk : Elixir.Module.Types.Descr.«tuple_empty?/2» (D m) x (.map S) =
      Elixir.Module.Types.Descr.«tuple_bdd_empty?/4» (D m) (.tuple #[.atom "open", .nil]) .nil x
        (.map ((.cons (.atom "tuple") x, .atom "true") :: S)) := by
    unfold Elixir.Module.Types.Descr.«tuple_empty?/2»
    simp [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Erlang.erlang.«is_map_key/2», fresh,
      Term.false, Erlang.maps.«put/3»]
  have noid' : idIn (refOf t) ((.cons (.atom "tuple") x, .atom "true") :: S) = Bool.false := by
    simp [idIn] at noid ⊢
    exact noid
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  rw [walk]
  rcases pure_cases fx with ⟨k, rfl⟩ | rfl | rfl | ⟨e, he, rfl⟩ | ⟨j, e, c, u, d, he, rfl⟩
  · rw [tuple_walk_top_leaf]; simp [denO_top, boolAtom]
  · rw [tuple_walk_top]; simp [denO, isOpenTop, boolAtom]
  · rw [tuple_walk_bot]; simp [denO, isOpenTop, boolAtom]
  · rw [walk_leaf_node he.node _ m', noid']; simp [denO, isOpenTop, litN, Term.list, boolAtom]
  · rw [walk_node_node he.node _ _ m', noid']
    cases c <;> cases u <;> cases d <;> simp [denO, isOpenTop, eval, bt, litN, Term.list, boolAtom]

theorem safeN_noid {N : Nat} {S : List (Term × Term)} (hS : SafeN N S) (r : List Nat) : idIn r S = Bool.false := by
  simp only [idIn, List.any_eq_false, beq_iff_eq]
  intro e me h
  obtain ⟨kind, b, e₁, -⟩ := hS e me
  rw [e₁] at h
  simp at h

end

end Elixir.STTDescrProofsTest.Nest

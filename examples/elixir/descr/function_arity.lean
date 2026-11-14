namespace Elixir.STTDescrProofsTest
open Lynx Lynx.Term BddProofs

/-- The arguments of the top function of arity `n`. -/
abbrev noneArgs (n : Nat) : Term := Term.list (List.replicate n (.map []))

theorem fun_arity_run (n : Nat) :
    Elixir.Module.Types.Descr.«fun/1» (.integer n) =
      .ok (.map [(.atom "fun", .tuple #[.atom "union", .map [(.integer n, .atom "bdd_top")]])]) := by
  unfold Elixir.Module.Types.Descr.«fun/1»
  simp [Erlang.erlang.«is_integer/1», Erlang.erlang.«>=/2», Lynx.Except.andAlso, Int.isGE_compare]

theorem fun_none_run (n : Nat) : ∃ k : Int, ∀ m, 1 ≤ m →
    Elixir.Module.Types.Descr.«fun/2» (D m) (noneArgs n) (.atom "term") =
      .ok (.map [(.atom "fun", .tuple #[.atom "union", .map [(.integer n, .tuple #[.integer k, noneArgs n, .atom "term"])]])]) ∧
    Elixir.Module.Types.Descr.«bdd_leaf_new/2» (noneArgs n) (.atom "term") = .ok (.tuple #[.integer k, noneArgs n, .atom "term"]) := by
  obtain ⟨k, leaf⟩ := leaf_fun (List.replicate n (.map []))
  obtain ⟨r, ⟨s, d, rfl⟩, run⟩ := foldl_uni 1 "Elixir.Module.Types.Descr" "-fun_descr/2-fun-0-" #[]
    (fun a => ∃ s d, a = .tuple #[s, d, .atom "false"]) (List.replicate n (.map [])) (by
      intro x mx a ⟨s, d, ha⟩
      subst ha
      rw [List.eq_of_mem_replicate mx]
      refine ⟨.tuple #[.cons (.map []) s, .cons (.map []) d, .atom "false"], ⟨_, _, rfl⟩, fun m hm => ?_⟩
      obtain ⟨m', rfl, -⟩ := succ_of_le hm
      rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_descr/2-fun-0-/2».pure]
      simp [Elixir.Module.Types.Descr.«-fun_descr/2-fun-0-/2», split_static (Or.inr (Or.inl ⟨[], rfl, rfl⟩)),
        Lynx.Except.orElse]) (.tuple #[.nil, .nil, .atom "false"]) ⟨_, _, rfl⟩
  refine ⟨k, fun m hm => ⟨?_, leaf⟩⟩
  have hl : Erlang.erlang.«is_list/1» (noneArgs n) = .ok (.atom "true") := by
    cases n <;> simp [noneArgs, Erlang.erlang.«is_list/1», Term.list, List.replicate]
  unfold Elixir.Module.Types.Descr.«fun/2» Elixir.Module.Types.Descr.«fun_descr/2»
  simp [hl, length_list, run m hm, split_static (Or.inl rfl), Lynx.Except.orElse, isMember,
    Elixir.Module.Types.Descr.«fun_new/3», leaf]

/-- The top function of arity `n` without its arrow leaves the negated leaf. -/
theorem fun_top_diff (n : Nat) (L : Term) (leaf : IsLeaf L) (m : Nat) : ∃ h : Int,
    Elixir.Module.Types.Descr.«bare_difference/3» (D (m + 1)) (.atom "fun")
        (.tuple #[.atom "union", .map [(.integer n, .atom "bdd_top")]]) (.tuple #[.atom "union", .map [(.integer n, L)]]) =
      .ok (.tuple #[.atom "union", .map [(.integer n, .tuple #[.integer h, L, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]),
        (.integer n, .atom "bdd_top")]]) := by
  obtain ⟨h, hN⟩ := node_new (okc := fun _ => True) (oku := fun _ => True) (okd := fun _ => True) L (.atom "bdd_bot")
    (.atom "bdd_bot") (.atom "bdd_top") leaf (by simp [Bdd]) (by simp [Bdd]) (by simp [Bdd])
  obtain ⟨k, x, y, rfl⟩ := leaf
  refine ⟨h, ?_⟩
  simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2»,
    Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»,
    Erlang.program.«Elixir.Module.Types.Descr:-fun_repr_difference/2-fun-0-/3».pure,
    Elixir.Module.Types.Descr.«-fun_repr_difference/2-fun-0-/3», getMapKeys_single, mapLookup, hN,
    Elixir.Module.Types.Descr.«bdd_difference/2», Elixir.Module.Types.Descr.«bdd_negation/1», Erlang.erlang.«=:=/2»,
    Erlang.erlang.«is_map/1»,
    Erlang.maps.«update/3», Erlang.maps.«remove/2», Erlang.erlang.«map_size/1», Erlang.erlang.«==/2»,
    Lynx.Except.andAlso, List.eraseDupsBy, List.eraseDupsBy.loop]

/-- An arrow leaf without the top function of its arity is empty. -/
theorem fun_leaf_diff (n : Nat) (L : Term) (leaf : IsLeaf L) (m : Nat) :
    Elixir.Module.Types.Descr.«bare_difference/3» (D (m + 1)) (.atom "fun")
        (.tuple #[.atom "union", .map [(.integer n, L)]]) (.tuple #[.atom "union", .map [(.integer n, .atom "bdd_top")]]) =
      .ok (.integer 0) := by
  obtain ⟨k, x, y, rfl⟩ := leaf
  simp [Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2»,
    Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»,
    Erlang.program.«Elixir.Module.Types.Descr:-fun_repr_difference/2-fun-0-/3».pure,
    Elixir.Module.Types.Descr.«-fun_repr_difference/2-fun-0-/3», getMapKeys_single, mapLookup,
    Elixir.Module.Types.Descr.«bdd_difference/2», Erlang.erlang.«=:=/2», Erlang.erlang.«is_map/1»,
    Erlang.maps.«update/3», Erlang.maps.«remove/2», Erlang.erlang.«map_size/1», Erlang.erlang.«==/2»,
    Lynx.Except.andAlso]

/-- A tuple domain is a subtype of itself. -/
theorem domain_sub_self (k : Int) (A : Term) (m : Nat) (S : Term) :
    Elixir.Module.Types.Descr.«subtype_seen?/3» (D (m + 2)) (.map [(.atom "tuple", .tuple #[.integer k, .atom "closed", A])])
      (.map [(.atom "tuple", .tuple #[.integer k, .atom "closed", A])]) S =
      .ok (.atom "true") := by
  simp [Elixir.Module.Types.Descr.«subtype_seen?/3»]
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  simp [Erlang.erlang.«==/2», unfold_map, Erlang.erlang.«is_map_key/2»]
  unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
  simp [Erlang.erlang.«==/2», Erlang.maps.«fold/3»,
    Erlang.program.«Elixir.Module.Types.Descr:-dynamic_difference/3-fun-0-/3».pure,
    Elixir.Module.Types.Descr.«-dynamic_difference/3-fun-0-/4», getMapKeys_single, mapLookup,
    Erlang.program.«Elixir.Module.Types.Descr:bare_difference/3».pure, Elixir.Module.Types.Descr.«bare_difference/3»,
    Elixir.Module.Types.Descr.«tuple_difference/2», bdd_difference_self, Erlang.maps.«remove/2», empty_none_seen]

theorem diff_none_none (d : Dispatcher) :
    Elixir.Module.Types.Descr.«bare_difference/2» d (.map []) (.map []) = .ok (.map []) := by
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  simp [Erlang.erlang.«==/2»]

/-- Arguments of `none()` stay empty after removing any arrow argument of `none()`. -/
theorem phi_args_none (n : Nat) (ret pos C S : Term) (m : Nat) : ∀ (r j : Nat), j + r = n →
    Elixir.Module.Types.Descr.«phi_arguments/7» (D m) (Term.list (List.replicate r (.map []))) (.integer j)
        (Term.list (List.replicate n (.tuple #[.atom "false", .map []]))) ret pos C S =
      .ok (.tuple #[.atom "true", C]) := by
  intro r
  induction r with
  | zero => intro j _; rw [Elixir.Module.Types.Descr.«phi_arguments/7».eq_def]; rfl
  | succ r ih =>
    intro j hj
    have nth := nth_list (List.replicate n (.tuple #[.atom "false", .map []])) j (by simp; omega)
    rw [List.getElem?_replicate_of_lt (by omega)] at nth
    have next := ih (j + 1) (by omega)
    rw [Elixir.Module.Types.Descr.«phi_arguments/7».eq_def]
    simp only [List.replicate_succ, Term.list, Erlang.erlang.«+/2_integers»]
    rw [show ((j + 1 : Nat) : Int) = (j : Int) + 1 by omega] at next
    simp [nth, diff_none_none, empty_none_seen, isMember, next]

/-- `phi/5` holds for arguments and a return of `none()` against the top arrow of their arity. -/
theorem phi_none (n : Nat) (k : Int) (S : Term) (m : Nat) : ∃ C,
    Elixir.Module.Types.Descr.«phi/5» (D m) (Term.list (List.replicate n (.tuple #[.atom "false", .map []])))
        (.tuple #[.atom "false", .map []]) (Term.list [.tuple #[.integer k, noneArgs n, .atom "term"]]) (.map []) S =
      .ok (.tuple #[.atom "true", C]) := by
  have args := phi_args_none n (.tuple #[.atom "false", .map []]) .nil (.map []) S m n 0 (by omega)
  have inter : Elixir.Module.Types.Descr.«bare_intersection/2» (D m) (.map []) (.atom "term") = .ok (.map []) := by
    unfold Elixir.Module.Types.Descr.«bare_intersection/2»; rfl
  refine ⟨.map [(.tuple #[Term.list (List.replicate n (.tuple #[.atom "false", .map []])),
    .tuple #[.atom "false", .map []], Term.list [.tuple #[.integer k, noneArgs n, .atom "term"]]], .atom "true")], ?_⟩
  rw [Elixir.Module.Types.Descr.«phi/5».eq_def]
  rw [show ((0 : Nat) : Int) = 0 from rfl] at args
  simp only [Term.list, noneArgs] at args ⊢
  simp [getMapKeys_single, mapLookup, inter, empty_none_seen, isMember, args, Erlang.maps.«put/3»]

theorem sub_none_term (d : Dispatcher) :
    Elixir.Module.Types.Descr.«subtype?/2» d (.map []) (.atom "term") = .ok (.atom "true") := by
  obtain ⟨T, term, -, -, -, staticT⟩ := unfolded_term_fields
  rw [subtype_term_r term]
  exact subtype_keys d [] T rfl staticT (by simp)

/-- With no arguments, the top arrow applies to the empty tuple and returns a subtype of `term()`. -/
theorem phi_starter_zero (k : Int) (S : Term) (m : Nat) (hm : 12 ≤ m) :
    Elixir.Module.Types.Descr.«phi_starter/4» (D m) .nil (.atom "term") (Term.list [.tuple #[.integer k, .nil, .atom "term"]])
      S = .ok (.atom "true") := by
  obtain ⟨ops, dops, fops, hnone, tail⟩ : ElemOk LElem 8 ∧ ElemDiff LElem 8 ∧ ElemFun LElem 8 ∧ LElem (.map []) ∧
      TailOk LElem :=
    ⟨lelemOk.mono (by omega), lelemDiff.mono (by omega), lelemFun, Or.inr ⟨[], rfl, basic_nil⟩, tail_lelem⟩
  have dm := domOk ops dops fops hnone tail
  obtain ⟨dom, hdom, rdom⟩ := dm.dom [] (by simp)
  obtain ⟨i, hi, ri⟩ := dm.inter hdom hdom
  obtain ⟨X, rfl⟩ := dm.isMap hi
  obtain ⟨e, he⟩ := dm.empty hi []
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have apply : ∃ r, (r = .map [] ∨ r = .atom "term") ∧
      Elixir.Module.Types.Descr.«apply_disjoint/2» (D (m' + 1)) .nil (Term.list [.tuple #[.integer k, .nil, .atom "term"]]) =
        .ok r := by
    simp only [Term.list] at rdom
    unfold Elixir.Module.Types.Descr.«apply_disjoint/2»
    cases e
    · refine ⟨.atom "term", Or.inr rfl, ?_⟩
      simp [rdom, Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»,
        Erlang.lists.«foldl_1/3», Erlang.program.«Elixir.Module.Types.Descr:-apply_disjoint/2-fun-0-/2».pure,
        Elixir.Module.Types.Descr.«-apply_disjoint/2-fun-0-/3», ri m' (by omega), Elixir.Module.Types.Descr.«empty?/1»,
        he m' (by omega), isMember]
      unfold Elixir.Module.Types.Descr.«bare_union/2»
      rfl
    · refine ⟨.map [], Or.inl rfl, ?_⟩
      simp [rdom, Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2»,
        Erlang.lists.«foldl_1/3», Erlang.program.«Elixir.Module.Types.Descr:-apply_disjoint/2-fun-0-/2».pure,
        Elixir.Module.Types.Descr.«-apply_disjoint/2-fun-0-/3», ri m' (by omega), Elixir.Module.Types.Descr.«empty?/1»,
        he m' (by omega), isMember]
  obtain ⟨r, hr, run⟩ := apply
  have sub : Elixir.Module.Types.Descr.«subtype?/2» (D (m' + 1)) r (.atom "term") = .ok (.atom "true") := by
    rcases hr with rfl | rfl
    · exact sub_none_term _
    · exact Nest.sub_term_term _
  unfold Elixir.Module.Types.Descr.«phi_starter/4» Elixir.Module.Types.Descr.«disjoint_non_empty_domains?/3»
  simp [Term.list, Erlang.lists.«all/2», Erlang.erlang.«is_function/2»,
    Elixir.Module.Types.Descr.«all_non_empty_arguments?/2»,
    Erlang.program.«Elixir.Module.Types.Descr:-all_non_empty_arguments?/2-fun-1-/1».pure,
    Elixir.Module.Types.Descr.«-all_non_empty_arguments?/2-fun-1-/2», Erlang.lists.«all_1/2»,
    Elixir.Module.Types.Descr.«all_disjoint_arguments?/1», Lynx.Except.andAlso, Erlang.erlang.«/=/2», run, sub]

/-- With arguments of `none()`, `phi/5` decides that the top arrow is covered. -/
theorem phi_starter_succ (n : Nat) (k : Int) (S : Term) (m : Nat) :
    Elixir.Module.Types.Descr.«phi_starter/4» (D (m + 1)) (noneArgs (n + 1)) (.atom "term")
      (Term.list [.tuple #[.integer k, noneArgs (n + 1), .atom "term"]]) S = .ok (.atom "true") := by
  have all := all_list (D (m + 1)) "Elixir.Module.Types.Descr" "-disjoint_non_empty_domains?/3-fun-0-" #[S]
    (fun _ => Bool.false) (List.replicate (n + 1) (.map [])) (by
      intro x mx
      rw [List.eq_of_mem_replicate mx, Erlang.program.«Elixir.Module.Types.Descr:-disjoint_non_empty_domains?/3-fun-0-/1».pure]
      simp [Elixir.Module.Types.Descr.«-disjoint_non_empty_domains?/3-fun-0-/2», empty_none_seen, Erlang.erlang.«not/1»,
        boolAtom])
  have args := map_list (D (m + 1)) "Elixir.Module.Types.Descr" "-phi_starter/4-fun-0-" #[]
    (fun x => .tuple #[.atom "false", x]) (List.replicate (n + 1) (.map [])) (fun x _ => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-phi_starter/4-fun-0-/1».pure]; rfl)
  have neg : Elixir.Module.Types.Descr.«bare_negation/1» (D (m + 1)) (.atom "term") = .ok (.map []) := by
    simp [Elixir.Module.Types.Descr.«bare_negation/1»]
  obtain ⟨C, phi⟩ := phi_none (n + 1) k S (m + 1)
  simp only [List.map_replicate] at args
  simp only [List.all_replicate] at all
  unfold Elixir.Module.Types.Descr.«phi_starter/4» Elixir.Module.Types.Descr.«disjoint_non_empty_domains?/3»
  simp [noneArgs, all, boolAtom, Lynx.Except.andAlso, args, neg, phi]

theorem phi_starter_none (n : Nat) (k : Int) (S : Term) (m : Nat) (hm : 12 ≤ m) :
    Elixir.Module.Types.Descr.«phi_starter/4» (D m) (noneArgs n) (.atom "term")
      (Term.list [.tuple #[.integer k, noneArgs n, .atom "term"]]) S = .ok (.atom "true") := by
  cases n with
  | zero => exact phi_starter_zero k S m hm
  | succ n =>
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact phi_starter_succ n k S m'

/-- The line of the top function of arity `n` without its arrow leaf is empty. -/
theorem fun_line_top (n : Nat) (k : Int) (S : Term) (m : Nat) (hm : 14 ≤ m)
    (leaf : Elixir.Module.Types.Descr.«bdd_leaf_new/2» (noneArgs n) (.atom "term") =
      .ok (.tuple #[.integer k, noneArgs n, .atom "term"])) :
    Elixir.Module.Types.Descr.«fun_line_empty?/3» (D m) .nil (Term.list [.tuple #[.integer k, noneArgs n, .atom "term"]]) S =
      .ok (.atom "true") := by
  obtain ⟨kd, dom⟩ := args_domain (List.replicate n (.map [])) (fun e me => by
    rw [List.eq_of_mem_replicate me]; exact Or.inr (Or.inl ⟨[], rfl, rfl⟩))
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
  have margs := map_list (D (m' + 3)) "Elixir.Module.Types.Descr" "-fun_line_empty?/3-fun-0-" #[]
    (fun _ => .map []) (List.replicate n (.map [])) (fun x _ => by
      rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_line_empty?/3-fun-0-/1».pure]; rfl)
  simp only [List.map_const'] at margs
  have fd : Elixir.Module.Types.Descr.«fetch_domain/1» (D (m' + 2)) (Term.list [.tuple #[.integer k, noneArgs n, .atom "term"]]) =
      .ok (.map [(.atom "tuple", .tuple #[.integer kd, .atom "closed", noneArgs n])]) := by
    unfold Elixir.Module.Types.Descr.«fetch_domain/1»
    simp [Erlang.lists.«foldl/3», Erlang.erlang.«is_function/2», Erlang.lists.«foldl_1/3»,
      Erlang.program.«Elixir.Module.Types.Descr:-fetch_domain/1-fun-0-/2».pure,
      Elixir.Module.Types.Descr.«-fetch_domain/1-fun-0-/2», dom]
    unfold Elixir.Module.Types.Descr.«bare_union/2»
    simp [Erlang.erlang.«==/2»]
  rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]
  simp [Term.list, margs, leaf]
  simp only [noneArgs] at fd leaf ⊢
  rw [Elixir.Module.Types.Descr.«fun_line_empty?/3».eq_def]
  simp [Erlang.lists.«any/2», Erlang.erlang.«is_function/2»,
    Erlang.program.«Elixir.Module.Types.Descr:-fun_line_empty?/3-fun-1-/1».pure,
    Elixir.Module.Types.Descr.«-fun_line_empty?/3-fun-1-/3», dom, fd, domain_sub_self kd _ m',
    phi_starter_none n k S (m' + 2) (by omega)]

/-- A negated leaf has a single line, whose only literal is negative. -/
theorem dnf_neg_leaf (h : Int) (L : Term) :
    Elixir.Module.Types.Descr.«bdd_to_dnf/4» .nil .nil .nil
        (.tuple #[.integer h, L, .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]) =
      .ok (Term.list [.tuple #[.nil, Term.list [L]]]) := by
  have bot : ∀ acc p q, Elixir.Module.Types.Descr.«bdd_to_dnf/4» acc p q (.atom "bdd_bot") = .ok acc := by
    intro acc p q; rw [Elixir.Module.Types.Descr.«bdd_to_dnf/4».eq_def]; rfl
  have top : ∀ acc p q, Elixir.Module.Types.Descr.«bdd_to_dnf/4» acc p q (.atom "bdd_top") =
      .ok (.cons (.tuple #[p, q]) acc) := by
    intro acc p q; rw [Elixir.Module.Types.Descr.«bdd_to_dnf/4».eq_def]; rfl
  rw [Elixir.Module.Types.Descr.«bdd_to_dnf/4».eq_def]
  simp [bot, top, Term.list]

/-- The top function of arity `n` without its arrow leaf is empty. -/
theorem fun_empty_top (n : Nat) (k h : Int) (m : Nat) (hm : 18 ≤ m)
    (leaf : Elixir.Module.Types.Descr.«bdd_leaf_new/2» (noneArgs n) (.atom "term") =
      .ok (.tuple #[.integer k, noneArgs n, .atom "term"])) :
    Elixir.Module.Types.Descr.«fun_empty?/2» (D m) (.tuple #[.atom "union", .map [(.integer n,
        .tuple #[.integer h, .tuple #[.integer k, noneArgs n, .atom "term"], .atom "bdd_bot", .atom "bdd_bot",
          .atom "bdd_top"]), (.integer n, .atom "bdd_top")]]) (.map []) = .ok (.atom "true") := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  unfold Elixir.Module.Types.Descr.«fun_empty?/2»
  simp only [Erlang.maps.«to_list/1», Lynx.Except.ok_bind]
  refine all_true _ _ _ _ _ fun x mx => ?_
  obtain ⟨e, me, rfl⟩ := List.mem_map.mp mx
  have hv := mapLookup_of_mem_mapEntries me
  have he : e.2 = .tuple #[.integer h, .tuple #[.integer k, noneArgs n, .atom "term"], .atom "bdd_bot", .atom "bdd_bot",
      .atom "bdd_top"] := by
    by_cases c : compareExact (fuel e.1 (.integer n)) e.1 (.integer n) = .eq
    · simp [mapLookup, c] at hv; exact hv.symm
    · simp [mapLookup, c] at hv
  rw [he]
  have line := fun_line_top n k (.map [(.cons e.1 (.tuple #[.integer h, .tuple #[.integer k, noneArgs n, .atom "term"],
    .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"]), .atom "true")]) m' (by omega) leaf
  rw [Erlang.program.«Elixir.Module.Types.Descr:-fun_empty?/2-fun-1-/1».pure]
  simp [Elixir.Module.Types.Descr.«-fun_empty?/2-fun-1-/2», Elixir.Module.Types.Descr.«empty_bdd_seen_key/2»,
    Erlang.erlang.«is_map_key/2», Erlang.maps.«put/3», Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf_neg_leaf]
  refine all_true _ _ _ _ _ fun y my => ?_
  rw [List.mem_singleton.mp my, Erlang.program.«Elixir.Module.Types.Descr:-fun_empty?/2-fun-0-/1».pure]
  simpa [Elixir.Module.Types.Descr.«-fun_empty?/2-fun-0-/2»] using line

/-- The top function of arity `n` is equal to the arrow from `n` arguments of `none()` to `term()`. -/
theorem fun_arity_equal_run (n : Nat) (m : Nat) (hm : 20 ≤ m) : ∃ right,
    Elixir.Module.Types.Descr.«fun/2» (D m) (noneArgs n) (.atom "term") = .ok right ∧
    Elixir.Module.Types.Descr.«equal?/2» (D m)
      (.map [(.atom "fun", .tuple #[.atom "union", .map [(.integer n, .atom "bdd_top")]])]) right = .ok (.atom "true") := by
  obtain ⟨k, run⟩ := fun_none_run n
  obtain ⟨r, leaf⟩ := run m (by omega)
  refine ⟨_, r, ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨h, diff⟩ := fun_top_diff n (.tuple #[.integer k, noneArgs n, .atom "term"]) ⟨k, _, _, rfl⟩ m'
  have sub₁ := subtype_keys (D (m' + 1)) [(.atom "fun", .tuple #[.atom "union", .map [(.integer n, .atom "bdd_top")]])]
    [(.atom "fun", .tuple #[.atom "union", .map [(.integer n, .tuple #[.integer k, noneArgs n, .atom "term"])]])]
    (by simp [mapLookup]) (by simp [mapLookup]) (by
      intro e me
      simp only [mapEntries_singleton, List.mem_singleton] at me
      subst me
      refine Or.inl ⟨_, _, by simp [mapLookup], diff, Or.inr (Or.inr ?_)⟩
      simp only [Elixir.Module.Types.Descr.«empty_key?/3»]
      exact fun_empty_top n k h (m' + 1) (by omega) leaf)
  have sub₂ := subtype_keys (D (m' + 1))
    [(.atom "fun", .tuple #[.atom "union", .map [(.integer n, .tuple #[.integer k, noneArgs n, .atom "term"])]])]
    [(.atom "fun", .tuple #[.atom "union", .map [(.integer n, .atom "bdd_top")]])]
    (by simp [mapLookup]) (by simp [mapLookup]) (by
      intro e me
      simp only [mapEntries_singleton, List.mem_singleton] at me
      subst me
      exact Or.inl ⟨_, _, by simp [mapLookup], fun_leaf_diff n _ ⟨k, _, _, rfl⟩ m', Or.inl rfl⟩)
  simp [Elixir.Module.Types.Descr.«equal?/2», Erlang.erlang.«==/2», Lynx.Except.orElse, Lynx.Except.andAlso, sub₁, sub₂]
  split <;> simp_all

end Elixir.STTDescrProofsTest

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The top type and `:term` operands, for types over the structural kinds. -/

section
variable {K : Nat} {Fn TF LF MF : Term → Prop} {TV LV MV : (Term → Bool) → Prop} {FV : Term → (Term → Bool) → Prop}

theorem topAt_fieldC (ks : Kinds K TF LF MF TV LV MV) (ftop : Fn funTopT) {name : String} {t : Term}
    (ht : TopAt name t) :
    FieldC Fn TF LF MF name t ∧ lh t = 0 ∧ ∀ p, PtOkC TV LV MV FV name p → dn name (some t) p = Bool.true := by
  have plain : name = "bitmap" ∨ name = "atom" ∨ name = "fun" →
      ∀ p, PtOkC TV LV MV FV name p → dn name (some t) p = Bool.true := fun h p ok =>
    (top_field (E := fun _ => True) ht).2.1 p ⟨ok.1, ok.2.1, fun e => by rcases h with rfl | rfl | rfl <;> simp at e⟩
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩ | ⟨rfl, e⟩
  · exact ⟨Or.inl ⟨rfl, 255, rfl, by decide, by decide⟩, lh_int _, plain (Or.inl rfl)⟩
  · refine ⟨Or.inr (Or.inl ⟨rfl, ⟨⟨Bool.false, [], rfl, no_atoms⟩, .nil, by simp [amemV, mapLookup]⟩⟩), ?_,
      plain (Or.inr (Or.inl rfl))⟩
    have := lh_nil_map
    simp [lh] at this ⊢; exact this
  · exact ⟨Or.inr (Or.inr (Or.inl ⟨rfl, ftop⟩)), lh_funTop, plain (Or.inr (Or.inr rfl))⟩
  · obtain ⟨f, l, d⟩ := ks.l.top t (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, e⟩))))
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, f⟩))), l, fun p ok => d p (ok.2.2.1 rfl)⟩
  · obtain ⟨f, l, d⟩ := ks.t.top t (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, e⟩)))))
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, f⟩)))), l, fun p ok => d p (ok.2.2.2.1 rfl)⟩
  · obtain ⟨f, l, d⟩ := ks.m.top t (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, e⟩)))))
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, f⟩)))), l, fun p ok => d p (ok.2.2.2.2.1 rfl)⟩

/-- The unfolded top type holds every point, at no height. -/
theorem termC (ks : Kinds K TF LF MF TV LV MV) (ftop : Fn funTopT) :
    ∃ T, Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T) ∧
    DescrC Fn TF LF MF T ∧ T ≠ [] ∧ lh (.map T) = 0 ∧
    ∀ name ∈ names, ∀ p, PtOkC TV LV MV FV name p → dn name (mapLookup T (.atom name)) p = Bool.true := by
  obtain ⟨T, term, -⟩ := unfolded_term_fields
  have keys : ∀ q, (mapLookup T q).isSome → ∃ name ∈ names, q = .atom name := fun q h => by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨name, m, e, -⟩ := term_top term ht
    exact ⟨name, m, e⟩
  have fields : ∀ name t, mapLookup T (.atom name) = some t → TopAt name t := fun name t h => by
    obtain ⟨name', -, e, ht⟩ := term_top term h
    simp only [Term.atom.injEq] at e
    subst e; exact ht
  refine ⟨T, term, ⟨keys, fun name t h => (topAt_fieldC (FV := FV) ks ftop (fields name t h)).1⟩, term_ne_nil term,
    Nat.le_zero.mp (lh_descr_le keys fun name t h => by rw [(topAt_fieldC (FV := FV) ks ftop (fields name t h)).2.1]; omega),
    fun name m p ok => ?_⟩
  obtain ⟨t, ht, top⟩ := term_at term m
  rw [ht]
  exact (topAt_fieldC ks ftop top).2.2 p ok

end

theorem diff_term_left (d : Dispatcher) {T B : List (Term × Term)}
    (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) (sT : mapLookup T (.atom "dynamic") = none)
    (sB : mapLookup B (.atom "dynamic") = none) (ne : B ≠ []) :
    Elixir.Module.Types.Descr.«bare_difference/2» d (.atom "term") (.map B) =
      Elixir.Module.Types.Descr.«bare_difference/2» d (.map T) (.map B) := by
  unfold Elixir.Module.Types.Descr.«bare_difference/2»
  simp [Erlang.erlang.«==/2», unfold_map, static_map sT, static_map sB, ne]
  unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
  simp [Erlang.erlang.«==/2», ne, term]

theorem opt_diff_term_left (d : Dispatcher) {T B : List (Term × Term)} (S : Term)
    (term : Elixir.Module.Types.Descr.«unfolded_term/0» = .ok (.map T)) (sT : mapLookup T (.atom "dynamic") = none)
    (sB : mapLookup B (.atom "dynamic") = none) (ne : B ≠ []) :
    Elixir.Module.Types.Descr.«opt_difference/3» d (.atom "term") (.map B) S =
      Elixir.Module.Types.Descr.«opt_difference/3» d (.map T) (.map B) S := by
  unfold Elixir.Module.Types.Descr.«opt_difference/3»
  simp [Erlang.erlang.«==/2», unfold_map, static_map sT, static_map sB, ne]
  unfold Elixir.Module.Types.Descr.«dynamic_difference/3»
  simp [Erlang.erlang.«==/2», ne, term]

theorem opt_union_term_r (d : Dispatcher) (a S : Term) :
    Elixir.Module.Types.Descr.«opt_union/3» d a (.atom "term") S = .ok (.atom "term") := by
  unfold Elixir.Module.Types.Descr.«opt_union/3»; split <;> simp_all

theorem opt_inter_term_r (d : Dispatcher) (a S : Term) :
    Elixir.Module.Types.Descr.«opt_intersection/3» d a (.atom "term") S = .ok a := by
  unfold Elixir.Module.Types.Descr.«opt_intersection/3»; split <;> simp_all

theorem fuse_term_l (d : Dispatcher) (b n : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» d (.atom "term") b n = .ok (.atom "nil") := by
  unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3»
  simp [Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1», getMapKeys]

theorem fuse_term_r (d : Dispatcher) (A : List (Term × Term)) (n : Term) :
    Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3» d (.map A) (.atom "term") n = .ok (.atom "nil") := by
  unfold Elixir.Module.Types.Descr.«opt_tuple_fuse_element/3»
  simp only [Elixir.Module.Types.Descr.«atom_or_bitmap_only?/1», getMapKeys]
  repeat' split
  all_goals simp_all [Lynx.Except.andAlso, Erlang.erlang.«==/2», Erlang.erlang.«map_size/1»]
  all_goals (repeat' split) <;> simp_all

end Elixir.STTDescrProofsTest.Nest

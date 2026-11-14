namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Element types hold only the top function type in their function fields. -/

def funTopT : Term := .tuple #[.atom "negation", .map []]

def FunTop (x : Term) : Prop := x = funTopT

theorem fun_top_inter (n : Nat) :
    Elixir.Module.Types.Descr.«bare_intersection/3» (D (n + 1)) (.atom "fun") funTopT funTopT = .ok funTopT := by
  have mrun := merge_with_eq (D (n + 1)) "Elixir.Module.Types.Descr" "-fun_repr_union/2-fun-0-" #[] [] []
    (fun _ _ _ => .nil) (by intro e me; simp at me)
  simp only [mergeList, mapEntries_nil] at mrun
  simp [funTopT, Elixir.Module.Types.Descr.«bare_intersection/3», Elixir.Module.Types.Descr.«fun_intersection/2»,
    Elixir.Module.Types.Descr.«fun_repr_union/2», Elixir.Module.Types.Descr.«symmetrical_merge/3», mrun, Erlang.erlang.«==/2»]

theorem fun_top_diff (n : Nat) :
    Elixir.Module.Types.Descr.«bare_difference/3» (D n) (.atom "fun") funTopT funTopT = .ok (.integer 0) := by
  simp [funTopT, Elixir.Module.Types.Descr.«bare_difference/3», Elixir.Module.Types.Descr.«fun_difference/2»,
    Elixir.Module.Types.Descr.«fun_repr_difference/2», Erlang.maps.«fold/3»,
    Erlang.erlang.«==/2», Erlang.erlang.«map_size/1»]

theorem fun_top_ne (d : Dispatcher) (S : Term) :
    Elixir.Module.Types.Descr.«empty_key?/3» d (.atom "fun") funTopT S = .ok (.atom "false") := by
  simp [funTopT, Elixir.Module.Types.Descr.«empty_key?/3», Elixir.Module.Types.Descr.«fun_empty?/2»]

theorem funF_top : FunF funTopT := ⟨Bool.false, [], rfl, fun q v h => by simp [mapLookup] at h⟩

theorem lh_funTop : lh funTopT = 0 := by
  have := lh_nil_map
  simp [funTopT, lh] at this ⊢
  exact this

theorem dn_funTop (p : Point) : dn "fun" (some funTopT) p = Bool.true := by
  simp [dn, funTopT, arityOf, mapLookup]

theorem funTopC {K : Nat} {FV : Term → (Term → Bool) → Prop} (hK : 1 ≤ K) (wit : ∃ a ρ, Resp ρ ∧ FV a ρ) :
    FunC K FunTop FV (fun _ => True) True where
  funF := fun h => h ▸ funF_top
  union := fun {x y} hx hy m w hm run => by
    subst hx; subst hy
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [funTopT, fun_top_union] at run
    cases run
    exact ⟨rfl, fun _ => by rw [← funTopT, lh_funTop]; simp⟩
  inter := fun {x y} hx hy m w hm run _ => by
    subst hx; subst hy
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [fun_top_inter] at run
    cases run
    exact ⟨rfl, fun _ => by simp [lh_funTop]⟩
  diff := fun {x y} hx hy m w hm run k => by
    subst hx; subst hy
    rw [fun_top_diff] at run
    cases run
    simp [kept] at k
  empty := fun {x} S {m} hx _ _ => by
    subst hx
    refine ⟨fun N _ _ h => ?_, fun _ => ⟨Bool.false, by simpa [boolAtom] using fun_top_ne (D m) (.map S),
      fun _ _ _ h => by cases h⟩⟩
    obtain ⟨a, ρ, r, f⟩ := wit
    have := h (0, a, ρ) r f
    rw [dn_funTop] at this
    cases this

/-! Element types are nested types of the plain laws, below their height. -/

section
variable {nd : Term} {E : Term → Prop} {V : Type} {den : Term → V → Prop} {tl : V → Prop} {K : Nat}

theorem tfield_nest {x : Term} (fx : TField E x) {N : Nat} (h : lh x < N) : OField (TupleOk (EB E N)) x := by
  rcases fx with top | wx
  · exact Or.inl top
  refine Or.inr ((bdd_lh_le wx (fun _ h => h) (lh x) (Nat.le_refl _)).mono fun t ⟨ht, le⟩ => ?_)
  obtain ⟨-, below⟩ := tlit_lh ht
  obtain ⟨⟨⟨k, tag, l, rfl, g, els⟩, nt⟩, -⟩ := ht
  exact ⟨⟨k, tag, l, rfl, g, fun e me => ⟨els e me, by have := (below k tag l rfl e me).1; omega⟩⟩, nt⟩

theorem mfield_nest {x : Term} (fx : MField E x) {N : Nat} (h : lh x < N) : OField (MapOk (EB E N)) x := by
  rcases fx with top | wx
  · exact Or.inl top
  refine Or.inr ((mbdd_lh_le wx (fun _ h => h) (lh x) (Nat.le_refl _)).mono fun t ⟨ht, le⟩ => ?_)
  obtain ⟨-, below⟩ := mlit_lh ht
  obtain ⟨⟨k, tag, l, rfl, g, ⟨fs, -⟩⟩, nt, -⟩ := ht
  obtain ⟨bf, bd⟩ := below k tag l rfl
  refine ⟨⟨k, tag, l, rfl, ?_, fun e me => ?_⟩, nt⟩
  · rcases g with rfl | rfl | ⟨dl, rfl, dv⟩
    · exact MapTag.atom_open
    · exact MapTag.atom_closed
    · refine Or.inr (Or.inr ⟨dl, rfl, fun e me => ⟨(dv.1 e me).2, ?_⟩⟩)
      have := bd e (by rw [domFields_fieldsTerm]; exact me); omega
  · obtain ⟨u, o, eu, hu⟩ := (fs e me).2
    exact ⟨u, o, eu, hu, by have := bf e me u o eu; omega⟩

theorem lf_nest (ef : EF nd E V den tl K) {x : Term} (fx : LF E x) {N : Nat} (hN : 0 < N) (h : lh x < N) :
    Bdd (LLit (EB E N)) x := by
  refine (nl_lit_le ef fx (fun _ h => h) (max (lh x) 1) (by omega) (fun _ => by omega)).mono fun t ⟨ht, le⟩ => ?_
  obtain ⟨k, a, b, rfl, ha, hb⟩ := ht
  rw [litH_eq] at le
  exact ⟨k, a, b, rfl, ⟨ha, by omega⟩, ⟨hb, by omega⟩⟩

end

end Elixir.STTDescrProofsTest.Nest

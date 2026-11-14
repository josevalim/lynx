namespace BddProofs

/-- BDD literals are leaves: triples with an integer key. -/
def IsLeaf (t : Term) : Prop := ∃ (k : Int) (x y : Term), t = .tuple #[.integer k, x, y]

/-- Ordered BDDs whose literals satisfy `ok`. -/
def Bdd (ok : Term → Prop) : Term → Prop
  | .atom "bdd_top" => True
  | .atom "bdd_bot" => True
  | .tuple ⟨[.integer _, lit, c, u, d]⟩ => IsLeaf lit ∧ ok lit ∧
      Bdd (fun t => ok t ∧ compare (fuel lit t) lit t = .lt) c ∧ Bdd (fun t => ok t ∧ compare (fuel lit t) lit t = .lt) u ∧
      Bdd (fun t => ok t ∧ compare (fuel lit t) lit t = .lt) d
  | .tuple ⟨[.integer k, x, y]⟩ => ok (.tuple #[.integer k, x, y])
  | _ => False

/-- The propositional semantics of a BDD, given the truth of each literal. -/
def eval (ρ : Term → Bool) : Term → Bool
  | .atom "bdd_top" => true
  | .tuple ⟨[_, lit, c, u, d]⟩ => (ρ lit && eval ρ c) || eval ρ u || (!ρ lit && eval ρ d)
  | .tuple ⟨[k, x, y]⟩ => ρ (.tuple #[k, x, y])
  | _ => false

theorem Bdd.shape {ok : Term → Prop} {b : Term} (wf : Bdd ok b) :
    b = .atom "bdd_top" ∨ b = .atom "bdd_bot" ∨ (∃ (k : Int) (x y : Term), b = .tuple #[.integer k, x, y]) ∨
      ∃ (h : Int) (lit c u d : Term), b = .tuple #[.integer h, lit, c, u, d] := by
  unfold Bdd at wf
  split at wf <;> simp_all

def bandI : Int → Int → Int
  | .ofNat x, .ofNat y => .ofNat (x &&& y)
  | .ofNat x, .negSucc y => .ofNat (x ^^^ (x &&& y))
  | .negSucc x, .ofNat y => .ofNat (y ^^^ (y &&& x))
  | .negSucc x, .negSucc y => .negSucc (x ||| y)

def bxorI : Int → Int → Int
  | .ofNat x, .ofNat y => .ofNat (x ^^^ y)
  | .ofNat x, .negSucc y => .negSucc (x ^^^ y)
  | .negSucc x, .ofNat y => .negSucc (x ^^^ y)
  | .negSucc x, .negSucc y => .ofNat (x ^^^ y)

@[simp] theorem band_int (x y : Int) : Erlang.erlang.«band/2» (.integer x) (.integer y) = .ok (.integer (bandI x y)) := by
  cases x <;> cases y <;> rfl
@[simp] theorem bxor_int (x y : Int) : Erlang.erlang.«bxor/2» (.integer x) (.integer y) = .ok (.integer (bxorI x y)) := by
  cases x <;> cases y <;> rfl
@[simp] theorem bsl_six (x : Int) : Erlang.erlang.«bsl/2» (.integer x) (.integer 6) = .ok (.integer (x <<< 6)) := rfl
@[simp] theorem bsr_two (x : Int) : Erlang.erlang.«bsr/2» (.integer x) (.integer 2) = .ok (.integer (x >>> 2)) := rfl

/-- Computations that return an integer. -/
def IntOk (e : Except Exception Term) : Prop := ∃ z : Int, e = .ok (.integer z)

theorem IntOk.bind {m : Except Exception Term} {f : Term → Except Exception Term} (hm : IntOk m)
    (hf : ∀ a : Int, IntOk (f (.integer a))) : IntOk (m >>= f) := by
  obtain ⟨a, rfl⟩ := hm
  exact hf a

theorem hash_ok {ok : Term → Prop} {b : Term} (wf : Bdd ok b) {e : Except Exception Term}
    (top : b = .atom "bdd_top" → IntOk e) (bot : b = .atom "bdd_bot" → IntOk e)
    (leaf : ∀ (k : Int) (x y : Term), b = .tuple #[.integer k, x, y] → IntOk e)
    (node : ∀ (h : Int) (lit c u d : Term), b = .tuple #[.integer h, lit, c, u, d] → IntOk e) : IntOk e := by
  rcases wf.shape with h | h | ⟨k, x, y, h⟩ | ⟨n, lit, c, u, d, h⟩
  · exact top h
  · exact bot h
  · exact leaf k x y h
  · exact node n lit c u d h

theorem node_new {okc oku okd : Term → Prop} (lit c u d : Term) (leaf : IsLeaf lit) (hc : Bdd okc c) (hu : Bdd oku u) (hd : Bdd okd d) :
    ∃ h : Int, Elixir.Module.Types.Descr.«bdd_node_new/4» lit c u d = .ok (.tuple #[.integer h, lit, c, u, d]) := by
  obtain ⟨k, x, y, rfl⟩ := leaf
  have hash : IntOk (Elixir.Module.Types.Descr.«bdd_compute_hash/4» (.tuple #[.integer k, x, y]) c u d) := by
    unfold Elixir.Module.Types.Descr.«bdd_compute_hash/4»
    refine IntOk.bind ?_ fun _ => ?_
    · apply Exists.intro
      simp only [band_int]
      try rfl
    refine IntOk.bind ?_ fun _ => ?_
    · refine hash_ok hc ?_ ?_ ?_ ?_ <;>
        (intros; subst_vars; apply Exists.intro
         simp only [band_int, pure, Except.pure]
         try rfl)
    refine IntOk.bind ?_ fun _ => ?_
    · apply Exists.intro
      simp only [Erlang.erlang.«+/2_integers», bsl_six, bsr_two, bxor_int, Lynx.Except.ok_bind]
      try rfl
    refine IntOk.bind ?_ fun _ => ?_
    · refine hash_ok hu ?_ ?_ ?_ ?_ <;>
        (intros; subst_vars; apply Exists.intro
         simp only [band_int, pure, Except.pure]
         try rfl)
    refine IntOk.bind ?_ fun _ => ?_
    · apply Exists.intro
      simp only [Erlang.erlang.«+/2_integers», bsl_six, bsr_two, bxor_int, Lynx.Except.ok_bind]
      try rfl
    refine IntOk.bind ?_ fun _ => ?_
    · refine hash_ok hd ?_ ?_ ?_ ?_ <;>
        (intros; subst_vars; apply Exists.intro
         simp only [band_int, pure, Except.pure]
         try rfl)
    refine IntOk.bind ?_ fun _ => ?_
    · apply Exists.intro
      simp only [Erlang.erlang.«+/2_integers», bsl_six, bsr_two, bxor_int, Lynx.Except.ok_bind]
      try rfl
    apply Exists.intro
    simp only [band_int]
    try rfl
  obtain ⟨h, run⟩ := hash
  exact ⟨h, by simp [Elixir.Module.Types.Descr.«bdd_node_new/4», run]⟩

/-- The literals of a node's children are above the node's literal. -/
abbrev Above (ok : Term → Prop) (lit : Term) : Term → Prop := fun t => ok t ∧ Term.compare (Term.fuel lit t) lit t = .lt

theorem Bdd.node_iff {ok : Term → Prop} {h : Int} {lit c u d : Term} :
    Bdd ok (.tuple #[.integer h, lit, c, u, d]) ↔
      IsLeaf lit ∧ ok lit ∧ Bdd (Above ok lit) c ∧ Bdd (Above ok lit) u ∧ Bdd (Above ok lit) d := by
  simp [Bdd]

theorem Bdd.leaf_iff {ok : Term → Prop} {k : Int} {x y : Term} :
    Bdd ok (.tuple #[.integer k, x, y]) ↔ ok (.tuple #[.integer k, x, y]) := by
  simp [Bdd]

theorem sizeOf_children (h lit c u d : Term) :
    sizeOf c < sizeOf (Term.tuple #[h, lit, c, u, d]) ∧ sizeOf u < sizeOf (Term.tuple #[h, lit, c, u, d]) ∧
      sizeOf d < sizeOf (Term.tuple #[h, lit, c, u, d]) := by
  simp only [Term.tuple.sizeOf_spec, Array.mk.sizeOf_spec, List.cons.sizeOf_spec,
    List.nil.sizeOf_spec]
  omega

/-- Induction over ordered BDDs. -/
theorem Bdd.induction {P : (Term → Prop) → Term → Prop}
    (top : ∀ ok, P ok (.atom "bdd_top")) (bot : ∀ ok, P ok (.atom "bdd_bot"))
    (leaf : ∀ ok (k : Int) x y, ok (.tuple #[.integer k, x, y]) → P ok (.tuple #[.integer k, x, y]))
    (node : ∀ ok (h : Int) lit c u d, IsLeaf lit → ok lit →
      Bdd (Above ok lit) c → Bdd (Above ok lit) u → Bdd (Above ok lit) d →
      P (Above ok lit) c → P (Above ok lit) u → P (Above ok lit) d →
      P ok (.tuple #[.integer h, lit, c, u, d])) :
    ∀ (ok : Term → Prop) (b : Term), Bdd ok b → P ok b := by
  suffices all : ∀ n, ∀ (ok : Term → Prop) (b : Term), sizeOf b ≤ n → Bdd ok b → P ok b from
    fun ok b => all _ ok b (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro ok b size; cases b <;> simp at size <;> omega
  | succ n ih =>
    intro ok b size wf
    rcases wf.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
    · exact top ok
    · exact bot ok
    · exact leaf ok k x y (Bdd.leaf_iff.mp wf)
    · obtain ⟨isLeaf, okLit, hc, hu, hd⟩ := Bdd.node_iff.mp wf
      obtain ⟨sc, su, sd⟩ := sizeOf_children (.integer h) lit c u d
      exact node ok h lit c u d isLeaf okLit hc hu hd (ih _ c (by omega) hc) (ih _ u (by omega) hu)
        (ih _ d (by omega) hd)

theorem Bdd.mono {ok ok' : Term → Prop} (h : ∀ t, ok t → ok' t) {b : Term} (wf : Bdd ok b) : Bdd ok' b := by
  revert ok'
  refine Bdd.induction (P := fun ok b => ∀ {ok'}, (∀ t, ok t → ok' t) → Bdd ok' b) ?_ ?_ ?_ ?_ ok b wf
  · intro ok ok' _; simp [Bdd]
  · intro ok ok' _; simp [Bdd]
  · intro ok k x y okb ok' h; exact Bdd.leaf_iff.mpr (h _ okb)
  · intro ok n lit c u d isLeaf okLit _ _ _ ihc ihu ihd ok' h
    have lift : ∀ t, Above ok lit t → Above ok' lit t := fun t ht => ⟨h t ht.1, ht.2⟩
    exact Bdd.node_iff.mpr ⟨isLeaf, h _ okLit, ihc lift, ihu lift, ihd lift⟩

/-- A BDD whose head is above `m` has all its literals above `m`. -/
def head : Term → Option Term
  | .tuple ⟨[_, lit, _, _, _]⟩ => some lit
  | .tuple ⟨[k, x, y]⟩ => some (.tuple #[k, x, y])
  | _ => none

theorem Bdd.raise {ok : Term → Prop} {b m : Term} (wf : Bdd ok b)
    (above : ∀ l, head b = some l → compare (fuel m l) m l = .lt) : Bdd (Above ok m) b := by
  rcases wf.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · simp [Bdd]
  · simp [Bdd]
  · exact Bdd.leaf_iff.mpr ⟨Bdd.leaf_iff.mp wf, above _ (by simp [head])⟩
  · obtain ⟨isLeaf, okLit, hc, hu, hd⟩ := Bdd.node_iff.mp wf
    have ml : compare (fuel m lit) m lit = .lt := above lit (by simp [head])
    have lift : ∀ t, Above ok lit t → Above (Above ok m) lit t :=
      fun t ht => ⟨⟨ht.1, Lynx.Term.compare_lt_trans ml ht.2⟩, ht.2⟩
    exact Bdd.node_iff.mpr ⟨isLeaf, ⟨okLit, ml⟩, hc.mono lift, hu.mono lift, hd.mono lift⟩

/-- A non-trivial BDD seen as a node: leaves `l` are `(l and top) or bot or (not l and bot)`. -/
def Split (a lit c u d : Term) : Prop :=
  (∃ h : Int, a = .tuple #[.integer h, lit, c, u, d]) ∨
    (a = lit ∧ IsLeaf lit ∧ c = .atom "bdd_top" ∧ u = .atom "bdd_bot" ∧ d = .atom "bdd_bot")

theorem head_some {ok : Term → Prop} {a l : Term} (wa : Bdd ok a) (ha : head a = some l) :
    (∃ (k : Int) (x y : Term), a = .tuple #[.integer k, x, y] ∧ l = a) ∨
      ∃ (h : Int) (c u d : Term), a = .tuple #[.integer h, l, c, u, d] := by
  rcases wa.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · simp [head] at ha
  · simp [head] at ha
  · simp [head] at ha; exact Or.inl ⟨k, x, y, rfl, ha.symm⟩
  · simp [head] at ha; subst ha; exact Or.inr ⟨h, c, u, d, rfl⟩

theorem head_shape {a l : Term} (ha : head a = some l) :
    (∃ x y z : Term, a = .tuple #[x, y, z] ∧ l = a) ∨ ∃ h c u d : Term, a = .tuple #[h, l, c, u, d] := by
  unfold head at ha
  split at ha
  · cases ha; exact Or.inr ⟨_, _, _, _, rfl⟩
  · cases ha; exact Or.inl ⟨_, _, _, rfl, rfl⟩
  · cases ha

theorem compare_lt {ok : Term → Prop} {a b la lb : Term} (wa : Bdd ok a) (ha : head a = some la)
    (hb : head b = some lb) (lt : compare (fuel la lb) la lb = .lt) :
    ∃ (h : Int) (c u d : Term), Elixir.Module.Types.Descr.«bdd_compare/2» a b =
      .ok (.tuple #[.atom "lt", .tuple #[.integer h, la, c, u, d], b]) ∧ Split a la c u d := by
  have top : Bdd (fun _ => True) (.atom "bdd_top") := by simp [Bdd]
  have bot : Bdd (fun _ => True) (.atom "bdd_bot") := by simp [Bdd]
  unfold Elixir.Module.Types.Descr.«bdd_compare/2»
  rcases head_some wa ha with ⟨k, x, y, rfl, rfl⟩ | ⟨n, c, u, d, rfl⟩
  · obtain ⟨h, run⟩ := node_new (.tuple #[.integer k, x, y]) _ _ _ ⟨k, x, y, rfl⟩ top bot bot
    refine ⟨h, _, _, _, ?_, Or.inr ⟨rfl, ⟨k, x, y, rfl⟩, rfl, rfl, rfl⟩⟩
    rcases head_shape hb with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
      simp [Erlang.erlang.«</2», lt, run]
  · refine ⟨n, c, u, d, ?_, Or.inl ⟨n, rfl⟩⟩
    rcases head_shape hb with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
      simp [Erlang.erlang.«</2», lt]

theorem compare_gt {ok : Term → Prop} {a b la lb : Term} (wb : Bdd ok b) (ha : head a = some la)
    (hb : head b = some lb) (gt : compare (fuel la lb) la lb = .gt) :
    ∃ (h : Int) (c u d : Term), Elixir.Module.Types.Descr.«bdd_compare/2» a b =
      .ok (.tuple #[.atom "gt", a, .tuple #[.integer h, lb, c, u, d]]) ∧ Split b lb c u d := by
  have top : Bdd (fun _ => True) (.atom "bdd_top") := by simp [Bdd]
  have bot : Bdd (fun _ => True) (.atom "bdd_bot") := by simp [Bdd]
  unfold Elixir.Module.Types.Descr.«bdd_compare/2»
  rcases head_some wb hb with ⟨k, x, y, rfl, rfl⟩ | ⟨n, c, u, d, rfl⟩
  · obtain ⟨h, run⟩ := node_new (.tuple #[.integer k, x, y]) _ _ _ ⟨k, x, y, rfl⟩ top bot bot
    refine ⟨h, _, _, _, ?_, Or.inr ⟨rfl, ⟨k, x, y, rfl⟩, rfl, rfl, rfl⟩⟩
    rcases head_shape ha with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
      simp [Erlang.erlang.«</2», Erlang.erlang.«>/2», gt, run]
  · refine ⟨n, c, u, d, ?_, Or.inl ⟨n, rfl⟩⟩
    rcases head_shape ha with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
      simp [Erlang.erlang.«</2», Erlang.erlang.«>/2», gt]

/-- The literal `bdd_compare/2` reads of a BDD. -/
theorem compare_eq {a b la lb : Term} (ha : head a = some la) (hb : head b = some lb)
    (eq : compare (fuel la lb) la lb = .eq) :
    Elixir.Module.Types.Descr.«bdd_compare/2» a b = .ok (.tuple #[.atom "eq", a, b]) := by
  unfold Elixir.Module.Types.Descr.«bdd_compare/2»
  rcases head_shape ha with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
    rcases head_shape hb with ⟨_, _, _, rfl, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
    simp [Erlang.erlang.«</2», Erlang.erlang.«>/2», eq]

/-! Semantics. -/

/-- Valuations give equal literals the same truth. -/
def Resp (ρ : Term → Bool) : Prop := ∀ a b, compare (fuel a b) a b = .eq → ρ a = ρ b

@[simp] theorem eval_top (ρ : Term → Bool) : eval ρ (.atom "bdd_top") = Bool.true := by simp [eval]
@[simp] theorem eval_bot (ρ : Term → Bool) : eval ρ (.atom "bdd_bot") = Bool.false := by simp [eval]
@[simp] theorem eval_node (ρ : Term → Bool) (h lit c u d : Term) :
    eval ρ (.tuple #[h, lit, c, u, d]) = ((ρ lit && eval ρ c) || eval ρ u || (!ρ lit && eval ρ d)) := by
  simp [eval]
@[simp] theorem eval_leaf (ρ : Term → Bool) (k x y : Term) :
    eval ρ (.tuple #[k, x, y]) = ρ (.tuple #[k, x, y]) := by
  simp [eval]

theorem Split.eval {a lit c u d : Term} (split : Split a lit c u d) (ρ : Term → Bool) :
    eval ρ a = ((ρ lit && eval ρ c) || eval ρ u || (!ρ lit && eval ρ d)) := by
  rcases split with ⟨h, rfl⟩ | ⟨rfl, ⟨k, x, y, rfl⟩, rfl, rfl, rfl⟩
  · simp
  · cases h : ρ (.tuple #[.integer k, x, y]) <;> simp [h]

theorem tuple3_exact {a₀ a₁ a₂ b : Term} (e : compareExact (fuel (.tuple #[a₀, a₁, a₂]) b) (.tuple #[a₀, a₁, a₂]) b = .eq) :
    ∃ b₀ b₁ b₂, b = .tuple #[b₀, b₁, b₂] ∧ compareExact (fuel a₀ b₀) a₀ b₀ = .eq ∧ compareExact (fuel a₁ b₁) a₁ b₁ = .eq ∧
      compareExact (fuel a₂ b₂) a₂ b₂ = .eq := by
  rw [compareExact_step] at e
  cases b <;> simp [Compare.compareStep] at e
  rename_i ys
  obtain ⟨ys⟩ := ys
  rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, rest⟩⟩⟩⟩ <;>
    simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
      List.compareLex_nil_cons] at e
  · exact ⟨b₀, b₁, b₂, rfl, e.1, e.2.1, e.2.2⟩

theorem tuple5_exact {a₀ a₁ a₂ a₃ a₄ b : Term} (e : compareExact (fuel (.tuple #[a₀, a₁, a₂, a₃, a₄]) b) (.tuple #[a₀, a₁, a₂, a₃, a₄]) b = .eq) :
    ∃ b₀ b₁ b₂ b₃ b₄, b = .tuple #[b₀, b₁, b₂, b₃, b₄] ∧ compareExact (fuel a₁ b₁) a₁ b₁ = .eq ∧
      compareExact (fuel a₂ b₂) a₂ b₂ = .eq ∧ compareExact (fuel a₃ b₃) a₃ b₃ = .eq ∧ compareExact (fuel a₄ b₄) a₄ b₄ = .eq := by
  rw [compareExact_step] at e
  cases b <;> simp [Compare.compareStep] at e
  rename_i ys
  obtain ⟨ys⟩ := ys
  rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨b₄, _ | ⟨b₅, rest⟩⟩⟩⟩⟩⟩ <;>
    simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
      List.compareLex_nil_cons] at e
  · exact ⟨b₀, b₁, b₂, b₃, b₄, rfl, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2⟩

/-- Exactly equal BDDs have the same semantics. -/
theorem eval_congr {ok : Term → Prop} {a : Term} (wa : Bdd ok a) {ρ : Term → Bool} (resp : Resp ρ) :
    ∀ {b}, compareExact (fuel a b) a b = .eq → eval ρ a = eval ρ b := by
  refine Bdd.induction (P := fun _ a => ∀ {b}, compareExact (fuel a b) a b = .eq → eval ρ a = eval ρ b)
    ?_ ?_ ?_ ?_ ok a wa
  · intro _ b e
    obtain rfl := (compareExact_eq_atom b "bdd_top").mp (Lynx.Term.compareExact_eq_symm e)
    rfl
  · intro _ b e
    obtain rfl := (compareExact_eq_atom b "bdd_bot").mp (Lynx.Term.compareExact_eq_symm e)
    rfl
  · intro _ k x y _ b e
    obtain ⟨b₀, b₁, b₂, rfl, -, -, -⟩ := tuple3_exact e
    simp only [eval_leaf]
    exact resp _ _ (compare_eq_of_compareExact_eq _ _ e)
  · intro _ h lit c u d _ _ _ _ _ ihc ihu ihd b e
    obtain ⟨b₀, b₁, b₂, b₃, b₄, rfl, el, ec, eu, ed⟩ := tuple5_exact e
    simp only [eval_node]
    rw [resp _ _ (compare_eq_of_compareExact_eq _ _ el), ihc ec, ihu eu, ihd ed]

theorem head_ok {ok : Term → Prop} {a l : Term} (wa : Bdd ok a) (ha : head a = some l) : ok l := by
  rcases head_some wa ha with ⟨k, x, y, rfl, rfl⟩ | ⟨h, c, u, d, rfl⟩
  · exact Bdd.leaf_iff.mp wa
  · exact (Bdd.node_iff.mp wa).2.1

theorem head_leaf {ok : Term → Prop} {a l : Term} (wa : Bdd ok a) (ha : head a = some l) : IsLeaf l := by
  rcases head_some wa ha with ⟨k, x, y, rfl, rfl⟩ | ⟨h, c, u, d, rfl⟩
  · exact ⟨k, x, y, rfl⟩
  · exact (Bdd.node_iff.mp wa).1

/-- The children of a split BDD hold literals above its head. -/
theorem Split.children {ok : Term → Prop} {a lit c u d : Term} (split : Split a lit c u d) (wa : Bdd ok a) :
    Bdd (Above ok lit) c ∧ Bdd (Above ok lit) u ∧ Bdd (Above ok lit) d := by
  rcases split with ⟨h, rfl⟩ | ⟨rfl, _, rfl, rfl, rfl⟩
  · exact (Bdd.node_iff.mp wa).2.2
  · simp [Bdd]

/-! Termination: each recursive call raises the smallest literal of its arguments. -/

/-- All literals of `b` are above `m`. -/
abbrev High (m : Term) : Term → Prop := Bdd (fun t => Term.compare (Term.fuel m t) m t = .lt)

open Classical in
/-- The literals of the universe that some argument does not exceed. -/
noncomputable def μ (U : List Term) (a b : Term) : Nat :=
  (U.filter fun m => !decide (High m a ∧ High m b)).length

theorem filter_le {α} (U : List α) (p q : α → Bool) (h : ∀ x ∈ U, p x → q x) :
    (U.filter p).length ≤ (U.filter q).length := by
  induction U with
  | nil => simp
  | cons x xs ih =>
    have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases px : p x <;> by_cases qx : q x <;> simp [px, qx] <;>
      first | omega | (have := h x List.mem_cons_self px; simp_all)

theorem filter_lt {α} (U : List α) (p q : α → Bool) (h : ∀ x ∈ U, p x → q x) {l : α} (hl : l ∈ U)
    (hp : p l = Bool.false) (hq : q l = Bool.true) : (U.filter p).length < (U.filter q).length := by
  induction U with
  | nil => simp at hl
  | cons x xs ih =>
    have le := filter_le xs p q (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases List.mem_cons.mp hl with rfl | hl
    · simp [hp, hq]; omega
    · have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) hl
      by_cases px : p x <;> by_cases qx : q x <;> simp [px, qx] <;>
        first | omega | (have := h x List.mem_cons_self px; simp_all)

theorem μ_le {U : List Term} {a b a' b' : Term}
    (mono : ∀ m, High m a → High m b → High m a' ∧ High m b') : μ U a' b' ≤ μ U a b := by
  unfold μ
  apply filter_le
  intro m _ hm
  simp at hm ⊢
  intro ha hb
  exact hm (mono m ha hb).1 (mono m ha hb).2

theorem μ_lt {U : List Term} {a b a' b' l : Term}
    (mono : ∀ m, High m a → High m b → High m a' ∧ High m b') (hl : l ∈ U)
    (old : ¬(High l a ∧ High l b)) (new : High l a' ∧ High l b') : μ U a' b' < μ U a b := by
  unfold μ
  refine filter_lt _ _ _ ?_ hl ?_ ?_
  · intro m _ hm
    simp at hm ⊢
    intro ha hb
    exact hm (mono m ha hb).1 (mono m ha hb).2
  · simp [new]
  · simp
    exact fun ha hb => old ⟨ha, hb⟩

/-- A BDD is never above its own head. -/
theorem not_high_head {ok : Term → Prop} {a l : Term} (_wa : Bdd ok a) (ha : head a = some l) : ¬High l a :=
  fun high => by have := head_ok high ha; simp at this

/-! BDDs without leaves, whose literals all sit in nodes. -/

def NoLeaf : Term → Prop
  | .atom "bdd_top" => True
  | .atom "bdd_bot" => True
  | .tuple ⟨[_, _, c, u, d]⟩ => NoLeaf c ∧ NoLeaf u ∧ NoLeaf d
  | _ => False

theorem NoLeaf.top : NoLeaf (.atom "bdd_top") := by simp [NoLeaf]
theorem NoLeaf.bot : NoLeaf (.atom "bdd_bot") := by simp [NoLeaf]

theorem NoLeaf.node {h lit c u d : Term} : NoLeaf (.tuple #[h, lit, c, u, d]) ↔ NoLeaf c ∧ NoLeaf u ∧ NoLeaf d := by
  simp [NoLeaf]

theorem NoLeaf.leaf {k x y : Term} (n : NoLeaf (.tuple #[k, x, y])) : False := by
  simp [NoLeaf] at n

theorem Split.noLeaf {a lit c u d : Term} (split : Split a lit c u d) (n : NoLeaf a) :
    NoLeaf c ∧ NoLeaf u ∧ NoLeaf d := by
  rcases split with ⟨h, rfl⟩ | ⟨rfl, ⟨k, x, y, rfl⟩, -⟩
  · exact NoLeaf.node.mp n
  · exact n.leaf.elim

/-! Unions. -/

def UnionOk (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_union/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ ∀ ρ, Resp ρ → eval ρ r = (eval ρ a || eval ρ b)

/-- What unions and removals guarantee, including that they keep BDDs without leaves. -/
def UnionOkN (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_union/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ (∀ ρ, Resp ρ → eval ρ r = (eval ρ a || eval ρ b)) ∧
      (NoLeaf a → NoLeaf b → NoLeaf r)

def RemoveOkN (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_remove/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ (∀ ρ, Resp ρ → (eval ρ r || eval ρ b) = (eval ρ a || eval ρ b)) ∧
      (NoLeaf a → NoLeaf b → NoLeaf r)

def RemoveBddOk (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_remove_bdd/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ (∀ ρ, Resp ρ → (eval ρ r || eval ρ b) = (eval ρ a || eval ρ b)) ∧
      (NoLeaf a → NoLeaf b → NoLeaf r)

/-- Every pair of BDDs over the universe below the measure `n` unites and removes. -/
def Below (U : List Term) (n : Nat) : Prop :=
  ∀ a b, Bdd (· ∈ U) a → Bdd (· ∈ U) b → μ U a b < n → UnionOkN a b ∧ RemoveOkN a b ∧ RemoveBddOk a b

theorem Bdd.top {ok : Term → Prop} : Bdd ok (.atom "bdd_top") := by simp [Bdd]
theorem Bdd.bot {ok : Term → Prop} : Bdd ok (.atom "bdd_bot") := by simp [Bdd]

theorem nontrivial_head {ok : Term → Prop} {a : Term} (wa : Bdd ok a) (t : a ≠ .atom "bdd_top")
    (f : a ≠ .atom "bdd_bot") : ∃ l, head a = some l := by
  rcases wa.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h, lit, c, u, d, rfl⟩
  · exact absurd rfl t
  · exact absurd rfl f
  · exact ⟨.tuple #[.integer k, x, y], by simp [head]⟩
  · exact ⟨lit, by simp [head]⟩

/-- Arguments above `m` keep the result above `m`. -/
theorem High.split {ok : Term → Prop} {a lit c u d m : Term} (split : Split a lit c u d) (_wa : Bdd ok a)
    (high : High m a) : High m c ∧ High m u ∧ High m d := by
  obtain ⟨hc, hu, hd⟩ := split.children high
  exact ⟨hc.mono fun _ h => h.1, hu.mono fun _ h => h.1, hd.mono fun _ h => h.1⟩

theorem Split.high {ok : Term → Prop} {a lit c u d : Term} (split : Split a lit c u d) (wa : Bdd ok a) :
    High lit c ∧ High lit u ∧ High lit d := by
  obtain ⟨hc, hu, hd⟩ := split.children wa
  exact ⟨hc.mono fun _ h => h.2, hu.mono fun _ h => h.2, hd.mono fun _ h => h.2⟩

theorem Split.head {a lit c u d : Term} (split : Split a lit c u d) : head a = some lit := by
  rcases split with ⟨h, rfl⟩ | ⟨rfl, ⟨k, x, y, rfl⟩, -⟩ <;> simp [BddProofs.head]

theorem Bdd.congr {ok : Term → Prop} {x la lb : Term} (e : Term.compare (Term.fuel la lb) la lb = .eq)
    (w : Bdd (Above ok lb) x) : Bdd (Above ok la) x :=
  w.mono fun t h => ⟨h.1, by rw [Lynx.Term.compare_congr_left e]; exact h.2⟩

theorem High.congr {x la lb : Term} (e : Term.compare (Term.fuel la lb) la lb = .eq) (w : High lb x) : High la x :=
  w.mono fun t h => by rw [Lynx.Term.compare_congr_left e]; exact h

theorem union_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
    (ih : Below U (μ U a b)) : UnionOkN a b := by
  by_cases same : compareExact (fuel b a) b a = .eq
  · refine ⟨a, ?_, fun ok wa _ => wa, fun ρ resp => ?_, fun na _ => na⟩
    · unfold Elixir.Module.Types.Descr.«bdd_union/2»
      simp [Erlang.erlang.«=:=/2», same]
    · rw [← eval_congr wb resp same]; simp
  by_cases ta : a = .atom "bdd_top"
  · subst ta
    refine ⟨.atom "bdd_top", ?_, fun ok _ _ => Bdd.top, fun ρ _ => by simp, fun _ _ => NoLeaf.top⟩
    unfold Elixir.Module.Types.Descr.«bdd_union/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases tb : b = .atom "bdd_top"
  · subst tb
    refine ⟨.atom "bdd_top", ?_, fun ok _ _ => Bdd.top, fun ρ _ => by simp, fun _ _ => NoLeaf.top⟩
    unfold Elixir.Module.Types.Descr.«bdd_union/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases fa : a = .atom "bdd_bot"
  · subst fa
    refine ⟨b, ?_, fun ok _ wb => wb, fun ρ _ => by simp, fun _ nb => nb⟩
    unfold Elixir.Module.Types.Descr.«bdd_union/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases fb : b = .atom "bdd_bot"
  · subst fb
    refine ⟨a, ?_, fun ok wa _ => wa, fun ρ _ => by simp, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_union/2»
    simp [Erlang.erlang.«=:=/2», same]
  obtain ⟨la, ha⟩ := nontrivial_head wa ta fa
  obtain ⟨lb, hb⟩ := nontrivial_head wb tb fb
  have lU : la ∈ U := head_ok wa ha
  have lbU : lb ∈ U := head_ok wb hb
  have lower : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
      High la a' ∧ High la b' → μ U a' b' < μ U a b :=
    fun mono new => μ_lt mono lU (fun hh => not_high_head wa ha hh.1) new
  rcases order : Term.compare (Term.fuel la lb) la lb
  · -- lt
    obtain ⟨h₀, c₁, u₁, d₁, run, split⟩ := compare_lt wa ha hb order
    have raiseB : ∀ {ok : Term → Prop}, Bdd ok b → Bdd (Above ok la) b :=
      fun w => w.raise fun l hl => by rw [hb] at hl; cases hl; exact order
    obtain ⟨hc, hu, hd⟩ := split.children wa
    obtain ⟨Hc, Hu, Hd⟩ := split.high wa
    have HB : High la b := (raiseB wb).mono fun _ h => h.2
    obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := (ih c₁ b (hc.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').1, hb'⟩) ⟨Hc, HB⟩)).2.1
    obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := (ih u₁ b (hu.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.1, hb'⟩) ⟨Hu, HB⟩)).1
    obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := (ih d₁ b (hd.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.2, hb'⟩) ⟨Hd, HB⟩)).2.1
    obtain ⟨h₁, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) (keep₁ _ hc (raiseB wb))
      (keep₂ _ hu (raiseB wb)) (keep₃ _ hd (raiseB wb))
    have body : Elixir.Module.Types.Descr.«bdd_union/2» a b =
        if compareExact (fuel r₃ r₁) r₃ r₁ = .eq then Elixir.Module.Types.Descr.«bdd_union/2» r₁ r₂
        else .ok (.tuple #[.integer h₁, la, r₁, r₂, r₃]) := by
      conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
      simp [Erlang.erlang.«=:=/2», same]
      simp [run, run₁, run₂, run₃, node]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
    by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq
    · obtain ⟨r, runr, keepr, semr, nlr⟩ := (ih r₁ r₂ (keep₁ _ (hc.mono fun _ h => h.1) wb)
        (keep₂ _ (hu.mono fun _ h => h.1) wb)
        (lower (fun m ha' hb' => ⟨keep₁ _ (High.split split wa ha').1 hb', keep₂ _ (High.split split wa ha').2.1 hb'⟩)
          ⟨keep₁ _ Hc HB, keep₂ _ Hu HB⟩)).1
      refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka okb => ?_, fun ρ resp => ?_,
        fun na nb => nlr (nl₁ (split.noLeaf na).1 nb) (nl₂ (split.noLeaf na).2.1 nb)⟩
      · obtain ⟨oc, ou, -⟩ := split.children oka
        exact keepr ok (keep₁ ok (oc.mono fun _ h => h.1) okb) (keep₂ ok (ou.mono fun _ h => h.1) okb)
      · have e₃ := eval_congr (keep₃ _ (hd.mono fun _ h => h.1) wb) resp post
        have s₁ := sem₁ ρ resp
        have s₂ := sem₂ ρ resp
        have s₃ := sem₃ ρ resp
        rw [semr ρ resp, split.eval ρ, s₂]
        rw [← e₃] at s₁
        rw [← e₃]
        revert s₁ s₃
        generalize eval ρ r₃ = R
        generalize eval ρ c₁ = C
        generalize eval ρ u₁ = V
        generalize eval ρ d₁ = D
        generalize eval ρ b = B
        generalize ρ la = L
        revert R C V D B L
        decide
    · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka okb => ?_, fun ρ resp => ?_,
        fun na nb => NoLeaf.node.mpr ⟨nl₁ (split.noLeaf na).1 nb, nl₂ (split.noLeaf na).2.1 nb,
          nl₃ (split.noLeaf na).2.2 nb⟩⟩
      · obtain ⟨oc, ou, od⟩ := split.children oka
        exact Bdd.node_iff.mpr ⟨head_leaf wa ha, head_ok oka ha, keep₁ _ oc (raiseB okb),
          keep₂ _ ou (raiseB okb), keep₃ _ od (raiseB okb)⟩
      · have s₁ := sem₁ ρ resp
        have s₂ := sem₂ ρ resp
        have s₃ := sem₃ ρ resp
        rw [eval_node, split.eval ρ, s₂]
        revert s₁ s₃
        generalize eval ρ r₁ = R₁
        generalize eval ρ r₃ = R₃
        generalize eval ρ c₁ = C
        generalize eval ρ u₁ = V
        generalize eval ρ d₁ = D
        generalize eval ρ b = B
        generalize ρ la = L
        revert R₁ R₃ C V D B L
        decide
  · -- eq
    have run := compare_eq ha hb order
    have lowerB : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
        High lb a' ∧ High lb b' → μ U a' b' < μ U a b :=
      fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
    have sameLit : ∀ ρ, Resp ρ → ρ la = ρ lb := fun ρ resp => resp _ _ order
    rcases head_some wa ha with ⟨k₁, x₁, y₁, rfl, rfl⟩ | ⟨h₁, c₁, u₁, d₁, rfl⟩ <;>
      rcases head_some wb hb with ⟨k₂, x₂, y₂, rfl, rfl⟩ | ⟨h₂, c₂, u₂, d₂, rfl⟩
    · -- two leaves
      refine ⟨_, ?_, fun ok oka _ => oka, fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
      · unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Erlang.erlang.«=:=/2», same, run]
      · simp [sameLit ρ resp]
    · -- a leaf below a node
      obtain ⟨-, -, hc, hu, hd⟩ := Bdd.node_iff.mp wb
      have Hu : High lb u₂ := hu.mono fun _ h => h.2
      have Hd : High lb d₂ := hd.mono fun _ h => h.2
      obtain ⟨h₃, node⟩ := node_new lb (.atom "bdd_top") u₂ d₂ (head_leaf wb hb) (Bdd.top (ok := fun _ => True)) hu hd
      have body : Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer k₁, x₁, y₁])
          (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) =
          if compareExact (fuel d₂ (.atom "bdd_top")) d₂ (.atom "bdd_top") = .eq then
            Elixir.Module.Types.Descr.«bdd_union/2» (.atom "bdd_top") u₂
          else .ok (.tuple #[.integer h₃, lb, .atom "bdd_top", u₂, d₂]) := by
        conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Erlang.erlang.«=:=/2», same, run, node]
        by_cases post : compareExact (fuel d₂ (.atom "bdd_top")) d₂ (.atom "bdd_top") = .eq <;> simp [post]
      by_cases post : compareExact (fuel d₂ (.atom "bdd_top")) d₂ (.atom "bdd_top") = .eq
      · obtain rfl := (compareExact_eq_atom _ _).mp post
        obtain ⟨r, runr, keepr, semr, -⟩ := (ih (.atom "bdd_top") u₂ Bdd.top (hu.mono fun _ h => h.1)
          (lowerB (fun m _ hb' => ⟨Bdd.top, (High.split (Or.inl ⟨h₂, rfl⟩) wb hb').2.1⟩) ⟨Bdd.top, Hu⟩)).1
        refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok _ okb => ?_,
          fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
        · exact keepr ok Bdd.top ((Bdd.node_iff.mp okb).2.2.2.1.mono fun _ h => h.1)
        · rw [semr ρ resp]
          cases hl : ρ lb <;> simp [hl, sameLit ρ resp]
      · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok _ okb => ?_,
          fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
        · obtain ⟨leaf, okl, -, ou, od⟩ := Bdd.node_iff.mp okb
          exact Bdd.node_iff.mpr ⟨leaf, okl, Bdd.top, ou, od⟩
        · cases hl : ρ lb <;> simp [hl, sameLit ρ resp]
    · -- a node above a leaf
      obtain ⟨-, -, hc, hu, hd⟩ := Bdd.node_iff.mp wa
      have Hu : High la u₁ := hu.mono fun _ h => h.2
      obtain ⟨h₃, node⟩ := node_new la (.atom "bdd_top") u₁ d₁ (head_leaf wa ha) (Bdd.top (ok := fun _ => True)) hu hd
      have body : Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer h₁, la, c₁, u₁, d₁])
          (.tuple #[.integer k₂, x₂, y₂]) =
          if compareExact (fuel d₁ (.atom "bdd_top")) d₁ (.atom "bdd_top") = .eq then
            Elixir.Module.Types.Descr.«bdd_union/2» (.atom "bdd_top") u₁
          else .ok (.tuple #[.integer h₃, la, .atom "bdd_top", u₁, d₁]) := by
        conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Erlang.erlang.«=:=/2», same, run, node]
        by_cases post : compareExact (fuel d₁ (.atom "bdd_top")) d₁ (.atom "bdd_top") = .eq <;> simp [post]
      by_cases post : compareExact (fuel d₁ (.atom "bdd_top")) d₁ (.atom "bdd_top") = .eq
      · obtain rfl := (compareExact_eq_atom _ _).mp post
        obtain ⟨r, runr, keepr, semr, -⟩ := (ih (.atom "bdd_top") u₁ Bdd.top (hu.mono fun _ h => h.1)
          (lower (fun m ha' _ => ⟨Bdd.top, (High.split (Or.inl ⟨h₁, rfl⟩) wa ha').2.1⟩) ⟨Bdd.top, Hu⟩)).1
        refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka _ => ?_,
          fun ρ resp => ?_, fun _ nb => nb.leaf.elim⟩
        · exact keepr ok Bdd.top ((Bdd.node_iff.mp oka).2.2.2.1.mono fun _ h => h.1)
        · rw [semr ρ resp]
          cases hl : ρ la <;> simp [hl, ← sameLit ρ resp]
      · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka _ => ?_,
          fun ρ resp => ?_, fun _ nb => nb.leaf.elim⟩
        · obtain ⟨leaf, okl, -, ou, od⟩ := Bdd.node_iff.mp oka
          exact Bdd.node_iff.mpr ⟨leaf, okl, Bdd.top, ou, od⟩
        · cases hl : ρ la <;> simp [hl, ← sameLit ρ resp]
    · -- two nodes
      have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
      have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
      obtain ⟨hc₁, hu₁, hd₁⟩ := splitA.children wa
      obtain ⟨hc₂, hu₂, hd₂⟩ := splitB.children wb
      obtain ⟨Hc₁, Hu₁, Hd₁⟩ := splitA.high wa
      obtain ⟨Hc₂, Hu₂, Hd₂⟩ := splitB.high wb
      obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := (ih c₁ c₂ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1)
        (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').1, (High.split splitB wb hb').1⟩)
          ⟨Hc₁, Hc₂.congr order⟩)).1
      obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := (ih u₁ u₂ (hu₁.mono fun _ h => h.1) (hu₂.mono fun _ h => h.1)
        (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.1, (High.split splitB wb hb').2.1⟩)
          ⟨Hu₁, Hu₂.congr order⟩)).1
      obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := (ih d₁ d₂ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1)
        (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.2, (High.split splitB wb hb').2.2⟩)
          ⟨Hd₁, Hd₂.congr order⟩)).1
      obtain ⟨h₃, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) (keep₁ _ hc₁ (hc₂.congr order))
        (keep₂ _ hu₁ (hu₂.congr order)) (keep₃ _ hd₁ (hd₂.congr order))
      have body : Elixir.Module.Types.Descr.«bdd_union/2» (.tuple #[.integer h₁, la, c₁, u₁, d₁])
          (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) =
          if compareExact (fuel r₃ r₁) r₃ r₁ = .eq then Elixir.Module.Types.Descr.«bdd_union/2» r₁ r₂
          else .ok (.tuple #[.integer h₃, la, r₁, r₂, r₃]) := by
        conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
        simp [Erlang.erlang.«=:=/2», same, run, run₁, run₂, run₃, node]
        by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq
      · obtain ⟨r, runr, keepr, semr, nlr⟩ := (ih r₁ r₂ (keep₁ _ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1))
          (keep₂ _ (hu₁.mono fun _ h => h.1) (hu₂.mono fun _ h => h.1))
          (lower (fun m ha' hb' => ⟨keep₁ _ (High.split splitA wa ha').1 (High.split splitB wb hb').1,
            keep₂ _ (High.split splitA wa ha').2.1 (High.split splitB wb hb').2.1⟩)
            ⟨keep₁ _ Hc₁ (Hc₂.congr order), keep₂ _ Hu₁ (Hu₂.congr order)⟩)).1
        refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka okb => ?_,
          fun ρ resp => ?_, fun na nb => nlr (nl₁ (NoLeaf.node.mp na).1 (NoLeaf.node.mp nb).1)
            (nl₂ (NoLeaf.node.mp na).2.1 (NoLeaf.node.mp nb).2.1)⟩
        · obtain ⟨oc₁, ou₁, -⟩ := splitA.children oka
          obtain ⟨oc₂, ou₂, -⟩ := splitB.children okb
          exact keepr ok (keep₁ ok (oc₁.mono fun _ h => h.1) (oc₂.mono fun _ h => h.1))
            (keep₂ ok (ou₁.mono fun _ h => h.1) (ou₂.mono fun _ h => h.1))
        · have e₃ := eval_congr (keep₃ _ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1)) resp post
          have s₁ := sem₁ ρ resp
          have s₂ := sem₂ ρ resp
          have s₃ := sem₃ ρ resp
          rw [semr ρ resp, eval_node, eval_node, s₁, s₂, ← sameLit ρ resp]
          rw [e₃, s₁] at s₃
          revert s₃
          generalize ρ la = L
          generalize eval ρ c₁ = C₁
          generalize eval ρ c₂ = C₂
          generalize eval ρ d₁ = D₁
          generalize eval ρ d₂ = D₂
          generalize eval ρ u₁ = U₁
          generalize eval ρ u₂ = U₂
          revert L C₁ C₂ D₁ D₂ U₁ U₂
          decide
      · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka okb => ?_,
          fun ρ resp => ?_, fun na nb => NoLeaf.node.mpr ⟨nl₁ (NoLeaf.node.mp na).1 (NoLeaf.node.mp nb).1,
            nl₂ (NoLeaf.node.mp na).2.1 (NoLeaf.node.mp nb).2.1, nl₃ (NoLeaf.node.mp na).2.2 (NoLeaf.node.mp nb).2.2⟩⟩
        · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
          obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
          exact Bdd.node_iff.mpr ⟨head_leaf wa ha, head_ok oka ha, keep₁ _ oc₁ (oc₂.congr order),
            keep₂ _ ou₁ (ou₂.congr order), keep₃ _ od₁ (od₂.congr order)⟩
        · rw [eval_node, eval_node, eval_node, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp, ← sameLit ρ resp]
          cases ρ la <;> simp [Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
  · -- gt
    have order' : Term.compare (Term.fuel lb la) lb la = .lt := Lynx.Term.compare_lt_of_gt order
    obtain ⟨h₀, c₂, u₂, d₂, run, split⟩ := compare_gt wb ha hb order
    have lowerB : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
        High lb a' ∧ High lb b' → μ U a' b' < μ U a b :=
      fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
    have raiseA : ∀ {ok : Term → Prop}, Bdd ok a → Bdd (Above ok lb) a :=
      fun w => w.raise fun l hl => by rw [ha] at hl; cases hl; exact order'
    obtain ⟨hc, hu, hd⟩ := split.children wb
    obtain ⟨Hc, Hu, Hd⟩ := split.high wb
    have HA : High lb a := (raiseA wa).mono fun _ h => h.2
    obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := (ih c₂ a (hc.mono fun _ h => h.1) wa
      (lowerB (fun m ha' hb' => ⟨(High.split split wb hb').1, ha'⟩) ⟨Hc, HA⟩)).2.1
    obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := (ih a u₂ wa (hu.mono fun _ h => h.1)
      (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.1⟩) ⟨HA, Hu⟩)).1
    obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := (ih d₂ a (hd.mono fun _ h => h.1) wa
      (lowerB (fun m ha' hb' => ⟨(High.split split wb hb').2.2, ha'⟩) ⟨Hd, HA⟩)).2.1
    obtain ⟨h₁, node⟩ := node_new lb r₁ r₂ r₃ (head_leaf wb hb) (keep₁ _ hc (raiseA wa))
      (keep₂ _ (raiseA wa) hu) (keep₃ _ hd (raiseA wa))
    have body : Elixir.Module.Types.Descr.«bdd_union/2» a b =
        if compareExact (fuel r₃ r₁) r₃ r₁ = .eq then Elixir.Module.Types.Descr.«bdd_union/2» r₁ r₂
        else .ok (.tuple #[.integer h₁, lb, r₁, r₂, r₃]) := by
      conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_union/2»
      simp [Erlang.erlang.«=:=/2», same]
      simp [run, run₁, run₂, run₃, node]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
    by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq
    · obtain ⟨r, runr, keepr, semr, nlr⟩ := (ih r₁ r₂ (keep₁ _ (hc.mono fun _ h => h.1) wa)
        (keep₂ _ wa (hu.mono fun _ h => h.1))
        (lowerB (fun m ha' hb' => ⟨keep₁ _ (High.split split wb hb').1 ha', keep₂ _ ha' (High.split split wb hb').2.1⟩)
          ⟨keep₁ _ Hc HA, keep₂ _ HA Hu⟩)).1
      refine ⟨r, by rw [body, ite_eq_left_of_eq_true _ _ (eq_true post), runr], fun ok oka okb => ?_, fun ρ resp => ?_,
        fun na nb => nlr (nl₁ (split.noLeaf nb).1 na) (nl₂ na (split.noLeaf nb).2.1)⟩
      · obtain ⟨oc, ou, -⟩ := split.children okb
        exact keepr ok (keep₁ ok (oc.mono fun _ h => h.1) oka) (keep₂ ok oka (ou.mono fun _ h => h.1))
      · have e₃ := eval_congr (keep₃ _ (hd.mono fun _ h => h.1) wa) resp post
        have s₁ := sem₁ ρ resp
        have s₂ := sem₂ ρ resp
        have s₃ := sem₃ ρ resp
        rw [semr ρ resp, split.eval ρ, s₂]
        rw [← e₃] at s₁
        rw [← e₃]
        revert s₁ s₃
        generalize eval ρ r₃ = R
        generalize eval ρ c₂ = C
        generalize eval ρ u₂ = V
        generalize eval ρ d₂ = D
        generalize eval ρ a = A
        generalize ρ lb = L
        revert R C V D A L
        decide
    · refine ⟨_, by rw [body, ite_eq_right_of_eq_false _ _ (eq_false post)], fun ok oka okb => ?_, fun ρ resp => ?_,
        fun na nb => NoLeaf.node.mpr ⟨nl₁ (split.noLeaf nb).1 na, nl₂ na (split.noLeaf nb).2.1,
          nl₃ (split.noLeaf nb).2.2 na⟩⟩
      · obtain ⟨oc, ou, od⟩ := split.children okb
        exact Bdd.node_iff.mpr ⟨head_leaf wb hb, head_ok okb hb, keep₁ _ oc (raiseA oka),
          keep₂ _ (raiseA oka) ou, keep₃ _ od (raiseA oka)⟩
      · have s₁ := sem₁ ρ resp
        have s₂ := sem₂ ρ resp
        have s₃ := sem₃ ρ resp
        rw [eval_node, split.eval ρ, s₂]
        revert s₁ s₃
        generalize eval ρ r₁ = R₁
        generalize eval ρ r₃ = R₃
        generalize eval ρ c₂ = C
        generalize eval ρ u₂ = V
        generalize eval ρ d₂ = D
        generalize eval ρ a = A
        generalize ρ lb = L
        revert R₁ R₃ C V D A L
        decide

theorem Below.mono {U : List Term} {n m : Nat} (le : m ≤ n) (below : Below U n) : Below U m :=
  fun a b wa wb lt => below a b wa wb (by omega)

/-- Removing a BDD from another one that is not a node above it. -/
theorem remove_bdd_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
    (ih : Below U (μ U a b)) : RemoveBddOk a b := by
  by_cases same : compareExact (fuel b a) b a = .eq
  · refine ⟨.atom "bdd_bot", ?_, fun ok _ _ => Bdd.bot, fun ρ resp => ?_, fun _ _ => NoLeaf.bot⟩
    · unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
      simp [Erlang.erlang.«=:=/2», same]
    · rw [eval_congr wb resp same]; simp
  rcases wa.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h₁, la, c₁, u₁, d₁, rfl⟩
  · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
    simp [Erlang.erlang.«=:=/2», same]
  · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
    simp [Erlang.erlang.«=:=/2», same]
  · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
    simp [Erlang.erlang.«=:=/2», same]
  rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h₂, lb, c₂, u₂, d₂, rfl⟩
  · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
    simp [Erlang.erlang.«=:=/2», same]
  · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
    simp [Erlang.erlang.«=:=/2», same]
  · refine ⟨_, ?_, fun ok oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
    simp [Erlang.erlang.«=:=/2», same]
  have ha : head (.tuple #[.integer h₁, la, c₁, u₁, d₁]) = some la := by simp [head]
  have hb : head (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) = some lb := by simp [head]
  have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
  have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
  have lU : la ∈ U := head_ok wa ha
  have lbU : lb ∈ U := head_ok wb hb
  have lower : ∀ {a' b'}, (∀ m, High m (.tuple #[.integer h₁, la, c₁, u₁, d₁]) → High m (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) → High m a' ∧ High m b') →
      High la a' ∧ High la b' → μ U a' b' < μ U (.tuple #[.integer h₁, la, c₁, u₁, d₁]) (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) :=
    fun mono new => μ_lt mono lU (fun hh => not_high_head wa ha hh.1) new
  have lowerB : ∀ {a' b'}, (∀ m, High m (.tuple #[.integer h₁, la, c₁, u₁, d₁]) → High m (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) → High m a' ∧ High m b') →
      High lb a' ∧ High lb b' → μ U a' b' < μ U (.tuple #[.integer h₁, la, c₁, u₁, d₁]) (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) :=
    fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
  obtain ⟨hc₁, hu₁, hd₁⟩ := splitA.children wa
  obtain ⟨hc₂, hu₂, hd₂⟩ := splitB.children wb
  obtain ⟨Hc₁, Hu₁, Hd₁⟩ := splitA.high wa
  obtain ⟨Hc₂, Hu₂, Hd₂⟩ := splitB.high wb
  rcases order : Term.compare (Term.fuel la lb) la lb
  · -- lt: remove the right BDD from each branch
    have raiseB : ∀ {ok : Term → Prop}, Bdd ok (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) →
        Bdd (Above ok la) (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) :=
      fun w => w.raise fun l hl => by rw [hb] at hl; cases hl; exact order
    have HB := (raiseB wb).mono fun _ h => h.2
    obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := (ih c₁ _ (hc₁.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').1, hb'⟩) ⟨Hc₁, HB⟩)).2.2
    obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := (ih u₁ _ (hu₁.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.1, hb'⟩) ⟨Hu₁, HB⟩)).2.2
    obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := (ih d₁ _ (hd₁.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.2, hb'⟩) ⟨Hd₁, HB⟩)).2.2
    obtain ⟨h₃, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) (keep₁ _ hc₁ (raiseB wb))
      (keep₂ _ hu₁ (raiseB wb)) (keep₃ _ hd₁ (raiseB wb))
    refine ⟨.tuple #[.integer h₃, la, r₁, r₂, r₃], ?_, fun ok oka okb => ?_, fun ρ resp => ?_,
      fun na nb => NoLeaf.node.mpr ⟨nl₁ (NoLeaf.node.mp na).1 nb, nl₂ (NoLeaf.node.mp na).2.1 nb,
        nl₃ (NoLeaf.node.mp na).2.2 nb⟩⟩
    · unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
      simp [Erlang.erlang.«=:=/2», same, Erlang.erlang.«</2», order, run₁, run₂, run₃, node]
    · obtain ⟨oc, ou, od⟩ := splitA.children oka
      exact Bdd.node_iff.mpr ⟨head_leaf wa ha, head_ok oka ha, keep₁ _ oc (raiseB okb),
        keep₂ _ ou (raiseB okb), keep₃ _ od (raiseB okb)⟩
    · have s₁ := sem₁ ρ resp
      have s₂ := sem₂ ρ resp
      have s₃ := sem₃ ρ resp
      simp only [eval_node] at s₁ s₂ s₃ ⊢
      revert s₁ s₂ s₃
      generalize ρ la = L
      generalize ρ lb = L'
      generalize eval ρ c₂ = C₂
      generalize eval ρ u₂ = U₂
      generalize eval ρ d₂ = D₂
      generalize eval ρ c₁ = C₁
      generalize eval ρ u₁ = U₁
      generalize eval ρ d₁ = D₁
      generalize eval ρ r₁ = R₁
      generalize eval ρ r₂ = R₂
      generalize eval ρ r₃ = R₃
      revert L L' C₂ U₂ D₂ C₁ U₁ D₁ R₁ R₂ R₃
      decide
  · -- eq: remove each branch, and the union branch of the right BDD
    obtain ⟨x₁, runx₁, keepx₁, semx₁, nlx₁⟩ := (ih c₁ c₂ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1)
      (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').1, (High.split splitB wb hb').1⟩)
        ⟨Hc₁, Hc₂.congr order⟩)).2.1
    obtain ⟨x₂, runx₂, keepx₂, semx₂, nlx₂⟩ := (ih x₁ u₂ (keepx₁ _ (hc₁.mono fun _ h => h.1) (hc₂.mono fun _ h => h.1))
      (hu₂.mono fun _ h => h.1)
      (lower (fun m ha' hb' => ⟨keepx₁ _ (High.split splitA wa ha').1 (High.split splitB wb hb').1,
        (High.split splitB wb hb').2.1⟩) ⟨keepx₁ _ Hc₁ (Hc₂.congr order), Hu₂.congr order⟩)).2.1
    obtain ⟨y₁, runy₁, keepy₁, semy₁, nly₁⟩ := (ih d₁ d₂ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1)
      (lower (fun m ha' hb' => ⟨(High.split splitA wa ha').2.2, (High.split splitB wb hb').2.2⟩)
        ⟨Hd₁, Hd₂.congr order⟩)).2.1
    obtain ⟨y₂, runy₂, keepy₂, semy₂, nly₂⟩ := (ih y₁ u₂ (keepy₁ _ (hd₁.mono fun _ h => h.1) (hd₂.mono fun _ h => h.1))
      (hu₂.mono fun _ h => h.1)
      (lower (fun m ha' hb' => ⟨keepy₁ _ (High.split splitA wa ha').2.2 (High.split splitB wb hb').2.2,
        (High.split splitB wb hb').2.1⟩) ⟨keepy₁ _ Hd₁ (Hd₂.congr order), Hu₂.congr order⟩)).2.1
    have bx := keepx₂ _ (keepx₁ _ hc₁ (hc₂.congr order)) (hu₂.congr order)
    have byy := keepy₂ _ (keepy₁ _ hd₁ (hd₂.congr order)) (hu₂.congr order)
    obtain ⟨h₃, node⟩ := node_new la x₂ u₁ y₂ (head_leaf wa ha) bx hu₁ byy
    refine ⟨.tuple #[.integer h₃, la, x₂, u₁, y₂], ?_, fun ok oka okb => ?_, fun ρ resp => ?_,
      fun na nb => NoLeaf.node.mpr ⟨nlx₂ (nlx₁ (NoLeaf.node.mp na).1 (NoLeaf.node.mp nb).1) (NoLeaf.node.mp nb).2.1,
        (NoLeaf.node.mp na).2.1, nly₂ (nly₁ (NoLeaf.node.mp na).2.2 (NoLeaf.node.mp nb).2.2) (NoLeaf.node.mp nb).2.1⟩⟩
    · unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
      simp [Erlang.erlang.«=:=/2», same, Erlang.erlang.«</2», Erlang.erlang.«>/2», order,
        runx₁, runx₂, runy₁, runy₂, node]
    · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
      obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
      exact Bdd.node_iff.mpr ⟨head_leaf wa ha, head_ok oka ha,
        keepx₂ _ (keepx₁ _ oc₁ (oc₂.congr order)) (ou₂.congr order), ou₁,
        keepy₂ _ (keepy₁ _ od₁ (od₂.congr order)) (ou₂.congr order)⟩
    · have s₁ := semx₁ ρ resp
      have s₂ := semx₂ ρ resp
      have s₃ := semy₁ ρ resp
      have s₄ := semy₂ ρ resp
      have l := resp _ _ order
      simp only [eval_node]
      revert s₁ s₂ s₃ s₄ l
      generalize ρ la = L
      generalize ρ lb = L'
      generalize eval ρ c₂ = C₂
      generalize eval ρ u₂ = U₂
      generalize eval ρ d₂ = D₂
      generalize eval ρ c₁ = C₁
      generalize eval ρ u₁ = U₁
      generalize eval ρ d₁ = D₁
      generalize eval ρ x₁ = X₁
      generalize eval ρ x₂ = X₂
      generalize eval ρ y₁ = Y₁
      generalize eval ρ y₂ = Y₂
      revert L L' C₂ U₂ D₂ C₁ U₁ D₁ X₁ X₂ Y₁ Y₂
      decide
  · -- gt: what the right BDD always removes
    have order' : Term.compare (Term.fuel lb la) lb la = .lt := Lynx.Term.compare_lt_of_gt order
    have raiseA : ∀ {ok : Term → Prop}, Bdd ok (.tuple #[.integer h₁, la, c₁, u₁, d₁]) →
        Bdd (Above ok lb) (.tuple #[.integer h₁, la, c₁, u₁, d₁]) :=
      fun w => w.raise fun l hl => by rw [ha] at hl; cases hl; exact order'
    have HA := (raiseA wa).mono fun _ h => h.2
    obtain ⟨r, run, keep, sem, nl⟩ := (ih _ u₂ wa (hu₂.mono fun _ h => h.1)
      (lowerB (fun m ha' hb' => ⟨ha', (High.split splitB wb hb').2.1⟩) ⟨HA, Hu₂⟩)).2.1
    refine ⟨r, ?_, fun ok oka okb => keep ok oka ((splitB.children okb).2.1.mono fun _ h => h.1),
      fun ρ resp => ?_, fun na nb => nl na (NoLeaf.node.mp nb).2.1⟩
    · unfold Elixir.Module.Types.Descr.«bdd_remove_bdd/2»
      have notLt : Term.compare (Term.fuel la lb) la lb ≠ .lt := by rw [order]; decide
      simp [Erlang.erlang.«=:=/2», same, Erlang.erlang.«</2», Erlang.erlang.«>/2», order, run]
    · have s := sem ρ resp
      rw [eval_node]
      revert s
      generalize eval ρ (.tuple #[.integer h₁, la, c₁, u₁, d₁]) = A
      generalize ρ lb = L
      generalize eval ρ c₂ = C₂
      generalize eval ρ u₂ = U₂
      generalize eval ρ d₂ = D₂
      generalize eval ρ r = R
      revert A L C₂ U₂ D₂ R
      decide

/-- Removing a BDD from another one. -/
theorem remove_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
    (ih : Below U (μ U a b)) : RemoveOkN a b := by
  rcases wb.shape with rfl | rfl | ⟨k, x, y, rfl⟩ | ⟨h₂, lb, c₂, u₂, d₂, rfl⟩
  · refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ _ => by simp, fun _ _ => NoLeaf.bot⟩
    simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
  · refine ⟨a, ?_, fun _ oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
  · -- removing a leaf
    have leafRun : Elixir.Module.Types.Descr.«bdd_remove/2» a (.tuple #[.integer k, x, y]) =
        Elixir.Module.Types.Descr.«bdd_remove_leaf/2» a (.tuple #[.integer k, x, y]) := by
      simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
    have fallback : ¬(∃ (h : Int) (la c u d : Term), a = .tuple #[.integer h, la, c, u, d] ∧
        compareExact (fuel (.tuple #[.integer k, x, y]) la) (.tuple #[.integer k, x, y]) la = .eq) → RemoveOkN a (.tuple #[.integer k, x, y]) := by
      intro notFirst
      have run : Elixir.Module.Types.Descr.«bdd_remove_leaf/2» a (.tuple #[.integer k, x, y]) =
          if compareExact (fuel (.tuple #[.integer k, x, y]) a) (.tuple #[.integer k, x, y]) a = .eq then .ok (.atom "bdd_bot") else .ok a := by
        unfold Elixir.Module.Types.Descr.«bdd_remove_leaf/2»
        rcases wa.shape with rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨h, la, c, u, d, rfl⟩
        · by_cases same : compareExact (fuel (.tuple #[.integer k, x, y]) (.atom "bdd_top")) (.tuple #[.integer k, x, y]) (.atom "bdd_top") = .eq <;>
            simp [Erlang.erlang.«=:=/2», same]
        · by_cases same : compareExact (fuel (.tuple #[.integer k, x, y]) (.atom "bdd_bot")) (.tuple #[.integer k, x, y]) (.atom "bdd_bot") = .eq <;>
            simp [Erlang.erlang.«=:=/2», same]
        · rename_i k' x' y'
          by_cases same : compareExact (fuel (.tuple #[.integer k, x, y]) (.tuple #[.integer k', x', y'])) (.tuple #[.integer k, x, y]) (.tuple #[.integer k', x', y']) = .eq <;>
            simp [Erlang.erlang.«=:=/2», same]
        · have ne : ¬compareExact (fuel (.tuple #[.integer k, x, y]) la) (.tuple #[.integer k, x, y]) la = .eq := fun e => notFirst ⟨h, la, c, u, d, rfl, e⟩
          by_cases same : compareExact (fuel (.tuple #[.integer k, x, y]) (.tuple #[.integer h, la, c, u, d])) (.tuple #[.integer k, x, y]) (.tuple #[.integer h, la, c, u, d]) = .eq <;>
            simp [Erlang.erlang.«=:=/2», same, ne]
      by_cases same : compareExact (fuel (.tuple #[.integer k, x, y]) a) (.tuple #[.integer k, x, y]) a = .eq
      · refine ⟨.atom "bdd_bot", by rw [leafRun, run, ite_eq_left same], fun _ _ _ => Bdd.bot, fun ρ resp => ?_,
          fun _ _ => NoLeaf.bot⟩
        rw [eval_congr wb resp same]; simp
      · exact ⟨a, by rw [leafRun, run, ite_eq_right same], fun _ oka _ => oka, fun ρ _ => rfl, fun na _ => na⟩
    by_cases first : ∃ (h : Int) (la c u d : Term), a = .tuple #[.integer h, la, c, u, d] ∧
        compareExact (fuel (.tuple #[.integer k, x, y]) la) (.tuple #[.integer k, x, y]) la = .eq
    · obtain ⟨h, la, c, u, d, rfl, e⟩ := first
      have ha : head (.tuple #[.integer h, la, c, u, d]) = some la := by simp [head]
      have splitA : Split _ la c u d := Or.inl ⟨h, rfl⟩
      obtain ⟨hc, hu, hd⟩ := splitA.children wa
      have wl : Bdd (· ∈ U) la := by
        obtain ⟨k', x', y', rfl⟩ := head_leaf wa ha
        exact Bdd.leaf_iff.mpr (head_ok wa ha)
      have highLit : ∀ {m}, High m (.tuple #[.integer h, la, c, u, d]) → High m la := fun high => by
        obtain ⟨k', x', y', rfl⟩ := head_leaf wa ha
        exact Bdd.leaf_iff.mpr (head_ok high ha)
      have okLit : ∀ {ok : Term → Prop}, Bdd ok (.tuple #[.integer h, la, c, u, d]) → Bdd ok la := fun w => by
        obtain ⟨k', x', y', rfl⟩ := head_leaf wa ha
        exact Bdd.leaf_iff.mpr (head_ok w ha)
      obtain ⟨r₁, run₁, keep₁, sem₁, -⟩ := union_step U la u wl (hu.mono fun _ h => h.1)
        (ih.mono (μ_le fun m ha' _ => ⟨highLit ha', (High.split splitA wa ha').2.1⟩))
      have wr₁ := keep₁ _ wl (hu.mono fun _ h => h.1)
      obtain ⟨r₂, run₂, keep₂, sem₂, -⟩ := union_step U r₁ d wr₁ (hd.mono fun _ h => h.1)
        (ih.mono (μ_le fun m ha' _ =>
          ⟨keep₁ _ (highLit ha') (High.split splitA wa ha').2.1, (High.split splitA wa ha').2.2⟩))
      refine ⟨r₂, ?_, fun ok oka _ => ?_, fun ρ resp => ?_, fun _ nb => nb.leaf.elim⟩
      · rw [leafRun]
        unfold Elixir.Module.Types.Descr.«bdd_remove_leaf/2»
        simp [Erlang.erlang.«=:=/2», e, run₁, run₂]
      · obtain ⟨-, ou, od⟩ := splitA.children oka
        exact keep₂ ok (keep₁ ok (okLit oka) (ou.mono fun _ h => h.1)) (od.mono fun _ h => h.1)
      · have l : ρ (.tuple #[.integer k, x, y]) = ρ la := resp _ _ (compare_eq_of_compareExact_eq _ _ e)
        rw [sem₂ ρ resp, sem₁ ρ resp]
        obtain ⟨k', x', y', rfl⟩ := head_leaf wa ha
        simp only [eval_node, eval_leaf, l]
        cases ρ (.tuple #[.integer k', x', y']) <;> simp [Bool.or_comm]
    · exact fallback first
  · have run : Elixir.Module.Types.Descr.«bdd_remove/2» a (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) =
        Elixir.Module.Types.Descr.«bdd_remove_bdd/2» a (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) := by
      simp [Elixir.Module.Types.Descr.«bdd_remove/2»]
    obtain ⟨r, runr, keep, sem, nl⟩ := remove_bdd_step U a _ wa wb ih
    exact ⟨r, by rw [run, runr], keep, sem, nl⟩

/-- Every pair of BDDs over a universe unites and removes. -/
theorem below_all (U : List Term) : ∀ n, Below U n := by
  intro n
  induction n with
  | zero => intro a b _ _ lt; omega
  | succ n ih =>
    intro a b wa wb lt
    have ih' : Below U (μ U a b) := ih.mono (by omega)
    exact ⟨union_step U a b wa wb ih', remove_step U a b wa wb ih', remove_bdd_step U a b wa wb ih'⟩

theorem Bdd.and {p q : Term → Prop} {b : Term} (hp : Bdd p b) (hq : Bdd q b) :
    Bdd (fun t => p t ∧ q t) b := by
  revert hq
  refine Bdd.induction (P := fun p b => ∀ {q}, Bdd q b → Bdd (fun t => p t ∧ q t) b) ?_ ?_ ?_ ?_ p b hp
  · intro _ _ _; exact Bdd.top
  · intro _ _ _; exact Bdd.bot
  · intro _ k x y okp q hq; exact Bdd.leaf_iff.mpr ⟨okp, Bdd.leaf_iff.mp hq⟩
  · intro p h lit c u d leaf okp _ _ _ ic iu id q hq
    obtain ⟨-, okq, qc, qu, qd⟩ := Bdd.node_iff.mp hq
    refine Bdd.node_iff.mpr ⟨leaf, ⟨okp, okq⟩, ?_, ?_, ?_⟩
    · exact (ic qc).mono fun t ht => ⟨⟨ht.1.1, ht.2.1⟩, ht.1.2⟩
    · exact (iu qu).mono fun t ht => ⟨⟨ht.1.1, ht.2.1⟩, ht.1.2⟩
    · exact (id qd).mono fun t ht => ⟨⟨ht.1.1, ht.2.1⟩, ht.1.2⟩

/-- The literals of a BDD. -/
def lits : Term → List Term
  | Term.tuple ⟨[_, lit, c, u, d]⟩ => lit :: (lits c ++ lits u ++ lits d)
  | .tuple ⟨[k, x, y]⟩ => [.tuple #[k, x, y]]
  | _ => []

-- Stated by `rfl`: the equation of the last clause of `lits` takes seconds to generate.
theorem lits_node (h lit c u d : Term) : lits (.tuple #[h, lit, c, u, d]) = lit :: (lits c ++ lits u ++ lits d) :=
  rfl

theorem lits_leaf (k x y : Term) : lits (.tuple #[k, x, y]) = [.tuple #[k, x, y]] := rfl

theorem Bdd.lits {ok : Term → Prop} {a : Term} (wa : Bdd ok a) : Bdd (· ∈ BddProofs.lits a) a := by
  refine Bdd.induction (P := fun _ a => Bdd (· ∈ BddProofs.lits a) a) ?_ ?_ ?_ ?_ ok a wa
  · intro _; exact Bdd.top
  · intro _; exact Bdd.bot
  · intro _ k x y _; exact Bdd.leaf_iff.mpr (by simp [lits_leaf])
  · intro _ h lit c u d leaf _ hc hu hd ic iu id
    refine Bdd.node_iff.mpr ⟨leaf, by simp [lits_node], ?_, ?_, ?_⟩
    · exact (Bdd.and ic hc).mono fun t ht => ⟨by simp [lits_node, ht.1], ht.2.2⟩
    · exact (Bdd.and iu hu).mono fun t ht => ⟨by simp [lits_node, ht.1], ht.2.2⟩
    · exact (Bdd.and id hd).mono fun t ht => ⟨by simp [lits_node, ht.1], ht.2.2⟩

theorem union_okN {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : UnionOkN a b :=
  let U := lits a ++ lits b
  (below_all U _ a b (wa.lits.mono fun _ h => List.mem_append_left _ h)
    (wb.lits.mono fun _ h => List.mem_append_right _ h) (Nat.lt_succ_self _)).1

theorem union_ok {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : UnionOk a b :=
  let ⟨r, run, keep, sem, _⟩ := union_okN wa wb
  ⟨r, run, keep, sem⟩

/-! Intersections. -/

/-- Nodes whose constrained and dual branches are equal collapse into a union. -/
theorem post_spec (lit r₁ r₂ r₃ : Term) (h : Int) {okU : Term → Prop}
    (w₁ : Bdd okU r₁) (w₂ : Bdd okU r₂) (w₃ : Bdd okU r₃) :
    ∃ r, (if compareExact (fuel r₃ r₁) r₃ r₁ = .eq then Elixir.Module.Types.Descr.«bdd_union/2» r₁ r₂
        else .ok (.tuple #[.integer h, lit, r₁, r₂, r₃])) = .ok r ∧
      (∀ ok : Term → Prop, IsLeaf lit → ok lit → Bdd (Above ok lit) r₁ → Bdd (Above ok lit) r₂ →
        Bdd (Above ok lit) r₃ → Bdd ok r) ∧
      (∀ ρ, Resp ρ → eval ρ r = ((ρ lit && eval ρ r₁) || eval ρ r₂ || (!ρ lit && eval ρ r₃))) ∧
      (NoLeaf r₁ → NoLeaf r₂ → NoLeaf r₃ → NoLeaf r) := by
  by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq
  · obtain ⟨r, run, keep, sem, nl⟩ := union_okN w₁ w₂
    refine ⟨r, by rw [ite_eq_left_of_eq_true _ _ (eq_true post), run], fun ok _ _ o₁ o₂ _ =>
      keep ok (o₁.mono fun _ h => h.1) (o₂.mono fun _ h => h.1), fun ρ resp => ?_, fun n₁ n₂ _ => nl n₁ n₂⟩
    rw [sem ρ resp, eval_congr w₃ resp post]
    cases ρ lit <;> cases eval ρ r₁ <;> simp
  · exact ⟨_, ite_eq_right_of_eq_false _ _ (eq_false post), fun ok leaf okl o₁ o₂ o₃ =>
      Bdd.node_iff.mpr ⟨leaf, okl, o₁, o₂, o₃⟩, fun ρ _ => eval_node ρ _ _ _ _ _,
      fun n₁ n₂ n₃ => NoLeaf.node.mpr ⟨n₁, n₂, n₃⟩⟩

theorem same_lit_bool (x y : Term) :
    Elixir.Module.Types.Descr.«same_lit?/2» x y = .ok (.atom "true") ∨
      Elixir.Module.Types.Descr.«same_lit?/2» x y = .ok (.atom "false") := by
  unfold Elixir.Module.Types.Descr.«same_lit?/2»
  split
  · simp only [Lynx.Except.guard, Erlang.erlang.«=:=/2», Lynx.Except.tryWith]
    split <;> simp
  · simp

theorem orElse_bool {x y : Except Exception Term}
    (hx : x = .ok (.atom "true") ∨ x = .ok (.atom "false")) (hy : y = .ok (.atom "true") ∨ y = .ok (.atom "false")) :
    Lynx.Except.orElse x y Bool.true = .ok (.atom "true") ∨ Lynx.Except.orElse x y Bool.true = .ok (.atom "false") := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [Lynx.Except.orElse]

def InterOk (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_intersection/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ ∀ ρ, Resp ρ → eval ρ r = (eval ρ a && eval ρ b)

def InterOkN (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_intersection/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ (∀ ρ, Resp ρ → eval ρ r = (eval ρ a && eval ρ b)) ∧
      (NoLeaf a → NoLeaf b → NoLeaf r)

theorem inter_eq_spec {okU : Term → Prop} (cd₁ cd₂ u₁ u₂ : Term) (w₁ : Bdd okU cd₁) (w₂ : Bdd okU cd₂)
    (w₃ : Bdd okU u₁) (w₄ : Bdd okU u₂) (i₁ : InterOkN cd₁ cd₂) (i₂ : InterOkN cd₁ u₂) (i₃ : InterOkN u₁ cd₂) :
    ∃ r, Elixir.Module.Types.Descr.«bdd_intersection_eq/4» cd₁ cd₂ u₁ u₂ = .ok r ∧
      (∀ ok, Bdd ok cd₁ → Bdd ok cd₂ → Bdd ok u₁ → Bdd ok u₂ → Bdd ok r) ∧
      (∀ ρ, Resp ρ → eval ρ r = ((eval ρ cd₁ && eval ρ cd₂) || (eval ρ cd₁ && eval ρ u₂) ||
        (eval ρ u₁ && eval ρ cd₂))) ∧ (NoLeaf cd₁ → NoLeaf cd₂ → NoLeaf u₁ → NoLeaf u₂ → NoLeaf r) := by
  obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := i₁
  obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := i₂
  obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := i₃
  by_cases top : r₁ = .atom "bdd_top"
  · subst top
    refine ⟨.atom "bdd_top", ?_, fun _ _ _ _ _ => Bdd.top, fun ρ resp => ?_, fun _ _ _ _ => NoLeaf.top⟩
    · unfold Elixir.Module.Types.Descr.«bdd_intersection_eq/4»
      simp [run₁]
    · have := sem₁ ρ resp
      simp at this
      simp [this]
  · obtain ⟨r₄, run₄, keep₄, sem₄, nl₄⟩ := union_okN (keep₂ _ w₁ w₄) (keep₃ _ w₃ w₂)
    obtain ⟨r, runr, keepr, semr, nlr⟩ := union_okN (keep₁ _ w₁ w₂) (keep₄ _ (keep₂ _ w₁ w₄) (keep₃ _ w₃ w₂))
    refine ⟨r, ?_, fun ok o₁ o₂ o₃ o₄ => keepr ok (keep₁ ok o₁ o₂)
      (keep₄ ok (keep₂ ok o₁ o₄) (keep₃ ok o₃ o₂)), fun ρ resp => ?_,
      fun n₁ n₂ n₃ n₄ => nlr (nl₁ n₁ n₂) (nl₄ (nl₂ n₁ n₄) (nl₃ n₃ n₂))⟩
    · unfold Elixir.Module.Types.Descr.«bdd_intersection_eq/4»
      simp only [run₁, Lynx.Except.ok_bind]
      simp [run₂, run₃, run₄, runr]
    · rw [semr ρ resp, sem₄ ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp]
      simp [Bool.or_assoc]

def BelowI (U : List Term) (n : Nat) : Prop :=
  ∀ a b, Bdd (· ∈ U) a → Bdd (· ∈ U) b → μ U a b < n → InterOkN a b

theorem inter_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
    (ih : BelowI U (μ U a b)) : InterOkN a b := by
  by_cases same : compareExact (fuel b a) b a = .eq
  · refine ⟨a, ?_, fun ok wa _ => wa, fun ρ resp => ?_, fun na _ => na⟩
    · unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      simp [Erlang.erlang.«=:=/2», same]
    · rw [← eval_congr wb resp same]; simp
  by_cases ta : a = .atom "bdd_top"
  · subst ta
    refine ⟨b, ?_, fun ok _ okb => okb, fun ρ _ => by simp, fun _ nb => nb⟩
    unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases tb : b = .atom "bdd_top"
  · subst tb
    refine ⟨a, ?_, fun ok oka _ => oka, fun ρ _ => by simp, fun na _ => na⟩
    unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases fa : a = .atom "bdd_bot"
  · subst fa
    refine ⟨.atom "bdd_bot", ?_, fun ok _ _ => Bdd.bot, fun ρ _ => by simp, fun _ _ => NoLeaf.bot⟩
    unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases fb : b = .atom "bdd_bot"
  · subst fb
    refine ⟨.atom "bdd_bot", ?_, fun ok _ _ => Bdd.bot, fun ρ _ => by simp, fun _ _ => NoLeaf.bot⟩
    unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
    simp [Erlang.erlang.«=:=/2», same]
  obtain ⟨la, ha⟩ := nontrivial_head wa ta fa
  obtain ⟨lb, hb⟩ := nontrivial_head wb tb fb
  have lU : la ∈ U := head_ok wa ha
  have lbU : lb ∈ U := head_ok wb hb
  have lower : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
      High la a' ∧ High la b' → μ U a' b' < μ U a b :=
    fun mono new => μ_lt mono lU (fun hh => not_high_head wa ha hh.1) new
  have lowerB : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
      High lb a' ∧ High lb b' → μ U a' b' < μ U a b :=
    fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
  rcases order : Term.compare (Term.fuel la lb) la lb
  · -- lt
    obtain ⟨h₀, c₁, u₁, d₁, run, split⟩ := compare_lt wa ha hb order
    have raiseB : ∀ {ok : Term → Prop}, Bdd ok b → Bdd (Above ok la) b :=
      fun w => w.raise fun l hl => by rw [hb] at hl; cases hl; exact order
    obtain ⟨hc, hu, hd⟩ := split.children wa
    obtain ⟨Hc, Hu, Hd⟩ := split.high wa
    have HB : High la b := (raiseB wb).mono fun _ h => h.2
    obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := ih c₁ b (hc.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').1, hb'⟩) ⟨Hc, HB⟩)
    obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := ih u₁ b (hu.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.1, hb'⟩) ⟨Hu, HB⟩)
    obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := ih d₁ b (hd.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.2, hb'⟩) ⟨Hd, HB⟩)
    have w₁ := keep₁ _ hc (raiseB wb)
    have w₂ := keep₂ _ hu (raiseB wb)
    have w₃ := keep₃ _ hd (raiseB wb)
    obtain ⟨h₁, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) w₁ w₂ w₃
    obtain ⟨r, runr, keep, sem, nl⟩ := post_spec la r₁ r₂ r₃ h₁ w₁ w₂ w₃
    refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_,
      fun na nb => nl (nl₁ (split.noLeaf na).1 nb) (nl₂ (split.noLeaf na).2.1 nb) (nl₃ (split.noLeaf na).2.2 nb)⟩
    · rw [← runr]
      unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      simp [Erlang.erlang.«=:=/2», same, run, run₁, run₂, run₃, node]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
    · obtain ⟨oc, ou, od⟩ := split.children oka
      exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc (raiseB okb)) (keep₂ _ ou (raiseB okb))
        (keep₃ _ od (raiseB okb))
    · rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp, split.eval ρ]
      cases ρ la <;> cases eval ρ b <;> simp
  · -- eq
    have run := compare_eq ha hb order
    have sameLit : ∀ ρ, Resp ρ → ρ la = ρ lb := fun ρ resp => resp _ _ order
    rcases head_some wa ha with ⟨k₁, x₁, y₁, rfl, rfl⟩ | ⟨h₁, c₁, u₁, d₁, rfl⟩ <;>
      rcases head_some wb hb with ⟨k₂, x₂, y₂, rfl, rfl⟩ | ⟨h₂, c₂, u₂, d₂, rfl⟩
    · -- two leaves
      refine ⟨_, ?_, fun ok oka _ => oka, fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
      · unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Erlang.erlang.«=:=/2», same, run]
      · simp [sameLit ρ resp]
    · -- a leaf below a node
      have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
      obtain ⟨hc, hu, hd⟩ := splitB.children wb
      obtain ⟨r₁, run₁, keep₁, sem₁⟩ := union_ok hc hu
      have w₁ := keep₁ _ hc hu
      obtain ⟨h₃, node⟩ := node_new lb r₁ (.atom "bdd_bot") (.atom "bdd_bot") (head_leaf wb hb) w₁
        (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
      obtain ⟨r, runr, keep, sem, -⟩ := post_spec lb r₁ (.atom "bdd_bot") (.atom "bdd_bot") h₃ w₁ Bdd.bot Bdd.bot
      refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun na _ => na.leaf.elim⟩
      · rw [← runr]
        unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Erlang.erlang.«=:=/2», same, run, run₁, node]
        by_cases post : compareExact (fuel (.atom "bdd_bot") r₁) (.atom "bdd_bot") r₁ = .eq <;> simp [post]
      · obtain ⟨oc, ou, -⟩ := splitB.children okb
        exact keep ok (head_leaf wb hb) (head_ok okb hb) (keep₁ _ oc ou) Bdd.bot Bdd.bot
      · rw [sem ρ resp, sem₁ ρ resp]
        simp only [eval_node, eval_leaf, eval_bot, sameLit ρ resp]
        cases ρ lb <;> simp
    · -- a node above a leaf
      have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
      obtain ⟨hc, hu, hd⟩ := splitA.children wa
      obtain ⟨r₁, run₁, keep₁, sem₁⟩ := union_ok hc hu
      have w₁ := keep₁ _ hc hu
      obtain ⟨h₃, node⟩ := node_new la r₁ (.atom "bdd_bot") (.atom "bdd_bot") (head_leaf wa ha) w₁
        (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
      obtain ⟨r, runr, keep, sem, -⟩ := post_spec la r₁ (.atom "bdd_bot") (.atom "bdd_bot") h₃ w₁ Bdd.bot Bdd.bot
      refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun _ nb => nb.leaf.elim⟩
      · rw [← runr]
        unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
        simp [Erlang.erlang.«=:=/2», same, run, run₁, node]
        by_cases post : compareExact (fuel (.atom "bdd_bot") r₁) (.atom "bdd_bot") r₁ = .eq <;> simp [post]
      · obtain ⟨oc, ou, -⟩ := splitA.children oka
        exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc ou) Bdd.bot Bdd.bot
      · rw [sem ρ resp, sem₁ ρ resp]
        simp only [eval_node, eval_leaf, eval_bot, ← sameLit ρ resp]
        cases ρ la <;> simp
    · -- two nodes
      have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
      have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
      obtain ⟨hc₁, hu₁, hd₁⟩ := splitA.children wa
      obtain ⟨hc₂', hu₂', hd₂'⟩ := splitB.children wb
      have hc₂ := hc₂'.congr order
      have hu₂ := hu₂'.congr order
      have hd₂ := hd₂'.congr order
      obtain ⟨Hc₁, Hu₁, Hd₁⟩ := splitA.high wa
      have Hc₂ := (splitB.high wb).1.congr order
      have Hu₂ := (splitB.high wb).2.1.congr order
      have Hd₂ := (splitB.high wb).2.2.congr order
      have mA := fun m (ha' : High m _) => High.split splitA wa ha'
      have mB := fun m (hb' : High m _) => High.split splitB wb hb'
      have U' : ∀ {x : Term}, Bdd (Above (· ∈ U) la) x → Bdd (· ∈ U) x := fun w => w.mono fun _ h => h.1
      have pair : ∀ {x y : Term}, Bdd (Above (· ∈ U) la) x → Bdd (Above (· ∈ U) la) y → High la x → High la y →
          (∀ m, High m (.tuple #[.integer h₁, la, c₁, u₁, d₁]) → High m (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) →
            High m x ∧ High m y) → InterOkN x y :=
        fun wx wy hx hy mono => ih _ _ (U' wx) (U' wy) (lower mono ⟨hx, hy⟩)
      have bool : ∀ ρ, Resp ρ → ρ lb = ρ la := fun ρ resp => (sameLit ρ resp).symm
      by_cases su : compareExact (fuel u₂ u₁) u₂ u₁ = .eq
      · obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := pair hc₁ hc₂ Hc₁ Hc₂ fun m ha' hb' => ⟨(mA m ha').1, (mB m hb').1⟩
        obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := pair hd₁ hd₂ Hd₁ Hd₂ fun m ha' hb' => ⟨(mA m ha').2.2, (mB m hb').2.2⟩
        have w₁ := keep₁ _ hc₁ hc₂
        have w₃ := keep₃ _ hd₁ hd₂
        obtain ⟨h₃, node⟩ := node_new la r₁ u₁ r₃ (head_leaf wa ha) w₁ hu₁ w₃
        obtain ⟨r, runr, keep, sem, nl⟩ := post_spec la r₁ u₁ r₃ h₃ w₁ hu₁ w₃
        refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun na nb => nl
          (nl₁ (NoLeaf.node.mp na).1 (NoLeaf.node.mp nb).1) (NoLeaf.node.mp na).2.1
          (nl₃ (NoLeaf.node.mp na).2.2 (NoLeaf.node.mp nb).2.2)⟩
        · rw [← runr]
          unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
          simp [Erlang.erlang.«=:=/2», same, run, su, run₁, run₃, node]
          by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
        · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
          obtain ⟨oc₂, -, od₂⟩ := splitB.children okb
          exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc₁ (oc₂.congr order)) ou₁
            (keep₃ _ od₁ (od₂.congr order))
        · have eu := eval_congr (hu₂'.mono fun _ h => h.1) resp su
          rw [sem ρ resp, sem₁ ρ resp, sem₃ ρ resp]
          simp only [eval_node, bool ρ resp, eu]
          generalize ρ la = L
          generalize eval ρ c₁ = C₁
          generalize eval ρ c₂ = C₂
          generalize eval ρ d₁ = D₁
          generalize eval ρ d₂ = D₂
          generalize eval ρ u₁ = U₁
          revert L C₁ C₂ D₁ D₂ U₁
          decide
      · rcases orElse_bool (same_lit_bool c₁ c₂) (same_lit_bool d₁ d₂) with so | so
        · -- equal literals below: intersect the branches with each other's unions
          obtain ⟨i₁, ri₁, ki₁, si₁, ni₁⟩ := pair hc₁ hc₂ Hc₁ Hc₂ fun m ha' hb' => ⟨(mA m ha').1, (mB m hb').1⟩
          obtain ⟨i₂, ri₂, ki₂, si₂, ni₂⟩ := pair hc₁ hu₂ Hc₁ Hu₂ fun m ha' hb' => ⟨(mA m ha').1, (mB m hb').2.1⟩
          obtain ⟨i₃, ri₃, ki₃, si₃, ni₃⟩ := pair hu₁ hc₂ Hu₁ Hc₂ fun m ha' hb' => ⟨(mA m ha').2.1, (mB m hb').1⟩
          obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := inter_eq_spec c₁ c₂ u₁ u₂ hc₁ hc₂ hu₁ hu₂
            ⟨i₁, ri₁, ki₁, si₁, ni₁⟩ ⟨i₂, ri₂, ki₂, si₂, ni₂⟩ ⟨i₃, ri₃, ki₃, si₃, ni₃⟩
          obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := pair hu₁ hu₂ Hu₁ Hu₂ fun m ha' hb' => ⟨(mA m ha').2.1, (mB m hb').2.1⟩
          obtain ⟨j₁, rj₁, kj₁, sj₁, nj₁⟩ := pair hd₁ hd₂ Hd₁ Hd₂ fun m ha' hb' => ⟨(mA m ha').2.2, (mB m hb').2.2⟩
          obtain ⟨j₂, rj₂, kj₂, sj₂, nj₂⟩ := pair hd₁ hu₂ Hd₁ Hu₂ fun m ha' hb' => ⟨(mA m ha').2.2, (mB m hb').2.1⟩
          obtain ⟨j₃, rj₃, kj₃, sj₃, nj₃⟩ := pair hu₁ hd₂ Hu₁ Hd₂ fun m ha' hb' => ⟨(mA m ha').2.1, (mB m hb').2.2⟩
          obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := inter_eq_spec d₁ d₂ u₁ u₂ hd₁ hd₂ hu₁ hu₂
            ⟨j₁, rj₁, kj₁, sj₁, nj₁⟩ ⟨j₂, rj₂, kj₂, sj₂, nj₂⟩ ⟨j₃, rj₃, kj₃, sj₃, nj₃⟩
          have w₁ := keep₁ _ hc₁ hc₂ hu₁ hu₂
          have w₂ := keep₂ _ hu₁ hu₂
          have w₃ := keep₃ _ hd₁ hd₂ hu₁ hu₂
          obtain ⟨h₃, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) w₁ w₂ w₃
          obtain ⟨r, runr, keep, sem, nl⟩ := post_spec la r₁ r₂ r₃ h₃ w₁ w₂ w₃
          refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun na nb => by
            obtain ⟨c₁', u₁', d₁'⟩ := NoLeaf.node.mp na
            obtain ⟨c₂', u₂', d₂'⟩ := NoLeaf.node.mp nb
            exact nl (nl₁ c₁' c₂' u₁' u₂') (nl₂ u₁' u₂') (nl₃ d₁' d₂' u₁' u₂')⟩
          · rw [← runr]
            unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
            simp [Erlang.erlang.«=:=/2», same, run, su, so, isMember, run₁, run₂, run₃, node]
            by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
          · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
            obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
            exact keep ok (head_leaf wa ha) (head_ok oka ha)
              (keep₁ _ oc₁ (oc₂.congr order) ou₁ (ou₂.congr order)) (keep₂ _ ou₁ (ou₂.congr order))
              (keep₃ _ od₁ (od₂.congr order) ou₁ (ou₂.congr order))
          · rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp]
            simp only [eval_node, bool ρ resp]
            generalize ρ la = L
            generalize eval ρ c₁ = C₁
            generalize eval ρ c₂ = C₂
            generalize eval ρ d₁ = D₁
            generalize eval ρ d₂ = D₂
            generalize eval ρ u₁ = U₁
            generalize eval ρ u₂ = U₂
            revert L C₁ C₂ D₁ D₂ U₁ U₂
            decide
        · -- intersect the unions of each side
          obtain ⟨x, rx, kx, sx, nx⟩ := union_okN hc₁ hu₁
          obtain ⟨y, ry, ky, sy, ny⟩ := union_okN hc₂ hu₂
          obtain ⟨x', rx', kx', sx', nx'⟩ := union_okN hd₁ hu₁
          obtain ⟨y', ry', ky', sy', ny'⟩ := union_okN hd₂ hu₂
          obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := pair (kx _ hc₁ hu₁) (ky _ hc₂ hu₂) (kx _ Hc₁ Hu₁) (ky _ Hc₂ Hu₂)
            fun m ha' hb' => ⟨kx _ (mA m ha').1 (mA m ha').2.1, ky _ (mB m hb').1 (mB m hb').2.1⟩
          obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := pair (kx' _ hd₁ hu₁) (ky' _ hd₂ hu₂) (kx' _ Hd₁ Hu₁) (ky' _ Hd₂ Hu₂)
            fun m ha' hb' => ⟨kx' _ (mA m ha').2.2 (mA m ha').2.1, ky' _ (mB m hb').2.2 (mB m hb').2.1⟩
          have w₁ := keep₁ _ (kx _ hc₁ hu₁) (ky _ hc₂ hu₂)
          have w₃ := keep₃ _ (kx' _ hd₁ hu₁) (ky' _ hd₂ hu₂)
          obtain ⟨h₃, node⟩ := node_new la r₁ (.atom "bdd_bot") r₃ (head_leaf wa ha) w₁
            (Bdd.bot (ok := fun _ => True)) w₃
          obtain ⟨r, runr, keep, sem, nl⟩ := post_spec la r₁ (.atom "bdd_bot") r₃ h₃ w₁ Bdd.bot w₃
          refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_, fun na nb => by
            obtain ⟨c₁', u₁', d₁'⟩ := NoLeaf.node.mp na
            obtain ⟨c₂', u₂', d₂'⟩ := NoLeaf.node.mp nb
            exact nl (nl₁ (nx c₁' u₁') (ny c₂' u₂')) NoLeaf.bot (nl₃ (nx' d₁' u₁') (ny' d₂' u₂'))⟩
          · rw [← runr]
            unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
            simp [Erlang.erlang.«=:=/2», same, run, su, so, isMember, rx, ry, rx', ry',
              run₁, run₃, node]
            by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
          · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
            obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
            exact keep ok (head_leaf wa ha) (head_ok oka ha)
              (keep₁ _ (kx _ oc₁ ou₁) (ky _ (oc₂.congr order) (ou₂.congr order))) Bdd.bot
              (keep₃ _ (kx' _ od₁ ou₁) (ky' _ (od₂.congr order) (ou₂.congr order)))
          · rw [sem ρ resp, sem₁ ρ resp, sem₃ ρ resp, sx ρ resp, sy ρ resp, sx' ρ resp, sy' ρ resp]
            simp only [eval_node, eval_bot, bool ρ resp]
            generalize ρ la = L
            generalize eval ρ c₁ = C₁
            generalize eval ρ c₂ = C₂
            generalize eval ρ d₁ = D₁
            generalize eval ρ d₂ = D₂
            generalize eval ρ u₁ = U₁
            generalize eval ρ u₂ = U₂
            revert L C₁ C₂ D₁ D₂ U₁ U₂
            decide
  · -- gt
    have order' : Term.compare (Term.fuel lb la) lb la = .lt := Lynx.Term.compare_lt_of_gt order
    obtain ⟨h₀, c₂, u₂, d₂, run, split⟩ := compare_gt wb ha hb order
    have raiseA : ∀ {ok : Term → Prop}, Bdd ok a → Bdd (Above ok lb) a :=
      fun w => w.raise fun l hl => by rw [ha] at hl; cases hl; exact order'
    obtain ⟨hc, hu, hd⟩ := split.children wb
    obtain ⟨Hc, Hu, Hd⟩ := split.high wb
    have HA : High lb a := (raiseA wa).mono fun _ h => h.2
    obtain ⟨r₁, run₁, keep₁, sem₁, nl₁⟩ := ih a c₂ wa (hc.mono fun _ h => h.1)
      (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').1⟩) ⟨HA, Hc⟩)
    obtain ⟨r₂, run₂, keep₂, sem₂, nl₂⟩ := ih a u₂ wa (hu.mono fun _ h => h.1)
      (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.1⟩) ⟨HA, Hu⟩)
    obtain ⟨r₃, run₃, keep₃, sem₃, nl₃⟩ := ih a d₂ wa (hd.mono fun _ h => h.1)
      (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.2⟩) ⟨HA, Hd⟩)
    have w₁ := keep₁ _ (raiseA wa) hc
    have w₂ := keep₂ _ (raiseA wa) hu
    have w₃ := keep₃ _ (raiseA wa) hd
    obtain ⟨h₁, node⟩ := node_new lb r₁ r₂ r₃ (head_leaf wb hb) w₁ w₂ w₃
    obtain ⟨r, runr, keep, sem, nl⟩ := post_spec lb r₁ r₂ r₃ h₁ w₁ w₂ w₃
    refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_,
      fun na nb => nl (nl₁ na (split.noLeaf nb).1) (nl₂ na (split.noLeaf nb).2.1) (nl₃ na (split.noLeaf nb).2.2)⟩
    · rw [← runr]
      unfold Elixir.Module.Types.Descr.«bdd_intersection/2»
      simp [Erlang.erlang.«=:=/2», same, run, run₁, run₂, run₃, node]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
    · obtain ⟨oc, ou, od⟩ := split.children okb
      exact keep ok (head_leaf wb hb) (head_ok okb hb) (keep₁ _ (raiseA oka) oc) (keep₂ _ (raiseA oka) ou)
        (keep₃ _ (raiseA oka) od)
    · rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp, split.eval ρ]
      cases ρ lb <;> cases eval ρ a <;> simp

theorem belowI_all (U : List Term) : ∀ n, BelowI U n := by
  intro n
  induction n with
  | zero => intro a b _ _ lt; omega
  | succ n ih =>
    intro a b wa wb lt
    exact inter_step U a b wa wb fun a' b' wa' wb' lt' => ih a' b' wa' wb' (by omega)

theorem inter_okN {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : InterOkN a b :=
  belowI_all (lits a ++ lits b) _ a b (wa.lits.mono fun _ h => List.mem_append_left _ h)
    (wb.lits.mono fun _ h => List.mem_append_right _ h) (Nat.lt_succ_self _)

theorem inter_ok {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : InterOk a b :=
  let ⟨r, run, keep, sem, _⟩ := inter_okN wa wb
  ⟨r, run, keep, sem⟩

/-! Negations. -/

def NegOk (b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_negation/1» b = .ok r ∧ (∀ ok, Bdd ok b → Bdd ok r) ∧
    ∀ ρ, Resp ρ → eval ρ r = !eval ρ b

/-- Negations, which never have leaves. -/
def NegOkN (b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_negation/1» b = .ok r ∧ (∀ ok, Bdd ok b → Bdd ok r) ∧
    (∀ ρ, Resp ρ → eval ρ r = !eval ρ b) ∧ NoLeaf r

theorem neg_okN {ok₀ : Term → Prop} {b : Term} (wb : Bdd ok₀ b) : NegOkN b := by
  refine Bdd.induction (P := fun _ b => NegOkN b) ?_ ?_ ?_ ?_ ok₀ b wb
  · intro _
    exact ⟨.atom "bdd_bot", by simp [Elixir.Module.Types.Descr.«bdd_negation/1»], fun _ _ => Bdd.bot,
      fun ρ _ => by simp, NoLeaf.bot⟩
  · intro _
    exact ⟨.atom "bdd_top", by simp [Elixir.Module.Types.Descr.«bdd_negation/1»], fun _ _ => Bdd.top,
      fun ρ _ => by simp, NoLeaf.top⟩
  · intro ok k x y okl
    obtain ⟨h, node⟩ := node_new (.tuple #[.integer k, x, y]) (.atom "bdd_bot") (.atom "bdd_bot")
      (.atom "bdd_top") ⟨k, x, y, rfl⟩ (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
      (Bdd.top (ok := fun _ => True))
    refine ⟨.tuple #[.integer h, .tuple #[.integer k, x, y], .atom "bdd_bot", .atom "bdd_bot", .atom "bdd_top"],
      by simp [Elixir.Module.Types.Descr.«bdd_negation/1», node], fun ok' w => ?_, fun ρ _ => ?_,
      NoLeaf.node.mpr ⟨NoLeaf.bot, NoLeaf.bot, NoLeaf.top⟩⟩
    · exact Bdd.node_iff.mpr ⟨⟨k, x, y, rfl⟩, Bdd.leaf_iff.mp w, Bdd.bot, Bdd.bot, Bdd.top⟩
    · cases ρ (.tuple #[.integer k, x, y]) <;> simp
  · intro ok h lit c u d leaf okl hc hu hd ⟨nc, runc, keepc, semc, nlc⟩ ⟨nu, runu, keepu, semu, nlu⟩
      ⟨nd, rund, keepd, semd, nld⟩
    have wnc := keepc _ hc
    have wnd := keepd _ hd
    obtain ⟨h₁, inner⟩ := node_new lit nc (.atom "bdd_bot") nd leaf wnc (Bdd.bot (ok := fun _ => True)) wnd
    have winner : Bdd ok (.tuple #[.integer h₁, lit, nc, .atom "bdd_bot", nd]) :=
      Bdd.node_iff.mpr ⟨leaf, okl, wnc, Bdd.bot, wnd⟩
    have wnu : Bdd ok nu := (keepu _ hu).mono fun _ h => h.1
    obtain ⟨i, runi, keepi, semi, nli⟩ := inter_okN winner wnu
    have wi := keepi _ winner wnu
    have ni : NoLeaf i := nli (NoLeaf.node.mpr ⟨nlc, NoLeaf.bot, nld⟩) nlu
    -- the result before and after the final simplification
    have final : ∃ r, (∀ ok', Bdd ok' (.tuple #[.integer h, lit, c, u, d]) → Bdd ok' r) ∧
        (∀ ρ, Resp ρ → eval ρ r = eval ρ i) ∧
        Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer h, lit, c, u, d]) = .ok r ∧ NoLeaf r := by
      have keepI : ∀ ok', Bdd ok' (.tuple #[.integer h, lit, c, u, d]) → Bdd ok' i := fun ok' w => by
        obtain ⟨-, okl', oc, ou, od⟩ := Bdd.node_iff.mp w
        exact keepi ok' (Bdd.node_iff.mpr ⟨leaf, okl', keepc _ oc, Bdd.bot, keepd _ od⟩)
          ((keepu _ ou).mono fun _ h => h.1)
      rcases wi.shape with rfl | rfl | ⟨_, _, _, rfl⟩ | ⟨hi, li, c', u', d', rfl⟩
      · refine ⟨_, keepI, fun _ _ => rfl, ?_, ni⟩
        conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_negation/1»
        simp only [runc, rund, inner, runu, runi, Lynx.Except.ok_bind]
        rfl
      · refine ⟨_, keepI, fun _ _ => rfl, ?_, ni⟩
        conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_negation/1»
        simp only [runc, rund, inner, runu, runi, Lynx.Except.ok_bind]
        rfl
      · refine ⟨_, keepI, fun _ _ => rfl, ?_, ni⟩
        conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_negation/1»
        simp only [runc, rund, inner, runu, runi, Lynx.Except.ok_bind]
        rfl
      · have base : Elixir.Module.Types.Descr.«bdd_negation/1» (.tuple #[.integer h, lit, c, u, d]) =
            if compareExact (fuel d' c') d' c' = .eq then Elixir.Module.Types.Descr.«bdd_union/2» u' c'
            else .ok (.tuple #[.integer hi, li, c', u', d']) := by
          conv => lhs; unfold Elixir.Module.Types.Descr.«bdd_negation/1»
          simp only [runc, rund, inner, runu, runi, Lynx.Except.ok_bind]
          by_cases e : compareExact (fuel d' c') d' c' = .eq <;> simp [Erlang.erlang.«=:=/2», e]
        by_cases e : compareExact (fuel d' c') d' c' = .eq
        · obtain ⟨-, -, wc', wu', wd'⟩ := Bdd.node_iff.mp wi
          obtain ⟨r, runr, keepr, semr, nlr⟩ := union_okN wu' wc'
          refine ⟨r, fun ok' w => ?_, fun ρ resp => ?_, by rw [base, ite_eq_left e, runr],
            nlr (NoLeaf.node.mp ni).2.1 (NoLeaf.node.mp ni).1⟩
          · obtain ⟨-, -, oc', ou', -⟩ := Bdd.node_iff.mp (keepI ok' w)
            exact keepr ok' (ou'.mono fun _ h => h.1) (oc'.mono fun _ h => h.1)
          · rw [semr ρ resp, eval_node, eval_congr wd' resp e]
            cases ρ li <;> cases eval ρ c' <;> simp
        · exact ⟨_, keepI, fun _ _ => rfl, by rw [base, ite_eq_right e], ni⟩
    obtain ⟨r, keepr, semr, runr, nlr⟩ := final
    refine ⟨r, runr, keepr, fun ρ resp => ?_, nlr⟩
    rw [semr ρ resp, semi ρ resp, eval_node, eval_node, semc ρ resp, semd ρ resp, semu ρ resp]
    cases ρ lit <;> cases eval ρ c <;> cases eval ρ u <;> cases eval ρ d <;> simp

theorem neg_ok {ok₀ : Term → Prop} {b : Term} (wb : Bdd ok₀ b) : NegOk b :=
  let ⟨r, run, keep, sem, _⟩ := neg_okN wb
  ⟨r, run, keep, sem⟩

/-! Differences. -/

theorem tuple3_cmp {a₀ a₁ a₂ b : Term} (e : Term.compare (Term.fuel (.tuple #[a₀, a₁, a₂]) b) (.tuple #[a₀, a₁, a₂]) b = .eq) :
    ∃ b₀ b₁ b₂, b = .tuple #[b₀, b₁, b₂] ∧ Term.compare (Term.fuel a₀ b₀) a₀ b₀ = .eq ∧ Term.compare (Term.fuel a₁ b₁) a₁ b₁ = .eq ∧
      Term.compare (Term.fuel a₂ b₂) a₂ b₂ = .eq := by
  rw [compare_step] at e
  cases b <;> simp [Compare.compareStep] at e
  rename_i ys
  obtain ⟨ys⟩ := ys
  rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, rest⟩⟩⟩⟩ <;>
    simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
      List.compareLex_nil_cons] at e
  · exact ⟨b₀, b₁, b₂, rfl, e.1, e.2.1, e.2.2⟩

theorem tuple5_cmp {a₀ a₁ a₂ a₃ a₄ b : Term} (e : Term.compare (Term.fuel (.tuple #[a₀, a₁, a₂, a₃, a₄]) b) (.tuple #[a₀, a₁, a₂, a₃, a₄]) b = .eq) :
    ∃ b₀ b₁ b₂ b₃ b₄, b = .tuple #[b₀, b₁, b₂, b₃, b₄] ∧ Term.compare (Term.fuel a₁ b₁) a₁ b₁ = .eq ∧
      Term.compare (Term.fuel a₂ b₂) a₂ b₂ = .eq ∧ Term.compare (Term.fuel a₃ b₃) a₃ b₃ = .eq ∧ Term.compare (Term.fuel a₄ b₄) a₄ b₄ = .eq := by
  rw [compare_step] at e
  cases b <;> simp [Compare.compareStep] at e
  rename_i ys
  obtain ⟨ys⟩ := ys
  rcases ys with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨b₄, _ | ⟨b₅, rest⟩⟩⟩⟩⟩⟩ <;>
    simp [List.compareLex_cons_cons, List.compareLex_nil_nil, List.compareLex_cons_nil,
      List.compareLex_nil_cons] at e
  · exact ⟨b₀, b₁, b₂, b₃, b₄, rfl, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2⟩

/-- Equal BDDs have the same semantics. -/
theorem eval_congr_cmp {ok : Term → Prop} {a : Term} (wa : Bdd ok a) {ρ : Term → Bool} (resp : Resp ρ) :
    ∀ {b}, Term.compare (Term.fuel a b) a b = .eq → eval ρ a = eval ρ b := by
  refine Bdd.induction (P := fun _ a => ∀ {b}, Term.compare (Term.fuel a b) a b = .eq → eval ρ a = eval ρ b)
    ?_ ?_ ?_ ?_ ok a wa
  · intro _ b e
    obtain rfl := (compare_eq_atom b "bdd_top").mp (Lynx.Term.compare_eq_symm e)
    rfl
  · intro _ b e
    obtain rfl := (compare_eq_atom b "bdd_bot").mp (Lynx.Term.compare_eq_symm e)
    rfl
  · intro _ k x y _ b e
    obtain ⟨b₀, b₁, b₂, rfl, -, -, -⟩ := tuple3_cmp e
    simp only [eval_leaf]
    exact resp _ _ e
  · intro _ h lit c u d _ _ _ _ _ ihc ihu ihd b e
    obtain ⟨b₀, b₁, b₂, b₃, b₄, rfl, el, ec, eu, ed⟩ := tuple5_cmp e
    simp only [eval_node]
    rw [resp _ _ el, ihc ec, ihu eu, ihd ed]

def DiffOk (a b : Term) : Prop :=
  ∃ r, Elixir.Module.Types.Descr.«bdd_difference/2» a b = .ok r ∧
    (∀ ok, Bdd ok a → Bdd ok b → Bdd ok r) ∧ ∀ ρ, Resp ρ → eval ρ r = (eval ρ a && !eval ρ b)

def BelowD (U : List Term) (n : Nat) : Prop :=
  ∀ a b, Bdd (· ∈ U) a → Bdd (· ∈ U) b → μ U a b < n → DiffOk a b

theorem diff_union_spec {okU : Term → Prop} {i u₁ u₂ : Term} (wu₁ : Bdd okU u₁) (wu₂ : Bdd okU u₂)
    (diff : ∀ u, Elixir.Module.Types.Descr.«bdd_union/2» u₁ u₂ = .ok u → DiffOk i u) :
    ∃ r, Elixir.Module.Types.Descr.«bdd_difference_union/3» i u₁ u₂ = .ok r ∧
      (∀ ok, Bdd ok i → Bdd ok u₁ → Bdd ok u₂ → Bdd ok r) ∧
      ∀ ρ, Resp ρ → eval ρ r = (eval ρ i && !(eval ρ u₁ || eval ρ u₂)) := by
  by_cases bot : i = .atom "bdd_bot"
  · subst bot
    exact ⟨.atom "bdd_bot", by unfold Elixir.Module.Types.Descr.«bdd_difference_union/3»; rfl,
      fun _ _ _ _ => Bdd.bot, fun _ _ => by simp⟩
  obtain ⟨u, runU, keepU, semU⟩ := union_ok wu₁ wu₂
  obtain ⟨r, run, keep, sem⟩ := diff u runU
  refine ⟨r, ?_, fun ok oi o₁ o₂ => keep ok oi (keepU ok o₁ o₂), fun ρ resp => by rw [sem ρ resp, semU ρ resp]⟩
  unfold Elixir.Module.Types.Descr.«bdd_difference_union/3»
  split
  · exact absurd rfl bot
  · simp [runU, run]

theorem neg_union_spec {okU : Term → Prop} {u₁ u₂ : Term} (wu₁ : Bdd okU u₁) (wu₂ : Bdd okU u₂) :
    ∃ r, Elixir.Module.Types.Descr.«bdd_negation_union/2» u₁ u₂ = .ok r ∧
      (∀ ok, Bdd ok u₁ → Bdd ok u₂ → Bdd ok r) ∧
      ∀ ρ, Resp ρ → eval ρ r = !(eval ρ u₁ || eval ρ u₂) := by
  obtain ⟨n₁, run₁, keep₁, sem₁⟩ := neg_ok wu₁
  obtain ⟨n₂, run₂, keep₂, sem₂⟩ := neg_ok wu₂
  obtain ⟨r, run, keep, sem⟩ := inter_ok (keep₁ _ wu₁) (keep₂ _ wu₂)
  refine ⟨r, by simp [Elixir.Module.Types.Descr.«bdd_negation_union/2», run₁, run₂, run],
    fun ok o₁ o₂ => keep ok (keep₁ ok o₁) (keep₂ ok o₂), fun ρ resp => ?_⟩
  rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp]
  cases eval ρ u₁ <;> cases eval ρ u₂ <;> rfl

theorem diff_step (U : List Term) (a b : Term) (wa : Bdd (· ∈ U) a) (wb : Bdd (· ∈ U) b)
    (ih : BelowD U (μ U a b)) : DiffOk a b := by
  by_cases same : compareExact (fuel b a) b a = .eq
  · refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ resp => ?_⟩
    · unfold Elixir.Module.Types.Descr.«bdd_difference/2»
      simp [Erlang.erlang.«=:=/2», same]
    · rw [eval_congr wb resp same]; simp
  by_cases tb : b = .atom "bdd_top"
  · subst tb
    refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ _ => by simp⟩
    unfold Elixir.Module.Types.Descr.«bdd_difference/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases fa : a = .atom "bdd_bot"
  · subst fa
    refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ _ => by simp⟩
    unfold Elixir.Module.Types.Descr.«bdd_difference/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases fb : b = .atom "bdd_bot"
  · subst fb
    refine ⟨a, ?_, fun _ oka _ => oka, fun ρ _ => by simp⟩
    unfold Elixir.Module.Types.Descr.«bdd_difference/2»
    simp [Erlang.erlang.«=:=/2», same]
  by_cases ta : a = .atom "bdd_top"
  · subst ta
    obtain ⟨r, run, keep, sem⟩ := neg_ok wb
    refine ⟨r, ?_, fun ok _ okb => keep ok okb, fun ρ resp => by simp [sem ρ resp]⟩
    unfold Elixir.Module.Types.Descr.«bdd_difference/2»
    simp [Erlang.erlang.«=:=/2», same, run]
  obtain ⟨la, ha⟩ := nontrivial_head wa ta fa
  obtain ⟨lb, hb⟩ := nontrivial_head wb tb fb
  have lU : la ∈ U := head_ok wa ha
  have lbU : lb ∈ U := head_ok wb hb
  have lower : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
      High la a' ∧ High la b' → μ U a' b' < μ U a b :=
    fun mono new => μ_lt mono lU (fun hh => not_high_head wa ha hh.1) new
  have lowerB : ∀ {a' b'}, (∀ m, High m a → High m b → High m a' ∧ High m b') →
      High lb a' ∧ High lb b' → μ U a' b' < μ U a b :=
    fun mono new => μ_lt mono lbU (fun hh => not_high_head wb hb hh.2) new
  rcases order : Term.compare (Term.fuel la lb) la lb
  · -- lt
    obtain ⟨h₀, c₁, u₁, d₁, run, split⟩ := compare_lt wa ha hb order
    have raiseB : ∀ {ok : Term → Prop}, Bdd ok b → Bdd (Above ok la) b :=
      fun w => w.raise fun l hl => by rw [hb] at hl; cases hl; exact order
    obtain ⟨hc, hu, hd⟩ := split.children wa
    obtain ⟨Hc, Hu, Hd⟩ := split.high wa
    have HB : High la b := (raiseB wb).mono fun _ h => h.2
    obtain ⟨r₁, run₁, keep₁, sem₁⟩ := ih c₁ b (hc.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').1, hb'⟩) ⟨Hc, HB⟩)
    obtain ⟨r₂, run₂, keep₂, sem₂⟩ := ih u₁ b (hu.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.1, hb'⟩) ⟨Hu, HB⟩)
    obtain ⟨r₃, run₃, keep₃, sem₃⟩ := ih d₁ b (hd.mono fun _ h => h.1) wb
      (lower (fun m ha' hb' => ⟨(High.split split wa ha').2.2, hb'⟩) ⟨Hd, HB⟩)
    have w₁ := keep₁ _ hc (raiseB wb)
    have w₂ := keep₂ _ hu (raiseB wb)
    have w₃ := keep₃ _ hd (raiseB wb)
    obtain ⟨h₁, node⟩ := node_new la r₁ r₂ r₃ (head_leaf wa ha) w₁ w₂ w₃
    obtain ⟨r, runr, keep, sem, -⟩ := post_spec la r₁ r₂ r₃ h₁ w₁ w₂ w₃
    refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
    · rw [← runr]
      unfold Elixir.Module.Types.Descr.«bdd_difference/2»
      simp [Erlang.erlang.«=:=/2», same, run, run₁, run₂, run₃, node]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
    · obtain ⟨oc, ou, od⟩ := split.children oka
      exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc (raiseB okb)) (keep₂ _ ou (raiseB okb))
        (keep₃ _ od (raiseB okb))
    · rw [sem ρ resp, sem₁ ρ resp, sem₂ ρ resp, sem₃ ρ resp, split.eval ρ]
      cases ρ la <;> cases eval ρ b <;> simp
  · -- eq
    have run := compare_eq ha hb order
    have sameLit : ∀ ρ, Resp ρ → ρ la = ρ lb := fun ρ resp => resp _ _ order
    rcases head_some wa ha with ⟨k₁, x₁, y₁, rfl, rfl⟩ | ⟨h₁, c₁, u₁, d₁, rfl⟩ <;>
      rcases head_some wb hb with ⟨k₂, x₂, y₂, rfl, rfl⟩ | ⟨h₂, c₂, u₂, d₂, rfl⟩
    · -- two leaves
      refine ⟨.atom "bdd_bot", ?_, fun _ _ _ => Bdd.bot, fun ρ resp => ?_⟩
      · unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Erlang.erlang.«=:=/2», same, run]
      · simp [sameLit ρ resp]
    · -- a leaf below a node
      have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
      obtain ⟨hc, hu, hd⟩ := splitB.children wb
      obtain ⟨r₁, run₁, keep₁, sem₁⟩ := neg_union_spec hc hu
      have w₁ := keep₁ _ hc hu
      obtain ⟨h₃, node⟩ := node_new lb r₁ (.atom "bdd_bot") (.atom "bdd_bot") (head_leaf wb hb) w₁
        (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True))
      obtain ⟨r, runr, keep, sem, -⟩ := post_spec lb r₁ (.atom "bdd_bot") (.atom "bdd_bot") h₃ w₁ Bdd.bot Bdd.bot
      refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
      · rw [← runr]
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Erlang.erlang.«=:=/2», same, run, run₁, node]
        by_cases post : compareExact (fuel (.atom "bdd_bot") r₁) (.atom "bdd_bot") r₁ = .eq <;> simp [post]
      · obtain ⟨oc, ou, -⟩ := splitB.children okb
        exact keep ok (head_leaf wb hb) (head_ok okb hb) (keep₁ _ oc ou) Bdd.bot Bdd.bot
      · rw [sem ρ resp, sem₁ ρ resp]
        simp only [eval_node, eval_leaf, eval_bot, sameLit ρ resp]
        cases ρ lb <;> simp
    · -- a node above a leaf
      have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
      obtain ⟨hc, hu, hd⟩ := splitA.children wa
      obtain ⟨r₃, run₃, keep₃, sem₃⟩ := union_ok hd hu
      have w₃ := keep₃ _ hd hu
      obtain ⟨h₃, node⟩ := node_new la (.atom "bdd_bot") (.atom "bdd_bot") r₃ (head_leaf wa ha)
        (Bdd.bot (ok := fun _ => True)) (Bdd.bot (ok := fun _ => True)) w₃
      obtain ⟨r, runr, keep, sem, -⟩ := post_spec la (.atom "bdd_bot") (.atom "bdd_bot") r₃ h₃ Bdd.bot Bdd.bot w₃
      refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
      · rw [← runr]
        unfold Elixir.Module.Types.Descr.«bdd_difference/2»
        simp [Erlang.erlang.«=:=/2», same, run, run₃, node]
        by_cases post : compareExact (fuel r₃ (.atom "bdd_bot")) r₃ (.atom "bdd_bot") = .eq <;> simp [post]
      · obtain ⟨-, ou, od⟩ := splitA.children oka
        exact keep ok (head_leaf wa ha) (head_ok oka ha) Bdd.bot Bdd.bot (keep₃ _ od ou)
      · rw [sem ρ resp, sem₃ ρ resp]
        simp only [eval_node, eval_leaf, eval_bot, ← sameLit ρ resp]
        cases ρ la <;> cases eval ρ u₁ <;> cases eval ρ d₁ <;> simp
    · -- two nodes
      have splitA : Split _ la c₁ u₁ d₁ := Or.inl ⟨h₁, rfl⟩
      have splitB : Split _ lb c₂ u₂ d₂ := Or.inl ⟨h₂, rfl⟩
      obtain ⟨hc₁, hu₁, hd₁⟩ := splitA.children wa
      obtain ⟨hc₂', hu₂', hd₂'⟩ := splitB.children wb
      have hc₂ := hc₂'.congr order
      have hu₂ := hu₂'.congr order
      have hd₂ := hd₂'.congr order
      obtain ⟨Hc₁, Hu₁, Hd₁⟩ := splitA.high wa
      have Hc₂ := (splitB.high wb).1.congr order
      have Hu₂ := (splitB.high wb).2.1.congr order
      have Hd₂ := (splitB.high wb).2.2.congr order
      have mA := fun m (ha' : High m _) => High.split splitA wa ha'
      have mB := fun m (hb' : High m _) => High.split splitB wb hb'
      have U' : ∀ {x : Term}, Bdd (Above (· ∈ U) la) x → Bdd (· ∈ U) x := fun w => w.mono fun _ h => h.1
      have pair : ∀ {x y : Term}, Bdd (Above (· ∈ U) la) x → Bdd (Above (· ∈ U) la) y → High la x → High la y →
          (∀ m, High m (.tuple #[.integer h₁, la, c₁, u₁, d₁]) → High m (.tuple #[.integer h₂, lb, c₂, u₂, d₂]) →
            High m x ∧ High m y) → DiffOk x y :=
        fun wx wy hx hy mono => ih _ _ (U' wx) (U' wy) (lower mono ⟨hx, hy⟩)
      have bool : ∀ ρ, Resp ρ → ρ lb = ρ la := fun ρ resp => (sameLit ρ resp).symm
      by_cases cond : Term.compare (Term.fuel u₁ (.atom "bdd_bot")) u₁ (.atom "bdd_bot") = .eq ∨ Term.compare (Term.fuel u₁ u₂) u₁ u₂ = .eq
      · obtain ⟨q₁, runQ₁, keepQ₁, semQ₁⟩ := union_ok hc₂ hu₂
        obtain ⟨q₃, runQ₃, keepQ₃, semQ₃⟩ := union_ok hd₂ hu₂
        obtain ⟨r₁, run₁, keep₁, sem₁⟩ := diff_union_spec (i := c₁) hc₂ hu₂ fun u ru => by
          rw [runQ₁] at ru; cases ru
          exact pair hc₁ (keepQ₁ _ hc₂ hu₂) Hc₁ (keepQ₁ _ Hc₂ Hu₂)
            fun m ha' hb' => ⟨(mA m ha').1, keepQ₁ _ (mB m hb').1 (mB m hb').2.1⟩
        obtain ⟨r₃, run₃, keep₃, sem₃⟩ := diff_union_spec (i := d₁) hd₂ hu₂ fun u ru => by
          rw [runQ₃] at ru; cases ru
          exact pair hd₁ (keepQ₃ _ hd₂ hu₂) Hd₁ (keepQ₃ _ Hd₂ Hu₂)
            fun m ha' hb' => ⟨(mA m ha').2.2, keepQ₃ _ (mB m hb').2.2 (mB m hb').2.1⟩
        have w₁ := keep₁ _ hc₁ hc₂ hu₂
        have w₃ := keep₃ _ hd₁ hd₂ hu₂
        obtain ⟨h₃, node⟩ := node_new la r₁ (.atom "bdd_bot") r₃ (head_leaf wa ha) w₁
          (Bdd.bot (ok := fun _ => True)) w₃
        obtain ⟨r, runr, keep, sem, -⟩ := post_spec la r₁ (.atom "bdd_bot") r₃ h₃ w₁ Bdd.bot w₃
        refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
        · rw [← runr]
          unfold Elixir.Module.Types.Descr.«bdd_difference/2»
          have yes : Lynx.Except.orElse (Erlang.erlang.«==/2» u₁ (.atom "bdd_bot")) (Erlang.erlang.«==/2» u₁ u₂) =
              .ok (.atom "true") := by
            by_cases c₀ : Term.compare (Term.fuel u₁ (.atom "bdd_bot")) u₁ (.atom "bdd_bot") = .eq
            · simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c₀, Term.true]
            · have c := cond.resolve_left c₀
              simp [Erlang.erlang.«==/2», Lynx.Except.orElse, c₀, c, Term.true, Term.false]
          simp [Erlang.erlang.«=:=/2», same, run, yes, run₁, run₃, node]
          by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
        · obtain ⟨oc₁, -, od₁⟩ := splitA.children oka
          obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
          exact keep ok (head_leaf wa ha) (head_ok oka ha) (keep₁ _ oc₁ (oc₂.congr order) (ou₂.congr order)) Bdd.bot
            (keep₃ _ od₁ (od₂.congr order) (ou₂.congr order))
        · have hU : eval ρ u₁ = Bool.false ∨ eval ρ u₁ = eval ρ u₂ := by
            rcases cond with c | c
            · left; rw [(compare_eq_atom _ _).mp c]; simp
            · right; exact eval_congr_cmp (hu₁.mono fun _ h => h.1) resp c
          rw [sem ρ resp, sem₁ ρ resp, sem₃ ρ resp]
          simp only [eval_node, eval_bot, bool ρ resp]
          revert hU
          generalize ρ la = L
          generalize eval ρ c₁ = C₁
          generalize eval ρ c₂ = C₂
          generalize eval ρ d₁ = D₁
          generalize eval ρ d₂ = D₂
          generalize eval ρ u₁ = U₁
          generalize eval ρ u₂ = U₂
          revert L C₁ C₂ D₁ D₂ U₁ U₂
          decide
      · obtain ⟨p₁, runP₁, keepP₁, semP₁⟩ := union_ok hc₁ hu₁
        obtain ⟨q₁, runQ₁, keepQ₁, semQ₁⟩ := union_ok hc₂ hu₂
        obtain ⟨p₃, runP₃, keepP₃, semP₃⟩ := union_ok hd₁ hu₁
        obtain ⟨q₃, runQ₃, keepQ₃, semQ₃⟩ := union_ok hd₂ hu₂
        obtain ⟨r₁', run₁, keep₁, sem₁⟩ := pair (keepP₁ _ hc₁ hu₁) (keepQ₁ _ hc₂ hu₂) (keepP₁ _ Hc₁ Hu₁)
          (keepQ₁ _ Hc₂ Hu₂) fun m ha' hb' => ⟨keepP₁ _ (mA m ha').1 (mA m ha').2.1, keepQ₁ _ (mB m hb').1 (mB m hb').2.1⟩
        obtain ⟨r₃', run₃, keep₃, sem₃⟩ := pair (keepP₃ _ hd₁ hu₁) (keepQ₃ _ hd₂ hu₂) (keepP₃ _ Hd₁ Hu₁)
          (keepQ₃ _ Hd₂ Hu₂) fun m ha' hb' => ⟨keepP₃ _ (mA m ha').2.2 (mA m ha').2.1,
            keepQ₃ _ (mB m hb').2.2 (mB m hb').2.1⟩
        obtain ⟨r₁, wr₁, s₁, def₁⟩ : ∃ r₁, (∀ ok, Bdd (Above ok la) c₁ → Bdd (Above ok la) c₂ →
            Bdd (Above ok la) u₁ → Bdd (Above ok la) u₂ → Bdd (Above ok la) r₁) ∧
            (∀ ρ, Resp ρ → eval ρ r₁ = ((eval ρ c₁ || eval ρ u₁) && !(eval ρ c₂ || eval ρ u₂))) ∧
            ((c₂ = .atom "bdd_top" ∧ r₁ = .atom "bdd_bot") ∨ (¬c₂ = .atom "bdd_top" ∧ r₁ = r₁')) := by
          by_cases ct : c₂ = .atom "bdd_top"
          · exact ⟨.atom "bdd_bot", fun _ _ _ _ _ => Bdd.bot, fun ρ _ => by simp [ct], Or.inl ⟨ct, rfl⟩⟩
          · exact ⟨r₁', fun ok o₁ o₂ o₃ o₄ => keep₁ _ (keepP₁ _ o₁ o₃) (keepQ₁ _ o₂ o₄),
              fun ρ resp => by rw [sem₁ ρ resp, semP₁ ρ resp, semQ₁ ρ resp], Or.inr ⟨ct, rfl⟩⟩
        obtain ⟨r₃, wr₃, s₃, def₃⟩ : ∃ r₃, (∀ ok, Bdd (Above ok la) d₁ → Bdd (Above ok la) d₂ →
            Bdd (Above ok la) u₁ → Bdd (Above ok la) u₂ → Bdd (Above ok la) r₃) ∧
            (∀ ρ, Resp ρ → eval ρ r₃ = ((eval ρ d₁ || eval ρ u₁) && !(eval ρ d₂ || eval ρ u₂))) ∧
            ((d₂ = .atom "bdd_top" ∧ r₃ = .atom "bdd_bot") ∨ (¬d₂ = .atom "bdd_top" ∧ r₃ = r₃')) := by
          by_cases dt : d₂ = .atom "bdd_top"
          · exact ⟨.atom "bdd_bot", fun _ _ _ _ _ => Bdd.bot, fun ρ _ => by simp [dt], Or.inl ⟨dt, rfl⟩⟩
          · exact ⟨r₃', fun ok o₁ o₂ o₃ o₄ => keep₃ _ (keepP₃ _ o₁ o₃) (keepQ₃ _ o₂ o₄),
              fun ρ resp => by rw [sem₃ ρ resp, semP₃ ρ resp, semQ₃ ρ resp], Or.inr ⟨dt, rfl⟩⟩
        have w₁ := wr₁ _ hc₁ hc₂ hu₁ hu₂
        have w₃ := wr₃ _ hd₁ hd₂ hu₁ hu₂
        obtain ⟨h₃, node⟩ := node_new la r₁ (.atom "bdd_bot") r₃ (head_leaf wa ha) w₁
          (Bdd.bot (ok := fun _ => True)) w₃
        obtain ⟨r, runr, keep, sem, -⟩ := post_spec la r₁ (.atom "bdd_bot") r₃ h₃ w₁ Bdd.bot w₃
        refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
        · rw [← runr]
          unfold Elixir.Module.Types.Descr.«bdd_difference/2»
          have no : Lynx.Except.orElse (Erlang.erlang.«==/2» u₁ (.atom "bdd_bot")) (Erlang.erlang.«==/2» u₁ u₂) =
              .ok (.atom "false") := by
            simp only [not_or] at cond
            simp [Erlang.erlang.«==/2», Lynx.Except.orElse, cond.1, cond.2, Term.false]
          simp [Erlang.erlang.«=:=/2», same, run, no]
          clear keep sem s₁ s₃ wr₁ wr₃ w₁ w₃ pair lower lowerB ih mA mB
          rcases def₁ with ⟨ct, rfl⟩ | ⟨ct, rfl⟩ <;> rcases def₃ with ⟨dt, rfl⟩ | ⟨dt, rfl⟩ <;>
            simp [Erlang.erlang.«==/2», ct, dt, Term.true, Term.false, runP₁, runQ₁, run₁, runP₃, runQ₃, run₃, node] <;>
            split <;> simp_all
        · obtain ⟨oc₁, ou₁, od₁⟩ := splitA.children oka
          obtain ⟨oc₂, ou₂, od₂⟩ := splitB.children okb
          exact keep ok (head_leaf wa ha) (head_ok oka ha)
            (wr₁ _ oc₁ (oc₂.congr order) ou₁ (ou₂.congr order)) Bdd.bot
            (wr₃ _ od₁ (od₂.congr order) ou₁ (ou₂.congr order))
        · rw [sem ρ resp, s₁ ρ resp, s₃ ρ resp]
          simp only [eval_node, eval_bot, bool ρ resp]
          generalize ρ la = L
          generalize eval ρ c₁ = C₁
          generalize eval ρ c₂ = C₂
          generalize eval ρ d₁ = D₁
          generalize eval ρ d₂ = D₂
          generalize eval ρ u₁ = U₁
          generalize eval ρ u₂ = U₂
          revert L C₁ C₂ D₁ D₂ U₁ U₂
          decide
  · -- gt
    have order' : Term.compare (Term.fuel lb la) lb la = .lt := Lynx.Term.compare_lt_of_gt order
    obtain ⟨h₀, c₂, u₂, d₂, run, split⟩ := compare_gt wb ha hb order
    have raiseA : ∀ {ok : Term → Prop}, Bdd ok a → Bdd (Above ok lb) a :=
      fun w => w.raise fun l hl => by rw [ha] at hl; cases hl; exact order'
    obtain ⟨hc, hu, hd⟩ := split.children wb
    obtain ⟨Hc, Hu, Hd⟩ := split.high wb
    have HA : High lb a := (raiseA wa).mono fun _ h => h.2
    obtain ⟨m, runM, keepM, semM⟩ := ih a u₂ wa (hu.mono fun _ h => h.1)
      (lowerB (fun m ha' hb' => ⟨ha', (High.split split wb hb').2.1⟩) ⟨HA, Hu⟩)
    have wm := keepM _ (raiseA wa) hu
    have Hm : High lb m := keepM _ HA Hu
    obtain ⟨r₁, run₁, keep₁, sem₁⟩ := ih m c₂ (wm.mono fun _ h => h.1) (hc.mono fun _ h => h.1)
      (lowerB (fun m' ha' hb' => ⟨keepM _ ha' (High.split split wb hb').2.1, (High.split split wb hb').1⟩) ⟨Hm, Hc⟩)
    obtain ⟨r₃, run₃, keep₃, sem₃⟩ := ih m d₂ (wm.mono fun _ h => h.1) (hd.mono fun _ h => h.1)
      (lowerB (fun m' ha' hb' => ⟨keepM _ ha' (High.split split wb hb').2.1, (High.split split wb hb').2.2⟩) ⟨Hm, Hd⟩)
    have w₁ := keep₁ _ wm hc
    have w₃ := keep₃ _ wm hd
    obtain ⟨h₁, node⟩ := node_new lb r₁ (.atom "bdd_bot") r₃ (head_leaf wb hb) w₁ (Bdd.bot (ok := fun _ => True)) w₃
    obtain ⟨r, runr, keep, sem, -⟩ := post_spec lb r₁ (.atom "bdd_bot") r₃ h₁ w₁ Bdd.bot w₃
    refine ⟨r, ?_, fun ok oka okb => ?_, fun ρ resp => ?_⟩
    · rw [← runr]
      unfold Elixir.Module.Types.Descr.«bdd_difference/2»
      simp [Erlang.erlang.«=:=/2», same, run, runM, run₁, run₃, node]
      by_cases post : compareExact (fuel r₃ r₁) r₃ r₁ = .eq <;> simp [post]
    · obtain ⟨oc, ou, od⟩ := split.children okb
      have om := keepM _ (raiseA oka) ou
      exact keep ok (head_leaf wb hb) (head_ok okb hb) (keep₁ _ om oc) Bdd.bot (keep₃ _ om od)
    · rw [sem ρ resp, sem₁ ρ resp, sem₃ ρ resp, semM ρ resp, split.eval ρ]
      cases ρ lb <;> cases eval ρ a <;> cases eval ρ u₂ <;> simp

theorem belowD_all (U : List Term) : ∀ n, BelowD U n := by
  intro n
  induction n with
  | zero => intro a b _ _ lt; omega
  | succ n ih =>
    intro a b wa wb lt
    exact diff_step U a b wa wb fun a' b' wa' wb' lt' => ih a' b' wa' wb' (by omega)

theorem diff_ok {oka okb : Term → Prop} {a b : Term} (wa : Bdd oka a) (wb : Bdd okb b) : DiffOk a b :=
  belowD_all (lits a ++ lits b) _ a b (wa.lits.mono fun _ h => List.mem_append_left _ h)
    (wb.lits.mono fun _ h => List.mem_append_right _ h) (Nat.lt_succ_self _)

/-! Unsatisfiable ordered BDDs have no lines. -/

/-- Valuations agreeing on the literals of a BDD agree on the BDD. -/
theorem eval_ext {ok : Term → Prop} {x : Term} (wx : Bdd ok x) {ρ ρ' : Term → Bool}
    (agree : ∀ t, ok t → ρ' t = ρ t) : eval ρ' x = eval ρ x := by
  revert agree
  refine Bdd.induction (P := fun ok x => (∀ t, ok t → ρ' t = ρ t) → eval ρ' x = eval ρ x)
    ?_ ?_ ?_ ?_ ok x wx
  · intro _ _; simp
  · intro _ _; simp
  · intro _ k x y okl agree; simp [agree _ okl]
  · intro ok h lit c u d _ okl _ _ _ ic iu id agree
    have below : ∀ t, Above ok lit t → ρ' t = ρ t := fun t ht => agree t ht.1
    simp [agree _ okl, ic below, iu below, id below]

/-- Setting the truth of a literal. -/
def flip (ρ : Term → Bool) (l : Term) (v : Bool) : Term → Bool :=
  fun t => if Term.compare (Term.fuel t l) t l = .eq then v else ρ t

theorem Resp.flip {ρ : Term → Bool} (resp : Resp ρ) (l : Term) (v : Bool) : Resp (flip ρ l v) := by
  intro a b e
  simp only [BddProofs.flip]
  by_cases ha : Term.compare (Term.fuel a l) a l = .eq
  · have hb : Term.compare (Term.fuel b l) b l = .eq := Lynx.Term.compare_eq_trans (Lynx.Term.compare_eq_symm e) ha
    simp [ha, hb]
  · have hb : ¬Term.compare (Term.fuel b l) b l = .eq := fun hb => ha (Lynx.Term.compare_eq_trans e hb)
    simp [ha, hb, resp a b e]

def Unsat (r : Term) : Prop := ∀ ρ, Resp ρ → eval ρ r = Bool.false

theorem resp_const (v : Bool) : Resp (fun _ => v) := fun _ _ _ => rfl

theorem dnf_unsat {ok : Term → Prop} {r : Term} (wr : Bdd ok r) (unsat : Unsat r) :
    ∀ acc pos neg, Elixir.Module.Types.Descr.«bdd_to_dnf/4» acc pos neg r = .ok acc := by
  revert unsat
  refine Bdd.induction (P := fun _ r => Unsat r → ∀ acc pos neg,
    Elixir.Module.Types.Descr.«bdd_to_dnf/4» acc pos neg r = .ok acc) ?_ ?_ ?_ ?_ ok r wr
  · intro _ unsat; have := unsat _ (resp_const Bool.true); simp at this
  · intro _ _ acc pos neg; simp [Elixir.Module.Types.Descr.«bdd_to_dnf/4»]
  · intro _ k x y _ unsat; have := unsat _ (resp_const Bool.true); simp at this
  · intro ok h lit c u d _ _ hc hu hd ic iu id unsat acc pos neg
    have above : ∀ v ρ t, Above ok lit t → flip ρ lit v t = ρ t := fun v ρ t ht => by
      have : Term.compare (Term.fuel t lit) t lit ≠ .eq := fun e => by
        have := ht.2; rw [Lynx.Term.compare_eq_symm e] at this; cases this
      simp [BddProofs.flip, this]
    have parts : ∀ ρ, Resp ρ → eval ρ c = Bool.false ∧ eval ρ u = Bool.false ∧ eval ρ d = Bool.false := by
      intro ρ resp
      have t := unsat _ (resp.flip lit Bool.true)
      have f := unsat _ (resp.flip lit Bool.false)
      simp only [eval_node, eval_ext hc (above Bool.true ρ), eval_ext hu (above Bool.true ρ),
        eval_ext hd (above Bool.true ρ)] at t
      simp only [eval_node, eval_ext hc (above Bool.false ρ), eval_ext hu (above Bool.false ρ),
        eval_ext hd (above Bool.false ρ)] at f
      simp [BddProofs.flip] at t f
      exact ⟨t.1, t.2, f.2⟩
    simp only [Elixir.Module.Types.Descr.«bdd_to_dnf/4»]
    rw [iu (fun ρ resp => (parts ρ resp).2.1), Lynx.Except.ok_bind, ic (fun ρ resp => (parts ρ resp).1),
      Lynx.Except.ok_bind, id (fun ρ resp => (parts ρ resp).2.2)]

/-- Unsatisfiable list BDDs are empty. -/
theorem list_empty_unsat (dsp : Dispatcher) {ok : Term → Prop} {r : Term} (wr : Bdd ok r) (unsat : Unsat r)
    (S : List (Term × Term)) :
    Elixir.Module.Types.Descr.«list_empty?/2» dsp r (.map S) = .ok (.atom "true") := by
  have dnf := dnf_unsat wr unsat .nil .nil .nil
  unfold Elixir.Module.Types.Descr.«list_empty?/2»
  split
  · have := unsat _ (resp_const Bool.true); simp at this
  · simp only [Elixir.Module.Types.Descr.«empty_bdd_seen_key/2», Elixir.Module.Types.Descr.«bdd_to_dnf/1», dnf,
      Lynx.Except.ok_bind]
    by_cases seen : S.any (fun e => Term.compareExact (Term.fuel (.cons (.atom "list") r) e.1) (.cons (.atom "list") r) e.1 == .eq) = Bool.true
    · simp [Erlang.erlang.«is_map_key/2», seen, Term.true]
    · simp [Erlang.erlang.«is_map_key/2», seen, Term.true, Term.false, Erlang.maps.«put/3»,
        Erlang.lists.«all/2», Erlang.erlang.«is_function/2»]

end BddProofs

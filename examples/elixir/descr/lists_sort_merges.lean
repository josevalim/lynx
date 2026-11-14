namespace Elixir.STTDescrProofsTest.USort
open Lynx

section
variable (κ : Term → Term) (Kd : Term → Prop)

/-! Ascending sources merged into a descending accumulator (`ukeymerge*`, `umerge*`). -/

/-- Every key of the accumulator is below `x`. -/
def Above (M : List Term) (x : Term) : Prop := ∀ m ∈ M, Term.compare (Term.fuel (κ m) (κ x)) (κ m) (κ x) = .lt

/-- `x` is above the accumulator or a duplicate of its head. -/
def Up (M : List Term) (x : Term) : Prop :=
  Above κ M x ∨ ∃ m M', M = m :: M' ∧ Term.compare (Term.fuel (κ x) (κ m)) (κ x) (κ m) = .eq

/-- The tracked head key of the accumulator; when it is empty no source key matches it. -/
def HdOK (M : List Term) (h : Term) (S : List Term) : Prop :=
  match M with
  | [] => ∀ x ∈ S, Term.compare (Term.fuel (κ x) h) (κ x) h ≠ .eq
  | m :: _ => Term.compare (Term.fuel h (κ m)) h (κ m) = .eq

structure Pre (M A B C : List Term) : Prop where
  sm : SD κ M
  sa : SA κ A
  sb : SA κ B
  sc : SA κ C
  ka : ∀ x ∈ A, Kd x
  kb : ∀ x ∈ B, Kd x
  kc : ∀ x ∈ C, Kd x
  ua : ∀ x ∈ A, Above κ M x
  ub : ∀ x ∈ B, Up κ M x
  uc : ∀ x ∈ C, Up κ M x

/-- A descending result with the contents of the state, earlier sources first. -/
def Res (M A B C R : List Term) : Prop := SD κ R ∧ Eqv κ R (M ++ A ++ B ++ C)

variable {κ Kd}

theorem above_lt {M : List Term} {x y : Term} (hx : Above κ M x)
    (h : Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt) : Above κ M y :=
  fun m hm => c_lt_trans (hx m hm) h

theorem above_cons {M : List Term} {x y : Term} (hx : Above κ M x)
    (h : Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt) : Above κ (x :: M) y := by
  intro m hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact h
  · exact above_lt hx h m hm

theorem up_cons {M : List Term} {x y : Term} (hx : Above κ M x)
    (h : (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE) : Up κ (x :: M) y := by
  cases e : Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)
  · exact Or.inl (above_cons hx e)
  · exact Or.inr ⟨x, M, rfl, c_eq_symm e⟩
  · simp [e] at h

theorem up_of_above {M : List Term} {x : Term} (h : Above κ M x) : Up κ M x := Or.inl h

/-- A tracked head decides whether a source element duplicates the accumulator head. -/
theorem up_split {M S : List Term} {h x : Term} (hd : HdOK κ M h S) (hx : x ∈ S)
    (u : Up κ M x) :
    (Term.compare (Term.fuel (κ x) h) (κ x) h = .eq → ∃ m M', M = m :: M' ∧ Term.compare (Term.fuel (κ x) (κ m)) (κ x) (κ m) = .eq) ∧
    (Term.compare (Term.fuel (κ x) h) (κ x) h ≠ .eq → Above κ M x) := by
  cases M with
  | nil => exact ⟨fun e => absurd e (hd x hx), fun _ m hm => by simp at hm⟩
  | cons m M' =>
    simp only [HdOK] at hd
    refine ⟨fun e => ⟨m, M', rfl, c_eq_trans e hd⟩, fun ne => ?_⟩
    rcases u with u | ⟨m', M'', e, u⟩
    · exact u
    · cases e; exact absurd (c_eq_trans u (c_eq_symm hd)) ne

theorem hd_self {M S : List Term} {x : Term} : HdOK κ (x :: M) (κ x) S := by
  simp [HdOK]

theorem eqv_mid {M A : List Term} {x : Term} (hm : Above κ M x)
    (ha : ∀ y ∈ A, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt) (B' : List Term) :
    Eqv κ (x :: M ++ A ++ B') (M ++ A ++ x :: B') := by
  have := eqv_move (κ := κ) (x := x) (A := M ++ A) (B := B') (by
    intro y hy e
    simp only [List.mem_append] at hy
    rcases hy with hy | hy
    · exact absurd (hm y hy) (by simp [e])
    · have := ha y hy; rw [c_swap, e] at this; simp at this)
  simpa using this.symm

theorem pushA {M A B C : List Term} {x : Term} (p : Pre κ Kd M (x :: A) B C)
    (hb : ∀ y ∈ B.head?, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE)
    (hc : ∀ y ∈ C.head?, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE) :
    Pre κ Kd (x :: M) A B C ∧ ∀ R, Res κ (x :: M) A B C R → Res κ M (x :: A) B C R := by
  have hx : Above κ M x := p.ua x (by simp)
  have sa := SA_cons.1 p.sa
  have le_all : ∀ {S : List Term}, SA κ S → (∀ y ∈ S.head?, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE) →
      ∀ y ∈ S, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE := by
    intro S s h y hy
    cases S with
    | nil => simp at hy
    | cons b S => exact SA.le_all s (h b (by simp)) y hy
  refine ⟨⟨SD_cons.2 ⟨fun m hm => c_gt_of_lt (hx m hm), p.sm⟩, sa.2, p.sb, p.sc,
    fun y hy => p.ka y (by simp [hy]), p.kb, p.kc,
    fun y hy => above_cons hx (sa.1 y hy),
    fun y hy => up_cons hx (le_all p.sb hb y hy),
    fun y hy => up_cons hx (le_all p.sc hc y hy)⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  simpa using eqv_mid (A := []) hx (fun _ h => by simp at h) (A ++ B ++ C)

theorem pushB {M A B C : List Term} {x : Term} (p : Pre κ Kd M A (x :: B) C) (hx : Above κ M x)
    (ha : ∀ y ∈ A.head?, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt)
    (hc : ∀ y ∈ C.head?, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE) :
    Pre κ Kd (x :: M) A B C ∧ ∀ R, Res κ (x :: M) A B C R → Res κ M A (x :: B) C R := by
  have sb := SA_cons.1 p.sb
  have lt_a : ∀ y ∈ A, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt := by
    intro y hy
    cases A with
    | nil => simp at hy
    | cons b A => exact SA.lt_all p.sa (ha b (by simp)) y hy
  have le_c : ∀ y ∈ C, (Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y)).isLE := by
    intro y hy
    cases C with
    | nil => simp at hy
    | cons b C => exact SA.le_all p.sc (hc b (by simp)) y hy
  refine ⟨⟨SD_cons.2 ⟨fun m hm => c_gt_of_lt (hx m hm), p.sm⟩, p.sa, sb.2, p.sc,
    p.ka, fun y hy => p.kb y (by simp [hy]), p.kc,
    fun y hy => above_cons hx (lt_a y hy),
    fun y hy => up_of_above (above_cons hx (sb.1 y hy)),
    fun y hy => up_cons hx (le_c y hy)⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  simpa using eqv_mid hx lt_a (B ++ C)

theorem pushC {M A B C : List Term} {x : Term} (p : Pre κ Kd M A B (x :: C)) (hx : Above κ M x)
    (ha : ∀ y ∈ A.head?, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt)
    (hb : ∀ y ∈ B.head?, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt) :
    Pre κ Kd (x :: M) A B C ∧ ∀ R, Res κ (x :: M) A B C R → Res κ M A B (x :: C) R := by
  have sc := SA_cons.1 p.sc
  have lt_all : ∀ {S : List Term}, SA κ S → (∀ y ∈ S.head?, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt) →
      ∀ y ∈ S, Term.compare (Term.fuel (κ x) (κ y)) (κ x) (κ y) = .lt := by
    intro S s h y hy
    cases S with
    | nil => simp at hy
    | cons b S => exact SA.lt_all s (h b (by simp)) y hy
  refine ⟨⟨SD_cons.2 ⟨fun m hm => c_gt_of_lt (hx m hm), p.sm⟩, p.sa, p.sb, sc.2,
    p.ka, p.kb, fun y hy => p.kc y (by simp [hy]),
    fun y hy => above_cons hx (lt_all p.sa ha y hy),
    fun y hy => up_of_above (above_cons hx (lt_all p.sb hb y hy)),
    fun y hy => up_of_above (above_cons hx (sc.1 y hy))⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  have := eqv_mid (A := A ++ B) hx (fun y hy => by
    simp only [List.mem_append] at hy
    rcases hy with hy | hy
    · exact lt_all p.sa ha y hy
    · exact lt_all p.sb hb y hy) C
  simpa using this

theorem dropB {M A B C : List Term} {x : Term} (p : Pre κ Kd M A (x :: B) C)
    (hd : ∃ m M', M = m :: M' ∧ Term.compare (Term.fuel (κ x) (κ m)) (κ x) (κ m) = .eq) :
    Pre κ Kd M A B C ∧ (∀ y ∈ B, Above κ M y) ∧
      ∀ R, Res κ M A B C R → Res κ M A (x :: B) C R := by
  have sb := SA_cons.1 p.sb
  obtain ⟨m, M', rfl, e⟩ := hd
  have ab : ∀ y ∈ B, Above κ (m :: M') y := by
    intro y hy m' hm'
    have hmx : (Term.compare (Term.fuel (κ m') (κ x)) (κ m') (κ x)).isLE := by
      simp only [List.mem_cons] at hm'
      rcases hm' with rfl | hm'
      · simp [c_eq_symm e]
      · have := (SD_cons.1 p.sm).1 m' hm'
        have := c_lt_eq (c_lt_of_gt this) (c_eq_symm e); simp [this]
    exact c_le_lt hmx (sb.1 y hy)
  refine ⟨⟨p.sm, p.sa, sb.2, p.sc, p.ka, fun y hy => p.kb y (by simp [hy]), p.kc, p.ua,
    fun y hy => up_of_above (ab y hy), p.uc⟩, ab, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  have := eqv_drop (κ := κ) (A := m :: M' ++ A) (B := B ++ C) (x := x) (y := m) (by simp)
    (c_eq_symm e)
  simpa using this.symm

theorem dropC {M A B C : List Term} {x : Term} (p : Pre κ Kd M A B (x :: C))
    (hd : ∃ m M', M = m :: M' ∧ Term.compare (Term.fuel (κ x) (κ m)) (κ x) (κ m) = .eq) :
    Pre κ Kd M A B C ∧ (∀ y ∈ C, Above κ M y) ∧
      ∀ R, Res κ M A B C R → Res κ M A B (x :: C) R := by
  have sc := SA_cons.1 p.sc
  obtain ⟨m, M', rfl, e⟩ := hd
  have ac : ∀ y ∈ C, Above κ (m :: M') y := by
    intro y hy m' hm'
    have hmx : (Term.compare (Term.fuel (κ m') (κ x)) (κ m') (κ x)).isLE := by
      simp only [List.mem_cons] at hm'
      rcases hm' with rfl | hm'
      · simp [c_eq_symm e]
      · have := (SD_cons.1 p.sm).1 m' hm'
        have := c_lt_eq (c_lt_of_gt this) (c_eq_symm e); simp [this]
    exact c_le_lt hmx (sc.1 y hy)
  refine ⟨⟨p.sm, p.sa, p.sb, sc.2, p.ka, p.kb, fun y hy => p.kc y (by simp [hy]), p.ua, p.ub,
    fun y hy => up_of_above (ac y hy)⟩, ac, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  have := eqv_drop (κ := κ) (A := m :: M' ++ A ++ B) (B := C) (x := x) (y := m) (by simp)
    (c_eq_symm e)
  simpa using this.symm

theorem res_congr {M A B C M' A' B' C' R : List Term}
    (h : M ++ A ++ B ++ C = M' ++ A' ++ B' ++ C') (r : Res κ M A B C R) : Res κ M' A' B' C' R :=
  ⟨r.1, h ▸ r.2⟩

/-- Reversing the last source onto the accumulator. -/
theorem finish {M T : List Term} (sm : SD κ M) (st : SA κ T) (ht : ∀ y ∈ T, Above κ M y) :
    SD κ (T.reverse ++ M) ∧ Eqv κ (T.reverse ++ M) (M ++ T) := by
  refine ⟨?_, ?_⟩
  · simp only [SD, List.pairwise_append]
    refine ⟨SD_reverse.2 st, sm, fun a ha m hm => c_gt_of_lt (ht a (by simpa using ha) m hm)⟩
  · refine (Eqv.append (eqv_reverse st.ne) (Eqv.refl M)).trans (eqv_comm ?_)
    intro a ha m hm e
    have := ht a ha m hm; rw [c_swap, e] at this; simp at this

/-! Descending sources merged into an ascending accumulator (`rukeymerge*`, `rumerge*`). -/

variable (κ Kd)

def Below (M : List Term) (x : Term) : Prop := ∀ m ∈ M, Term.compare (Term.fuel (κ x) (κ m)) (κ x) (κ m) = .lt

structure PreD (M A B C : List Term) : Prop where
  sm : SA κ M
  sa : SD κ A
  sb : SD κ B
  sc : SD κ C
  ka : ∀ x ∈ A, Kd x
  kb : ∀ x ∈ B, Kd x
  kc : ∀ x ∈ C, Kd x
  ua : ∀ x ∈ A, Below κ M x
  ub : ∀ x ∈ B, Below κ M x
  uc : ∀ x ∈ C, Below κ M x

def ResD (M A B C R : List Term) : Prop := SA κ R ∧ Eqv κ R (M ++ A ++ B ++ C)

variable {κ Kd}

theorem resD_congr {M A B C M' A' B' C' R : List Term}
    (h : M ++ A ++ B ++ C = M' ++ A' ++ B' ++ C') (r : ResD κ M A B C R) : ResD κ M' A' B' C' R :=
  ⟨r.1, h ▸ r.2⟩

theorem below_cons {M : List Term} {x y : Term} (hx : Below κ M x)
    (h : Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt) : Below κ (x :: M) y := by
  intro m hm
  simp only [List.mem_cons] at hm
  rcases hm with rfl | hm
  · exact h
  · exact c_lt_trans h (hx m hm)

theorem gt_all {S : List Term} {x : Term} (s : SD κ S)
    (h : ∀ y ∈ S.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt) : ∀ y ∈ S, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt := by
  intro y hy
  cases S with
  | nil => simp at hy
  | cons b S =>
    have := SD.gt_all s (x := x) (c_gt_of_lt (h b (by simp))) y hy
    exact c_lt_of_gt this

theorem eqv_midD {M A : List Term} {x : Term} (hm : Below κ M x)
    (ha : ∀ y ∈ A, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt) (B' : List Term) :
    Eqv κ (x :: M ++ A ++ B') (M ++ A ++ x :: B') := by
  have := eqv_move (κ := κ) (x := x) (A := M ++ A) (B := B') (by
    intro y hy e
    simp only [List.mem_append] at hy
    rcases hy with hy | hy
    · have := hm y hy; rw [c_swap, e] at this; simp at this
    · exact absurd (ha y hy) (by simp [e]))
  simpa using this.symm

theorem pushDA {M A B C : List Term} {x : Term} (p : PreD κ Kd M (x :: A) B C)
    (hb : ∀ y ∈ B.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt)
    (hc : ∀ y ∈ C.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt) :
    PreD κ Kd (x :: M) A B C ∧ ∀ R, ResD κ (x :: M) A B C R → ResD κ M (x :: A) B C R := by
  have hx := p.ua x (by simp)
  have sa := SD_cons.1 p.sa
  refine ⟨⟨SA_cons.2 ⟨fun m hm => hx m hm, p.sm⟩, sa.2, p.sb, p.sc,
    fun y hy => p.ka y (by simp [hy]), p.kb, p.kc,
    fun y hy => below_cons hx (c_lt_of_gt (sa.1 y hy)),
    fun y hy => below_cons hx (gt_all p.sb hb y hy),
    fun y hy => below_cons hx (gt_all p.sc hc y hy)⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  simpa using eqv_midD (A := []) hx (fun _ h => by simp at h) (A ++ B ++ C)

theorem pushDB {M A B C : List Term} {x : Term} (p : PreD κ Kd M A (x :: B) C)
    (ha : ∀ y ∈ A.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt)
    (hc : ∀ y ∈ C.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt) :
    PreD κ Kd (x :: M) A B C ∧ ∀ R, ResD κ (x :: M) A B C R → ResD κ M A (x :: B) C R := by
  have hx := p.ub x (by simp)
  have sb := SD_cons.1 p.sb
  have la := gt_all p.sa ha
  refine ⟨⟨SA_cons.2 ⟨fun m hm => hx m hm, p.sm⟩, p.sa, sb.2, p.sc,
    p.ka, fun y hy => p.kb y (by simp [hy]), p.kc,
    fun y hy => below_cons hx (la y hy),
    fun y hy => below_cons hx (c_lt_of_gt (sb.1 y hy)),
    fun y hy => below_cons hx (gt_all p.sc hc y hy)⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  simpa using eqv_midD hx la (B ++ C)

theorem pushDC {M A B C : List Term} {x : Term} (p : PreD κ Kd M A B (x :: C))
    (ha : ∀ y ∈ A.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt)
    (hb : ∀ y ∈ B.head?, Term.compare (Term.fuel (κ y) (κ x)) (κ y) (κ x) = .lt) :
    PreD κ Kd (x :: M) A B C ∧ ∀ R, ResD κ (x :: M) A B C R → ResD κ M A B (x :: C) R := by
  have hx := p.uc x (by simp)
  have sc := SD_cons.1 p.sc
  have la := gt_all p.sa ha
  have lb := gt_all p.sb hb
  refine ⟨⟨SA_cons.2 ⟨fun m hm => hx m hm, p.sm⟩, p.sa, p.sb, sc.2,
    p.ka, p.kb, fun y hy => p.kc y (by simp [hy]),
    fun y hy => below_cons hx (la y hy),
    fun y hy => below_cons hx (lb y hy),
    fun y hy => below_cons hx (c_lt_of_gt (sc.1 y hy))⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  have := eqv_midD (A := A ++ B) hx (fun y hy => by
    simp only [List.mem_append] at hy
    rcases hy with hy | hy
    · exact la y hy
    · exact lb y hy) C
  simpa using this

/-- A source head equal to the head of an earlier source is shadowed. -/
theorem dropDB {M A B C : List Term} {x a : Term} (p : PreD κ Kd M A (x :: B) C)
    (ha : a ∈ A) (e : Term.compare (Term.fuel (κ a) (κ x)) (κ a) (κ x) = .eq) :
    PreD κ Kd M A B C ∧ ∀ R, ResD κ M A B C R → ResD κ M A (x :: B) C R := by
  refine ⟨⟨p.sm, p.sa, (SD_cons.1 p.sb).2, p.sc, p.ka, fun y hy => p.kb y (by simp [hy]), p.kc,
    p.ua, fun y hy => p.ub y (by simp [hy]), p.uc⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  have := eqv_drop (κ := κ) (A := M ++ A) (B := B ++ C) (x := x) (y := a) (by simp [ha]) e
  simpa using this.symm

theorem dropDC {M A B C : List Term} {x a : Term} (p : PreD κ Kd M A B (x :: C))
    (ha : a ∈ A ++ B) (e : Term.compare (Term.fuel (κ a) (κ x)) (κ a) (κ x) = .eq) :
    PreD κ Kd M A B C ∧ ∀ R, ResD κ M A B C R → ResD κ M A B (x :: C) R := by
  refine ⟨⟨p.sm, p.sa, p.sb, (SD_cons.1 p.sc).2, p.ka, p.kb, fun y hy => p.kc y (by simp [hy]),
    p.ua, p.ub, fun y hy => p.uc y (by simp [hy])⟩, ?_⟩
  rintro R ⟨sr, er⟩
  refine ⟨sr, er.trans ?_⟩
  have := eqv_drop (κ := κ) (A := M ++ A ++ B) (B := C) (x := x) (y := a)
    (by simp only [List.mem_append] at ha ⊢; rcases ha with ha | ha <;> simp [ha]) e
  simpa using this.symm

theorem finishD {M T : List Term} (sm : SA κ M) (st : SD κ T) (ht : ∀ y ∈ T, Below κ M y) :
    SA κ (T.reverse ++ M) ∧ Eqv κ (T.reverse ++ M) (M ++ T) := by
  refine ⟨?_, ?_⟩
  · simp only [SA, List.pairwise_append]
    refine ⟨SA_reverse.2 st, sm, fun a ha m hm => ht a (by simpa using ha) m hm⟩
  · refine (Eqv.append (eqv_reverse st.ne) (Eqv.refl M)).trans (eqv_comm ?_)
    intro a ha m hm e
    exact absurd (ht a ha m hm) (by simp [e])

end

end Elixir.STTDescrProofsTest.USort

namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! Types without function fields checked empty hold no points. -/

section
variable {L : Level}

/-- Emptiness is sound on top-level types, whose function types are arrows. -/
theorem tc_empty_sound {C : List (Term × Term)} (sC : DC L C) {m : Nat} (hm : L.K + 11 ≤ m)
    (h : Elixir.Module.Types.Descr.«empty?/1» (D m) (.map C) = .ok (.atom "true")) :
    ∀ v : TP L, ¬denD (.map C) v := by
  obtain ⟨b, run, ex⟩ := descr_empty (tks L) (tfc L) trivial hm sC [] trivial
  rw [empty_map_seen, run] at h
  have hb : b = Bool.true := by cases b <;> simp_all [boolAtom]
  have none := (ex (lh (.map C) + 1) (by omega) (safeN_nil _)).2 hb
  intro v hv
  have := none v.1.1 v.1.2 v.2.2
  rw [(denD_map v).mp hv] at this
  cases this

end

end Elixir.STTDescrProofsTest.Nest

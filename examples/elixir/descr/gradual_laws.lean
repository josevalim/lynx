namespace Elixir.STTDescrProofsTest.Nest
open Lynx Lynx.Term BddProofs

/-! The laws on gradual types, at both bounds. -/

section
variable {L : Level} {m : Nat}

theorem gd_opt_de_morgan_union {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 15 ≤ m) :
    ∃ u x nl nr y, Elixir.Module.Types.Descr.«opt_union/2» (D m) a b = .ok u ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) u = .ok x ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) a = .ok nl ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) b = .ok nr ∧
      Elixir.Module.Types.Descr.«opt_intersection/2» (D m) nl nr = .ok y ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) x y = .ok (.atom "true") := by
  obtain ⟨u, hu, ru, su⟩ := gc_opt_union2 ha hb (m := m) (by omega)
  obtain ⟨x, hx, rx, sx⟩ := gc_opt_neg hu hm
  obtain ⟨nl, hnl, rnl, snl⟩ := gc_opt_neg ha hm
  obtain ⟨nr, hnr, rnr, snr⟩ := gc_opt_neg hb hm
  obtain ⟨y, hy, ry, sy⟩ := gc_opt_inter2 hnl hnr (m := m) (by omega)
  exact ⟨u, x, nl, nr, y, ru, rx, rnl, rnr, ry, gc_equal hx hy (by omega)
    (fun v => by rw [sx.1, su.2, sy.1, snl.1, snr.1]; exact not_or)
    (fun v => by rw [sx.2, su.1, sy.2, snl.2, snr.2]; exact not_or)⟩

theorem gd_opt_de_morgan_inter {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 15 ≤ m) :
    ∃ i x nl nr y, Elixir.Module.Types.Descr.«opt_intersection/2» (D m) a b = .ok i ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) i = .ok x ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) a = .ok nl ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) b = .ok nr ∧
      Elixir.Module.Types.Descr.«opt_union/2» (D m) nl nr = .ok y ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) x y = .ok (.atom "true") := by
  obtain ⟨i, hi, ri, si⟩ := gc_opt_inter2 ha hb (m := m) (by omega)
  obtain ⟨x, hx, rx, sx⟩ := gc_opt_neg hi hm
  obtain ⟨nl, hnl, rnl, snl⟩ := gc_opt_neg ha hm
  obtain ⟨nr, hnr, rnr, snr⟩ := gc_opt_neg hb hm
  obtain ⟨y, hy, ry, sy⟩ := gc_opt_union2 hnl hnr (m := m) (by omega)
  exact ⟨i, x, nl, nr, y, ri, rx, rnl, rnr, ry, gc_equal hx hy (by omega)
    (fun v => by rw [sx.1, si.2, sy.1, snl.1, snr.1]; exact Classical.not_and_iff_not_or_not)
    (fun v => by rw [sx.2, si.1, sy.2, snl.2, snr.2]; exact Classical.not_and_iff_not_or_not)⟩

theorem gd_opt_inter_sub {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ i, Elixir.Module.Types.Descr.«opt_intersection/2» (D m) a b = .ok i ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) i a = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) i b = .ok (.atom "true") := by
  obtain ⟨i, hi, ri, si⟩ := gc_opt_inter2 ha hb hm
  exact ⟨i, ri, gc_sub hi ha (by omega) (fun v h => ((si.1 v).mp h).1) (fun v h => ((si.2 v).mp h).1),
    gc_sub hi hb (by omega) (fun v h => ((si.1 v).mp h).2) (fun v h => ((si.2 v).mp h).2)⟩

theorem gd_opt_union_sup {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ u, Elixir.Module.Types.Descr.«opt_union/2» (D m) a b = .ok u ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a u = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) b u = .ok (.atom "true") := by
  obtain ⟨u, hu, ru, su⟩ := gc_opt_union2 ha hb hm
  exact ⟨u, ru, gc_sub ha hu (by omega) (fun v h => (su.1 v).mpr (Or.inl h)) (fun v h => (su.2 v).mpr (Or.inl h)),
    gc_sub hb hu (by omega) (fun v h => (su.1 v).mpr (Or.inr h)) (fun v h => (su.2 v).mpr (Or.inr h))⟩

theorem gd_inter_sub {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ i, Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok i ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) i a = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) i b = .ok (.atom "true") := by
  obtain ⟨i, hi, ri, si, -⟩ := gc_inter ha hb hm
  exact ⟨i, ri, gc_sub hi ha (by omega) (fun v h => ((si.1 v).mp h).1) (fun v h => ((si.2 v).mp h).1),
    gc_sub hi hb (by omega) (fun v h => ((si.1 v).mp h).2) (fun v h => ((si.2 v).mp h).2)⟩

theorem gd_union_sup {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ u, Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok u ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) a u = .ok (.atom "true") ∧
      Elixir.Module.Types.Descr.«subtype?/2» (D m) b u = .ok (.atom "true") := by
  obtain ⟨u, hu, ru, su⟩ := gc_union ha hb hm
  exact ⟨u, ru, gc_sub ha hu (by omega) (fun v h => (su.1 v).mpr (Or.inl h)) (fun v h => (su.2 v).mpr (Or.inl h)),
    gc_sub hb hu (by omega) (fun v h => (su.1 v).mpr (Or.inr h)) (fun v h => (su.2 v).mpr (Or.inr h))⟩

theorem gd_union_equal {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ u w, Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok u ∧
      Elixir.Module.Types.Descr.«opt_union/2» (D m) a b = .ok w ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) u w = .ok (.atom "true") := by
  obtain ⟨u, hu, ru, su⟩ := gc_union ha hb hm
  obtain ⟨w, hw, rw', sw⟩ := gc_opt_union2 ha hb hm
  exact ⟨u, w, ru, rw', gc_equal hu hw (by omega) (fun v => by rw [su.1, sw.1]) (fun v => by rw [su.2, sw.2])⟩

theorem gd_inter_equal {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ i j, Elixir.Module.Types.Descr.«bare_intersection/2» (D m) a b = .ok i ∧
      Elixir.Module.Types.Descr.«opt_intersection/2» (D m) a b = .ok j ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) i j = .ok (.atom "true") := by
  obtain ⟨i, hi, ri, si, -⟩ := gc_inter ha hb hm
  obtain ⟨j, hj, rj, sj⟩ := gc_opt_inter2 ha hb hm
  exact ⟨i, j, ri, rj, gc_equal hi hj (by omega) (fun v => by rw [si.1, sj.1]) (fun v => by rw [si.2, sj.2])⟩

theorem gd_distrib {t a b : Term} (ht : GC L t) (ha : GC L a) (hb : GC L b) (hm : L.K + 14 ≤ m) :
    ∃ u x y z w, Elixir.Module.Types.Descr.«bare_union/2» (D m) a b = .ok u ∧
      Elixir.Module.Types.Descr.«bare_intersection/2» (D m) t u = .ok x ∧
      Elixir.Module.Types.Descr.«bare_intersection/2» (D m) t a = .ok y ∧
      Elixir.Module.Types.Descr.«bare_intersection/2» (D m) t b = .ok z ∧
      Elixir.Module.Types.Descr.«bare_union/2» (D m) y z = .ok w ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) x w = .ok (.atom "true") := by
  obtain ⟨u, hu, ru, su⟩ := gc_union ha hb hm
  obtain ⟨x, hx, rx, sx, -⟩ := gc_inter ht hu hm
  obtain ⟨y, hy, ry, sy, -⟩ := gc_inter ht ha hm
  obtain ⟨z, hz, rz, sz, -⟩ := gc_inter ht hb hm
  obtain ⟨w, hw, rw', sw⟩ := gc_union hy hz hm
  exact ⟨u, x, y, z, w, ru, rx, ry, rz, rw', gc_equal hx hw (by omega)
    (fun v => by rw [sx.1, su.1, sw.1, sy.1, sz.1]; exact and_or_left)
    (fun v => by rw [sx.2, su.2, sw.2, sy.2, sz.2]; exact and_or_left)⟩

theorem gd_neg_equal {a : Term} (ha : GC L a) (hm : L.K + 15 ≤ m) :
    ∃ x y, Elixir.Module.Types.Descr.«bare_negation/1» (D m) a = .ok x ∧
      Elixir.Module.Types.Descr.«opt_negation/1» (D m) a = .ok y ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) x y = .ok (.atom "true") := by
  obtain ⟨x, hx, rx, sx⟩ := gc_neg ha hm
  obtain ⟨y, hy, ry, sy⟩ := gc_opt_neg ha hm
  exact ⟨x, y, rx, ry, gc_equal hx hy (by omega) (fun v => by rw [sx.1, sy.1]) (fun v => by rw [sx.2, sy.2])⟩

theorem gd_diff_equal {a b : Term} (ha : GC L a) (hb : GC L b) (hm : L.K + 15 ≤ m) :
    ∃ x y, Elixir.Module.Types.Descr.«bare_difference/2» (D m) a b = .ok x ∧
      Elixir.Module.Types.Descr.«opt_difference/2» (D m) a b = .ok y ∧
      Elixir.Module.Types.Descr.«equal?/2» (D m) x y = .ok (.atom "true") := by
  obtain ⟨x, hx, rx, sx⟩ := gc_diff ha hb hm
  obtain ⟨y, hy, ry, sy⟩ := gc_opt_diff2 ha hb hm
  exact ⟨x, y, rx, ry, gc_equal hx hy (by omega) (fun v => by rw [sx.1, sy.1]) (fun v => by rw [sx.2, sy.2])⟩

end

end Elixir.STTDescrProofsTest.Nest

module

import Lynx.Modules.Erlang.erlang
meta import Lynx.Modules.Erlang.erlang
meta import LynxTest.ProofAudit
import Lynx

namespace LynxTest.Modules.Hashing
open Lynx

/-! Portable hashes, checked against `erlang:phash2/1,2` on Erlang/OTP 29.1.2.
Each case is a term, its `phash2/1` value, and its `phash2/2` value with range
`2^32`, which is the full hash. -/

private meta def cases : List (Term × Nat × Nat) := [
  ((.integer (0)), 88723725, 3175731469),
  ((.integer (1)), 2614250, 539485162),
  ((.integer (-1)), 44071773, 1117813597),
  ((.integer (255)), 44734653, 715823293),
  ((.integer (256)), 37021655, 3929335767),
  ((.integer (1000)), 65787489, 4226537057),
  ((.integer (-1000)), 121372174, 2537291278),
  ((.integer (134217727)), 112602999, 4273352567),
  ((.integer (134217728)), 12354923, 2562491755),
  ((.integer (-134217728)), 69672967, 874979335),
  ((.integer (-134217729)), 76739502, 1418916782),
  ((.integer (4294967296)), 95057355, 2108323275),
  ((.integer (576460752303423487)), 27520264, 1638133000),
  ((.integer (-576460752303423488)), 35173814, 2316875190),
  ((.integer (576460752303423488)), 26969617, 2442888721),
  ((.integer (18446744073709551616)), 103122609, 2519041713),
  ((.integer (-18446744073709551616)), 13457787, 2563594619),
  ((.integer (18446744073709551615)), 53435350, 321870806),
  ((.integer (1267650600228229401496703205376)), 126219984, 528873168),
  ((.integer (-1267650600228229401496703205369)), 17713402, 3373156602),
  ((.integer (123456789012345678901234567890)), 132143600, 3353369072),
  ((.float ⟨false, 0, 0⟩), 20875736, 423528920),
  ((.float ⟨true, 0, 0⟩), 20875736, 423528920),
  ((.float ⟨false, 1023, 0⟩), 77147068, 3029937084),
  ((.float ⟨true, 1023, 2251799813685248⟩), 13753666, 1758584130),
  ((.float ⟨false, 1024, 2570632149304942⟩), 4008880, 1211968432),
  ((.float ⟨false, 2019, 2221273467876764⟩), 119088650, 387524106),
  ((.float ⟨false, 0, 1⟩), 107647591, 3731526247),
  ((.atom "a"), 97, 97),
  ((.atom "open"), 485054, 485054),
  ((.atom "closed"), 111372724, 111372724),
  ((.atom "term"), 502925, 502925),
  ((.atom "bdd_bot"), 11163908, 145381636),
  ((.atom "bdd_top"), 11168512, 145386240),
  ((.atom "hello world"), 18131988, 18131988),
  ((.atom "café"), 432201, 432201),
  ((.atom "π"), 3440, 3440),
  ((.atom "Elixir.Module.Types.Descr"), 84247378, 218465106),
  ((.atom "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"), 124846081, 124846081),
  ((.atom "Ã©"), 3289, 3289),
  ((.atom "日本語"), 67592990, 67592990),
  ((.bitstring ⟨#[]⟩ 0 (Term.Bitstring.valid_aligned _)), 13708901, 147926629),
  ((.bitstring ⟨#[1]⟩ 0 (Term.Bitstring.valid_aligned _)), 76691218, 881997586),
  ((.bitstring ⟨#[97, 98, 99]⟩ 0 (Term.Bitstring.valid_aligned _)), 98228475, 1306188027),
  ((.bitstring ⟨#[104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100, 33]⟩ 0 (Term.Bitstring.valid_aligned _)), 25699699, 965223795),
  ((.bitstring ⟨#[104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100, 33, 33]⟩ 0 (Term.Bitstring.valid_aligned _)), 2064796, 2552201628),
  ((.bitstring ⟨#[48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 48, 49, 50, 51, 52]⟩ 0 (Term.Bitstring.valid_aligned _)), 133071961, 1206813785),
  ((.bitstring ⟨#[128]⟩ 1 (by decide)), 102233125, 3994547237),
  ((.bitstring ⟨#[160]⟩ 3 (by decide)), 133543196, 3354768668),
  ((.bitstring ⟨#[1, 2, 48]⟩ 4 (by decide)), 11286013, 2292987389),
  ((.bitstring ⟨#[116, 119, 101, 108, 118, 101, 32, 98, 121, 116, 101, 115, 128]⟩ 1 (by decide)), 43471676, 4070003516),
  (.nil, 113427502, 3468870702),
  ((.cons (.integer (1)) .nil), 84609158, 2768963718),
  ((.cons (.integer (1)) (.cons (.integer (2)) (.cons (.integer (3)) .nil))), 25788620, 4186538188),
  ((.cons (.integer (1)) (.cons (.integer (2)) (.cons (.integer (3)) (.cons (.integer (4)) .nil)))), 90049352, 1029573448),
  ((.cons (.integer (1)) (.cons (.integer (2)) (.cons (.integer (3)) (.cons (.integer (4)) (.cons (.integer (5)) .nil))))), 66056394, 3824152778),
  ((.cons (.integer (104)) (.cons (.integer (101)) (.cons (.integer (108)) (.cons (.integer (108)) (.cons (.integer (111)) .nil))))), 81920127, 753008767),
  ((.cons (.atom "a") (.atom "b")), 74710280, 2356411656),
  ((.cons (.integer (1)) (.integer (2))), 86124794, 3844221178),
  ((.cons (.integer (1)) (.cons (.integer (2)) (.integer (3)))), 8851781, 4169601349),
  ((.cons (.integer (256)) (.cons (.integer (1)) (.cons (.integer (2)) .nil))), 88628884, 4115160724),
  ((.cons (.integer (1)) (.cons (.atom "a") (.cons (.integer (2)) (.cons (.integer (3)) .nil)))), 73260087, 2354961463),
  ((.cons (.cons (.integer (1)) .nil) (.cons (.cons (.integer (2)) .nil) .nil)), 109942119, 2928514407),
  ((.cons (.atom "open") .nil), 61102469, 1805932933),
  ((.cons (.atom "open") .nil), 61102469, 1805932933),
  ((.cons (.atom "term") (.atom "term")), 46675407, 3804771791),
  ((.cons .nil .nil), 96416884, 499070068),
  ((.cons (.integer (1)) (.cons (.integer (-1)) .nil)), 26242804, 428895988),
  ((.cons (.integer (300)) (.cons (.integer (1)) (.cons (.integer (2)) (.cons (.integer (3)) (.cons (.integer (4)) (.cons (.integer (5)) .nil)))))), 86869940, 221087668),
  ((.tuple #[]), 87486268, 221703996),
  ((.tuple #[(.atom "a")]), 35332806, 2853905094),
  ((.tuple #[(.integer (1)), (.integer (2))]), 91564110, 4118095950),
  ((.tuple #[(.atom "a"), (.tuple #[(.atom "b"), (.atom "c")]), (.cons (.integer (1)) (.cons (.integer (2)) .nil))]), 93309890, 1569704898),
  ((.map []), 39679005, 844985373),
  ((.map [((.atom "a"), (.integer (1)))]), 59617982, 1401795262),
  ((.map [((.atom "b"), (.integer (2))), ((.atom "a"), (.integer (1)))]), 103634663, 1982682855),
  ((.map [((.integer (1)), (.atom "a")), ((.cons (.atom "x") .nil), (.tuple #[(.atom "y")]))]), 87590499, 2637727331),
  ((.map [((.map []), (.map [((.atom "a"), .nil)]))]), 24740751, 3111748495),
  ((.map [((.integer (18)), (.integer (18))), ((.integer (4)), (.integer (4))), ((.integer (34)), (.integer (34))), ((.integer (12)), (.integer (12))), ((.integer (19)), (.integer (19))), ((.integer (29)), (.integer (29))), ((.integer (13)), (.integer (13))), ((.integer (2)), (.integer (2))), ((.integer (7)), (.integer (7))), ((.integer (38)), (.integer (38))), ((.integer (31)), (.integer (31))), ((.integer (8)), (.integer (8))), ((.integer (10)), (.integer (10))), ((.integer (23)), (.integer (23))), ((.integer (9)), (.integer (9))), ((.integer (15)), (.integer (15))), ((.integer (35)), (.integer (35))), ((.integer (36)), (.integer (36))), ((.integer (32)), (.integer (32))), ((.integer (1)), (.integer (1))), ((.integer (25)), (.integer (25))), ((.integer (28)), (.integer (28))), ((.integer (20)), (.integer (20))), ((.integer (6)), (.integer (6))), ((.integer (11)), (.integer (11))), ((.integer (17)), (.integer (17))), ((.integer (24)), (.integer (24))), ((.integer (37)), (.integer (37))), ((.integer (40)), (.integer (40))), ((.integer (14)), (.integer (14))), ((.integer (33)), (.integer (33))), ((.integer (3)), (.integer (3))), ((.integer (16)), (.integer (16))), ((.integer (30)), (.integer (30))), ((.integer (21)), (.integer (21))), ((.integer (5)), (.integer (5))), ((.integer (27)), (.integer (27))), ((.integer (26)), (.integer (26))), ((.integer (22)), (.integer (22))), ((.integer (39)), (.integer (39)))]), 55048502, 2202532150)]

#guard cases.all fun (term, short, full) =>
  match Erlang.erlang.«phash2/1» term, Erlang.erlang.«phash2/2» term (.integer (2 ^ 32)) with
  | .ok (.integer short'), .ok (.integer full') => short' == short && full' == full
  | _, _ => false

private meta def result : Except Exception Term → Option Int
  | .ok (.integer value) => some value
  | .error (.error (.atom "badarg")) => some (-1)
  | _ => none

-- Shadowed bindings are not hashed.
#guard result (Erlang.erlang.«phash2/1» (.map [(.atom "a", .integer 1), (.atom "a", .integer 2)])) ==
  result (Erlang.erlang.«phash2/1» (.map [(.atom "a", .integer 1)]))

/-- Exactly equal maps hash the same, whatever their shadowed bindings. -/
theorem shadowed_bindings_hash (k v w : Term) :
    Erlang.erlang.«phash2/1» (.map [(k, v), (k, w)]) = Erlang.erlang.«phash2/1» (.map [(k, v)]) := by
  apply Erlang.erlang.phash2_congr
  apply Term.map_exactCompare_eq_of_lookup
  intro q
  by_cases same : Term.exactCompare q k = .eq <;> simp [same]

/-- Closures hash the same when their captures are exactly equal. -/
theorem capture_hash (k v w : Term) :
    Erlang.erlang.«phash2/1» (.function "m" "f" 0 #[.map [(k, v), (k, w)]]) =
      Erlang.erlang.«phash2/1» (.function "m" "f" 0 #[.map [(k, v)]]) := by
  apply Erlang.erlang.phash2_congr
  have := Term.map_exactCompare_eq_of_lookup [(k, v), (k, w)] [(k, v)] fun q => by
    by_cases same : Term.exactCompare q k = .eq <;> simp [same]
  rw [Term.exactCompare_eq_step]
  simp [Term.Compare.compareStep, List.compareLex_cons_cons, List.compareLex_nil_nil, this]

#guard result (Erlang.erlang.«phash2/2» (.atom "a") (.integer 7)) == some 6
#guard result (Erlang.erlang.«phash2/2» (.atom "a") (.integer 0)) == some (-1)
#guard result (Erlang.erlang.«phash2/2» (.atom "a") (.integer (2 ^ 32 + 1))) == some (-1)

end LynxTest.Modules.Hashing

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Modules.Hashing

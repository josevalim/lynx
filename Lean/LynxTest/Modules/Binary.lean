module

import Lynx.Modules.Erlang.binary
meta import Lynx.Modules.Erlang.binary
meta import LynxTest.ProofAudit

namespace LynxTest.Modules.Binary
open Lynx

private meta def bin (text : String) : Term :=
  .bitstring text.toUTF8 0 (Term.Bitstring.valid_aligned _)

private meta def bins (texts : List String) : Term := Term.list (texts.map bin)

private meta def badarg : Except Exception Term := .error (.error (.atom "badarg"))

private meta def global : Term := Term.list [.atom "global"]

private meta def scope (start length : Int) : Term :=
  .tuple #[.atom "scope", .tuple #[.integer start, .integer length]]

private meta def same (left right : Except Exception Term) : Bool :=
  match left, right with
  | .ok a, .ok b => Term.exactCompare a b == .eq
  | .error (.error a), .error (.error b) => Term.exactCompare a b == .eq
  | _, _ => false

-- Expected values come from Erlang/OTP 29.1.2.
private meta def splitCases : List ((Term × Term × Term) × Except Exception Term) := [
  ((bin "a&b&c", bin "&", .nil), .ok (bins ["a", "b&c"])),
  ((bin "a&b&c", bin "&", global), .ok (bins ["a", "b", "c"])),
  ((bin "&a&&b&", bin "&", global), .ok (bins ["", "a", "", "b", ""])),
  ((bin "&a&&b&", bin "&", Term.list [.atom "global", .atom "trim"]), .ok (bins ["", "a", "", "b"])),
  ((bin "&a&&b&", bin "&", Term.list [.atom "global", .atom "trim_all"]), .ok (bins ["a", "b"])),
  ((bin "abc", bin "&", global), .ok (bins ["abc"])),
  ((bin "", bin "&", global), .ok (bins [""])),
  ((bin "", bin "&", Term.list [.atom "global", .atom "trim"]), .ok .nil),
  ((bin "a,b,c", bin ",", Term.list [scope 2 3]), .ok (bins ["a,b", "c"])),
  ((bin "a,b,c", bin ",", Term.list [scope 2 3, .atom "global"]), .ok (bins ["a,b", "c"])),
  ((bin "a,b,c", bin ",", Term.list [scope 4 (-3), .atom "global"]), .ok (bins ["a", "b", "c"])),
  ((bin "abcab", bins ["a", "ab"], global), .ok (bins ["", "c", ""])),
  ((bin "abc", bin "", .nil), badarg),
  ((bin "abc", .nil, .nil), badarg),
  ((bin "abc", bin "b", Term.list [scope 2 5]), badarg),
  ((bin "abc", bin "b", Term.list [.atom "bad"]), badarg)]

#guard splitCases.all fun ((subject, pattern, options), expected) =>
  same (Erlang.binary.«split/3» subject pattern options) expected

#guard same (Erlang.binary.«split/2» (bin "k=v=w") (bin "=")) (.ok (bins ["k", "v=w"]))

private meta def matchCases : List ((Term × Term × Term) × Except Exception Term) := [
  ((bin "a[b]", bin "[", .nil), .ok (.tuple #[.integer 1, .integer 1])),
  ((bin "ab", bin "[", .nil), .ok (.atom "nomatch")),
  ((bin "abcab", bins ["a", "ab"], .nil), .ok (.tuple #[.integer 0, .integer 2])),
  ((bin "abcab", bin "ab", Term.list [scope 1 4]), .ok (.tuple #[.integer 3, .integer 2])),
  ((bin "abcab", bin "ab", Term.list [scope 1 3]), .ok (.atom "nomatch"))]

#guard matchCases.all fun ((subject, pattern, options), expected) =>
  same (Erlang.binary.«match/3» subject pattern options) expected

#guard same (Erlang.binary.«last/1» (bin "ab]")) (.ok (.integer 93))
#guard same (Erlang.binary.«last/1» (bin "")) badarg

end LynxTest.Modules.Binary

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Modules.Erlang.binary
  LynxTest.ProofAudit.checkModule `LynxTest.Modules.Binary

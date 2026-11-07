module

public import Lynx.Concurrent

/-! Readable reports of the runs `Lynx.Concurrent.counterexample` finds.

Terms are shown in Erlang syntax. PIDs and references have no Erlang spelling
in the model, so a PID shows its path in the process tree, starting at `<0>`
for the run's first process, and a reference shows the PID that allocated it
followed by its allocation count. -/

public section

namespace Lynx.Concurrent

open Lynx

private def path (numbers : List Nat) : String :=
  ".".intercalate ("0" :: numbers.map toString)

private def showPid (pid : PID) : String := s!"<{path pid}>"

private def showReference (reference : List Nat) : String := s!"#Ref<{path reference}>"

private def isAtomStart (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

private def isAtomRest (c : Char) : Bool := c.isAlphanum || c == '_' || c == '@'

private def reserved : List String :=
  ["after", "and", "andalso", "band", "begin", "bnot", "bor", "bsl", "bsr", "bxor",
   "case", "catch", "cond", "div", "else", "end", "fun", "if", "let", "maybe", "not",
   "of", "or", "orelse", "receive", "rem", "try", "when", "xor"]

private def showAtom (name : String) : String :=
  match name.toList with
  | first :: rest =>
      if isAtomStart first && rest.all isAtomRest && !reserved.contains name then name
      else "'" ++ String.join (name.toList.map fun c =>
        if c == '\'' || c == '\\' then s!"\\{c}" else c.toString) ++ "'"
  | [] => "''"

private def showFloat (value : Term.FiniteFloat) : String :=
  toString (Float.ofBits (UInt64.ofNat
    ((if value.negative then 2 ^ 63 else 0) +
      value.exponent.val * 2 ^ 52 + value.fraction.val)))

/-- A bitstring as a quoted string when its bytes are printable ASCII. -/
private def showBitstring (bytes : ByteArray) (lastBits : Fin 8) : String :=
  let values := bytes.toList.map (·.toNat)
  let printable := values.all fun byte => 32 ≤ byte && byte < 127 && byte != 34 && byte != 92
  if lastBits.val == 0 && printable && !values.isEmpty then
    "<<\"" ++ String.ofList (values.map Char.ofNat) ++ "\">>"
  else
    let segments := if lastBits.val == 0 then values.map toString else
      (values.dropLast.map toString) ++
        [s!"{values.getLast! / 2 ^ (8 - lastBits.val)}:{lastBits.val}"]
    "<<" ++ ", ".intercalate segments ++ ">>"

/-- A term in Erlang syntax. -/
private partial def showTerm : Term → String
  | .integer value => toString value
  | .float value => showFloat value
  | .atom name => showAtom name
  | .reference reference => showReference reference
  | .function id arity _ => s!"#Fun<{id}/{arity}>"
  | .pid pid => showPid pid
  | .tuple elements => "{" ++ ", ".intercalate (elements.toList.map showTerm) ++ "}"
  | .map pairs =>
      "#{" ++ ", ".intercalate (pairs.map fun (key, value) => s!"{showTerm key} => {showTerm value}") ++ "}"
  | .nil => "[]"
  | .cons head tail =>
      let rec elements : Term → List String × Option String
        | .nil => ([], none)
        | .cons head tail =>
            let (rest, improper) := elements tail
            (showTerm head :: rest, improper)
        | other => ([], some (showTerm other))
      let (rest, improper) := elements tail
      let shown := ", ".intercalate (showTerm head :: rest)
      match improper with
      | none => s!"[{shown}]"
      | some tail => s!"[{shown} | {tail}]"
  | .bitstring bytes lastBits _ => showBitstring bytes lastBits

private def showRequest (processId : PID) (reply : Term) : Request → String
  | .monitor target alias =>
      let kind := if alias then "monitors with an alias" else "monitors"
      s!"{showPid processId} {kind} {showPid target}, getting {showTerm reply}"
  | .demonitor reference flush =>
      let how := if flush then "demonitors and flushes" else "demonitors"
      let found := match reply with | .atom "true" => "active" | _ => "inactive"
      s!"{showPid processId} {how} {showReference reference}, which was {found}"
  | .link target => s!"{showPid processId} links to {showPid target}, getting {showTerm reply}"
  | .unlink target => s!"{showPid processId} unlinks from {showPid target}"
  | .exit target reason =>
      s!"{showPid processId} sends exit signal {showTerm reason} to {showPid target}"
  | .trapExit enabled => s!"{showPid processId} sets trap_exit to {enabled}"
  | .alive target =>
      s!"{showPid processId} checks whether {showPid target} is alive: {showTerm reply}"
  | .sendAlias alias message =>
      s!"{showPid processId} sends {showTerm message} to alias {showReference alias}"

/-- One step of a run, or `none` for environment accesses, which other
processes cannot observe. -/
private def showEvent : Event → Option String
  | .internal _ => none
  | .spawn parent child => some s!"{showPid parent} spawns {showPid child}"
  | .send sender receiver message =>
      some s!"{showPid sender} sends {showTerm message} to {showPid receiver}"
  | .receive receiver message => some s!"{showPid receiver} receives {showTerm message}"
  | .timeout processId => some s!"{showPid processId} times out waiting for a message"
  | .exit processId reason => some s!"{showPid processId} exits with {showTerm reason}"
  | .request processId query reply => some (showRequest processId reply query)

private def showException : Exception → String
  | .error reason => s!"raises error {showTerm reason}"
  | .throw value => s!"throws {showTerm value}"
  | .exit reason => s!"exits with {showTerm reason}"
  | .exhausted => "does not return"

private def showOutcome : Outcome Term → String
  | .ok value => s!"returns {showTerm value}"
  | .error exception => showException exception
  | .deadlock => "deadlocks"

/-- Describe the first run that `check` rejects, if any, with one line per
observable step. -/
def report (accept : Outcome Term → Bool) (depth : Nat) (config : Config Term) : Option String :=
  (counterexample accept depth config).map fun (events, failure) =>
    let header := match failure with
      | .rejected outcome => s!"Found a schedule where the program {showOutcome outcome}:"
      | .unfinished => s!"Found a schedule that takes more than {depth} steps; increase the depth:"
    let steps := events.filterMap showEvent
    let numbered := (List.range steps.length).zip steps |>.map fun (index, step) =>
      s!"  {index + 1}. {step}"
    "\n".intercalate (header :: numbered)

end Lynx.Concurrent

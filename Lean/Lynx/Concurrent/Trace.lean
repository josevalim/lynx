module

public import Lynx.Concurrent.Reduction

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
  | .function module name arity _ => s!"#Fun<{module}.{name}.{arity}>"
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

private def showReply (reply : Option Term) : String :=
  match reply with
  | some reply => showTerm reply
  | none => "nothing yet"

private def showRequest (processId : PID) (reply : Option Term) : Request → String
  | .monitor target alias =>
      let kind := if alias then "monitors with an alias" else "monitors"
      s!"{showPid processId} {kind} {showPid target}, getting {showReply reply}"
  | .demonitor reference flush =>
      let how := if flush then "demonitors and flushes" else "demonitors"
      match reply with
      | some (.atom "true") => s!"{showPid processId} {how} {showReference reference}, which was active"
      | _ => s!"{showPid processId} {how} {showReference reference}, which was inactive"
  | .link target => s!"{showPid processId} links to {showPid target}, getting {showReply reply}"
  | .unlink target => s!"{showPid processId} unlinks from {showPid target}"
  | .exit target reason _ =>
      s!"{showPid processId} sends exit signal {showTerm reason} to {showPid target}"
  | .trapExit enabled => s!"{showPid processId} sets trap_exit to {enabled}"
  | .alive target =>
      match reply with
      | some reply => s!"{showPid processId} checks whether {showPid target} is alive: {showTerm reply}"
      | none => s!"{showPid processId} asks whether {showPid target} is alive"
  | .processInfo target =>
      match reply with
      | some reply => s!"{showPid processId} reads whether {showPid target} is alive: {showTerm reply}"
      | none => s!"{showPid processId} reads whether {showPid target} is alive"
  | .sendAlias alias message =>
      s!"{showPid processId} sends {showTerm message} to alias {showReference alias}"
  | .startTimer destination message _ =>
      s!"{showPid processId} starts timer {showReply reply} sending {showTerm message} to {showPid destination}"
  | .cancelTimer reference =>
      s!"{showPid processId} cancels timer {showReference reference}, getting {showReply reply}"
  | .persistentGet key =>
      match reply with
      | some (.cons value .nil) => s!"{showPid processId} reads persistent term {showTerm key}: {showTerm value}"
      | _ => s!"{showPid processId} finds no persistent term {showTerm key}"
  | .persistentPut key value _ =>
      match reply with
      | some (.atom "badarg") =>
          s!"{showPid processId} finds persistent term {showTerm key} stored with another value"
      | some _ => s!"{showPid processId} finds persistent term {showTerm key} already {showTerm value}"
      | none => s!"{showPid processId} stages persistent term {showTerm key} as {showTerm value}"
  | .persistentErase key =>
      match reply with
      | some _ => s!"{showPid processId} finds no persistent term {showTerm key} to erase"
      | none => s!"{showPid processId} stages erasing persistent term {showTerm key}"
  | .persistentAwait => s!"{showPid processId} resumes after its persistent term update"

/-- A process handling a signal from its queue. -/
private def showHandle (receiver : PID) (entry : Entry) : String :=
  let receiver := showPid receiver
  let source := if entry.source == clock then "the timer service" else showPid entry.source
  match entry.signal with
  | .message message => s!"{receiver} takes {showTerm message} from {source} into its mailbox"
  | .aliasMessage alias message =>
      s!"{receiver} handles {showTerm message} from {source} through alias {showReference alias}"
  | .exit reason true _ => s!"{receiver} handles exit signal {showTerm reason} from linked {source}"
  | .exit reason false _ => s!"{receiver} handles exit signal {showTerm reason} from {source}"
  | .link => s!"{receiver} is linked by {source}"
  | .unlink _ => s!"{receiver} is unlinked by {source}"
  | .unlinkAck _ => s!"{receiver} gets the unlink acknowledgement from {source}"
  | .monitor reference => s!"{receiver} is monitored by {source} with {showReference reference}"
  | .down reference reason =>
      s!"{receiver} handles DOWN for {showReference reference} from {source} with {showTerm reason}"
  | .isAlive => s!"{receiver} answers {source} that it is alive"
  | .reply value => s!"{receiver} gets the answer {showTerm value} from {source}"
  | .flush => s!"{receiver} has handled the signals queued before"

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
  | .handle receiver entry => some (showHandle receiver entry)
  | .phase processId => some s!"{showPid processId}, which ended, signals its links, watchers or requesters"
  | .unpark processId => some s!"{showPid processId}'s monitor signal is sent"
  | .fire reference => some s!"timer {showReference reference} fires"
  | .commit owner => some s!"the persistent term update of {showPid owner} becomes visible"

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

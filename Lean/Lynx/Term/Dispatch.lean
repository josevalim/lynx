module

public import Lynx.Term.DataTypes

namespace Lynx.Result

/-- Continue with either the returned value or exception. Unlike `bind`, this
also catches exceptions raised by a dispatched implementation. -/
private def resume (computation : Result β)
    (next : Except Exception β → Result α) : Result α :=
  match computation with
  | .ok value => next (.ok value)
  | .error exception => next (.error exception)
  | .exhausted => .exhausted
  | .get continuation => .get fun env => resume (continuation env) next
  | .set env continuation => .set env (resume continuation next)
  | .spawn child continuation =>
      .spawn child fun result => resume (continuation result) next
  | Result.schedule child continuation => Result.schedule child fun pid => resume (continuation pid) next
  | .send pid message continuation => .send pid message (resume continuation next)
  | .receive select continuation => .receive select fun value => resume (continuation value) next
  | .apply function arguments continuation =>
      .apply function arguments fun result => resume (continuation result) next

private def expand (dispatch : Bool → Term → Array Term → Result Term) : Result α → Result α
  | .ok value => .ok value
  | .error exception => .error exception
  | .exhausted => .exhausted
  | .get next => .get fun env => expand dispatch (next env)
  | .set env next => .set env (expand dispatch next)
  | .spawn child next =>
      resume (dispatch true child #[]) fun result => expand dispatch (next result)
  | Result.schedule child next => .schedule (expand dispatch child) fun pid => expand dispatch (next pid)
  | .send pid message next => .send pid message (expand dispatch next)
  | .receive select next => .receive select fun value => expand dispatch (next value)
  | .apply function arguments next =>
      resume (dispatch false function arguments) fun result => expand dispatch (next result)

/-- Resolve dynamic calls against one immutable program table. The budget bounds
nested dispatch, including function-based spawning, not ordinary evaluation or
sequential calls. Recursive spawn chains therefore also consume the budget. Expansion preserves
state operations and scheduling boundaries for the process runner. -/
public def resolve (table : Term.FunTable) (depth : Nat) (computation : Result α) : Result α :=
  expand (fun spawn function arguments =>
    let invalid := if spawn then .error (.atom "badarg")
      else .error (.tuple #[.atom "badfun", function])
    match function with
    | .function id arity captures =>
      match table[id]? with
      | none => .error invalid
      | some implementation =>
        if arguments.size != arity then
          .error (if spawn then .error (.atom "badarg") else
            .error (.tuple #[.atom "badarity", .tuple #[function,
              arguments.toList.foldr Term.cons Term.nil]]))
        else
          match depth with
          | 0 => .exhausted
          | depth + 1 =>
            let body := resolve table depth (implementation captures arguments)
            if spawn then Result.schedule body (fun pid => .ok (.pid pid)) else body
    | _ => .error invalid) computation
termination_by depth

end Lynx.Result

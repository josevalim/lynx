module

public import Lynx
public import Erlang.functions

namespace Erlang.program

public def fun_table : Lynx.Term.FunTable :=
  #[Lynx.Term.FunEntry.pure fun captures args =>
      match captures, args with
      | #[cap1], #[arg1] =>
        Lynx.Result.toExcept (Erlang.functions.«$lynx_fun_0/2» cap1 arg1) (by simp)
      | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")),
    Lynx.Term.FunEntry.effectful fun captures args =>
      match captures, args with
      | #[cap1], #[arg1] => Erlang.functions.«$lynx_fun_1/2» cap1 arg1
      | _, _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg")),
    Lynx.Term.FunEntry.pure fun captures args =>
      match captures, args with
      | #[], #[] => Lynx.Result.toExcept Erlang.functions.«zero/0» (by simp)
      | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")),
    Lynx.Term.FunEntry.pure fun captures args =>
      match captures, args with
      | #[], #[arg1] => Lynx.Result.toExcept (Erlang.functions.«inc/1» arg1) (by simp)
      | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")),
    Lynx.Term.FunEntry.effectful fun captures args =>
      match captures, args with
      | #[], #[arg1] => Erlang.functions.«remember/1» arg1
      | _, _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg"))]

@[simp↓]
public theorem fun_table_apply_0_bind {α : Type} (depth : Nat) (cap1 : Lynx.Term) (arg1 : Lynx.Term)
    (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table depth
        (Lynx.Term.apply (Lynx.Term.function 0 1 #[cap1]) #[arg1] >>= next) =
      Lynx.Result.resolve fun_table depth (Erlang.functions.«$lynx_fun_0/2» cap1 arg1 >>= next) :=
  by
  rw [Lynx.Result.resolve_apply_pure fun_table depth 0 1 #[cap1] #[arg1]
      (fun captures args =>
        match captures, args with
        | #[cap1], #[arg1] =>
          Lynx.Result.toExcept (Erlang.functions.«$lynx_fun_0/2» cap1 arg1) (by simp)
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")))
      next (by rfl) (by rfl)]
  change
    Lynx.Result.resolve fun_table depth
        (Lynx.Result.ofExcept
            (Lynx.Result.toExcept (Erlang.functions.«$lynx_fun_0/2» cap1 arg1) (by simp)) >>=
          next) =
      _
  rw [Lynx.Result.ofExcept_toExcept (Erlang.functions.«$lynx_fun_0/2» cap1 arg1)]

@[simp↓]
public theorem fun_table_apply_0_bind_explicit {α : Type} (depth : Nat) (cap1 : Lynx.Term)
    (arg1 : Lynx.Term) (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table depth
        (Lynx.Result.bind (Lynx.Term.apply (Lynx.Term.function 0 1 #[cap1]) #[arg1]) next) =
      Lynx.Result.resolve fun_table depth
        (Lynx.Result.bind (Erlang.functions.«$lynx_fun_0/2» cap1 arg1) next) :=
  by exact fun_table_apply_0_bind depth cap1 arg1 next

@[simp]
public theorem fun_table_apply_0 (depth : Nat) (cap1 : Lynx.Term) (arg1 : Lynx.Term) :
    Lynx.Result.resolve fun_table depth (Lynx.Term.apply (Lynx.Term.function 0 1 #[cap1]) #[arg1]) =
      Erlang.functions.«$lynx_fun_0/2» cap1 arg1 :=
  by
  simpa only [(Lynx.Result.bind_ok),
    (Lynx.Result.resolve_of_isPure fun_table depth (Erlang.functions.«$lynx_fun_0/2» cap1 arg1)
        (by simp))] using
    fun_table_apply_0_bind depth cap1 arg1 (fun value => Lynx.Result.ok value)

@[simp↓]
public theorem fun_table_apply_1_bind {α : Type} (depth : Nat) (cap1 : Lynx.Term) (arg1 : Lynx.Term)
    (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table (depth + 1)
        (Lynx.Term.apply (Lynx.Term.function 1 1 #[cap1]) #[arg1] >>= next) =
      (Lynx.Result.resolve fun_table depth (Erlang.functions.«$lynx_fun_1/2» cap1 arg1) >>=
        fun value => Lynx.Result.resolve fun_table (depth + 1) (next value)) :=
  by
  rw [Lynx.Result.resolve_bind fun_table (depth + 1)
      (Lynx.Term.apply (Lynx.Term.function 1 1 #[cap1]) #[arg1]) next,
    Lynx.Result.resolve_apply_effectful fun_table depth 1 1 #[cap1] #[arg1]
      (fun captures args =>
        match captures, args with
        | #[cap1], #[arg1] => Erlang.functions.«$lynx_fun_1/2» cap1 arg1
        | _, _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg")))
      (by rfl) (by rfl)]
  rfl

@[simp↓]
public theorem fun_table_apply_1_bind_explicit {α : Type} (depth : Nat) (cap1 : Lynx.Term)
    (arg1 : Lynx.Term) (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table (depth + 1)
        (Lynx.Result.bind (Lynx.Term.apply (Lynx.Term.function 1 1 #[cap1]) #[arg1]) next) =
      Lynx.Result.bind
        (Lynx.Result.resolve fun_table depth (Erlang.functions.«$lynx_fun_1/2» cap1 arg1))
        (fun value => Lynx.Result.resolve fun_table (depth + 1) (next value)) :=
  by exact fun_table_apply_1_bind depth cap1 arg1 next

@[simp]
public theorem fun_table_apply_1 (depth : Nat) (cap1 : Lynx.Term) (arg1 : Lynx.Term) :
    Lynx.Result.resolve fun_table (depth + 1)
        (Lynx.Term.apply (Lynx.Term.function 1 1 #[cap1]) #[arg1]) =
      Lynx.Result.resolve fun_table depth (Erlang.functions.«$lynx_fun_1/2» cap1 arg1) :=
  by
  simpa only [(Lynx.Result.bind_ok), (Lynx.Result.resolve_of_isPure), (Lynx.Result.isPure_ok)] using
    fun_table_apply_1_bind depth cap1 arg1 (fun value => Lynx.Result.ok value)

@[simp↓]
public theorem fun_table_apply_2_bind {α : Type} (depth : Nat) (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table depth
        (Lynx.Term.apply (Lynx.Term.function 2 0 #[]) #[] >>= next) =
      Lynx.Result.resolve fun_table depth (Erlang.functions.«zero/0» >>= next) :=
  by
  rw [Lynx.Result.resolve_apply_pure fun_table depth 2 0 #[] #[]
      (fun captures args =>
        match captures, args with
        | #[], #[] => Lynx.Result.toExcept Erlang.functions.«zero/0» (by simp)
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")))
      next (by rfl) (by rfl)]
  change
    Lynx.Result.resolve fun_table depth
        (Lynx.Result.ofExcept (Lynx.Result.toExcept Erlang.functions.«zero/0» (by simp)) >>= next) =
      _
  rw [Lynx.Result.ofExcept_toExcept Erlang.functions.«zero/0»]

@[simp↓]
public theorem fun_table_apply_2_bind_explicit {α : Type} (depth : Nat)
    (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table depth
        (Lynx.Result.bind (Lynx.Term.apply (Lynx.Term.function 2 0 #[]) #[]) next) =
      Lynx.Result.resolve fun_table depth (Lynx.Result.bind Erlang.functions.«zero/0» next) :=
  by exact fun_table_apply_2_bind depth next

@[simp]
public theorem fun_table_apply_2 (depth : Nat) :
    Lynx.Result.resolve fun_table depth (Lynx.Term.apply (Lynx.Term.function 2 0 #[]) #[]) =
      Erlang.functions.«zero/0» :=
  by
  simpa only [(Lynx.Result.bind_ok),
    (Lynx.Result.resolve_of_isPure fun_table depth Erlang.functions.«zero/0» (by simp))] using
    fun_table_apply_2_bind depth (fun value => Lynx.Result.ok value)

@[simp↓]
public theorem fun_table_apply_3_bind {α : Type} (depth : Nat) (arg1 : Lynx.Term)
    (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table depth
        (Lynx.Term.apply (Lynx.Term.function 3 1 #[]) #[arg1] >>= next) =
      Lynx.Result.resolve fun_table depth (Erlang.functions.«inc/1» arg1 >>= next) :=
  by
  rw [Lynx.Result.resolve_apply_pure fun_table depth 3 1 #[] #[arg1]
      (fun captures args =>
        match captures, args with
        | #[], #[arg1] => Lynx.Result.toExcept (Erlang.functions.«inc/1» arg1) (by simp)
        | _, _ => Except.error (Lynx.Exception.error (Lynx.Term.atom "badarg")))
      next (by rfl) (by rfl)]
  change
    Lynx.Result.resolve fun_table depth
        (Lynx.Result.ofExcept (Lynx.Result.toExcept (Erlang.functions.«inc/1» arg1) (by simp)) >>=
          next) =
      _
  rw [Lynx.Result.ofExcept_toExcept (Erlang.functions.«inc/1» arg1)]

@[simp↓]
public theorem fun_table_apply_3_bind_explicit {α : Type} (depth : Nat) (arg1 : Lynx.Term)
    (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table depth
        (Lynx.Result.bind (Lynx.Term.apply (Lynx.Term.function 3 1 #[]) #[arg1]) next) =
      Lynx.Result.resolve fun_table depth (Lynx.Result.bind (Erlang.functions.«inc/1» arg1) next) :=
  by exact fun_table_apply_3_bind depth arg1 next

@[simp]
public theorem fun_table_apply_3 (depth : Nat) (arg1 : Lynx.Term) :
    Lynx.Result.resolve fun_table depth (Lynx.Term.apply (Lynx.Term.function 3 1 #[]) #[arg1]) =
      Erlang.functions.«inc/1» arg1 :=
  by
  simpa only [(Lynx.Result.bind_ok),
    (Lynx.Result.resolve_of_isPure fun_table depth (Erlang.functions.«inc/1» arg1) (by simp))] using
    fun_table_apply_3_bind depth arg1 (fun value => Lynx.Result.ok value)

@[simp↓]
public theorem fun_table_apply_4_bind {α : Type} (depth : Nat) (arg1 : Lynx.Term)
    (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table (depth + 1)
        (Lynx.Term.apply (Lynx.Term.function 4 1 #[]) #[arg1] >>= next) =
      (Lynx.Result.resolve fun_table depth (Erlang.functions.«remember/1» arg1) >>= fun value =>
        Lynx.Result.resolve fun_table (depth + 1) (next value)) :=
  by
  rw [Lynx.Result.resolve_bind fun_table (depth + 1)
      (Lynx.Term.apply (Lynx.Term.function 4 1 #[]) #[arg1]) next,
    Lynx.Result.resolve_apply_effectful fun_table depth 4 1 #[] #[arg1]
      (fun captures args =>
        match captures, args with
        | #[], #[arg1] => Erlang.functions.«remember/1» arg1
        | _, _ => Lynx.Result.error (Lynx.Exception.error (Lynx.Term.atom "badarg")))
      (by rfl) (by rfl)]
  rfl

@[simp↓]
public theorem fun_table_apply_4_bind_explicit {α : Type} (depth : Nat) (arg1 : Lynx.Term)
    (next : Lynx.Term → Lynx.Result α) :
    Lynx.Result.resolve fun_table (depth + 1)
        (Lynx.Result.bind (Lynx.Term.apply (Lynx.Term.function 4 1 #[]) #[arg1]) next) =
      Lynx.Result.bind (Lynx.Result.resolve fun_table depth (Erlang.functions.«remember/1» arg1))
        (fun value => Lynx.Result.resolve fun_table (depth + 1) (next value)) :=
  by exact fun_table_apply_4_bind depth arg1 next

@[simp]
public theorem fun_table_apply_4 (depth : Nat) (arg1 : Lynx.Term) :
    Lynx.Result.resolve fun_table (depth + 1)
        (Lynx.Term.apply (Lynx.Term.function 4 1 #[]) #[arg1]) =
      Lynx.Result.resolve fun_table depth (Erlang.functions.«remember/1» arg1) :=
  by
  simpa only [(Lynx.Result.bind_ok), (Lynx.Result.resolve_of_isPure), (Lynx.Result.isPure_ok)] using
    fun_table_apply_4_bind depth arg1 (fun value => Lynx.Result.ok value)

end Erlang.program

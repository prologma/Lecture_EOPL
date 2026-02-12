Set Warnings "-masking-absolute-name".
Unset Guard Checking.

From Coq Require Import String ZArith Bool.
Require Import Expr Env.

Module Interp.

Module Import ExprNS := Expr.
Module Import EnvNS := Env.

Open Scope string_scope.
Open Scope Z_scope.

Local Unset Guard Checking.

Definition bind_option {A B : Type} (oa : option A) (k : A -> option B) : option B :=
  match oa with
  | Some a => k a
  | None => None
  end.

Fixpoint value_of (exp : Exp) (env : Env) {struct exp} : option ExpVal :=
  match exp with
  | Const_Exp n => Some (Num_Val n)
  | Var_Exp var => apply_env env var
  | Diff_Exp e1 e2 =>
      bind_option (value_of e1 env) (fun v1 =>
      bind_option (value_of e2 env) (fun v2 =>
        match v1, v2 with
        | Num_Val n1, Num_Val n2 => Some (Num_Val (n1 - n2))
        | _, _ => None
        end))
  | IsZero_Exp e =>
      bind_option (value_of e env) (fun v =>
        match v with
        | Num_Val n => Some (Bool_Val (Z.eqb n 0))
        | _ => None
        end)
  | If_Exp cond_exp then_exp else_exp =>
      bind_option (value_of cond_exp env) (fun v =>
        match v with
        | Bool_Val true => value_of then_exp env
        | Bool_Val false => value_of else_exp env
        | _ => None
        end)
  | Let_Exp var exp1 body =>
      bind_option (value_of exp1 env) (fun val1 =>
        value_of body (extend_env var val1 env))
  | Letrec_Exp _ proc_name bound_var _ proc_body letrec_body =>
      value_of letrec_body (extend_env_rec proc_name bound_var proc_body env)
  | Proc_Exp var _ body =>
      Some (Proc_Val (procedure var body env))
  | Call_Exp rator rand =>
      bind_option (value_of rator env) (fun proc_val =>
      bind_option (value_of rand env) (fun arg_val =>
        match proc_val with
        | Proc_Val p => apply_procedure p arg_val
        | _ => None
        end))
  end
with apply_procedure (proc : Proc) (arg : ExpVal) {struct proc} : option ExpVal :=
  match proc with
  | Procedure var body saved_env =>
      value_of body (extend_env var arg saved_env)
  end.

Definition initEnv : Env :=
  extend_env "i" (Num_Val 1)
    (extend_env "v" (Num_Val 5)
      (extend_env "x" (Num_Val 10) empty_env)).

Definition value_of_program (exp : Exp) : option ExpVal :=
  value_of exp initEnv.

End Interp.

Export Interp.

Set Guard Checking.
Set Warnings "+masking-absolute-name".

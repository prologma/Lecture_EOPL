Set Warnings "-masking-absolute-name".

From Coq Require Import String.
Require Import Expr TyEnv Env Interp TypeCheck.

Module TypeSound.

Module Import ExprNS := Expr.
Module Import TyEnvNS := TyEnv.
Module Import EnvNS := Env.
Module Import InterpNS := Interp.
Module Import TypeCheckNS := TypeCheck.

(* Typing relation for environments and expressed values. *)
Inductive env_has_type : Env -> TyEnv -> Prop :=
| EnvEmptyHasType :
    env_has_type Empty_env Empty_tyenv
| EnvExtendHasType :
    forall env tenv var val ty,
      value_has_type val ty ->
      env_has_type env tenv ->
      env_has_type (Extend_env var val env) (Extend_tyenv var ty tenv)
| EnvExtendRecHasType :
    forall env tenv proc_name bound_var proc_body argTy resultTy,
      env_has_type env tenv ->
      type_of proc_body
        (extend_tyenv bound_var argTy
          (extend_tyenv proc_name (TyFun argTy resultTy) tenv)) = inr resultTy ->
      env_has_type (Extend_env_rec proc_name bound_var proc_body env)
                   (Extend_tyenv proc_name (TyFun argTy resultTy) tenv)
with value_has_type : ExpVal -> Ty -> Prop :=
| ValueHasTypeNum :
    forall n,
      value_has_type (Num_Val n) TyInt
| ValueHasTypeBool :
    forall b,
      value_has_type (Bool_Val b) TyBool
| ValueHasTypeProc :
    forall param body saved_env tenv argTy resultTy,
      env_has_type saved_env tenv ->
      type_of body (extend_tyenv param argTy tenv) = inr resultTy ->
      value_has_type (Proc_Val (Procedure param body saved_env))
                      (TyFun argTy resultTy).

Scheme env_has_type_mut := Induction for env_has_type Sort Prop
with value_has_type_mut := Induction for value_has_type Sort Prop.

Combined Scheme env_value_has_type_mut_ind from env_has_type_mut, value_has_type_mut.

Lemma equal_ty_refl : forall ty, equal_ty ty ty = true.
Proof.
  induction ty; simpl;
    try rewrite IHty1; try rewrite IHty2; reflexivity.
Qed.

Lemma equal_ty_eq : forall ty1 ty2, equal_ty ty1 ty2 = true -> ty1 = ty2.
Proof.
  induction ty1; destruct ty2; simpl; intros H;
    try discriminate.
  - reflexivity.
  - reflexivity.
  - apply andb_prop in H as [H1 H2].
    specialize (IHty1_1 ty2_1 H1).
    specialize (IHty1_2 ty2_2 H2).
    subst; reflexivity.
Qed.

Lemma env_has_type_extend_rec_preserves :
  forall env tenv proc_name bound_var proc_body argTy resultTy,
    env_has_type env tenv ->
    type_of proc_body
      (extend_tyenv bound_var argTy
        (extend_tyenv proc_name (TyFun argTy resultTy) tenv)) = inr resultTy ->
    env_has_type (extend_env_rec proc_name bound_var proc_body env)
                 (extend_tyenv proc_name (TyFun argTy resultTy) tenv).
Proof.
  intros env tenv proc_name bound_var proc_body argTy resultTy Henv Hty.
  now constructor.
Qed.

Lemma env_lookup_sound :
  forall env tenv, env_has_type env tenv ->
  forall var ty val,
    apply_tyenv tenv var = inr ty ->
    apply_env env var = Some val ->
    value_has_type val ty.
Proof.
  induction 1; intros var ty val Htyenv Happ;
    simpl in *.
  - discriminate.
  - repeat (rewrite String.eqb_sym in *).
    destruct (String.eqb var var0) eqn:Heq.
    + apply String.eqb_eq in Heq; subst.
      inversion Htyenv; inversion Happ; subst; assumption.
    + apply IHenv_has_type; assumption.
  - repeat (rewrite String.eqb_sym in *).
    destruct (String.eqb var proc_name) eqn:Heq.
    + apply String.eqb_eq in Heq; subst.
      inversion Happ; subst.
      constructor;
        [ constructor; assumption
        | assumption ].
    + apply IHenv_has_type; assumption.
Qed.

Lemma env_extend_has_type :
  forall env tenv var val ty,
    env_has_type env tenv ->
    value_has_type val ty ->
    env_has_type (extend_env var val env) (extend_tyenv var ty tenv).
Proof.
  intros; now constructor.
Qed.

Lemma value_has_type_proc_intro :
  forall param body saved_env tenv argTy resultTy,
    env_has_type saved_env tenv ->
    type_of body (extend_tyenv param argTy tenv) = inr resultTy ->
    value_has_type (Proc_Val (procedure param body saved_env))
                   (TyFun argTy resultTy).
Proof.
  intros; constructor; assumption.
Qed.

Lemma type_of_program_env :
  env_has_type initEnv empty_tyenv.
Proof.
  unfold initEnv.
  repeat constructor; constructor.
Qed.

Lemma bind_option_some :
  forall (A B : Type) (oa : option A) (k : A -> option B) b,
    bind_option oa k = Some b ->
    exists a, oa = Some a /\n+              k a = Some b.
Proof.
  intros A B [a|] k b H;
    simpl in H;
    try discriminate.
  eauto.
Qed.

Lemma bind_inr :
  forall (r : TyResult) (k : Ty -> TyResult) ty,
    bind r k = inr ty ->
    exists v, r = inr v /
              k v = inr ty.
Proof.
  intros [err|v] k ty H;
    simpl in H.
  - discriminate.
  - eauto.
Qed.

Lemma type_sound_env :
  forall exp env tenv ty val,
    env_has_type env tenv ->
    type_of exp tenv = inr ty ->
    value_of exp env = Some val ->
    value_has_type val ty
with type_sound_proc :
  forall proc arg val argTy resultTy,
    value_has_type (Proc_Val proc) (TyFun argTy resultTy) ->
    value_has_type arg argTy ->
    apply_procedure proc arg = Some val ->
    value_has_type val resultTy.
Proof.
  - intros exp env tenv ty val Henv Hty Hval.
    revert env tenv ty val Henv Hty Hval.
    induction exp; intros env tenv ty val Henv Hty Hval; simpl in *.
    + inversion Hty; inversion Hval; constructor.
    + (* Diff_Exp *)
      apply bind_inr in Hty as [ty1 [Hty1 Hty]].
      apply bind_inr in Hty as [ty2 [Hty2 Hty]].
      destruct ty1; try (simpl in Hty; discriminate).
      destruct ty2; try (simpl in Hty; discriminate).
      inversion Hty; subst ty.
      apply bind_option_some in Hval as [v1 [Hv1 Hval]].
      apply bind_option_some in Hval as [v2 [Hv2 Hval]].
      destruct v1; try discriminate.
      destruct v2; try discriminate.
      inversion Hval; subst val.
      pose proof (IHexp1 env tenv TyInt (Num_Val n) Henv Hty1 Hv1) as Hv1_ty.
      pose proof (IHexp2 env tenv TyInt (Num_Val n0) Henv Hty2 Hv2) as Hv2_ty.
      inversion Hv1_ty; subst.
      inversion Hv2_ty; subst.
      constructor.
    + (* IsZero_Exp *)
      apply bind_option_some in Hval as [v [Hv Hval]].
      destruct v; try discriminate.
      inversion Hval; subst.
      apply bind_inr in Hty as [ty1 [Hty1 Hty]].
      destruct ty1; try (simpl in Hty; discriminate).
      inversion Hty; subst ty.
      pose proof (IHexp env tenv TyInt (Num_Val n) Henv Hty1 Hv) as Hv_ty.
      inversion Hv_ty; subst.
      constructor.
    + (* If_Exp *)
      apply bind_inr in Hty as [condTy [HcondTy Hty]].
      destruct condTy; try (simpl in Hty; discriminate).
      apply bind_inr in Hty as [thenTy [HthenTy Hty]].
      destruct (equal_ty thenTy (let '(If_Exp _ _ _) := If_Exp exp1 exp2 exp3 in exp3) ); simpl in Hty.
Abort.

Theorem type_sound :
  forall (exp : Exp) (ty : Ty) (val : ExpVal),
    type_of_program exp = inr ty ->
    value_of_program exp = Some val ->
    value_has_type val ty.
Proof.
  intros exp ty val Htyped Heval.
  unfold type_of_program in Htyped.
  unfold value_of_program in Heval.
  eapply type_sound_env; eauto.
  apply type_of_program_env.
Qed.

End TypeSound.

Export TypeSound.

Set Warnings "+masking-absolute-name".

(* working title C++ *)

Require Import String.
Require Import Coq.Lists.List.
Import ListNotations.

(* Syntax *)
Inductive type : Type :=
  | T_Int : type              (* int *)
  | T_Bool : type             (* bool *)
  | T_Class : string -> type  (* C *)
  | T_Ptr : type -> type.     (* T* *)

Inductive expr : Type :=
  | Ex_Var : string -> expr                                (* x *)
  | Ex_Field_Access : expr -> string -> expr               (* e.f *)
  | Ex_Method_Call : expr -> string -> list expr -> expr   (* e.m(e_bar) *)
  | Ex_New : string -> list expr -> expr                   (* new C(e_bar) *)
  | Ex_Cast : type -> expr -> expr                         (* (C)e *)
  | Ex_Deref : expr -> expr                                (* *e *)
  | Ex_Ref : expr -> expr                                  (* &e *)
  | Ex_Seq : expr -> expr -> expr                          (* e;e *)
  | Ex_Asgn : string -> expr -> expr.                      (* T x := e *)

Inductive method : Type :=
  | Method : string -> list (type * string) -> expr -> method.

Inductive class : Type :=
  | Class : string -> string -> list (type * string) -> list method -> class.

(* Evaluation *)
Inductive value : Type :=
  | V_Int : nat -> value
  | V_Bool : bool -> value
  | V_Object : class -> value
  | V_Mem_Loc : nat -> value.

Definition env := string -> option nat.
Definition st := nat -> option value.
Definition empty_env : env := fun _ => None.
Definition empty_st : st := fun _ => None.

Definition update_env (e : env) (x : string) (n : nat) : env :=
  fun f => if String.eqb x f then Some n else e f.

Definition update_st (s : st) (n : nat) (v : value) : st :=
  fun f => if Nat.eqb n f then Some v else s f.

Definition next_loc (n: nat) : nat := S n.

Inductive eval : expr -> nat -> st * env -> nat -> st * env -> Prop :=
  | Ev_Asgn : forall x e n1 n2 s1 s2 env1 env2 v,
      eval e n1 (s1, env1) n2 (s2, env2) ->
      let s3 := update_st s2 n2 v in
      let env3 := update_env env2 x n2 in
      eval (Ex_Asgn x e) n1 (s1, env1) (next_loc n2) (s3, env3)
  | Ev_Var : forall x n s e loc v,
      e x = Some loc ->
      s loc = Some v ->
      eval (Ex_Var x) n (s, e) n (s, e)
  | Ev_Seq : forall e1 e2 n1 n2 n3 s1 s2 s3 env1 env2 env3,
      eval e1 n1 (s1, env1) n2 (s2, env2) ->
      eval e2 n2 (s2, env2) n3 (s3, env3) ->
      eval (Ex_Seq e1 e2) n1 (s1, env1) n3 (s3, env3)
  | Ev_Deref : forall e n1 n2 s1 s2 env1 env2 loc v,
      eval e n1 (s1, env1) n2 (s2, env2) ->
      s2 n2 = Some (V_Mem_Loc loc) ->
      s2 loc = Some v ->
      eval (Ex_Deref e) n1 (s1, env1) n2 (s2, env2)
  | Ev_Ref : forall e n1 n2 s1 s2 env1 env2 loc v,
      eval e n1 (s1, env1) n2 (s2, env2) ->
      s2 loc = Some v ->
      let ptr_val := V_Mem_Loc loc in
      let s3 := update_st s2 n2 ptr_val in
      eval (Ex_Ref e) n1 (s1, env1) (next_loc n2) (s3, env2).

Definition st_ex : st := 
  fun n => match n with 
  | 0 => Some (V_Int 777)
  | 1 => Some (V_Bool true)
  | 2 => Some (V_Mem_Loc 0)
  | _ => None
  end.

Definition env_ex : env :=
  fun s => 
    if String.eqb s "x" then Some 0
    else if String.eqb s "y" then Some 1
    else if String.eqb s "ptr" then Some 2
    else None.

Example eval_var :
  eval (Ex_Var "x") 3 (st_ex, env_ex) 3 (st_ex, env_ex).
Proof.
  apply Ev_Var with (loc := 0) (v := V_Int 777).
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Typing *)
Definition gamma := list (string * type).

Fixpoint check_type (x: string) (g: gamma) : option type :=
  match g with
  | [] => None
  | (y, t) :: rest => if string_dec x y then Some t else check_type x rest
  end.

Inductive is_of_type (g: gamma) : expr -> type -> Prop :=
  | Ty_Asgn : forall x e T,
      check_type x g = Some T ->
      is_of_type g e T ->
      is_of_type g (Ex_Asgn x e) T
  | Ty_Var : forall x T,
      check_type x g = Some T ->
      is_of_type g (Ex_Var x) T
  | Ty_Seq : forall e1 e2 T1 T2,
      is_of_type g e1 T1 ->
      is_of_type g e2 T2 ->
      is_of_type g (Ex_Seq e1 e2) T2
  | Ty_Deref : forall e T,
      is_of_type g e (T_Ptr T) ->
      is_of_type g (Ex_Deref e) T
  | Ty_Ref : forall e T,
      is_of_type g e T ->
      is_of_type g (Ex_Ref e) (T_Ptr T).

Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Definition gamma_ex : gamma := 
  [(X, T_Int); 
   (Y, T_Ptr T_Int);
   (Z, T_Bool)].

Example type_works :
  is_of_type gamma_ex (Ex_Var X) T_Int.
Proof.
  apply Ty_Var. simpl. reflexivity.
Qed.

Example type_works_deref :
  is_of_type gamma_ex (Ex_Deref (Ex_Var Y)) T_Int.
Proof.
  apply Ty_Deref. apply Ty_Var. simpl. reflexivity.
Qed.
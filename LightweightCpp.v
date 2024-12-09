(* working title C++ *)

Require Import String.

Inductive type : Type :=
  | T_Int : type              (* int *)
  | T_Bool : type             (* bool *)
  | T_Class : string -> type  (* C *)
  | T_Ptr : type -> type.     (* T* *)

Inductive expr : Type :=
  | E_Variable : string -> expr                           (* x *)
  | E_Field_Access : expr -> string -> expr               (* e.f *)
  | E_Method_Call : expr -> string -> list expr -> expr   (* e.m(e_bar) *)
  | E_New : string -> list expr -> expr                   (* new C(e_bar) *)
  | E_Cast : type -> expr -> expr                         (* (C)e *)
  | E_Deref : expr -> expr                                (* *e *)
  | E_Ref : expr -> expr                                  (* &e *)
  | E_Seq : expr -> expr -> expr                          (* e;e *)
  | E_Asgn : string -> expr -> expr.                      (* T x := e *)

Inductive method : Type :=
  | Method : string -> list (type * string) -> expr -> method.

Inductive class : Type :=
  | Class : string -> string -> list (type * string) -> list method -> class.

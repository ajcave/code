(* HOMEWORK 5 *)

exception notImplemented

(* -------------------------------------------------------------*)

(* Data-type for MiniML Types *)
datatype typ =                          (* MiniML Types               *)
      Int                               (* T ::= Int                  *)
    | Bool                              (*     | Bool                 *)
    | Arrow of typ * typ                (*     | T1 => T2             *)
    | Product of typ * typ                (*     | T1 x T2              *)
    | TVar of (typ option) ref          (*     | a                    *)


  
(* ------------------------------------------------------------ *)
(* QUESTION 2 : Unification [50 points]                         *) 
(* -------------------------------------------------------------*)

(* unify: typ * typ -> unit 

   unify(T1, T2) = () 
   
   succeeds if T1 and T2 are unifiable, fails otherwise.

   Side Effect: Type variables in T1 and T2 will have been
    updated, s.t. if T1 and T2 are unifiable AFTER unification
    they will denote the "same" type.

*)

exception UnifyError of string

fun occurs (_, Int) = false
  | occurs (_, Bool) = false
  | occurs (s, (Arrow (t1, t2))) =
      occurs (s, t1) orelse occurs (s, t2)
  | occurs (s, Product (t1, t2)) =
      occurs (s, t1) orelse occurs (s, t2)
  | occurs (s, t as TVar (ref NONE)) = (s = t)
  | occurs (s, t as TVar (ref (SOME t'))) =
      (s = t) orelse occurs (s, t')

fun unify (Int, Int) = ()
  | unify (Bool, Bool) = ()
  | unify (Arrow (s1, s2), Arrow (t1, t2)) =
      (unify (s1, t1); unify (s2, t2))
  | unify (Product (s1, s2), Product (t1, t2)) =
      (unify (s1, t1); unify (s2, t2))
  | unify (t, s as TVar (ref (SOME s'))) =
      unify (s', t)
  | unify (s as TVar (ref (SOME s')), t) =
      unify (s', t)
  | unify (s as TVar (s' as ref NONE), t as TVar (ref NONE)) =
      if s = t then () else s' := SOME t
  | unify (s as TVar (s' as ref NONE), t) =
      if occurs (s, t) then
        raise UnifyError "Cannot unify"
      else
        s' := SOME t
  | unify (t, s as TVar (s' as ref NONE)) =
      if occurs (s, t) then
        raise UnifyError "Cannot unify"
      else
        s' := SOME t
  | unify _ = raise UnifyError "Cannot unify";




(* ------------------------------------------------------------ *)
(* Pretty Print Function for printing types                     *)

(* Function to generate fresh names for type variables          *)
local
  val cntr =  ref 0
in
  (* freshVar : unit -> string *)
  fun freshVar () = 
    (cntr:= !cntr + 1; 
     "a"^Int.toString(!cntr))

  fun resetCtr () = 
    cntr := 0
end

(* member: 'a ref * ('b * 'a ref) list -> 'b *)
fun member (r, []) = NONE
  | member (r, ((n,r')::L)) = 
  if r=r' then SOME(n) else member(r, L)

(* *)
fun typToString' (L, Int) = ("int", L)
  | typToString' (L, Bool) = ("bool", L)
  | typToString' (L, Arrow(T,S)) = 
  let val (t, L') = typToString' (L, T)
      val (s, L'') = typToString' (L', S)
  in 
    ("(" ^ t ^ " -> " ^ s ^ ")", L'')
  end 
  | typToString' (L, Product(T,S)) = 
  let val (t, L') = typToString' (L, T)
      val (s, L'') = typToString' (L', S)
  in 
    ("(" ^ t ^ " * " ^ s ^ ")" , L'')
  end 

  | typToString' (L, TVar(r as ref NONE)) = 
  (case member(r, L) of 
     NONE => let val n = freshVar() in (n, ((n,r)::L)) end
   | SOME(n) => (n, L))

  | typToString' (L, TVar(r as ref (SOME(t)))) = 
     typToString'(L, t)
    

fun typToString (t) = 
  let val (s,_) = typToString'([], t) in s end
  
(* ------------------------------------------------------------------------ *)
  
(* ----------------------------------------------------------------- *)
(* Equality testing on types                                         *)
(* equal(t,s) = bool
   
   checks whether type t and s are equal 
  
   equal:tp * tp -> true 
*)
fun equal(Int, Int) = true
  | equal(Bool, Bool) = true
  | equal(Arrow(t1, t2), Arrow(s1, s2)) = 
     equal(t1, s1) andalso equal(t2, s2)
  | equal(Product(t1, t2), Product(s1, s2)) = 
     equal(t1, s1) andalso equal(t2, s2)
  | equal(TVar(a as ref(SOME(t))), s) = 
     equal(t, s)
  | equal(t, TVar(a as ref(SOME(s)))) = 
     equal(t, s)
  | equal(TVar(a as ref(NONE)), TVar(b as ref(NONE))) = 
     a = b
  | equal(t, s) = false

(* -------------------------------------------------------------------------*)
(* Some test cases *)
(* -------------------------------------------------------------------------*)
(* Define some type variables *)
val a1 : (typ option) ref = ref(NONE);
val a2 : (typ option) ref = ref(NONE);

val a3 : (typ option) ref = ref(NONE);
val a4 : (typ option) ref = ref(NONE);

val a5 : (typ option) ref = ref(NONE);
val a6 : (typ option) ref = ref(NONE);

val a7 : (typ option) ref = ref(NONE);
val a8 : (typ option) ref = ref(NONE);

(* Define some types *)
val t1 = Arrow(Product(TVar(a1), TVar(a1)), TVar(a2));
val t2 = Arrow(Product(Int, Int), TVar(a1));

val t3 = Arrow(Product(TVar(a3), TVar(a4)), TVar(a4));
val t4 = Arrow(Product(TVar(a4), TVar(a3)), TVar(a3));

val t5 = Arrow(Product(TVar(a5),TVar(a6)), TVar(a6));
val t6 = Arrow(TVar(a6), TVar(a5));

(* Tests *)
(*
- unify(t1, t2);
val it = () : unit
- typToString t1;
val it = "((int * int) -> int)" : string
- typToString t2;
val it = "((int * int) -> int)" : string
- equal (t1,t2);
val it = true : bool
- 
- unify(t3, t4);
val it = () : unit
- typToString t3;
val it = "((a5 * a5) -> a5)" : string
- typToString t4;
val it = "((a6 * a6) -> a6)" : string
- equal (t3,t4);
val it = true : bool

- unify(t5, t6);

uncaught exception UnifyError
  raised at: /tmp/mlQSBGfN:236.15-236.40
*)

Control.Print.printDepth := 100;

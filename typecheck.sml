structure TypeCheck : sig

(* return true if the first type is a subtype of the second *)
  val subty : Type.typ * Type.typ -> bool

(* for commonSupertype, use the s function from the PDF *)
(* if there isn't a common supertype, return NONE *)
  val commonSupertype : Type.typ * Type.typ -> Type.typ option
 
  val helpertypeof : TypeEnv.env * L23RR.term -> Type.typ 

  val typeof : L23RR.term -> Type.typ

  val selectRecord : string * (string * L23RR.term) list -> L23RR.term
							
end = struct

  structure L = L23RR
  structure T = Type
  structure E = TypeEnv

  open List;
  structure ListMergeSort = ListMergeSort;

  val compareLabels = fn (x : string * 'a, y : string * 'a) => #1 x < #1 y;

  fun subty (Type.Int, t2) = if t2 = Type.Int
                                then true 
                            else  
                                false 

    | subty (Type.Bool, t2) = if t2 = Type.Bool
                                then true 
                            else 
                                false 

    | subty (Type.Unit, t2) = if t2 = Type.Unit
                                then true 
                            else 
                                false 

    | subty (Type.Function (t1, t2), Type.Function (t3, t4)) = 
        if subty (t3, t1) andalso subty (t2, t4)
            then true 
        else 
            false 

    | subty (Type.Function (t1, t2), t3) = raise Fail "functions are only subtypes of functions"

    | subty (Type.Record (records), Type.Record (records2)) = 
        (case ListMergeSort.sort compareLabels records of 
            (label1, t1) :: morerecords => 
                (case ListMergeSort.sort compareLabels records2 
                    of (label2, t2) :: morerecords2 => 
                        if label1 = label2 
                            then if subty (t1, t2) 
                                    then subty (Type.Record (morerecords), Type.Record (morerecords2))
                                else 
                                    raise Fail "same labels have different types"
                        else 
                            subty (Type.Record (morerecords), Type.Record (records2))
                    | [] => true)
            | [] => (case records2 
                        of [] => true 
                        | _ => false))
     
    | subty (Type.Record (records), t2) = raise Fail "records are only subtypes of records"

  fun commonSupertype (typ1, typ2) = if subty (typ1, typ2)
                                        then SOME(typ2)
                                    else 
                                        if subty (typ2, typ1)
                                            then SOME(typ1)
                                        else 
                                            NONE

  fun selectRecord (str, record) = (case record 
                                    of ((string, t1)::morerecords) => 
                                        if str = string 
                                            then t1
                                        else 
                                            selectRecord (str, morerecords)
                                                            
                                    | ([]) => raise Fail "record not found")

  fun helpertypeof (env, L23RR.True) = Type.Bool

    | helpertypeof (env, L23RR.False) = Type.Bool

    | helpertypeof (env, L23RR.Int n) = Type.Int

    | helpertypeof (env, L23RR.Unit) = Type.Unit

    | helpertypeof (env, L23RR.Var s) = (case (TypeEnv.lookup (env, s))
                                            of NONE => raise Fail "variable not assigned"
                                             | SOME(typ) => typ)

    | helpertypeof (env, L23RR.Lam (s, typ, t1)) = 
        Type.Function(typ, helpertypeof (TypeEnv.extend(env, s, typ), t1))

    | helpertypeof (env, L23RR.App (t1, t2)) = (case helpertypeof (env, t1) 
                                                of (Type.Function (t3, t4)) => if subty (helpertypeof (env, t2), t3) 
                                                                                then t4
                                                                              else 
                                                                                raise Fail "function arguments are not subtypes"
                                                | _ => raise Fail "Application needs to take a function")

    | helpertypeof (env, L23RR.Fix (t1)) = 
        (case helpertypeof (env, t1)
            of (Type.Function (typ1, typ2)) => typ1 
            | _ => raise Fail "should be a lambda")


    | helpertypeof (env, L23RR.Let (s, t1, t2)) = helpertypeof (TypeEnv.extend(env, s, helpertypeof (env, t1)), t2)

    | helpertypeof (env, L23RR.Cond (t1, t2, t3)) = if helpertypeof (env, t1) = Type.Bool 
                                                        then (case commonSupertype (helpertypeof (env, t2), helpertypeof (env, t3)) 
                                                                of SOME(t4) => t4
                                                                | NONE => raise Fail "2nd and 3rd cond arguments don't share a type")
                                                    else 
                                                        raise Fail "First conditional argument should be bool"

    | helpertypeof (env, L23RR.Add (t1, t2)) = if helpertypeof (env, t1) = Type.Int andalso helpertypeof (env, t2) = Type.Int
                                                    then Type.Int 
                                                else 
                                                    raise Fail "Add should take two ints"

    | helpertypeof (env, L23RR.Sub (t1, t2)) = if helpertypeof (env, t1) = Type.Int andalso helpertypeof (env, t2) = Type.Int
                                                    then Type.Int 
                                                else 
                                                    raise Fail "Sub should take two ints"

    | helpertypeof (env, L23RR.Mul (t1, t2)) = if helpertypeof (env, t1) = Type.Int andalso helpertypeof (env, t2) = Type.Int
                                                    then Type.Int 
                                                else 
                                                    raise Fail "Mul should take two ints"

    | helpertypeof (env, L23RR.Eq (t1, t2)) = if helpertypeof (env, t1) = Type.Int andalso helpertypeof (env, t2) = Type.Int
                                                    then Type.Bool
                                                else 
                                                    raise Fail "Eq should take two ints"

    | helpertypeof (env, L23RR.LessThan (t1, t2)) = if helpertypeof (env, t1) = Type.Int andalso helpertypeof (env, t2) = Type.Int
                                                    then Type.Bool
                                                else 
                                                    raise Fail "Lessthan should take two ints"
    
    | helpertypeof (env, L23RR.Not (t1)) = if helpertypeof (env, t1) = Type.Bool 
                                                then Type.Bool
                                            else raise Fail "Not takes a boolean"

    | helpertypeof (env, L23RR.Record (records)) = (case records
                                                     of ((str, t1)::morerecords) => 
                                                        (case helpertypeof (env, L23RR.Record (morerecords))
                                                            of (Type.Record (types)) => Type.Record((str, helpertypeof (env, t1)) :: types)
                                                            | _ => raise Fail "should return a record")
                                                     | ([]) => Type.Record ([]))

    | helpertypeof (env, L23RR.Select (string, t1)) = (case helpertypeof (env, t1) 
                                                        of (Type.Record records) => selectRecord (string, records)
                                                        | _ => raise Fail "t1 must be a record")

  fun typeof (t1) = helpertypeof (TypeEnv.empty, t1)


	    
end

(* datatype typ
    = Int
    | Bool
    | Unit
    | Function of typ * typ
    | Record of (string * typ) list
     *)

(* datatype term
    | App of term * term
    | Cond of term * term * term
    | Record of (string * term) list
    | Select of string * term *)
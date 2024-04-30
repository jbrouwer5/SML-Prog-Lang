structure Eval : sig

  val eval : L23RR.term -> L23RR.term
	    
end = struct

  structure L = L23RR

  fun selectRecord (str, record) = (case record 
                                    of ((string, t1)::morerecords) => 
                                        if str = string 
                                            then t1
                                        else 
                                            selectRecord (str, morerecords)
                                                            
                                    | ([]) => raise Fail "record not found")

  fun eval (L23RR.Int n) = L23RR.Int n 

    | eval (L23RR.True) = L23RR.True 

    | eval (L23RR.False) = L23RR.False 

    | eval (L23RR.Unit) = L23RR.Unit 

    | eval (L23RR.Var s) = raise Fail "no free variables in eval"

    | eval (L23RR.Lam (s, typ, t1)) = (L23RR.Lam (s, typ, t1))

    | eval (L23RR.App (t1, t2)) = 
        (case eval t1 
           of (L23RR.Lam (x, typ, t11)) => eval (Subst.subst (x, eval t2, t11))
           | _ => raise Fail "Application takes a lambda")

    | eval (L23RR.Fix t1) = 
        (case eval t1 
            of (L23RR.Lam (f, typ, t11)) => 
                eval (Subst.subst (f, L23RR.Fix (L23RR.Lam (f, typ, t11)), t11))
            | _ => raise Fail "fix only takes a lambda")
    
    | eval (L23RR.Let (s, t1, t2)) = eval (Subst.subst (s, eval t1, t2))
    | eval (L23RR.Cond (t1, t2, t3)) = if (eval t1) = L23RR.True
                                        then eval t2 
                                       else 
                                        eval t3 
    | eval (L23RR.Add (t1, t2)) = (case eval t1
                                    of (L23RR.Int n1) => 
                                        (case eval t2
                                            of (L23RR.Int n2) => L23RR.Int (n1 + n2)
                                            | _ => raise Fail "t2 not an int")
                                    | _ => raise Fail "t1 not an int")

    | eval (L23RR.Sub (t1, t2)) = (case eval t1
                                    of (L23RR.Int n1) => 
                                        (case eval t2
                                            of (L23RR.Int n2) => L23RR.Int (n1 - n2)
                                            | _ => raise Fail "t2 not an int")
                                    | _ => raise Fail "t1 not an int")

    | eval (L23RR.Mul (t1, t2)) = (case eval t1
                                    of (L23RR.Int n1) => 
                                        (case eval t2
                                            of (L23RR.Int n2) => L23RR.Int (n1 * n2)
                                            | _ => raise Fail "t2 not an int")
                                    | _ => raise Fail "t1 not an int")

    | eval (L23RR.Eq (t1, t2)) = (case eval t1
                                    of (L23RR.Int n1) => 
                                        (case eval t2
                                            of (L23RR.Int n2) => 
                                                if n1 = n2
                                                    then L23RR.True 
                                                else 
                                                    L23RR.False
                                            | _ => raise Fail "t2 not an int")
                                    | _ => raise Fail "t1 not an int")

    | eval (L23RR.LessThan (t1, t2)) = (case eval t1
                                    of (L23RR.Int n1) => 
                                        (case eval t2
                                            of (L23RR.Int n2) => 
                                                if n1 < n2
                                                    then L23RR.True 
                                                else 
                                                    L23RR.False
                                            | _ => raise Fail "t2 not an int")
                                    | _ => raise Fail "t1 not an int")

    | eval (L23RR.Not t1) = if (eval t1) = L23RR.True
                                then L23RR.False 
                            else 
                                L23RR.True 

    | eval (L23RR.Record records) = 
        (case records 
            of ((string, t1) :: moreRecords) => 
                (case eval (L23RR.Record (moreRecords))
                    of (L23RR.Record valRecords) => 
                        L23RR.Record ((string, eval t1) :: valRecords)
                    | _ => raise Fail "not a record")
            | [] => L23RR.Record ([]))

    | eval (L23RR.Select (string, record)) = 
        (case eval record  
            of (L23RR.Record (records)) => selectRecord (string, records)
            | _ => raise Fail "not a record")


  (* 
  datatype term
    | Record of (string * term) list
    | Select of string * term
     *)
		 
end

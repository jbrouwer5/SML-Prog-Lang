structure Subst : sig

  val subst : string * L23RR.term * L23RR.term -> L23RR.term
	    
end = struct

  structure L = L23RR

		  
  fun subst (s, t1, L23RR.Var varString) = 
            if varString = s
                then t1
            else 
                L23RR.Var varString

    | subst (x, s, L23RR.App (t1, t2)) = 
        L23RR.App (subst (x, s, t1),
                 subst (x, s, t2))

    | subst (x, s, L23RR.Lam (varString, typ, t1)) = 
            if x = varString
                then L23RR.Lam (varString, typ, t1)
            else 
                L23RR.Lam (varString, typ, subst (x, s, t1))

    | subst (x, s, L23RR.Let (varString, t1, t2)) = 
            if x = varString
                then L23RR.Let (varString, t1, t2)
            else 
                L23RR.Let (varString, subst (x, s, t1), subst (x, s, t2))

    | subst (x, s, L23RR.Int n) = L23RR.Int n 

    | subst (x, s, L23RR.True) = L23RR.True 

    | subst (x, s, L23RR.False) = L23RR.False 

    | subst (x, s, L23RR.Unit) = L23RR.Unit 

    | subst (x, s, L23RR.Fix t1) = L23RR.Fix (subst (x, s, t1))

    | subst (x, s, L23RR.Cond (t1, t2, t3)) = 

        L23RR.Cond (subst (x, s, t1), subst (x, s, t2), subst (x, s, t3))

    | subst (x, s, L23RR.Add (t1, t2)) = L23RR.Add (subst (x, s, t1), subst (x, s, t2))

    | subst (x, s, L23RR.Sub (t1, t2)) = L23RR.Sub (subst (x, s, t1), subst (x, s, t2))

    | subst (x, s, L23RR.Mul (t1, t2)) = L23RR.Mul (subst (x, s, t1), subst (x, s, t2))

    | subst (x, s, L23RR.Eq (t1, t2)) = L23RR.Eq (subst (x, s, t1), subst (x, s, t2))

    | subst (x, s, L23RR.LessThan (t1, t2)) = L23RR.LessThan (subst (x, s, t1), subst (x, s, t2))

    | subst (x, s, L23RR.Not (t1)) = L23RR.Not (subst (x, s, t1))

    | subst (x, s, L23RR.Record (records)) = 
        (case records
            of ((string, t1) :: morerecords) => 
                (case subst (x, s, L23RR.Record (morerecords))
                    of (L23RR.Record (nextrecords)) => L23RR.Record ((string, subst (x, s, t1)) :: nextrecords)
                    | _ => raise Fail "idek")
            | [] => L23RR.Record ([]))

    | subst (x, s, L23RR.Select (string, t1)) = 
        L23RR.Select (string, subst (x, s, t1))

end

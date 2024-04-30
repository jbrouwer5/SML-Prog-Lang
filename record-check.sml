structure RecordCheck : sig

(* check for pairwise distinct labels at all levels of record expressions and record types *)
(* also, reject empty records *)

(* raise an exception if the term doesn't pass the check *)

(* otherwise, return the term as is *)

  val check : L23RR.term -> L23RR.term
  val record_check : string list * L23RR.term -> bool
	    
end = struct

  structure L = L23RR
  
  fun record_check (labels,L23RR.Record (pairs)) = 
    (case pairs
        of ((l1, t1) :: nextpairs) => 
            if (List.exists (fn x => x = l1) labels)
                then raise Fail "duplicate same-level record labels"
            else 
                record_check (l1 :: labels, L23RR.Record (nextpairs))
        | ([]) => true)
    | record_check (_) = raise Fail "record_check only takes a record"


  fun check (L23RR.Lam (str, typ, t1)) = L23RR.Lam (str, typ, check t1)
    | check (L23RR.App (t1, t2)) = L23RR.App (check t1, check t2)
    | check (L23RR.Fix t1) = L23RR.Fix (check t1)
    | check (L23RR.Let (str, t1, t2)) = L23RR.Let (str, check t1, check t2)
    | check (L23RR.Cond (t1, t2, t3)) = L23RR.Cond (check t1, check t2, check t3)
    | check (L23RR.Add (t1, t2)) = L23RR.Add (check t1, check t2)
    | check (L23RR.Sub (t1, t2)) = L23RR.Sub (check t1, check t2)
    | check (L23RR.Mul (t1, t2)) = L23RR.Mul (check t1, check t2)
    | check (L23RR.Eq (t1, t2)) = L23RR.Eq (check t1, check t2)
    | check (L23RR.LessThan (t1, t2)) = L23RR.LessThan (check t1, check t2)
    | check (L23RR.Not t1) = L23RR.Not (check t1)
    | check (L23RR.Record (pairs)) = if record_check ([], L23RR.Record (pairs)) 
            then (case pairs
                    of ((l1, t1)::[]) => L23RR.Record ([(l1, check t1)])
                    | ((l1, t1)::morepairs) => (case check (L23RR.Record (morepairs))
                                                of (L23RR.Record (nextpairs)) => L23RR.Record((l1, check t1)::nextpairs)
                                                | _ => raise Fail "error check failed")
                    | _ => raise Fail "empty record")
        else 
            raise Fail "duplicate same-level record labels"
    (* need to check if this record is valid, then recursively check that each 
    ti in the record is valid  *)
    | check (L23RR.Select (str, t2)) = L23RR.Select (str, check t2)
    | check (t1) = t1

end


(* 
    | Record of (string * term) list
    | Select of string * term *)
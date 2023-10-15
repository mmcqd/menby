module type Connective =
sig
  module U : NBE.Universe
  module Syn :
  sig
    type tele = [
      | `Cell of U.Syn.t * string * tele
      | `Empty
    ]
    val signature : tele -> U.Syn.t
    val structure : (string * U.Syn.t) list -> U.Syn.t
    val proj : string -> U.Syn.t -> U.Syn.t
  end
  module Dom :
  sig
    type tele = [
      | `Cell of U.Dom.t * string * Syn.tele U.Dom.clo
      | `Empty
    ]

    val signature : tele -> U.Dom.t
    val structure : (string * U.Dom.t) list -> U.Dom.t
    val proj : tp:U.Dom.t -> string -> U.Dom.neu -> U.Dom.neu

    val case : U.Dom.t -> ([ 
      | `Structure of (string * U.Dom.t) list
      | `Neu of U.Dom.neu * [`Signature of tele]
    ] -> 'a) -> 'a
  end
end


module Eval (U : NBE.Universe) (Sig : Connective with module U := U) =
struct
  module E = NBE.Eval(U)
  
  class virtual eval = object(self)
    inherit E.eval
    method tele : Sig.Syn.tele -> Sig.Dom.tele = function
      | `Empty -> `Empty
      | `Cell (tp, lbl, tele) -> `Cell (self#tm tp, lbl, U.Dom.clo (self#env ()) tele)
    method signature tele = Sig.Dom.signature (self#tele tele)
    method structure fields = Sig.Dom.structure @@ List.map (fun (lbl, tm) -> lbl, self#tm tm) fields
    method proj_neu neu lbl = 
      let rec go : Sig.Dom.tele -> U.Dom.neu = function
        | `Empty -> failwith "proj_neu"
        | `Cell (tp, lbl', _) when lbl = lbl' -> Sig.Dom.proj ~tp lbl neu
        | `Cell (tp, lbl', tele_clo) -> 
          let tm = U.Dom.embed @@ Sig.Dom.proj ~tp lbl' neu in
          let tele = self#elim_clo tele_clo [tm] self#tele in
          go tele
      in
      go
    method proj lbl x =
      Sig.Dom.case x @@ function
        | `Structure fields -> List.assoc lbl fields
        | `Neu (n, `Signature tele) -> U.Dom.embed @@ self#proj_neu n lbl tele
  end
end


module Quote (U : NBE.Universe) (Sig : Connective with module U := U) =
struct
  module Q = NBE.Quote(U)
  class virtual quote eval = object(self)
    inherit Q.quote(eval)
    method tele =
      let rec go : Sig.Dom.tele -> Sig.Syn.tele = function
      | `Empty -> `Empty
      | `Cell (tp, lbl, tele_clo) ->
        let tele = self#bind tp @@ fun x -> go @@ eval#elim_clo tele_clo [x] eval#tele in
        let tp = self#tp tp in
        `Cell (tp, lbl, tele)
      in
      go
    method signature tele = Sig.Syn.signature (self#tele tele)
    method structure (`Signature tele : [`Signature of _]) (fields : (string * U.Dom.t) list)= 
      let rec go tele fields =
        match tele,fields with
          | `Cell (tp, lbl, tele), (_, tm) :: fields -> 
            let tele = eval#elim_clo tele [tm] eval#tele in
            let tm = self#tm ~tp ~tm in
            (lbl, tm) :: go tele fields
          | `Empty, [] -> [] 
          | _ -> failwith "quote_struct"
        in
        Sig.Syn.structure @@ go tele fields
    
    method proj lbl = Sig.Syn.proj lbl
  end
end

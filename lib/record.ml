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

module Eval (Sig : Connective) (Eval : NBE.Evaluator with module U := Sig.U) =
struct
  module U = Sig.U

  let eval_tele : Sig.Syn.tele -> Sig.Dom.tele = function
    | `Empty -> `Empty
    | `Cell (tp, lbl, tele) -> `Cell (Eval.eval tp, lbl, U.Dom.clo (Eval.Eff.read ()) tele)

  let eval_signature tele = Sig.Dom.signature (eval_tele tele)

  let eval_struct fields = Sig.Dom.structure @@ List.map (fun (lbl, tm) -> lbl, Eval.eval tm) fields


  let rec proj_neu neu lbl : Sig.Dom.tele -> U.Dom.neu = function
    | `Empty -> failwith "proj_neu"
    | `Cell (tp, lbl', _) when lbl = lbl' -> Sig.Dom.proj ~tp lbl neu
    | `Cell (tp, lbl', tele_clo) -> 
      let tm = U.Dom.embed @@ Sig.Dom.proj ~tp lbl' neu in
      let tele = Eval.elim_clo tele_clo tm eval_tele in
      proj_neu neu lbl tele


  let eval_proj lbl x =
    Sig.Dom.case x @@ function
      | `Structure fields -> List.assoc lbl fields
      | `Neu (n, `Signature tele) -> U.Dom.embed @@ proj_neu n lbl tele
end

module Quote (Sig : Connective) (Quote : NBE.Quoter with module U := Sig.U) =
struct
  
  module U = Sig.U
  module SigEval = Eval (Sig) (Quote.Eval)

  let rec quote_tele : Sig.Dom.tele -> Sig.Syn.tele = function
    | `Empty -> `Empty
    | `Cell (tp, lbl, tele_clo) ->
      let tele = Quote.bind tp @@ fun x -> quote_tele @@ Quote.Eval.elim_clo tele_clo x SigEval.eval_tele in
      let tp = Quote.quote_tp tp in
      `Cell (tp, lbl, tele)
  
  let quote_signature tele = Sig.Syn.signature (quote_tele tele)

  let quote_struct (`Signature tele) fields = 
    let rec go tele fields =
      match tele,fields with
        | `Cell (tp, lbl, tele), (_, tm) :: fields -> 
          let tele = Quote.Eval.elim_clo tele tm SigEval.eval_tele in
          let tm = Quote.quote ~tp ~tm in
          (lbl, tm) :: go tele fields
        | `Empty, [] -> [] 
        | _ -> failwith "quote_struct"
      in
      Sig.Syn.structure @@ go tele fields

  let quote_proj lbl x = Sig.Syn.proj lbl x
end
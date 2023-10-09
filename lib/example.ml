open Bwd

module Syn =
struct

  type t =
    | Univ
    | Pi of t * t
    | Lam of t
    | App of t * t
    | Idx of int
    | Sg of t * t
    | Pair of t * t
    | Fst of t
    | Snd of t
    | Signature of tele
    | Structure of (string * t) list
    | Proj of string * t
  
  and tele = [
    | `Cell of t * string * tele
    | `Empty
  ]
end 
module Dom =
struct
  type t =
    | Univ
    | Pi of t * Syn.t clo
    | Lam of Syn.t clo
    | Sg of t * Syn.t clo
    | Pair of t * t   
    | Signature of tele
    | Structure of (string * t) list 
    | Neu of neu

  and tele = [
    | `Cell of t * string * Syn.tele clo
    | `Empty
  ]

  and neu = {hd : head; sp: spine; tp: t}

  and 'a clo = {body : 'a; env : env}

  and head =
    | Lvl of int

  and elim =
    | App of {tm: t; tp: t}
    | Fst
    | Snd
    | Proj of string

  and spine = elim Bwd.t

  and env = t Bwd.t

  let lvl tp l = Neu {hd = Lvl l; sp = Emp; tp}

  let embed n = Neu n
  let clo env body = {body; env}
  let empty () = Emp
  let add x env = Snoc (env, x)
end


module rec U : NBE.Universe with module Syn = Syn and module Dom = Dom =
struct
  module Syn = Syn
  module Dom = Dom
end
and PiConn : Pi.Connective with module U.Syn = Syn and module U.Dom = Dom =
struct
  module U = U
  module Syn = 
  struct
    let pi base fam = Syn.Pi (base, fam)
    let lam x = Syn.Lam x
    let app f x = Syn.App (f, x)
  end
  module Dom =
  struct
    let pi base fam = Dom.Pi (base, fam)
    let lam x = Dom.Lam x
    let app ~tp n (tm,tp')  = Dom.{n with sp = Snoc (n.sp, App {tm; tp = tp'}); tp}
    let case x f =
      match x with
        | Dom.Lam clo -> f (`Lam clo)
        | Dom.Neu ({tp = Dom.Pi (base,fam) ; _} as n) -> f (`Neu (n,`Pi (base,fam)))
        | _ -> failwith "bad pi case"
  end
end
and SigmaConn : Sigma.Connective with module U.Syn = Syn and module U.Dom = Dom =
struct
  module U = U
  module Syn = 
  struct
    let sg base fam = Syn.Sg (base, fam)
    let pair x y = Syn.Pair (x, y)
    let fst x = Syn.Fst x
    let snd x = Syn.Snd x
  end
  module Dom =
  struct
    let sg base fam = Dom.Sg (base, fam)
    let pair x y = Dom.Pair (x, y)
    let fst ~tp n = Dom.{n with sp = Snoc (n.sp, Fst); tp}
    let snd ~tp n = Dom.{n with sp = Snoc (n.sp, Snd); tp}
    let case x f =
      match x with
        | Dom.Pair (x,y) -> f (`Pair (x,y))
        | Dom.Neu ({tp = Dom.Sg (base,fam) ; _} as n) -> f (`Neu (n,`Sg (base,fam)))
        | _ -> failwith "bad sg case"
  end
end
and RecordConn : Record.Connective with module U.Syn = Syn and module U.Dom = Dom =
struct
  module U = U
  module Syn =
  struct
    type tele = Syn.tele
    let signature tele = Syn.Signature tele
    let structure fields = Syn.Structure fields
    let proj lbl x = Syn.Proj (lbl, x)
  end
  module Dom =
  struct
    type tele = Dom.tele
    let signature tele = Dom.Signature tele
    let structure fields = Dom.Structure fields
    let proj ~tp lbl n = Dom.{n with sp = Snoc (n.sp, Proj lbl); tp}
    let case x f =
      match x with
        | Dom.Structure fields -> f (`Structure fields)
        | Dom.Neu ({tp = Dom.Signature tele ; _} as n) -> f (`Neu (n,`Signature tele))
        | _ -> failwith "bad signature case"
  end
end

module rec Eval : NBE.Evaluator with module U := U =
struct
  module Eff = Algaeff.Reader.Make (struct type nonrec env = Dom.env end)

  module PiEval = Pi.Eval (PiConn) (Eval)
  module SigmaEval = Sigma.Eval (SigmaConn) (Eval)
  module SignatureEval = Record.Eval (RecordConn) (Eval)

  let rec eval : Syn.t -> Dom.t = function
    | Idx i -> Bwd.nth (Eff.read ()) i
    | Univ -> Univ
    | Pi (base, fam) -> PiEval.eval_pi base fam
    | Lam body -> PiEval.eval_lam body
    | App (f, arg) -> PiEval.eval_app (eval f) (eval arg)
    | Sg (base, fam) -> SigmaEval.eval_sg base fam
    | Pair (x, y) -> SigmaEval.eval_pair x y
    | Fst x -> SigmaEval.eval_fst (eval x)
    | Snd x -> SigmaEval.eval_snd (eval x)
    | Signature tele -> SignatureEval.eval_signature tele
    | Structure fields -> SignatureEval.eval_struct fields
    | Proj (lbl, x) -> SignatureEval.eval_proj lbl (eval x)


  let elim_clo clo arg f =
    Eff.scope (fun env -> Bwd.Snoc (env,arg)) @@ fun () -> f clo.Dom.body
end

module rec Quote : NBE.Quoter with module U := U and module Eval = Eval =
struct
  module Eval = Eval
  module Eff = Algaeff.Reader.Make (struct type env = int end)
  
  module PiQuote = Pi.Quote (PiConn) (Quote)
  module SigmaQuote = Sigma.Quote (SigmaConn) (Quote)
  module RecordQuote = Record.Quote (RecordConn) (Quote)

  let rec quote ~tp ~tm =
    match tp, tm with
      | Dom.Univ, Dom.Univ -> Syn.Univ
      | Dom.Univ, Dom.Pi (base, fam) -> PiQuote.quote_pi base fam
      | Dom.Pi (base, fam), Dom.Lam body -> PiQuote.quote_lam (`Pi (base, fam)) body
      | Dom.Univ, Dom.Sg (base, fam) -> SigmaQuote.quote_sg base fam
      | Dom.Sg (base, fam), Dom.Pair (x, y) -> SigmaQuote.quote_pair (`Sg (base, fam)) x y
      | Dom.Univ, Dom.Signature tele -> RecordQuote.quote_signature tele
      | Dom.Signature tele, Dom.Structure fields -> RecordQuote.quote_struct (`Signature tele) fields
      | _, Dom.Neu n -> quote_neu n.hd n.sp
      | _ -> failwith ""

  and quote_neu hd sp = BwdLabels.fold_left sp ~f:quote_elim ~init:(quote_hd hd)

  and quote_hd = function
    | Dom.Lvl l -> Syn.Idx (Eff.read() - l - 1)

  and quote_elim hd = function
    | Dom.App {tm; tp} -> PiQuote.quote_neu (tm,tp) hd
    | Dom.Fst -> SigmaQuote.quote_fst hd
    | Dom.Snd -> SigmaQuote.quote_snd hd
    | Dom.Proj lbl -> RecordQuote.quote_proj lbl hd

  let quote_tp tp = quote ~tm:tp ~tp:Dom.Univ

  let bind tp f =
    let arg = Dom.lvl tp (Eff.read ()) in
    Eff.scope (fun l -> l + 1) @@ fun () ->
    f arg
end

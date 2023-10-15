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
    | Nat
    | Zero
    | Suc of t
    | Elim of {mot : t; zero : t; suc : t; scrut : t}
  
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
    | Nat
    | Zero
    | Suc of t
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
    | Elim of {mot : Syn.t clo; zero : t; suc : Syn.t clo}

  and spine = elim Bwd.t

  and env = t Bwd.t

  let lvl tp l = Neu {hd = Lvl l; sp = Emp; tp}

  let embed n = Neu n
  let clo env body = {body; env}
  let empty () = Emp
  let add x env = Snoc (env, x)
end


module U : NBE.Universe with module Syn = Syn and module Dom = Dom =
struct
  module Syn = Syn
  module Dom = Dom
end
module PiConn : Pi.Connective with module U = U =
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
module SigmaConn : Sigma.Connective with module U = U =
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
module RecordConn : Record.Connective with module U = U =
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
module NatConn : Nat.Connective with module U = U =
struct
  module U = U
  module Syn =
  struct
    let nat = Syn.Nat
    let zero = Syn.Zero
    let suc x = Syn.Suc x
    let elim ~mot ~scrut ~zero ~suc = Syn.Elim {mot; scrut; zero; suc}
  end
  module Dom = 
  struct
    let nat = Dom.Nat
    let zero = Dom.Zero
    let suc x = Dom.Suc x
    let elim ~tp ~mot ~zero ~suc n = Dom.{n with sp = Snoc (n.sp, Elim {mot; zero; suc}); tp}
    let case x f =
      match x with
        | Dom.Zero -> f `Zero
        | Dom.Suc x -> f (`Suc x)
        | Dom.Neu ({tp = Dom.Nat ; _} as n) -> f (`Neu (n,`Nat))
        | _ -> failwith "bad nat case"
  end
end

module Eval =
struct
  module Eff = Algaeff.Reader.Make (struct type nonrec env = Dom.env end)

  module PiEval = Pi.Eval (U) (PiConn)
  module RecordEval = Record.Eval (U) (RecordConn)
  module SigmaEval = Sigma.Eval (U) (SigmaConn)
  module NatEval = Nat.Eval (U) (NatConn)
  class eval = object(self)
    inherit PiEval.eval
    inherit RecordEval.eval
    inherit SigmaEval.eval
    inherit NatEval.eval
    method tm : Syn.t -> Dom.t = function
      | Idx i -> Bwd.nth (Eff.read ()) i
      | Univ -> Univ
      | Pi (base, fam) -> self#pi base fam
      | Lam body -> self#lam body
      | App (f, arg) -> self#app (self#tm f) (self#tm arg)
      | Sg (base, fam) -> self#sg base fam
      | Pair (x, y) -> self#pair x y
      | Fst x -> self#fst (self#tm x)
      | Snd x -> self#snd (self#tm x)
      | Signature tele -> self#signature tele
      | Structure fields -> self#structure fields
      | Proj (lbl, x) -> self#proj lbl (self#tm x)
      | Nat -> self#nat
      | Zero -> self#zero
      | Suc x -> self#suc x
      | Elim {mot; scrut; zero; suc} -> self#elim mot (self#tm scrut) zero suc
    method elim_clo = 
      fun clo args f -> Eff.scope (fun env -> Bwd.append env args) @@ fun () -> f clo.Dom.body
    method env () = Eff.read ()
  end
end

module Quote =
struct
  module Eff = Algaeff.Reader.Make (struct type nonrec env = int end)

  module QuotePi = Pi.Quote (U) (PiConn)
  module QuoteSigma = Sigma.Quote (U) (SigmaConn)
  module QuoteRecord = Record.Quote (U) (RecordConn)
  module QuoteNat = Nat.Quote (U) (NatConn)

  class quote (eval : Eval.eval) = object(self)
    inherit QuotePi.quote(eval)
    inherit QuoteSigma.quote(eval)
    inherit QuoteRecord.quote(eval)
    inherit QuoteNat.quote(eval)

    method tm ~tp ~tm = 
      match tp, tm with
        | Univ, Univ -> Syn.Univ
        | Univ, Pi (base, fam) -> self#pi base fam
        | Pi (base, fam), Lam body -> self#lam (`Pi (base, fam)) body
        | Univ, Sg (base, fam) -> self#sg base fam
        | Sg (base, fam), Pair (x, y) -> self#pair (`Sg (base, fam)) x y
        | Univ, Signature tele -> self#signature tele
        | Signature tele, Structure fields -> self#structure (`Signature tele) fields
        | Univ, Nat -> self#nat
        | Nat, Zero -> self#zero `Nat
        | Nat, Suc x -> self#suc x `Nat
        | _, Neu n -> self#neu n.hd n.sp
        | _ -> failwith "ill typed quote"

      method neu hd sp =
        BwdLabels.fold_left sp ~f:self#eliminator ~init:(self#hd hd)
      
      method hd = function
        | Dom.Lvl l -> Syn.Idx (Eff.read () - l - 1)
      
      method eliminator hd = function
        | Dom.App {tm; tp} -> self#app (tm,tp) hd
        | Dom.Fst -> self#fst hd
        | Dom.Snd -> self#snd hd
        | Dom.Proj lbl -> self#proj lbl hd
        | Dom.Elim {mot; zero; suc} -> self#elim ~mot ~zero ~suc ~scrut:hd

    method tp tp = self#tm ~tp ~tm:Univ
    method bind tp f =
      let arg = Dom.lvl tp (Eff.read ()) in
      Eff.scope (fun l -> l + 1) @@ fun () ->
      f arg
  end
end
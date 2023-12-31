
module type Connective =
sig
  module U : NBE.Universe
  module Syn :
  sig
    val sg : U.Syn.t -> U.Syn.t -> U.Syn.t
    val pair : U.Syn.t -> U.Syn.t -> U.Syn.t
    val fst : U.Syn.t -> U.Syn.t
    val snd : U.Syn.t -> U.Syn.t
  end
  module Dom :
  sig
    val sg : U.Dom.t -> U.Syn.t U.Dom.clo -> U.Dom.t
    val pair : U.Dom.t -> U.Dom.t -> U.Dom.t
    val fst : tp:U.Dom.t -> U.Dom.neu -> U.Dom.neu
    val snd : tp:U.Dom.t -> U.Dom.neu -> U.Dom.neu
    val case : U.Dom.t -> ([ 
      | `Pair of U.Dom.t * U.Dom.t
      | `Neu of U.Dom.neu * [`Sg of U.Dom.t * U.Syn.t U.Dom.clo]
    ] -> 'a) -> 'a
  end
end

module Eval (U : NBE.Universe) (Sigma : Connective with module U := U) =
struct
  module E = NBE.Eval(U)
  
  class virtual eval = object(self)
    inherit E.eval
    method sg base fam = Sigma.Dom.sg (self#tm base) (U.Dom.clo (self#env ()) fam)
    method pair x y = Sigma.Dom.pair (self#tm x) (self#tm y)
    method fst p = Sigma.Dom.case p @@ function
      | `Pair (x,_) -> x
      | `Neu (n, `Sg (base,_)) -> U.Dom.embed @@ Sigma.Dom.fst ~tp:base n
    method snd p = Sigma.Dom.case p @@ function
      | `Pair (_,y) -> y
      | `Neu (n, `Sg (_,fam)) -> 
        let x = self#fst (U.Dom.embed n) in
        let tp = self#elim_clo fam [x] self#tm in
        U.Dom.embed @@ Sigma.Dom.snd ~tp n
  end
end

module Quote (U : NBE.Universe) (Sigma : Connective with module U := U) =
struct

  module Q = NBE.Quote(U)

  class virtual quote eval = object(self)
    inherit Q.quote(eval)
    method sg base fam =
      let fam = self#bind base @@ fun x -> self#tp @@ eval#elim_clo fam [x] eval#tm in
      let base = self#tp base in
      Sigma.Syn.sg base fam
    method pair (`Sg (base, fam) : [`Sg of _]) x y =
      let y = self#tm ~tm:y ~tp:(eval#elim_clo fam [x] eval#tm) in
      let x = self#tm ~tm:x ~tp:base in 
      Sigma.Syn.pair x y
    method fst = Sigma.Syn.fst
    method snd = Sigma.Syn.snd
  end
end


(* module Eval (Sigma : Connective) (Eval : NBE.Evaluator with module U := Sigma.U)=
struct
  module U = Sigma.U
  let eval_sg base fam = Sigma.Dom.sg (Eval.eval base) (U.Dom.clo (Eval.Eff.read ()) fam)
  let eval_pair x y = Sigma.Dom.pair (Eval.eval x) (Eval.eval y)
  let eval_fst p =
    Sigma.Dom.case p @@ function
      | `Pair (x,_) -> x
      | `Neu (n, `Sg (base,_)) -> U.Dom.embed @@ Sigma.Dom.fst ~tp:base n
  let eval_snd p =
    Sigma.Dom.case p @@ function
      | `Pair (_,y) -> y
      | `Neu (n, `Sg (_,fam)) -> 
        let x = eval_fst (U.Dom.embed n) in
        let tp = Eval.elim_clo fam [x] Eval.eval in
        U.Dom.embed @@ Sigma.Dom.snd ~tp n
end

module Quote (Sigma : Connective) (Quote : NBE.Quoter with module U := Sigma.U) =
struct
  module U = Sigma.U

  let quote_sg base fam =
    let fam = Quote.bind base @@ fun x -> Quote.quote_tp @@ Quote.Eval.elim_clo fam [x] Quote.Eval.eval in
    let base = Quote.quote_tp base in
    Sigma.Syn.sg base fam
  
  let quote_pair (`Sg (base, fam)) x y =
    let y = Quote.quote ~tm:y ~tp:(Quote.Eval.elim_clo fam [x] Quote.Eval.eval) in
    let x = Quote.quote ~tm:x ~tp:base in 
    Sigma.Syn.pair x y
  
  let quote_fst = Sigma.Syn.fst
  let quote_snd = Sigma.Syn.snd

end *)
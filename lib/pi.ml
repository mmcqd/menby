

module type Connective = 
  sig
    module U : NBE.Universe
    module Syn :
    sig
      val pi : U.Syn.t -> U.Syn.t -> U.Syn.t
      val lam : U.Syn.t -> U.Syn.t
      val app : U.Syn.t -> U.Syn.t -> U.Syn.t
    end
    module Dom :
    sig
      val pi : U.Dom.t -> U.Syn.t U.Dom.clo -> U.Dom.t
      val lam : U.Syn.t U.Dom.clo -> U.Dom.t
      val app : tp:U.Dom.t -> U.Dom.neu -> U.Dom.t * U.Dom.t -> U.Dom.neu
      val case : U.Dom.t -> ([ 
        | `Lam of U.Syn.t U.Dom.clo 
        | `Neu of U.Dom.neu * [`Pi of U.Dom.t * U.Syn.t U.Dom.clo]
      ] -> 'a) -> 'a
    end
  end

module Eval (Pi : Connective) (Eval : NBE.Evaluator with module U := Pi.U) =
struct
  module U = Pi.U
  let eval_pi base fam = Pi.Dom.pi (Eval.eval base) (U.Dom.clo (Eval.Eff.read ()) fam)
  let eval_lam e = Pi.Dom.lam (U.Dom.clo (Eval.Eff.read ()) e)
  let eval_app f arg =
    Pi.Dom.case f @@ function
      | `Lam clo -> Eval.elim_clo clo [arg] Eval.eval
      | `Neu (n, `Pi (base, fam)) -> 
        let tp = Eval.elim_clo fam [arg] Eval.eval in
        U.Dom.embed @@ Pi.Dom.app ~tp n (arg,base)
end

module Quote (Pi : Connective) (Quote : NBE.Quoter with module U := Pi.U) =
struct
  module U = Pi.U
  
  let quote_pi base fam =
    let fam = Quote.bind base @@ fun x -> Quote.quote_tp @@ Quote.Eval.elim_clo fam [x] Quote.Eval.eval in
    let base = Quote.quote_tp base in
    Pi.Syn.pi base fam
  
  let quote_lam (`Pi (base, fam)) body =
    Quote.bind base @@ fun x ->
    let tp = Quote.Eval.elim_clo fam [x] Quote.Eval.eval in
    let body = Quote.Eval.elim_clo body [x] Quote.Eval.eval |> fun tm -> Quote.quote ~tp ~tm in
    Pi.Syn.lam body

  let quote_app (tm,tp) f = Pi.Syn.app f @@ Quote.quote ~tp ~tm
end
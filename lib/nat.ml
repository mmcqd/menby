module type Connective =
sig
  module U : NBE.Universe

  module Syn :
  sig
    val nat : U.Syn.t
    val zero : U.Syn.t
    val suc : U.Syn.t -> U.Syn.t 
    val elim : mot:U.Syn.t -> scrut:U.Syn.t -> zero:U.Syn.t -> suc:U.Syn.t -> U.Syn.t 
  end
  module Dom :
  sig
    val nat : U.Dom.t
    val zero : U.Dom.t
    val suc : U.Dom.t -> U.Dom.t
    val elim : tp:U.Dom.t -> mot:U.Syn.t U.Dom.clo -> zero:U.Dom.t -> suc:U.Syn.t U.Dom.clo -> U.Dom.neu -> U.Dom.neu
    val case : U.Dom.t -> ([
      | `Zero
      | `Suc of U.Dom.t
      | `Neu of U.Dom.neu * [`Nat]
    ] -> 'a) -> 'a
  end
end

module Eval (Nat : Connective) (Eval : NBE.Evaluator with module U := Nat.U) =
struct
  module U = Nat.U
  let eval_nat () = Nat.Dom.nat
  let eval_zero () = Nat.Dom.zero
  let eval_suc n = Nat.Dom.suc (Eval.eval n)
  let eval_elim mot scrut zero suc =
    let mot = U.Dom.clo (Eval.Eff.read ()) mot in
    let suc = U.Dom.clo (Eval.Eff.read ()) suc in
    let zero = Eval.eval zero in
    let rec go n =
      Nat.Dom.case n @@ function
        | `Zero -> zero
        | `Suc n -> Eval.elim_clo suc [n ; go n] Eval.eval
        | `Neu (n, _) -> 
          let tp = Eval.elim_clo mot [U.Dom.embed n] Eval.eval in
          U.Dom.embed @@ Nat.Dom.elim ~tp ~mot ~zero ~suc n
    in
    go scrut
end

module Quote (Nat : Connective) (Quote : NBE.Quoter with module U := Nat.U) =
struct
  module U = Nat.U
  let quote_nat () = Nat.Syn.nat
  let quote_zero () = Nat.Syn.zero
  let quote_suc n = Nat.Syn.suc (Quote.quote ~tp:Nat.Dom.nat ~tm:n)
  let quote_elim ~mot ~scrut ~zero ~suc =
    let zero =
      let mot_zero = Quote.Eval.elim_clo mot [Nat.Dom.zero] Quote.Eval.eval in
      Quote.quote ~tp:mot_zero ~tm:zero
    in
    let suc = Quote.bind Nat.Dom.nat @@ fun x -> 
      let mot_suc = Quote.Eval.elim_clo mot [Nat.Dom.suc x] Quote.Eval.eval in
      Quote.quote ~tp:mot_suc ~tm:(Quote.Eval.elim_clo suc [x ; Nat.Dom.suc x] Quote.Eval.eval) 
    in
    let mot = Quote.bind Nat.Dom.nat @@ fun x -> Quote.quote_tp @@ Quote.Eval.elim_clo mot [x] Quote.Eval.eval in
    Nat.Syn.elim ~mot ~scrut ~zero ~suc
end

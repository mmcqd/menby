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

module Eval (U : NBE.Universe) (Nat : Connective with module U := U) (Eff : Algaeff.Reader.S with type env = U.Dom.env) =
struct

  module E = NBE.Eval(U)

  class virtual eval = object(self)
    inherit E.eval
    method nat = Nat.Dom.nat
    method zero = Nat.Dom.zero
    method suc n = Nat.Dom.suc (self#tm n)
    method elim mot scrut zero suc =
      let mot = U.Dom.clo (Eff.read ()) mot in
      let suc = U.Dom.clo (Eff.read ()) suc in
      let zero = self#tm zero in
      let rec go n =
        Nat.Dom.case n @@ function
          | `Zero -> zero
          | `Suc n -> self#elim_clo suc [n ; go n] self#tm
          | `Neu (n, _) -> 
            let tp = self#elim_clo mot [U.Dom.embed n] self#tm in
            U.Dom.embed @@ Nat.Dom.elim ~tp ~mot ~zero ~suc n
      in
      go scrut
  end
end

module Quote (U : NBE.Universe) (Nat : Connective with module U := U) (Eff : Algaeff.Reader.S) =
struct

  module Q = NBE.Quote(U)
  class virtual quote eval = object(self)
    inherit Q.quote(eval)
    method nat = Nat.Syn.nat
    method zero (_ : [`Nat]) = Nat.Syn.zero
    method suc n (_ : [`Nat]) = Nat.Syn.suc (self#tm ~tm:n ~tp:Nat.Dom.nat)
    method elim ~mot ~scrut ~zero ~suc =
      let zero =
        let mot_zero = eval#elim_clo mot [Nat.Dom.zero] eval#tm in
        self#tm ~tp:mot_zero ~tm:zero
      in
      let suc = self#bind Nat.Dom.nat @@ fun x -> 
        let mot_suc = eval#elim_clo mot [Nat.Dom.suc x] eval#tm in
        self#tm ~tp:mot_suc ~tm:(eval#elim_clo suc [x ; Nat.Dom.suc x] eval#tm) 
      in
      let mot = self#bind Nat.Dom.nat @@ fun x -> self#tp @@ eval#elim_clo mot [x] eval#tm in
      Nat.Syn.elim ~mot ~scrut ~zero ~suc
  end
end
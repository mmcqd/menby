

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


module Eval (U : NBE.Universe) (Pi : Connective with module U := U) (Eff : Algaeff.Reader.S with type env = U.Dom.env) =
struct

  module E = NBE.Eval(U)

  class virtual eval = object(self)
    inherit E.eval
    method pi base fam = Pi.Dom.pi (self#tm base) (U.Dom.clo (Eff.read ()) fam)
    method lam e = Pi.Dom.lam (U.Dom.clo (Eff.read ()) e)
    method app f arg = 
      Pi.Dom.case f @@ function
        | `Lam clo -> self#elim_clo clo [arg] self#tm
        | `Neu (n, `Pi (base, fam)) -> 
          let tp = self#elim_clo fam [arg] self#tm in
          U.Dom.embed @@ Pi.Dom.app ~tp n (arg,base)
  end
end

module Quote (U : NBE.Universe) (Pi : Connective with module U := U) (Eff : Algaeff.Reader.S) =
struct
  module E = NBE.Eval(U)
  module Q = NBE.Quote(U)
  class virtual quote (eval : _ E.t) = object(self)
    inherit Q.quote(eval)
    method pi base fam = 
      let fam = self#bind base @@ fun x -> self#tp @@ eval#elim_clo fam [x] eval#tm in
      let base = self#tp base in
      Pi.Syn.pi base fam
    method lam (`Pi (base, fam) : [`Pi of _]) body =
      self#bind base @@ fun x ->
      let tp = eval#elim_clo fam [x] eval#tm in
      let body = eval#elim_clo body [x] eval#tm |> fun tm -> self#tm ~tp ~tm in
      Pi.Syn.lam body
    method app (tm,tp) f = Pi.Syn.app f @@ self#tm ~tp ~tm
  end
end
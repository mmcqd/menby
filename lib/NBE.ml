module type Universe =
sig
  module Syn :
  sig
    type t
  end
  module Dom :
  sig
    type t
    type neu
    type 'a clo
    type env
    val embed : neu -> t
    val clo : env -> 'a -> 'a clo
    val empty : unit -> env
    val add : t -> env -> env
  end
end

module type Evaluator =
sig
  module U : Universe
  module Eff : Algaeff.Reader.S with type env = U.Dom.env
  val eval : U.Syn.t -> U.Dom.t
  val elim_clo : 'a U.Dom.clo -> U.Dom.t list -> ('a -> 'b) -> 'b
end

module type Quoter = 
sig
  module U : Universe
  module Eval : Evaluator with module U := U
  module Eff : Algaeff.Reader.S
  val quote : tp:U.Dom.t -> tm:U.Dom.t -> U.Syn.t
  val quote_tp : U.Dom.t -> U.Syn.t
  val bind : U.Dom.t -> (U.Dom.t -> 'a) -> 'a
end
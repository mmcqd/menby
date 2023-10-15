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


module Eval (U : Universe) =
struct
  type 'a t = 'a constraint 'a = <
    tm : U.Syn.t -> U.Dom.t;
    elim_clo : 'a 'b. 'a U.Dom.clo -> U.Dom.t list -> ('a -> 'b) -> 'b;
    ..
    >

  class virtual eval = object
    method virtual tm : U.Syn.t -> U.Dom.t
    method virtual elim_clo : 'a 'b. 'a U.Dom.clo -> U.Dom.t list -> ('a -> 'b) -> 'b
    method virtual env : unit -> U.Dom.env
  end
end

module Quote (U : Universe) =
struct
  class virtual quote (_ : _ Eval(U).t) = object
    method virtual tm : tp:U.Dom.t -> tm:U.Dom.t -> U.Syn.t
    method virtual tp : U.Dom.t -> U.Syn.t
    method virtual bind : 'a.U.Dom.t -> (U.Dom.t -> 'a) -> 'a
  end
end

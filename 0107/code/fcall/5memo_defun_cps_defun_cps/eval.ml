open Syntax
open Util
open Memo

(* ステッパ関数 *)
let rec eval (exp : e) (k : k) (k2 : k2) : a = match exp with
  | Val (v) -> apply_in k v k2
  | App (e1, e2) -> eval e2 (FApp2 (e1, k)) k2
  | Op (name, e) -> eval e (FOp (name, k)) k2
  | With (h, e) -> eval e FId (GHandle (h, k, k2))

(* handle 節内の継続を適用する関数 *)
and apply_in (k : k) (v : v) (k2 : k2) : a = match k with
  | FId -> apply_out k2 (Return v)
  | FApp2 (e1, k) -> let v2 = v in
    eval e1 (FApp1 (v2, k)) k2
  | FApp1 (v2, k) -> let v1 = v in
    (match v1 with
     | Fun (x, e) ->
       let redex = App (Val v1, Val v2) in  (* (fun x -> e) v2 *)
       let reduct = subst e [(x, v2)] in    (* e[v2/x] *)
       memo redex reduct (k, k2);
       eval reduct k k2
     | Cont (x, k') ->
       let redex = App (Val v1, Val v2) in               (* k' v2 *)
       let reduct = plug_in_handle (Val v2) (k' FId) in  (* k'[v2] *)
       memo redex reduct (k, k2);
       apply_in (k' k) v2 k2
     | _ -> failwith "type error")
  | FOp (name, k) -> apply_out k2 (OpCall (name, v, k))
  | FCall (k'', h, k') ->
    apply_in k' v (GHandle (h, k'', k2))

(* 全体の継続を適用する関数 *)
and apply_out (k2 : k2) (a : a) : a = match k2 with
  | GId -> a
  | GHandle (h, k, k2) ->
    apply_handler k h a k2

(* handle 節内の実行結果をハンドラで処理する関数 *)
and apply_handler (k : k) (h : h) (a : a) (k2 : k2) : a = match a with
  | Return v ->
    (match h with {return = (x, e)} ->
       let redex = With (h, Val v) in (* with handler{return x -> e} handle v *)
       let reduct = subst e [(x, v)] in  (* e[v/x] *)
       memo redex reduct (k, k2);
       eval reduct k k2)
  | OpCall (name, v, k') ->
    (match search_op name h with
     | None -> apply_out k2 (OpCall (name, v, FCall (k, h, k')))
     | Some (x, y, e) ->
       let redex = (* with handler {name(x; y) -> e} handle k'[(name v)] *)
         With (h, plug_in_handle (Op (name, Val v)) k') in
       let new_var = gen_var_name () in
       let cont_value =
         Cont (new_var, fun k'' -> FCall (k'', h, k')) in
       let reduct = (* e[v/x, k[with h handle k']/y] *)
         subst e [(x, v); (y, cont_value)] in
       memo redex reduct (k, k2);
       eval reduct k k2)

(* 初期継続を渡して実行を始める *)
let stepper (e : e) : a = eval e FId GId

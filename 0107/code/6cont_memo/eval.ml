open Syntax
open Util
open Memo

let rec compose_k2 (k2_in : k2) (h : h) ((k_out, k2_out) : k * k2) : k2 =
  match k2_in with
  | GId -> GHandle (h, k_out, k2_out)
  | GHandle (h', k', k2') -> GHandle (h', k', compose_k2 k2' h (k_out, k2_out))

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
     | Cont (x, cont_value) ->
       let redex = App (Val v1, Val v2) in               (* k' v2 *)
       let reduct = plug_all (Val v2) (cont_value (FId, GId)) in  (* k'[v2] *)
       memo redex reduct (k, k2);
       let (new_k, new_k2) = cont_value (k, k2) in
       apply_in new_k v2 new_k2
     | _ -> failwith "type error")
  | FOp (name, k) -> apply_out k2 (OpCall (name, v, (k, GId)))

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
  | OpCall (name, v, (k', k2')) ->
    (match search_op name h with
     | None ->
       apply_out k2 (OpCall (name, v, (k', compose_k2 k2' h (k, GId))))
     | Some (x, y, e) ->
       let redex = (* with handler {name(x; y) -> e} handle k'[(name v)] *)
         With (h, plug_all (Op (name, Val v)) (k', k2')) in
       let new_var = gen_var_name () in
       let cont_value =
         Cont (new_var, fun (k'', k2'') -> (k', compose_k2 k2' h (k'', k2''))) in
       let reduct = (* e[v/x, k[with h handle k']/y] *)
         subst e [(x, v); (y, cont_value)] in
       memo redex reduct (k, k2);
       eval reduct k k2)

(* 初期継続を渡して実行を始める *)
let stepper (e : e) : a = eval e FId GId

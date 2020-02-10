open Syntax
open Util
open Memo

let rec compose_c2 (c2_in : c2) (h : h) ((k_out, c2_out) : k * c2) : c2 =
  match c2_in with
  | GId -> GHandle (h, k_out, c2_out)
  | GHandle (h', k', c2') -> GHandle (h', k', compose_c2 c2' h (k_out, c2_out))

let rec compose_k2 (k2_in : k2) (h : h) ((k_out, (c2_out, k2_out)) : k * (c2 * k2)) : k2 =
  fun a ->
    let a' = k2_in a in
    apply_handler k_out h a' (c2_out, k2_out)

(* ステッパ関数 *)
and eval (exp : e) (k : k) ((c2, k2) : c2 * k2) : a = match exp with
  | Val (v) -> apply_in k v (c2, k2)
  | App (e1, e2) -> eval e2 (FApp2 (e1, k)) (c2, k2)
  | Op (name, e) -> eval e (FOp (name, k)) (c2, k2)
  | With (h, e) -> eval e FId ((GHandle (h, k, c2)),
                               (fun a -> apply_handler k h a (c2, k2)))

(* handle 節内の継続を適用する関数 *)
and apply_in (k : k) (v : v) ((c2, k2) : c2 * k2) : a = match k with
  | FId -> k2 (Return v)
  | FApp2 (e1, k) -> let v2 = v in
    eval e1 (FApp1 (v2, k)) (c2, k2)
  | FApp1 (v2, k) -> let v1 = v in
    (match v1 with
     | Fun (x, e) ->
       let redex = App (Val v1, Val v2) in
       let reduct = subst e [(x, v2)] in
       memo redex reduct (k, c2);
       eval reduct k (c2, k2)
     | Cont (x, (k', c2'), cont_value) ->
       let redex = App (Val v1, Val v2) in
       let reduct = plug_all (Val v2) (k', c2') in
       memo redex reduct (k, c2);
       let (new_k, (new_c2, new_k2)) = cont_value (k, (c2, k2)) in
       apply_in new_k v2 (new_c2, new_k2)
     | _ -> failwith "type error")
  | FOp (name, k) -> k2 (OpCall (name, v, (k, (GId, (fun a -> a)))))

(* handle 節内の実行結果をハンドラで処理する関数 *)
and apply_handler (k : k) (h : h) (a : a) ((c2, k2) : c2 * k2) : a = match a with
  | Return v ->
    (match h with {return = (x, e)} ->
       let redex = With (h, Val v) in
       let reduct = subst e [(x, v)] in
       memo redex reduct (k, c2);
       eval reduct k (c2, k2))
  | OpCall (name, v, (k', (c2', k2'))) ->
    (match search_op name h with
     | None ->
       k2 (OpCall (name, v, (k', (compose_c2 c2' h (k, GId),
                                  compose_k2 k2' h (k, (c2, fun a -> a))))))
     | Some (x, y, e) ->
       let redex = With (h, plug_all (Op (name, Val v)) (k', c2')) in
       let new_var = gen_var_name () in
       let cont_value =
         Cont (new_var,
               (k', compose_c2 c2' h (FId, GId)),
               (fun (k'', (c2'', k2'')) ->
                  (k', (compose_c2 c2' h (k'', c2''),
                        compose_k2 k2' h (k'', (c2'', k2'')))))) in
       let reduct = subst e [(x, v); (y, cont_value)] in
       memo redex reduct (k, c2);
       eval reduct k (c2, k2))

(* 初期継続を渡して実行を始める *)
let stepper (e : e) : a = eval e FId (GId, (fun a -> a))

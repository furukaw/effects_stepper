open Syntax
open Util
open Memo

let rec compose_k2 (k2_in : k2) (h : h) ((k_out, k2_out) : k * k2) : k2 =
  match k2_in with
  | GId -> GHandle (h, k_out, k2_out)
  | GHandle (h', k', k2') -> GHandle (h', k', compose_k2 k2' h (k_out, k2_out))

(* CPS インタプリタ *)
let rec eval (exp : e) (k : k) (k2 : k2) : a = match exp with
  | Val (v) -> apply_in k v k2
  | App (e1, e2) -> eval e2 (FApp2 (e1, k)) k2
  | Op (name, e) -> eval e (FOp (name, k)) k2
  | With (h, e) -> eval e FId (GHandle (h, k, k2))
 
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
     | Cont (x, (k', k2'), cont_value) ->
       let redex = App (Val v1, Val v2) in  (* (fun x => F[x]) v2 *)
       let reduct = plug_all (Val v2) (k', k2') in
       memo redex reduct (k, k2);
       (cont_value k) v2 k2
     | _ -> failwith "type error")
  | FOp (name, k) ->
    apply_out k2 (OpCall (name, v, (k, GId),
                          (fun v -> fun k2' -> apply_in k v k2')))

and apply_out (k2 : k2) (a : a) : a = match k2 with
  | GId -> a
  | GHandle (h, k, k2) -> apply_handler k h a k2

(* handle 節内の実行結果をハンドラで処理する関数 *)
and apply_handler (k : k) (h : h) (a : a) (k2 : k2) : a = match a with
  | Return v ->                         (* handle 節内が値 v を返したとき *)
    (match h with {return = (x, e)} ->  (* handler {return x -> e, ...} として*)
       let redex = With (h, Val v) in
       let reduct = subst e [(x, v)] in (* e[v/x] に簡約される *)
       memo redex reduct (k, k2);
       eval reduct k k2)                   (* e[v/x] を実行 *)
  | OpCall (name, v, (k', k2'), vk2a) ->
    (match search_op name h with
     | None ->                     (* ハンドラで定義されていない場合、 *)
       apply_out k2 (OpCall (name, v, (k', compose_k2 k2' h (k, GId)),
                             (fun v -> fun k2' ->
                                vk2a v (GHandle (h, k, k2')))))
     | Some (x, y, e) ->           (* ハンドラで定義されている場合、 *)
       let redex = With (h, plug_all (Op (name, Val v)) (k', k2')) in
       let new_var = gen_var_name () in
       let cont_value =
         Cont (new_var,
               (k', compose_k2 k2' h (FId, GId)),
               (fun k'' -> fun v -> fun k2 ->
             vk2a v (GHandle (h, k'', k2)))) in
       let reduct = subst e [(x, v); (y, cont_value)] in
       memo redex reduct (k, k2);
       eval reduct k k2)

(* 初期継続を渡して実行を始める *)
let interpreter (e : e) : a = eval e FId GId

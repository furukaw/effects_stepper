open Syntax
open Util
open Memo

let rec compose_c2 (c2_in : c2) (h : h) ((k_out, c2_out) : c * c2) : c2 =
  match c2_in with
  | GId -> GHandle (h, k_out, c2_out)
  | GHandle (h', k', c2') -> GHandle (h', k', compose_c2 c2' h (k_out, c2_out))

(* ステッパ関数 *)
and eval (exp : e) ((c, k) : c * k) (c2 : c2) : a = match exp with
  | Val (v) -> k v c2
  | App (e1, e2) -> eval e2 (FApp2 (e1, c), (fun v2 c2 ->
      eval e1 (FApp1 (v2, c), (fun v1 c2 ->
          (match v1 with
           | Fun (x, e) ->
             let redex = App (Val v1, Val v2) in
             let reduct = subst e [(x, v2)] in
             memo redex reduct (c, c2);
             eval reduct (c, k) c2
           | Cont (x, (c', c2'), cont_value) ->
             let redex = App (Val v1, Val v2) in
             let reduct = plug_all (Val v2) (c', c2') in
             memo redex reduct (c, c2);
             let ((new_c, new_k), new_c2) = cont_value ((c, k), c2) in
             new_k v2 new_c2
           | _ -> failwith "type error")
        )) c2)) c2
  | Op (name, e) -> eval e (FOp (name, c), (fun v c2 ->
      OpCall (name, v, ((c, k), GId)))) c2
  | With (h, e) ->
    let a = eval e (FId, (fun v c2 -> Return v)) (GHandle (h, c, c2)) in
    apply_handler (c, k) h a c2

(* handle 節内の実行結果をハンドラで処理する関数 *)
and apply_handler ((c, k) : c * k) (h : h) (a : a) (c2 : c2) : a = match a with
  | Return v ->
    (match h with {return = (x, e)} ->
       let redex = With (h, Val v) in
       let reduct = subst e [(x, v)] in
       memo redex reduct (c, c2);
       eval reduct (c, k) c2)
  | OpCall (name, v, ((c', k'), c2')) ->
    (match search_op name h with
     | None ->
       OpCall (name, v,
               ((c', (fun v' c2'' ->
                    let a' = k' v' c2'' in
                    apply_handler (c, k) h a' c2)),
                (compose_c2 c2' h (c, GId))))
     | Some (x, y, e) ->
       let redex = With (h, plug_all (Op (name, Val v)) (c', c2')) in
       let new_var = gen_var_name () in
       let cont_value =
         Cont (new_var,
               (c', compose_c2 c2' h (FId, GId)),
               (fun ((c'', k''), c2'') ->
                  ((c', (fun v' c2''' ->
                       let a' = k' v' c2''' in
                       apply_handler (c'', k'') h a' c2'')),
                    (compose_c2 c2' h (c'', c2''))))) in
       let reduct = subst e [(x, v); (y, cont_value)] in
       memo redex reduct (c, c2);
       eval reduct (c, k) c2)

(* 初期継続を渡して実行を始める *)
let stepper (e : e) : a = eval e (FId, (fun v c2 -> Return v)) GId

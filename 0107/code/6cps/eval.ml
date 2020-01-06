open Syntax
open Util
open Memo

let rec compose_k2 (k2_in : c2) (h : h) ((k_out, k2_out) : c * c2) : c2 =
  match k2_in with
  | GId -> GHandle (h, k_out, k2_out)
  | GHandle (h', k', k2') -> GHandle (h', k', compose_k2 k2' h (k_out, k2_out))

(* CPS インタプリタ *)
let rec eval (exp : e) ((c, k) : c * k) (c2 : c2) : a = match exp with
  | Val (v) -> k v c2
  | App (e1, e2) -> eval e2 (FApp2 (e1, c), (fun v2 c2 ->
      eval e1 (FApp1 (v2, c), (fun v1 c2 ->
          match v1 with
          | Fun (x, e) ->
            let redex = App (Val v1, Val v2) in  (* (fun x -> e) v2 *)
            let reduct = subst e [(x, v2)] in    (* e[v2/x] *)
            memo redex reduct (c, c2);
            eval reduct (c, k) c2
          | Cont (x, (k', k2'), cont_value) ->
            let redex = App (Val v1, Val v2) in  (* (fun x => F[x]) v2 *)
            let reduct = plug_all (Val v2) (k', k2') in
            memo redex reduct (c, c2);
            (cont_value (c, k)) v2 c2
          | _ -> failwith "type error"
        )) c2)) c2
  | Op (name, e) -> eval e (FOp (name, c), (fun v c2 ->
      OpCall (name, v, (c, GId),
              (fun v -> fun c2' -> k v c2')))) c2
  | With (h, e) ->
    let a = eval e (FId, (fun v c2 -> Return v)) (GHandle (h, c, c2)) in
    apply_handler (c, k) h a c2

(* and apply_out (k2 : k2) (a : a) : a = match k2 with
 *   | GId -> a
 *   | GHandle (h, k, k2) -> apply_handler k h a k2 *)

(* handle 節内の実行結果をハンドラで処理する関数 *)
and apply_handler ((c, k) : c * k) (h : h) (a : a) (c2 : c2) : a = match a with
  | Return v ->                         (* handle 節内が値 v を返したとき *)
    (match h with {return = (x, e)} ->  (* handler {return x -> e, ...} として*)
       let redex = With (h, Val v) in
       let reduct = subst e [(x, v)] in (* e[v/x] に簡約される *)
       memo redex reduct (c, c2);
       eval reduct (c, k) c2)                   (* e[v/x] を実行 *)
  | OpCall (name, v, (c', c2'), k') ->
    (match search_op name h with
     | None ->                     (* ハンドラで定義されていない場合、 *)
       OpCall (name, v, (c', compose_k2 c2' h (c, GId)),
               (fun v' -> fun c2'' ->
                  let a' = k' v' (GHandle (h, c, c2'')) in
                  apply_handler (c, k) h a' c2''))
     | Some (x, y, e) ->           (* ハンドラで定義されている場合、 *)
       let redex = With (h, plug_all (Op (name, Val v)) (c', c2')) in
       let new_var = gen_var_name () in
       let cont_value =
         Cont (new_var,
               (c', compose_k2 c2' h (FId, GId)),
               (fun (c'', k'') -> fun v' -> fun c2'' ->
                  let a' = k' v' (GHandle (h, c'', c2'')) in
                  apply_handler (c'', k'') h a' c2)) in
       let reduct = subst e [(x, v); (y, cont_value)] in
       memo redex reduct (c, c2);
       eval reduct (c, k) c2)

(* 初期継続を渡して実行を始める *)
let interpreter (e : e) : a = eval e (FId, (fun v c2 -> Return v)) GId

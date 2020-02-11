open Syntax
open Util
open Memo

(* コンテキスト k2_in の外側にフレーム GHandle (h, k_out, k2_out) を付加する *)
let rec compose_c2 (k2_in : c2) (h : h) ((k_out, k2_out) : c * c2) : c2 =
  match k2_in with
  | GId -> GHandle (h, k_out, k2_out)
  | GHandle (h', k', k2') -> GHandle (h', k', compose_c2 k2' h (k_out, k2_out))

(* CPS ステッパ *)
let rec eval (exp : e) ((c, k) : c * k) (c2 : c2) : a = match exp with
  | Val (v) -> k v c2
  | App (e1, e2) -> eval e2 (FApp2 (e1, c), (fun v2 c2 ->
    eval e1 (FApp1 (v2, c), (fun v1 c2 -> match v1 with
      | Fun (x, e) ->
        let redex = App (Val v1, Val v2) in  (* (fun x -> e) v2 *)
        let reduct = subst e [(x, v2)] in  (* e[v2/x] *)
        memo redex reduct (c, c2); eval reduct (c, k) c2
      | Cont (x, (c', c2'), cont_value) ->
        let redex = App (Val v1, Val v2) in  (* (fun x => c2[c[x]]) v2 *)
        let reduct = plug_all (Val v2) (c', c2') in  (* c2[c[v2]] *)
        memo redex reduct (c, c2); (cont_value (c, k)) v2 c2
      | _ -> failwith "type error")) c2)) c2
  | Op (name, e) -> eval e (FOp (name, c), (fun v c2 ->
    OpCall (name, v, (c, GId), (fun v c2' -> k v c2')))) c2
  | With (h, e) ->
    let a = eval e (FId, (fun v c2 -> Return v)) (GHandle (h, c, c2)) in
    apply_handler (c, k) h a c2

(* handle 節内の実行結果をハンドラで処理する関数 *)
and apply_handler ((c, k) : c * k) (h : h) (a : a) (c2 : c2) : a = match a with
  | Return v -> (match h with {return = (x, e)} ->
    let redex = With (h, Val v) in  (* with hdlr {return x -> e} handle v *)
    let reduct = subst e [(x, v)] in  (* e[v/x] *)
    memo redex reduct (c, c2); eval reduct (c, k) c2)
  | OpCall (name, v, (c', c2'), k') ->
    (match search_op name h with
      | None -> OpCall (name, v, (c', compose_c2 c2' h (c, GId)),
        (fun v' c2'' -> let a' = k' v' (GHandle (h, c, c2'')) in
          apply_handler (c, k) h a' c2''))
      | Some (x, y, e) ->
        (* with handler {name(x; y) -> e} handle c2'[c'[name v]] *)
        let redex = With (h, plug_all (Op (name, Val v)) (c', c2')) in
        let cont_value = Cont (gen_var_name (),
          (c', compose_c2 c2' h (FId, GId)),(fun (c'', k'') v' c2'' ->
        let a' = k' v' (GHandle (h, c'', c2'')) in
        apply_handler (c'', k'') h a' c2)) in
        (* e[v/x, (fun n => with h handle c2'[c'[y]])/y *)
        let reduct = subst e [(x, v); (y, cont_value)] in
        memo redex reduct (c, c2); eval reduct (c, k) c2)

let stepper (e : e) : a = eval e (FId, (fun v c2 -> Return v)) GId
